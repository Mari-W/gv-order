(** * Types, session types, duality, environments (§2.2, Fig. 5 top)

    T, U ::= ∗ | T ⊸ U | T ⊗ U | T ⊕ U | S
    S    ::= ?T.S | !T.S | Close *)

From stdpp Require Import base strings gmap.
From LRGV Require Export Syntax.

Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (T U : ty)              (* T ⊸ U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSum (T U : ty)                (* T ⊕ U *)
  | TBang (T : ty)                 (* □T — unlimited (replicable) values *)
  | TSess (S : sty)
with sty :=
  | SRcv (T : ty) (S : sty)        (* ?T.S *)
  | SSnd (T : ty) (S : sty)        (* !T.S *)
  | SEnd                           (* Close *)
  | SMu (S : sty)                  (* µα.S — binds one session variable *)
  | SVar (a : nat).                (* α — de Bruijn *)

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

(** ** Session-type substitution (§4.3)

    Equi-recursive types identify µα.S with its unfolding S[µα.S/α],
    so the unfolding has to be computed. A session variable may occur
    anywhere a session type may, including inside the payload of a
    communication, so renaming and substitution traverse [ty] and
    [sty] mutually. Term variables and session variables live in
    separate namespaces; [upren] from Syntax.v is reused for the
    latter's shifts. *)

Fixpoint sren_ty (r : nat → nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli T1 U => TLolli (sren_ty r T1) (sren_ty r U)
  | TProd T1 U => TProd (sren_ty r T1) (sren_ty r U)
  | TSum T1 U => TSum (sren_ty r T1) (sren_ty r U)
  | TBang T1 => TBang (sren_ty r T1)
  | TSess s => TSess (sren r s)
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv T s' => SRcv (sren_ty r T) (sren r s')
  | SSnd T s' => SSnd (sren_ty r T) (sren r s')
  | SEnd => SEnd
  | SMu s' => SMu (sren (upren r) s')
  | SVar a => SVar (r a)
  end.

Definition sup (σ : nat → sty) : nat → sty := SVar 0 .: (sren S ∘ σ).

Fixpoint sinst_ty (σ : nat → sty) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli T1 U => TLolli (sinst_ty σ T1) (sinst_ty σ U)
  | TProd T1 U => TProd (sinst_ty σ T1) (sinst_ty σ U)
  | TSum T1 U => TSum (sinst_ty σ T1) (sinst_ty σ U)
  | TBang T1 => TBang (sinst_ty σ T1)
  | TSess s => TSess (sinst σ s)
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv T s' => SRcv (sinst_ty σ T) (sinst σ s')
  | SSnd T s' => SSnd (sinst_ty σ T) (sinst σ s')
  | SEnd => SEnd
  | SMu s' => SMu (sinst (sup σ) s')
  | SVar a => σ a
  end.

(** One-step unrolling: µα.s ↦ s[µα.s/α]. *)
Definition unroll (s : sty) : sty := sinst (SMu s .: SVar) s.

(** ** Head normal form

    Under contractive definitions the leading µ's are finitely many,
    so unfolding until a communication constructor appears terminates.
    [unfoldS] is total: on a non-contractive type such as µα.α it
    simply stops, leaving a µ or a variable in head position, and the
    logical relation's clauses — which all match on the *unfolding* —
    are then unsatisfiable. Ill-formed types therefore need no
    well-formedness side condition; they just relate nothing. *)

Fixpoint mu_depth (s : sty) : nat :=
  match s with SMu s' => S (mu_depth s') | _ => 0 end.

Fixpoint unfoldN (k : nat) (s : sty) : sty :=
  match k with
  | 0 => s
  | S k' => match s with SMu s' => unfoldN k' (unroll s') | _ => s end
  end.

Definition unfoldS (s : sty) : sty := unfoldN (mu_depth s) s.

(** ** Session duality: swaps the direction of communication.

    Duality fixes session variables and commutes with µ; it does not
    descend into payloads, which keeps ?T.S and !T.S carrying the same
    T. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv T s' => SSnd T (dual s')
  | SSnd T s' => SRcv T (dual s')
  | SEnd => SEnd
  | SMu s' => SMu (dual s')
  | SVar a => SVar a
  end.

Lemma dual_involutive s : dual (dual s) = s.
Proof. induction s; simpl; congruence. Qed.

Lemma dual_mu_depth s : mu_depth (dual s) = mu_depth s.
Proof. induction s; simpl; auto. Qed.

(** ** Duality versus unfolding

    CONNECT gives one component c : s and the other c : dual s, so a
    session step on c must unfold both sides compatibly:

      dual (unfoldS s) = unfoldS (dual s)

    This is *not* unconditional. Unrolling substitutes µα.s for α in
    every position, payloads included, whereas duality rewrites tail
    positions and leaves payloads alone. For µα.!(α).α the two orders
    disagree: unrolling then dualizing leaves the payload µα.!(α).α,
    while dualizing then unrolling leaves µα.?(α).α.

    The standard remedy, adopted here, is that a session variable may
    occur only in *tail* position — payload types are closed with
    respect to the enclosing µ's ([tail_only] below). The paper's §4.3
    does not state this; it is what its "all our prior definitions and
    proofs carry over" quietly assumes. *)

Fixpoint sclosed_ty (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli T1 U | TProd T1 U | TSum T1 U => sclosed_ty k T1 ∧ sclosed_ty k U
  | TBang T1 => sclosed_ty k T1
  | TSess s => sclosed k s
  end
with sclosed (k : nat) (s : sty) : Prop :=
  match s with
  | SRcv T s' | SSnd T s' => sclosed_ty k T ∧ sclosed k s'
  | SEnd => True
  | SMu s' => sclosed (S k) s'
  | SVar a => a < k
  end.

(** Session variables occur only to the right of a communication. *)
Fixpoint tail_only (s : sty) : Prop :=
  match s with
  | SRcv T s' | SSnd T s' => sclosed_ty 0 T ∧ tail_only s'
  | SEnd => True
  | SMu s' => tail_only s'
  | SVar _ => True
  end.

Lemma sinst_ext_mut :
  (∀ T σ σ', (∀ a, σ a = σ' a) → sinst_ty σ T = sinst_ty σ' T) ∧
  (∀ s σ σ', (∀ a, σ a = σ' a) → sinst σ s = sinst σ' s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  apply H. intros [|a]; simpl; [done|]. unfold compose. by rewrite H0.
Qed.

Definition sinst_ext := proj2 sinst_ext_mut.
Definition sinst_ty_ext := proj1 sinst_ext_mut.

(** A payload closed under the enclosing µ's is untouched by unrolling. *)
Lemma sinst_closed_mut :
  (∀ T k σ, sclosed_ty k T → (∀ a, a < k → σ a = SVar a) →
            sinst_ty σ T = T) ∧
  (∀ s k σ, sclosed k s → (∀ a, a < k → σ a = SVar a) → sinst σ s = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; try done;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    f_equal; eauto.
  - eapply H; [done|]. intros [|a] Ha; simpl; [done|].
    unfold compose. rewrite H1; [done|lia].
Qed.

Definition sinst_closed := proj2 sinst_closed_mut.
Definition sinst_ty_closed := proj1 sinst_closed_mut.

Lemma dual_sren s : ∀ r, dual (sren r s) = sren r (dual s).
Proof. induction s; intros r; simpl; f_equal; auto. Qed.

Lemma dual_sinst s :
  tail_only s → ∀ σ, dual (sinst σ s) = sinst (dual ∘ σ) (dual s).
Proof.
  induction s as [T s IH|T s IH| |s IH|a]; simpl; intros Htl σ.
  - destruct Htl as [Hc Htl]. rewrite (IH Htl).
    by rewrite !(sinst_ty_closed T 0) by (done || lia).
  - destruct Htl as [Hc Htl]. rewrite (IH Htl).
    by rewrite !(sinst_ty_closed T 0) by (done || lia).
  - done.
  - f_equal. rewrite (IH Htl). apply sinst_ext.
    intros [|a]; simpl; [done|]. unfold compose. by rewrite dual_sren.
  - done.
Qed.

Lemma dual_unroll s : tail_only s → dual (unroll s) = unroll (dual s).
Proof.
  intros Htl. unfold unroll. rewrite (dual_sinst s Htl).
  apply sinst_ext. by intros [|a].
Qed.

(** [tail_only] survives renaming and unrolling, so the iteration in
    [unfoldS] stays inside the well-behaved fragment. *)

Lemma sclosed_sren_mut :
  (∀ T k k' r, sclosed_ty k T → (∀ a, a < k → r a < k') →
               sclosed_ty k' (sren_ty r T)) ∧
  (∀ s k k' r, sclosed k s → (∀ a, a < k → r a < k') →
               sclosed k' (sren r s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    try done; try (split; eauto; fail); eauto.
  eapply H; [done|]. intros [|a] Ha; simpl; [lia|].
  unfold compose. assert (r a < k') by (apply H1; lia). lia.
Qed.

Definition sclosed_ty_sren := proj1 sclosed_sren_mut.

Lemma tail_only_sren s : ∀ r, tail_only s → tail_only (sren r s).
Proof.
  induction s as [T s IH|T s IH| |s IH|a]; simpl; intros r Htl; try done.
  - destruct Htl as [Hc Htl]. split; [|by apply IH].
    eapply sclosed_ty_sren; [done|intros ? Ha; lia].
  - destruct Htl as [Hc Htl]. split; [|by apply IH].
    eapply sclosed_ty_sren; [done|intros ? Ha; lia].
  - by apply IH.
Qed.

Lemma tail_only_sinst s :
  tail_only s → ∀ σ, (∀ a, tail_only (σ a)) → tail_only (sinst σ s).
Proof.
  induction s as [T s IH|T s IH| |s IH|a]; simpl; intros Htl σ Hσ;
    try done.
  - destruct Htl as [Hc Htl]. split; [|by apply IH].
    rewrite (sinst_ty_closed T 0 σ Hc); [done|intros ? Ha; lia].
  - destruct Htl as [Hc Htl]. split; [|by apply IH].
    rewrite (sinst_ty_closed T 0 σ Hc); [done|intros ? Ha; lia].
  - apply IH; [done|]. intros [|b]; simpl; [done|].
    unfold compose. by apply tail_only_sren.
Qed.

Lemma tail_only_unroll s : tail_only s → tail_only (unroll s).
Proof.
  intros Htl. unfold unroll. apply tail_only_sinst; [done|].
  intros [|a]; simpl; [exact Htl|done].
Qed.

Lemma dual_unfoldN k :
  ∀ s, tail_only s → dual (unfoldN k s) = unfoldN k (dual s).
Proof.
  induction k as [|k IH]; intros s Htl; simpl; [done|].
  destruct s as [T s'|T s'| |s'|a]; simpl; try done.
  rewrite <-(dual_unroll s' Htl). apply IH. by apply tail_only_unroll.
Qed.

(** The property CONNECT needs: the two ends of a session unfold in
    lockstep. *)
Lemma dual_unfoldS s : tail_only s → dual (unfoldS s) = unfoldS (dual s).
Proof.
  intros Htl. unfold unfoldS. rewrite dual_mu_depth.
  by apply dual_unfoldN.
Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V)
  | prim_bang U : prim U → prim (TBang U).

(** ** Unlimited types

    The types whose variables admit contraction and weakening. The
    structural rules of Fig. 4 ([lsplit_unl], [lwk_drop]) and the
    relevance conjunct of semantic typing are stated against this
    predicate rather than against a single modality, so that adding
    one is a matter of extending the match below. *)

Definition unlimited (T : ty) : Prop :=
  match T with TBang _ => True | _ => False end.

Lemma unlimited_bang T : unlimited (TBang T).
Proof. done. Qed.

(** ** Session environments: finite maps from channels to session types.

    Splitting Σ = Σ1, Σ2 is disjoint union of the underlying maps. *)

(** A notation rather than a definition, so that stdpp's map lemmas
    apply by keyed unification without unfolding. *)
Notation senv := (gmap chan sty).

Definition senv_split (Σ Σ1 Σ2 : senv) : Prop :=
  Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2.

Lemma senv_split_empty_l Σ : senv_split Σ ∅ Σ.
Proof.
  split; [by rewrite (left_id ∅ (∪))|]. apply map_disjoint_empty_l.
Qed.

Lemma senv_split_comm Σ Σ1 Σ2 : senv_split Σ Σ1 Σ2 → senv_split Σ Σ2 Σ1.
Proof.
  intros [-> Hd]. split; [by apply map_union_comm|done].
Qed.

(** Inserting a fresh binding is the same as unioning a singleton on
    either side. *)
Lemma insert_as_union (Σ : senv) c s :
  c ∉ dom Σ → <[c := s]> Σ = Σ ∪ {[c := s]}.
Proof.
  intros. apply insert_union_singleton_r. by apply not_elem_of_dom.
Qed.

(** Cancellation of insertions of the same fresh key. *)
Lemma insert_fresh_inv (Σ1 Σ2 : senv) c s1 s2 :
  <[c := s1]> Σ1 = <[c := s2]> Σ2 → c ∉ dom Σ1 → c ∉ dom Σ2 →
  s1 = s2 ∧ Σ1 = Σ2.
Proof.
  intros Heq Hc1 Hc2.
  apply not_elem_of_dom in Hc1, Hc2.
  assert (s1 = s2).
  { pose proof (f_equal (λ m, m !! c) Heq) as Hl. cbv beta in Hl.
    rewrite !lookup_insert_eq in Hl. by simplify_eq. }
  split; [done|]. apply map_eq. intros i.
  destruct (decide (i = c)) as [->|Hi]; [congruence|].
  pose proof (f_equal (λ m, m !! i) Heq) as Hl. cbv beta in Hl.
  by rewrite !lookup_insert_ne in Hl.
Qed.

(** Rotating a disjoint union. *)
Lemma map_union_swap (Σa Σn Σb : senv) :
  Σn ##ₘ Σb → (Σa ∪ Σn) ∪ Σb = (Σa ∪ Σb) ∪ Σn.
Proof.
  intros. by rewrite <-!(assoc_L (∪)), (map_union_comm Σn Σb).
Qed.

(** Discharging disjointness of unions/inserts of session environments,
    allowing hypotheses phrased with [dom]. *)
Ltac senv_disj :=
  repeat match goal with
  | H : _ ∉ dom _ |- _ => rewrite not_elem_of_dom in H
  | H : _ ## dom _ |- _ => apply map_disjoint_dom_2 in H
  | H : dom _ ## _ |- _ => symmetry in H; apply map_disjoint_dom_2 in H
  end;
  solve_map_disjoint.

(** Discharging [dom]-membership side conditions. *)
Ltac senv_dom :=
  rewrite ?dom_union_L, ?dom_insert_L, ?dom_singleton_L, ?dom_empty_L;
  set_solver.

(** Proving equalities between unions/inserts of pairwise disjoint
    session environments (permutations, reassociations): turn inserts
    into singleton unions, then decide pointwise. *)
Ltac senv_perm :=
  repeat match goal with
  | H : _ ∉ dom _ |- _ => rewrite not_elem_of_dom in H
  | H : _ ## dom _ |- _ => apply map_disjoint_dom_2 in H
  | H : dom _ ## _ |- _ => symmetry in H; apply map_disjoint_dom_2 in H
  end;
  decompose_map_disjoint;
  apply map_eq; intros ?;
  apply option_eq; intros ?;
  rewrite ?insert_union_singleton_l;
  rewrite ?lookup_union_Some by solve_map_disjoint;
  rewrite ?lookup_singleton_Some, ?lookup_empty;
  naive_solver.

(** ** Type-indexed families of type signatures for constants (Fig. 4)

    fork : (S ⊸ ∗) ⊸ dual S     send : (T ⊗ !T.S) ⊸ S
    recv : ?T.S ⊸ T ⊗ S         clos : Close ⊸ ∗ *)

Inductive konst_ty : konst → ty → Prop :=
  | KTFork S :
      konst_ty KFork (TLolli (TLolli (TSess S) TUnit) (TSess (dual S)))
  | KTRecv T S :
      konst_ty KRecv (TLolli (TSess (SRcv T S)) (TProd T (TSess S)))
  | KTSend T S :
      konst_ty KSend (TLolli (TProd T (TSess (SSnd T S))) (TSess S))
  | KTClos :
      konst_ty KClos (TLolli (TSess SEnd) TUnit).
