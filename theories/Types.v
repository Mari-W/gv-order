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
  | TSess (S : sty)
with sty :=
  | SRcv (T : ty) (S : sty)        (* ?T.S *)
  | SSnd (T : ty) (S : sty)        (* !T.S *)
  | SEnd.                          (* Close *)

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

(** ** Session duality: swaps the direction of communication. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv T s' => SSnd T (dual s')
  | SSnd T s' => SRcv T (dual s')
  | SEnd => SEnd
  end.

Lemma dual_involutive s : dual (dual s) = s.
Proof. induction s; simpl; congruence. Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V).

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
