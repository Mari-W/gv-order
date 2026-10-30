(** * Types, session types, duality, environments (§2.2, Fig. 5 top)

    T, U ::= ∗ | T ⊸^β_λ U | T ⊗ U | T ⊕ U | S@ι | □(∀ιs. T)
    S    ::= ?P.S | !P.S | Close | µα.S | α | α̅      P ::= ∃ιs. T
    β    ::= ι | ⊥        λ ::= ι | ⊤
    ι    ::= (p, b)       p ::= a | point variable | p[b][i]   (no channels) *)

From stdpp Require Import base strings gmap countable.
From LRGV Require Export Syntax.

(** ** Points

    One sort of names (decision N). A point (p, b) is a name p with an
    offset b. A name is a point constant, a point variable (de Bruijn,
    bound by ∀ under □ or by ∃ in a payload), or the slot p[b][i], "the
    i-th point carried at (p, b)". Worlds and environments use ground
    points (constants and their slots), static types also use
    variables. No point mentions a channel, so renaming channels
    changes no type and no world.

    A slot writes the name and offset of its base unpacked, so that
    names are not mutual with points. *)

Inductive pname :=
  | NConst (a : nat)
  | NVar (a : nat)
  | NSlot (p : pname) (b : nat) (i : nat).   (* (p, b)[i] *)

Record point := Pt { pt_name : pname; pt_off : nat }.

Global Instance pname_eq_dec : EqDecision pname.
Proof. solve_decision. Defined.

Global Instance pname_countable : Countable pname.
Proof.
  set (enc := fix go p : gen_tree nat :=
    match p with
    | NConst a => GenNode 1 [GenLeaf a]
    | NVar a => GenLeaf a
    | NSlot p b i => GenNode 0 [go p; GenLeaf b; GenLeaf i]
    end).
  set (dec := fix go t : pname :=
    match t with
    | GenNode 1 [GenLeaf a] => NConst a
    | GenLeaf a => NVar a
    | GenNode 0 [t; GenLeaf b; GenLeaf i] => NSlot (go t) b i
    | _ => NVar 0
    end).
  apply (inj_countable' enc dec).
  intros p; induction p; simpl; congruence.
Qed.

Global Instance point_eq_dec : EqDecision point.
Proof. solve_decision. Defined.

Global Instance point_countable : Countable point.
Proof.
  apply (inj_countable' (λ x, (pt_name x, pt_off x)) (λ '(p, b), Pt p b)).
  by intros [].
Qed.

(** x + n, x[i], the variable a, and the constant a at offset 0. *)
Definition pt_shift (n : nat) (x : point) : point :=
  Pt (pt_name x) (pt_off x + n).
Definition pt_slot (x : point) (i : nat) : point :=
  Pt (NSlot (pt_name x) (pt_off x) i) 0.
Definition pvar (a : nat) : point := Pt (NVar a) 0.
Definition pconst (a : nat) : point := Pt (NConst a) 0.

(** Instantiation of point variables. A name denotes the point at
    offset 0; the offset of a point adds on top. *)
Fixpoint pn_inst (σ : nat → point) (p : pname) : point :=
  match p with
  | NConst a => Pt (NConst a) 0
  | NVar a => σ a
  | NSlot p b i => pt_slot (pt_shift b (pn_inst σ p)) i
  end.

Definition pt_inst (σ : nat → point) (x : point) : point :=
  pt_shift (pt_off x) (pn_inst σ (pt_name x)).

(** Lifting an instantiation under a binder of m point variables. *)
Definition pup (m : nat) (σ : nat → point) : nat → point :=
  λ a, if decide (a < m) then pvar a
       else pt_inst (λ a', pvar (a' + m)) (σ (a - m)).

(** The instantiation that sends the variable i to the i-th point of
    a list, and shifts the variables beyond it down. *)
Definition plist (xs : list point) : nat → point :=
  λ a, match xs !! a with Some x => x | None => pvar (a - length xs) end.

(** The slots x[0], …, x[m-1] of a point. *)
Definition slots (x : point) (m : nat) : list point :=
  (λ i, pt_slot x i) <$> seq 0 m.

(** The constraint of a box (sharp edges 58, 61): facts x ≺ y over the
    ιs and outer points, and a finite set of steps. A step is a list of
    points, the images of ι₀, …, ιₙ₋₁. No steps is the box of 58. *)
Record bcs := BCs { bc_steps : list (list point); bc_facts : list (point * point) }.

(** ** Types

    The arrow carries an upper point β ([None] = ⊥: the call never
    blocks) and a lower point λ ([None] = ⊤: the closure holds
    nothing). □ binds n point variables (∀ only directly under □), a
    payload binds m (∃). Session types are unannotated: the only points
    inside them are those of payloads, all bound by the payload's ∃, so
    point instantiation never enters a session type. *)

Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (ub lb : option point) (T U : ty)
                                   (* T ⊸^ub_lb U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSum (T U : ty)                (* T ⊕ U *)
  | TBox (n : nat) (C : bcs) (ub : option point) (T : ty)
                                   (* □(∀ι₀ … ιₙ₋₁. C.^ub T) — unlimited
                                      (replicable) values; the upper
                                      point ub ([None] = ⊥) lies under
                                      the binder (sharp edges 52); the
                                      constraint C has facts x ≺ y over
                                      the ιs and steps, also under the
                                      binder (sharp edges 58, 61) *)

  | TSess (S : sty) (x : point)   (* S@x *)
with sty :=
  | SRcv (m : nat) (T : ty) (S : sty)
                                   (* ?(∃ι₀ … ιₘ₋₁. T).S *)
  | SSnd (m : nat) (T : ty) (S : sty)
                                   (* !(∃ι₀ … ιₘ₋₁. T).S *)
  | SEnd                           (* Close *)
  | SMu (S : sty)                  (* µα.S — binds one session variable *)
  | SVar (a : nat)                 (* α — de Bruijn *)
  | SVarD (a : nat).               (* α̅ — the dual of what α stands for;
                                      never written in source types, it
                                      enters only through [dual] *)

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

(** ** Point instantiation

    T[σ]: instantiate the free point variables of T. Session types are
    left alone (see above), so this is a plain recursion on [ty]. *)

(** C[σ]: instantiate both sides of every fact of a constraint. *)
Definition pcs_inst (σ : nat → point) (C : list (point * point)) : list (point * point) :=
  (λ p, (pt_inst σ p.1, pt_inst σ p.2)) <$> C.

(** C holds in the order [lt]. *)
Definition pcs_hold (lt : point → point → Prop) (C : list (point * point)) : Prop :=
  ∀ p, p ∈ C → lt p.1 p.2.

(** A box constraint under σ: the steps and the facts. *)
Definition bcs_inst (σ : nat → point) (C : bcs) : bcs :=
  BCs ((λ s : list point, pt_inst σ <$> s) <$> bc_steps C) (pcs_inst σ (bc_facts C)).

(** One step as a substitution of the box's context: the i-th of the m
    ιs goes to the i-th point of s, every other variable stays. A word
    applies its last step first (sharp edges 61). *)
Definition pext (m : nat) (s : list point) : nat → point :=
  λ a, if decide (a < m) then match s !! a with Some x => x | None => pvar a end
       else pvar a.

Fixpoint wsub (m : nat) (w : list (list point)) : nat → point :=
  match w with
  | [] => pvar
  | s :: w' => λ a, pt_inst (pext m s) (wsub m w' a)
  end.

(** C holds at the instance xs: its facts hold at w(xs) for every word w
    over its steps. The empty word gives C[xs/ιs] (sharp edges 58). *)
Definition bcs_hold (lt : point → point → Prop) (C : bcs) (xs : list point) : Prop :=
  ∀ w, Forall (λ s, s ∈ bc_steps C) w →
    pcs_hold lt (pcs_inst (λ a, pt_inst (plist xs) (wsub (length xs) w a)) (bc_facts C)).

Lemma bcs_hold_mono (lt lt' : point → point → Prop) C xs :
  (∀ x y, lt x y → lt' x y) → bcs_hold lt C xs → bcs_hold lt' C xs.
Proof. intros Hl H w Hw p Hp. apply Hl, (H w Hw p Hp). Qed.

Fixpoint pinst_ty (σ : nat → point) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U =>
      TLolli (pt_inst σ <$> ub) (pt_inst σ <$> lb)
        (pinst_ty σ T1) (pinst_ty σ U)
  | TProd T1 U => TProd (pinst_ty σ T1) (pinst_ty σ U)
  | TSum T1 U => TSum (pinst_ty σ T1) (pinst_ty σ U)
  | TBox n C ub T1 =>
      TBox n (bcs_inst (pup n σ) C) (pt_inst (pup n σ) <$> ub) (pinst_ty (pup n σ) T1)
  | TSess s x => TSess s (pt_inst σ x)
  end.

(** T[xs/ιs]: instantiate the ∀ of a □ (or the ∃ of a payload) with a
    list of points. *)
Definition ty_inst (xs : list point) (T : ty) : ty := pinst_ty (plist xs) T.

(** The payload ∃ι₀ … ιₘ₋₁. T at the point x: P[x] = T[x[i]/ιᵢ]. *)
Definition payload_at (m : nat) (T : ty) (x : point) : ty :=
  ty_inst (slots x m) T.

(** ** Heads

    The points at which a value of the type is next used:
    heads(S@ι) = {ι}, heads(T ⊸^β_λ U) = {λ} ∖ {⊤}, ∅ for ∗ and □. *)

Definition opt_heads (o : option point) : gset point :=
  match o with Some x => {[x]} | None => ∅ end.

Fixpoint heads (T : ty) : gset point :=
  match T with
  | TUnit | TBox _ _ _ _ => ∅
  | TLolli _ lb _ _ => opt_heads lb
  | TProd T1 U | TSum T1 U => heads T1 ∪ heads U
  | TSess _ x => {[x]}
  end.

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
  | TLolli ub lb T1 U => TLolli ub lb (sren_ty r T1) (sren_ty r U)
  | TProd T1 U => TProd (sren_ty r T1) (sren_ty r U)
  | TSum T1 U => TSum (sren_ty r T1) (sren_ty r U)
  | TBox n C ub T1 => TBox n C ub (sren_ty r T1)
  | TSess s x => TSess (sren r s) x
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sren_ty r T) (sren r s')
  | SSnd m T s' => SSnd m (sren_ty r T) (sren r s')
  | SEnd => SEnd
  | SMu s' => SMu (sren (upren r) s')
  | SVar a => SVar (r a)
  | SVarD a => SVarD (r a)
  end.

(** ** Polarity flip

    [sflip k] swaps α ↔ α̅ at de Bruijn level k and leaves every other
    variable alone. Duality uses it to fix up the variable a µ binds:
    in [dual (SMu s)] the binder's meaning changes from the protocol
    to its dual, so occurrences that kept denoting the original
    protocol must switch polarity. *)

Fixpoint sflip_ty (k : nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (sflip_ty k T1) (sflip_ty k U)
  | TProd T1 U => TProd (sflip_ty k T1) (sflip_ty k U)
  | TSum T1 U => TSum (sflip_ty k T1) (sflip_ty k U)
  | TBox n C ub T1 => TBox n C ub (sflip_ty k T1)
  | TSess s x => TSess (sflip k s) x
  end
with sflip (k : nat) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sflip_ty k T) (sflip k s')
  | SSnd m T s' => SSnd m (sflip_ty k T) (sflip k s')
  | SEnd => SEnd
  | SMu s' => SMu (sflip (S k) s')
  | SVar a => if decide (a = k) then SVarD a else SVar a
  | SVarD a => if decide (a = k) then SVar a else SVarD a
  end.

(** ** Session duality: swaps the direction of communication.

    Polarized duality after Gay, Thiemann and Vasconcelos, "Duality of
    Session Types: The Final Cut". Payloads are left alone — ?T.S and
    !T.S carry the same T — and variables carry a polarity:

      dual α = α̅    dual α̅ = α    dual (µα.S) = µα. flip₀ (dual S)

    The flip at the binder makes tail occurrences ("continue as
    myself") come out as α again, while payload occurrences come out
    as α̅ and keep denoting the *original* protocol. The naive
    dual α = α is unsound here: for µα.!(α).α, unrolling then
    dualizing gives payload µα.!(α).α, dualizing then unrolling gives
    payload µα.?(α).α. With polarities the two orders agree —
    [dual_unfoldS] below, unconditionally. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv m T s' => SSnd m T (dual s')
  | SSnd m T s' => SRcv m T (dual s')
  | SEnd => SEnd
  | SMu s' => SMu (sflip 0 (dual s'))
  | SVar a => SVarD a
  | SVarD a => SVar a
  end.

(** Substituting under α̅ dualizes the substituend, matching its
    reading as "the dual of what α stands for". *)

Definition sty_up (σ : nat → sty) : nat → sty := SVar 0 .: (sren S ∘ σ).

Fixpoint sinst_ty (σ : nat → sty) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (sinst_ty σ T1) (sinst_ty σ U)
  | TProd T1 U => TProd (sinst_ty σ T1) (sinst_ty σ U)
  | TSum T1 U => TSum (sinst_ty σ T1) (sinst_ty σ U)
  | TBox n C ub T1 => TBox n C ub (sinst_ty σ T1)
  | TSess s x => TSess (sinst σ s) x
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sinst_ty σ T) (sinst σ s')
  | SSnd m T s' => SSnd m (sinst_ty σ T) (sinst σ s')
  | SEnd => SEnd
  | SMu s' => SMu (sinst (sty_up σ) s')
  | SVar a => σ a
  | SVarD a => dual (σ a)
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

(** A type already in head normal form is its own unfolding. *)
Lemma unfoldS_hd u : mu_depth u = 0 → unfoldS u = u.
Proof. unfold unfoldS. by intros ->. Qed.

Lemma mu_depth_rcv m T s : mu_depth (SRcv m T s) = 0.
Proof. done. Qed.

Lemma mu_depth_snd m T s : mu_depth (SSnd m T s) = 0.
Proof. done. Qed.

Lemma mu_depth_end : mu_depth SEnd = 0.
Proof. done. Qed.

(** ** Closedness of session variables *)

Fixpoint sclosed_ty (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U =>
      sclosed_ty k T1 ∧ sclosed_ty k U
  | TBox _ _ _ T1 => sclosed_ty k T1
  | TSess s _ => sclosed k s
  end
with sclosed (k : nat) (s : sty) : Prop :=
  match s with
  | SRcv _ T s' | SSnd _ T s' => sclosed_ty k T ∧ sclosed k s'
  | SEnd => True
  | SMu s' => sclosed (S k) s'
  | SVar a | SVarD a => a < k
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
  - by rewrite H0.
Qed.

Definition sinst_closed := proj2 sinst_closed_mut.
Definition sinst_ty_closed := proj1 sinst_closed_mut.

(** ** The flip algebra

    [sflip k] is an involution, distinct levels commute, and it
    commutes with [dual] — everything a polarity swap should be. *)

Lemma sflip_sflip_mut :
  (∀ T k, sflip_ty k (sflip_ty k T) = T) ∧
  (∀ s k, sflip k (sflip k s) = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto;
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_sflip := proj2 sflip_sflip_mut.

Lemma sflip_comm_mut :
  (∀ T j k, j ≠ k → sflip_ty j (sflip_ty k T) = sflip_ty k (sflip_ty j T)) ∧
  (∀ s j k, j ≠ k → sflip j (sflip k s) = sflip k (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; auto; done);
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_comm := proj2 sflip_comm_mut.

Lemma sflip_dual s : ∀ j, sflip j (dual s) = dual (sflip j s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros j; simpl; f_equal;
    auto.
  - rewrite <-IH. apply sflip_comm. lia.
  - repeat (case_decide; simpl); congruence.
  - repeat (case_decide; simpl); congruence.
Qed.

Lemma sflip_mu_depth s : ∀ k, mu_depth (sflip k s) = mu_depth s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros k; simpl; auto;
    case_decide; done.
Qed.

Lemma dual_involutive s : dual (dual s) = s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; simpl; f_equal; auto.
  rewrite <-sflip_dual, sflip_sflip. exact IH.
Qed.

Lemma dual_mu_depth s : mu_depth (dual s) = mu_depth s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; simpl; auto.
  by rewrite sflip_mu_depth, IH.
Qed.

(** ** Flip versus renaming and substitution

    [sflip k ∘ sren r] pushes through as [sren r ∘ sflip j] when r
    maps exactly the preimage of k to k ([sflip_sren_iff_mut]) and
    vanishes when nothing maps to k ([sflip_sren_ne_mut]). *)

Lemma sflip_sren_iff_mut :
  (∀ T j k r, (∀ a, r a = k ↔ a = j) →
     sflip_ty k (sren_ty r T) = sren_ty r (sflip_ty j T)) ∧
  (∀ s j k r, (∀ a, r a = k ↔ a = j) →
     sflip k (sren r s) = sren r (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. intros [|a]; simpl; unfold compose.
    + split; intros Heq; exfalso; lia.
    + destruct (H0 a) as [Hf Hb]. split; intros Heq.
      * f_equal. apply Hf. lia.
      * f_equal. apply Hb. lia.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
Qed.

Lemma sflip_sren_ne_mut :
  (∀ T k r, (∀ a, r a ≠ k) → sflip_ty k (sren_ty r T) = sren_ty r T) ∧
  (∀ s k r, (∀ a, r a ≠ k) → sflip k (sren r s) = sren r s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. intros [|a]; simpl; [lia|]. unfold compose.
    specialize (H0 a). lia.
  - case_decide; [naive_solver|done].
  - case_decide; [naive_solver|done].
Qed.

Lemma dual_sren s : ∀ r, dual (sren r s) = sren r (dual s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros r; simpl; f_equal;
    auto.
  rewrite IH. apply (proj2 sflip_sren_iff_mut).
  intros [|a]; simpl; unfold compose; split; intros; simplify_eq; done.
Qed.

(** [sflip k] slides through a substitution that is the identity at k
    and flip-invariant elsewhere — [sty_up]-lifted substitutions are. *)

Lemma sflip_sinst_mut :
  (∀ T k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip_ty k (sinst_ty σ T) = sinst_ty σ (sflip_ty k T)) ∧
  (∀ s k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip k (sinst σ s) = sinst σ (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H.
    + simpl. unfold compose. by rewrite H0.
    + intros [|a] Ha; simpl.
      * done.
      * unfold compose.
        rewrite (proj2 sflip_sren_iff_mut _ k) by (intros; lia).
        rewrite H1; [done|lia].
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + rewrite sflip_dual. by rewrite H0.
Qed.

(** ** Duality versus substitution and unfolding

    With polarized variables, duality commutes with substitution on
    the nose — same σ on both sides, no closedness needed. *)

Lemma dual_sinst s : ∀ σ, dual (sinst σ s) = sinst σ (dual s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros σ; simpl; f_equal;
    auto.
  - rewrite IH. apply (proj2 sflip_sinst_mut); [done|].
    intros [|a] Ha; simpl; [lia|]. unfold compose.
    apply (proj2 sflip_sren_ne_mut). intros; lia.
  - apply dual_involutive.
Qed.

(** Flipping the head variable of the term matches dualizing what the
    substitution feeds it. *)

Lemma sinst_sflip_dual_mut :
  (∀ T k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst_ty σ T = sinst_ty σ' (sflip_ty k T)) ∧
  (∀ s k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst σ s = sinst σ' (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H.
    + simpl. unfold compose. by rewrite H0, dual_sren.
    + intros [|a] Ha; simpl; [done|]. unfold compose.
      rewrite H1; [done|lia].
  - case_decide; simplify_eq; simpl.
    + by rewrite H, dual_involutive.
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + by rewrite H.
    + by rewrite H0.
Qed.

(** The two ends of a µ unroll in lockstep: unrolling substitutes
    µα.s at α and dual (µα.s) at α̅, which is exactly the reading
    [dual] gave the two polarities. *)

Lemma dual_unroll s : dual (unroll s) = unroll (sflip 0 (dual s)).
Proof.
  unfold unroll. rewrite dual_sinst.
  apply (proj2 sinst_sflip_dual_mut); [done|].
  intros [|a] Ha; [lia|done].
Qed.

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

Lemma dual_unfoldN k : ∀ s, dual (unfoldN k s) = unfoldN k (dual s).
Proof.
  induction k as [|k IH]; intros s; simpl; [done|].
  destruct s as [m T s'|m T s'| |s'|a|a]; simpl; try done.
  by rewrite IH, dual_unroll.
Qed.

(** The property CONNECT needs: the two ends of a session unfold in
    lockstep — unconditionally, thanks to the polarized dual. *)
Lemma dual_unfoldS s : dual (unfoldS s) = unfoldS (dual s).
Proof. unfold unfoldS. rewrite dual_mu_depth. apply dual_unfoldN. Qed.

(** ** Contractiveness (§4.3, paper-facing)

    Nothing below is threaded through typing or the logical relation:
    every clause reads session types through [unfoldS], and on an
    ill-formed type [unfoldS] leaves a µ or a variable in head
    position, so no clause applies — such types simply relate
    nothing. [unfoldS_form] is §4.3's "as equi-recursive types have
    contractive definitions, we can always determine the top-level
    constructor of a type in finite time", as a theorem. *)

(** The µ-spine ends in a communication constructor. *)
Fixpoint head_ok (s : sty) : Prop :=
  match s with
  | SMu s' => head_ok s'
  | SVar _ | SVarD _ => False
  | _ => True
  end.

Fixpoint contractive_ty (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U =>
      contractive_ty T1 ∧ contractive_ty U
  | TBox _ _ _ T1 => contractive_ty T1
  | TSess s _ => contractive s
  end
with contractive (s : sty) : Prop :=
  match s with
  | SRcv _ T s' | SSnd _ T s' => contractive_ty T ∧ contractive s'
  | SEnd => True
  | SMu s' => head_ok s' ∧ contractive s'
  | SVar _ | SVarD _ => True
  end.

(** A closed contractive type has a well-ended µ-spine. *)
Lemma contractive_head_ok s : sclosed 0 s → contractive s → head_ok s.
Proof. destruct s; simpl; intros; intuition lia. Qed.

Lemma head_ok_sinst s : ∀ σ, head_ok s → head_ok (sinst σ s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros σ Hh; simpl in *;
    auto; destruct Hh.
Qed.

Lemma mu_depth_sinst_hd s :
  ∀ σ, head_ok s → mu_depth (sinst σ s) = mu_depth s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros σ Hh; simpl in *;
    auto; destruct Hh.
Qed.

Lemma head_ok_unfoldN d : ∀ s, head_ok s → head_ok (unfoldN d s).
Proof.
  induction d as [|d IH]; intros s Hh; simpl; [done|].
  destruct s; try done. apply IH, head_ok_sinst, Hh.
Qed.

Lemma unfoldN_head d :
  ∀ s, head_ok s → mu_depth s = d → mu_depth (unfoldN d s) = 0.
Proof.
  induction d as [|d IH]; intros s Hh Hd;
    destruct s as [m T s'|m T s'| |s'|a|a]; simplify_eq/=; try done.
  apply IH; [by apply head_ok_sinst|].
  unfold unroll. by rewrite mu_depth_sinst_hd.
Qed.

Theorem unfoldS_head s : head_ok s → mu_depth (unfoldS s) = 0.
Proof. intros Hh. by eapply unfoldN_head. Qed.

Corollary unfoldS_form s :
  head_ok s →
  (∃ m T s', unfoldS s = SRcv m T s') ∨ (∃ m T s', unfoldS s = SSnd m T s') ∨
  unfoldS s = SEnd.
Proof.
  intros Hh.
  pose proof (unfoldS_head s Hh) as Hd.
  pose proof (head_ok_unfoldN (mu_depth s) s Hh) as Hh'.
  revert Hd Hh'. unfold unfoldS.
  destruct (unfoldN (mu_depth s) s) as [m T s'|m T s'| |s'|a|a];
    simpl; intros Hd Hh'; simplify_eq; eauto 10; destruct Hh'.
Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V)
  | prim_box n C ub U : prim U → prim (TBox n C ub U).

(** ** Unlimited types

    The types whose variables admit contraction and weakening. The
    structural rules of Fig. 4 ([lsplit_unl], [lwk_drop]) and the
    relevance conjunct of semantic typing are stated against this
    predicate rather than against a single modality, so that adding
    one is a matter of extending the match below. *)

Definition unlimited (T : ty) : Prop :=
  match T with TBox _ _ _ _ => True | _ => False end.

Lemma unlimited_box n C ub T : unlimited (TBox n C ub T).
Proof. done. Qed.

(** ** Session environments: finite maps from channels to session
    types at points, c : S@x, x the channel's current point. Each
    action on c moves x to x + 1.
    This is the process-level Σ, one end per channel.

    Splitting Σ = Σ1, Σ2 is disjoint union of the underlying maps. *)

(** A notation rather than a definition, so that stdpp's map lemmas
    apply by keyed unification without unfolding. *)
Notation senv := (gmap chan (sty * point)).

Definition senv_split (Σ Σ1 Σ2 : senv) : Prop :=
  Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2.

(** Σ assigns c a session type whose *unfolding* is u, at point k,
    over the rest Σ1. Every clause of the logical relation that inspects a session
    type goes through this, which is what makes the relation respect
    µα.S = S[µα.S/α] without ever comparing environments up to that
    equation: the stored type is whatever it is, and only its head
    normal form is matched. On a non-contractive type [unfoldS] leaves
    a µ or a variable in head position, so no clause applies. *)
Definition senv_hd (Σ : senv) (c : chan) (u : sty) (k : point)
    (Σ1 : senv) : Prop :=
  ∃ s, Σ = <[c := (s, k)]> Σ1 ∧ unfoldS s = u.

(** The non-recursive case: the type is stored already unfolded. *)
Lemma senv_hd_nf Σ c u k Σ1 :
  mu_depth u = 0 → Σ = <[c := (u, k)]> Σ1 → senv_hd Σ c u k Σ1.
Proof. intros Hd ->. exists u. split; [done|by apply unfoldS_hd]. Qed.

(** An empty environment assigns nothing. *)
Lemma senv_hd_not_empty c u k Σ1 : ¬ senv_hd ∅ c u k Σ1.
Proof. intros (s & Heq & _). exact (insert_non_empty _ _ _ (eq_sym Heq)). Qed.

Lemma senv_hd_dom Σ c u k Σ1 :
  senv_hd Σ c u k Σ1 → dom Σ = {[c]} ∪ dom Σ1.
Proof. intros (s & -> & _). by rewrite dom_insert_L. Qed.

(** Read a head form off a stored type. *)
Lemma senv_hd_intro Σ c s k u Σ1 :
  unfoldS s = u → Σ = <[c := (s, k)]> Σ1 → senv_hd Σ c u k Σ1.
Proof. intros Hu ->. by exists s. Qed.

(** Invert a head-form reading against a known insert: with c fresh
    for both rests, the stored entry is the inserted one. *)
Lemma senv_hd_insert_inv Σ1 c s k u k' Σr :
  c ∉ dom Σ1 → c ∉ dom Σr →
  senv_hd (<[c := (s, k)]> Σ1) c u k' Σr →
  unfoldS s = u ∧ k = k' ∧ Σ1 = Σr.
Proof.
  intros H1 Hr (s0 & Heq & Hu).
  assert ((s, k) = (s0, k')) as [= <- <-].
  { apply (f_equal (lookup c)) in Heq.
    rewrite !lookup_insert_eq in Heq. by simplify_eq. }
  split; [done|]. split; [done|].
  apply map_eq. intros i. destruct (decide (i = c)) as [->|Hi].
  - apply not_elem_of_dom in H1. apply not_elem_of_dom in Hr.
    by rewrite H1, Hr.
  - apply (f_equal (lookup i)) in Heq.
    by rewrite !lookup_insert_ne in Heq by congruence.
Qed.

(** How CONNECT transports a head reading to the peer end: the two
    ends of a session unfold in lockstep ([dual_unfoldS]), and the
    payload agrees on the nose. *)
Lemma unfoldS_dual_rcv s m U s' :
  unfoldS s = SRcv m U s' → unfoldS (dual s) = SSnd m U (dual s').
Proof. intros Hu. by rewrite <-dual_unfoldS, Hu. Qed.

Lemma unfoldS_dual_snd s m U s' :
  unfoldS s = SSnd m U s' → unfoldS (dual s) = SRcv m U (dual s').
Proof. intros Hu. by rewrite <-dual_unfoldS, Hu. Qed.

Lemma unfoldS_dual_end s : unfoldS s = SEnd → unfoldS (dual s) = SEnd.
Proof. intros Hu. by rewrite <-dual_unfoldS, Hu. Qed.

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

(** ** Term-level environments

    Θ may hold both ends of a channel (both carry the channel's one
    name): after [new], and after receiving the other end of a channel
    the thread already holds. An entry of Θ is a channel with one end
    ([One]) or two ([Both]); the two ends of a [Both] are unordered,
    and that they are dual at the same point is stated where it is needed
    ([Coequal.tenv_dual]). The process-level Σ embeds as [One]s. *)

Inductive ends :=
  | One (e : sty * point)
  | Both (e1 e2 : sty * point).

Notation tenv := (gmap chan ends).

Definition tenv_of (Σ : senv) : tenv := One <$> Σ.

(** Entries, one per end, keyed by the channel and a side bit (the
    second end of a [Both] is side [true]). Keys keep two equal ends of
    a channel apart: ready counts entries, not names. *)
Notation ekey := (chan * bool)%type.

Definition tenv_entry (Θ : tenv) (k : ekey) : option (sty * point) :=
  match Θ !! k.1, k.2 with
  | Some (One e), false => Some e
  | Some (Both e _), false => Some e
  | Some (Both _ e), true => Some e
  | _, _ => None
  end.

(** head(c : S@x) = x. *)
Definition entry_head (k : ekey) (e : sty * point) : point := e.2.

Definition ends_heads (c : chan) (o : ends) : gset point :=
  match o with
  | One e => {[e.2]}
  | Both e1 e2 => {[e1.2; e2.2]}
  end.

Definition tenv_heads (Θ : tenv) : gset point :=
  map_fold (λ c o X, ends_heads c o ∪ X) ∅ Θ.

Definition senv_heads (Σ : senv) : gset point := tenv_heads (tenv_of Σ).

(** Θ = Θ1, c : e. *)
Definition tenv_ext (Θ1 : tenv) (c : chan) (e : sty * point) (Θ : tenv)
    : Prop :=
  (Θ1 !! c = None ∧ Θ = <[c := One e]> Θ1) ∨
  (∃ e', Θ1 !! c = Some (One e') ∧
     (Θ = <[c := Both e e']> Θ1 ∨ Θ = <[c := Both e' e]> Θ1)).

(** The term-level [senv_hd]: Θ = Θ1, c : S@x with S unfolding to u. *)
Definition tenv_hd (Θ : tenv) (c : chan) (u : sty) (k : point) (Θ1 : tenv)
    : Prop :=
  ∃ s, tenv_ext Θ1 c (s, k) Θ ∧ unfoldS s = u.

(** Θ = Θ1, Θ2: pointwise, and only defined where the overlap is one
    end on each side. *)
Inductive ends_join : option ends → option ends → option ends → Prop :=
  | ends_join_none : ends_join None None None
  | ends_join_l o : ends_join (Some o) None (Some o)
  | ends_join_r o : ends_join None (Some o) (Some o)
  | ends_join_both e1 e2 :
      ends_join (Some (One e1)) (Some (One e2)) (Some (Both e1 e2))
  | ends_join_both' e1 e2 :
      ends_join (Some (One e1)) (Some (One e2)) (Some (Both e2 e1)).

Definition tenv_join (Θ Θ1 Θ2 : tenv) : Prop :=
  ∀ c, ends_join (Θ1 !! c) (Θ2 !! c) (Θ !! c).

Lemma tenv_join_dom Θ Θ1 Θ2 :
  tenv_join Θ Θ1 Θ2 → dom Θ = dom Θ1 ∪ dom Θ2.
Proof.
  intros H. apply set_eq. intros c. rewrite elem_of_union, !elem_of_dom.
  pose proof (H c) as Hc.
  destruct (Θ1 !! c), (Θ2 !! c), (Θ !! c); inversion Hc;
    split; intros; try (by left); try (by right); try done;
    destruct_or?; by destruct select (is_Some None).
Qed.

Lemma tenv_join_empty Θ : tenv_join Θ ∅ ∅ → Θ = ∅.
Proof.
  intros H. apply map_empty. intros c. specialize (H c).
  rewrite !lookup_empty in H. by inversion H.
Qed.

(** ** Type-indexed families of type signatures for constants
    (§9)

    new    : ∗ ⊸^⊥_⊤ S@ι ⊗ dual S@ι
    spawn  : (∗ ⊸^β_λ ∗) ⊸^⊥_⊤ ∗
    send   : (P[ι] ⊗ (!P.S)@ι) ⊸^ι_⊤ S@(ι+1)     {ι} ≺ heads(P[ι])
    recv   : (?P.S)@ι ⊸^ι_⊤ P[ι] ⊗ S@(ι+1)
    close  : Close@ι ⊸^ι_⊤ ∗
    link   : S@ι ⊗ dual S@ι′ ⊸^ι_⊤ ∗       ι ≡ ι′
    force  : □(∀ιs. C.^u T) ⊸^{u[ιs′/ιs]}_⊤ T[ιs′/ιs]   C[ιs′/ιs]   (52, 58)

    The side conditions on points are read in an order given as two
    relations: the world G generates for typing, a world W for the
    logical relation. Freshness of ι in [new] is a typing condition
    (Typing.v). [pk] says which points the order knows: the point of
    [new] must be one, so that the created point can be aliased to it
    (sharp edges 49). force asks its instance known and the box's
    constraint at every word of the instance (sharp edges 61). *)

Inductive konst_ty (peq plt : point → point → Prop) (pk : point → Prop)
    : konst → ty → Prop :=
  | KTNew S x :
      pk x →
      konst_ty peq plt pk KNew
        (TLolli None None TUnit (TProd (TSess S x) (TSess (dual S) x)))
  | KTSpawn ub lb :
      konst_ty peq plt pk KSpawn
        (TLolli None None (TLolli ub lb TUnit TUnit) TUnit)
  | KTSend m T S x :
      (∀ h, h ∈ heads (payload_at m T x) → plt x h) →
      konst_ty peq plt pk KSend
        (TLolli (Some x) None
           (TProd (payload_at m T x) (TSess (SSnd m T S) x))
           (TSess S (pt_shift 1 x)))
  | KTRecv m T S x :
      konst_ty peq plt pk KRecv
        (TLolli (Some x) None
           (TSess (SRcv m T S) x)
           (TProd (payload_at m T x) (TSess S (pt_shift 1 x))))
  | KTClos x :
      konst_ty peq plt pk KClos (TLolli (Some x) None (TSess SEnd x) TUnit)
  | KTLink S x x' :
      peq x x' →
      konst_ty peq plt pk KLink
        (TLolli (Some x) None (TProd (TSess S x) (TSess (dual S) x')) TUnit)
  | KTForce n C ub T xs :
      length xs = n → bcs_hold plt C xs → Forall pk xs →
      konst_ty peq plt pk KForce
        (TLolli (pt_inst (plist xs) <$> ub) None (TBox n C ub T) (ty_inst xs T)).

