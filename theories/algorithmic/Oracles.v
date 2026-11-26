(** * The oracles of the algorithmic judgment

    The algorithm is decidable relative to the theory of constraints and
    the theory of session types. [Oracles] collects the decision
    procedures it takes as parameters. None of them is an axiom: every
    theorem of algorithmic/Decide.v is stated for an arbitrary instance.

    - [o_slt] decides entailment Γ ⊢_W x ≺ y ([slt]).
    - [o_hold] decides that a constraint holds at an instance
      ([hold_at]), the premise of E-Force, E-Pack and Sub-Ex.
    - [o_cons] decides the bridge condition of E-Open ([cons_open]).
    - [o_new] decides the creation premise of E-New ([new_ok]).
    - [o_bcs] decides equality of constraints. A constraint is a
      predicate on facts, so this is the one place where types are
      compared as data.
    - [o_sequiv] and [o_ssub] decide equivalence and subtyping of
      context-free session types.

    For finite constraints the first five reduce to finite searches
    (.claude/notes/redesign/algorithmic-plan.md, section 4). From them
    this file derives decision procedures for equality of types, for the
    scoping and readiness premises and for subtyping ([tsub_dec]). *)

From GV Require Export algorithmic.Algo.

(** One class per oracle. A field separator would clash with the
    notation of the typing judgment. *)
Class SltOracle := o_slt W Γ x y :: Decision (slt W Γ x y).
Class HoldOracle := o_hold W Γ C xs :: Decision (hold_at W Γ C xs).
Class ConsOracle := o_cons W Γ m C :: Decision (cons_open W Γ m C).
Class NewOracle := o_new N W Γ C :: Decision (new_ok N W Γ C).
Class BcsOracle := o_bcs (C C' : bcs) :: Decision (C = C').
Class SequivOracle := o_sequiv s r :: Decision (sequiv s r).
Class SsubOracle := o_ssub s r :: Decision (ssub s r).

Global Instance frest_eq_dec : EqDecision frest.
Proof. solve_decision. Defined.

Global Instance fle_dec a b : Decision (fle a b).
Proof. destruct a, b; simpl; apply _. Defined.

Global Instance lgt_dec N a m : Decision (lgt N a m).
Proof. unfold lgt. destruct N; [apply fle_dec|apply _]. Defined.

Global Instance tsum_ok_dec N m1 m2 : Decision (tsum_ok N m1 m2).
Proof. unfold tsum_ok. apply fle_dec. Defined.

Global Instance idle_dec S : Decision (idle S).
Proof.
  unfold idle. destruct (unfoldS S); try (right; discriminate). by left.
Defined.

Global Instance unlimited_dec T : Decision (unlimited T).
Proof. destruct T; simpl; apply _. Defined.

Global Instance pt_pscoped_dec k x : Decision (pt_pscoped k x).
Proof.
  unfold pt_pscoped. destruct (pt_root x) as [a|a|p b κ].
  - left. intros a' [=].
  - destruct (decide (a < k)); [left; intros a' [= <-]; done|right; intros H; apply n, H; done].
  - left. intros a' [=].
Defined.

Fixpoint pscoped_dec k T {struct T} : Decision (pscoped k T)
with sscoped_dec s {struct s} : Decision (sscoped s).
Proof.
  - destruct T as [|ub lb c T1 U a|T1 U|T1 U|n kk C ub c U|s x a mt|lb n C T1]; simpl.
    + left. done.
    + assert (Decision (∀ x, ub = UPt x → pt_pscoped k x)).
      { destruct ub as [|x|]; [left; by intros ? ?| |left; by intros ? ?].
        destruct (decide (pt_pscoped k x)); [left; by intros ? [= <-]|right; intros Hc; auto]. }
      assert (Decision (∀ x, lb = LPt x → pt_pscoped k x)).
      { destruct lb as [| |x]; [left; by intros ? ?|left; by intros ? ?|].
        destruct (decide (pt_pscoped k x)); [left; by intros ? [= <-]|right; intros Hc; auto]. }
      pose proof (pscoped_dec k T1). pose proof (pscoped_dec k U). apply _.
    + pose proof (pscoped_dec k T1). pose proof (pscoped_dec k U). apply _.
    + pose proof (pscoped_dec k T1). pose proof (pscoped_dec k U). apply _.
    + assert (Decision (∀ x, ub = Some x → pt_pscoped (n + k) x)).
      { destruct ub as [x|]; [|left; by intros ? ?].
        destruct (decide (pt_pscoped (n + k) x)); [left; by intros ? [= <-]|right; intros Hc; auto]. }
      pose proof (pscoped_dec (n + k) U). apply _.
    + pose proof (sscoped_dec s). apply _.
    + assert (Decision (∀ x, lb = LPt x → pt_pscoped k x)).
      { destruct lb as [| |x]; [left; by intros ? ?|left; by intros ? ?|].
        destruct (decide (pt_pscoped k x)); [left; by intros ? [= <-]|right; intros Hc; auto]. }
      pose proof (pscoped_dec (n + k) T1). apply _.
  - destruct s as [m T|m T| |s'|a|a| |s1 s2|s1 s2|s1 s2]; simpl.
    + apply pscoped_dec.
    + apply pscoped_dec.
    + left. done.
    + apply sscoped_dec.
    + left. done.
    + left. done.
    + left. done.
    + pose proof (sscoped_dec s1). pose proof (sscoped_dec s2). apply _.
    + pose proof (sscoped_dec s1). pose proof (sscoped_dec s2). apply _.
    + pose proof (sscoped_dec s1). pose proof (sscoped_dec s2). apply _.
Defined.
Global Existing Instance pscoped_dec.
Global Existing Instance sscoped_dec.

Section oracles.
  Context `{SltOracle, HoldOracle, BcsOracle, SequivOracle, SsubOracle}.

  Fixpoint ty_eq_dec (T U : ty) {struct T} : Decision (T = U)
  with sty_eq_dec (s r : sty) {struct s} : Decision (s = r).
  Proof.
    - refine (match T, U with
        | TUnit, TUnit => left eq_refl
        | TLolli ub lb c T1 U1 a, TLolli ub' lb' c' T1' U1' a' =>
            cast_if_and6 (decide (ub = ub')) (decide (lb = lb')) (decide (c = c'))
              (ty_eq_dec T1 T1') (ty_eq_dec U1 U1') (decide (a = a'))
        | TProd T1 U1, TProd T1' U1' => cast_if_and (ty_eq_dec T1 T1') (ty_eq_dec U1 U1')
        | TSum T1 U1, TSum T1' U1' => cast_if_and (ty_eq_dec T1 T1') (ty_eq_dec U1 U1')
        | TBox n k C ub c U1, TBox n' k' C' ub' c' U1' =>
            cast_if_and6 (decide (n = n')) (decide (k = k')) (decide (C = C'))
              (decide (ub = ub')) (decide (c = c')) (ty_eq_dec U1 U1')
        | TSess s x a m, TSess s' x' a' m' =>
            cast_if_and4 (sty_eq_dec s s') (decide (x = x')) (decide (a = a')) (decide (m = m'))
        | TEx lb n C T1, TEx lb' n' C' T1' =>
            cast_if_and4 (decide (lb = lb')) (decide (n = n')) (decide (C = C')) (ty_eq_dec T1 T1')
        | _, _ => right _
        end); clear ty_eq_dec sty_eq_dec; abstract (try congruence; intros [=]; congruence).
    - refine (match s, r with
        | SRcv m T, SRcv m' T' => cast_if_and (decide (m = m')) (ty_eq_dec T T')
        | SSnd m T, SSnd m' T' => cast_if_and (decide (m = m')) (ty_eq_dec T T')
        | SEnd, SEnd => left eq_refl
        | SMu s1, SMu s1' => cast_if (sty_eq_dec s1 s1')
        | SVar a, SVar a' => cast_if (decide (a = a'))
        | SVarD a, SVarD a' => cast_if (decide (a = a'))
        | SSkip, SSkip => left eq_refl
        | SSeq s1 s2, SSeq s1' s2' => cast_if_and (sty_eq_dec s1 s1') (sty_eq_dec s2 s2')
        | SPlus s1 s2, SPlus s1' s2' => cast_if_and (sty_eq_dec s1 s1') (sty_eq_dec s2 s2')
        | SWith s1 s2, SWith s1' s2' => cast_if_and (sty_eq_dec s1 s1') (sty_eq_dec s2 s2')
        | _, _ => right _
        end); clear ty_eq_dec sty_eq_dec; abstract (try congruence; intros [=]; congruence).
  Defined.
  Global Existing Instance ty_eq_dec.
  Global Existing Instance sty_eq_dec.

  Global Instance tentry_eq_dec : EqDecision tentry.
  Proof. solve_decision. Defined.

  Global Instance sle_dec W Γ x y : Decision (sle W Γ x y).
  Proof. unfold sle. apply _. Defined.

  Global Instance rest_below_dec W Γ x r : Decision (rest_below W Γ x r).
  Proof. destruct r; simpl; apply _. Defined.

  Global Instance ub_below_s_dec W Γ ub F : Decision (ub_below_s W Γ ub F).
  Proof.
    destruct ub as [x|]; simpl; [|apply _].
    assert (Decision (∀ y, y ∈ F.1 → slt W Γ x y)).
    { destruct (decide (set_Forall (λ y, slt W Γ x y) F.1)) as [Hf|Hf]; [left; exact Hf|right; exact Hf]. }
    assert (Decision (∀ r, F.2 = Some r → rest_below W Γ x r)).
    { destruct F.2 as [r|]; [|left; by intros ? ?].
      destruct (decide (rest_below W Γ x r)); [left; by intros ? [= <-]|right; intros Hr; auto]. }
    apply and_dec; assumption.
  Defined.

  Global Instance ub_below_u_dec W Γ ub F : Decision (ub_below_u W Γ ub F).
  Proof. destruct ub; unfold ub_below_u; [apply _|apply ub_below_s_dec|apply _]. Defined.

  Global Instance lbx_below_h_dec W Γ lb X b : Decision (lbx_below_h W Γ lb X b).
  Proof.
    destruct lb as [| |x]; simpl; [apply _|apply _|].
    assert (Decision (∀ y, y ∈ X → sle W Γ x y)).
    { destruct (decide (set_Forall (λ y, sle W Γ x y) X)) as [Hf|Hf]; [left; exact Hf|right; exact Hf]. }
    apply and_dec; [assumption|apply _].
  Defined.

  Global Instance below_ty_dec W Γ x T : Decision (below_ty W Γ x T).
  Proof.
    unfold below_ty.
    assert (Decision (∀ y, y ∈ heads T → slt W Γ x y)).
    { destruct (decide (set_Forall (λ y, slt W Γ x y) (heads T))) as [Hf|Hf]; [left; exact Hf|right; exact Hf]. }
    apply and_dec; [apply _|assumption].
  Defined.

  Global Instance ex_wf_dec W Γ lb m C T : Decision (ex_wf W Γ lb m C T).
  Proof. unfold ex_wf. apply _. Defined.

  Global Instance sinsts_dec N ss : Decision (sinsts N ss).
  Proof.
    unfold sinsts. assert (Decision (N = None → Forall (λ s, sty_df s = s) ss)).
    { destruct N; [left; by intros ?|]. destruct (decide (Forall (λ s, sty_df s = s) ss));
        [left; by intros _|right; auto]. }
    unfold contractive. apply _.
  Defined.

  Global Instance teq_dec : RelDecision teq.
  Proof.
    intros T. unfold teq. induction T as [|ub lb c T1 IH1 U IH2 a|T1 IH1 U IH2|T1 IH1 U IH2|n k C ub c U IH|s x a mt|lb n C T1 IH];
      intros [|ub' lb' c' T1' U' a'|T1' U'|T1' U'|n' k' C' ub' c' U'|s' x' a' mt'|lb' n' C' T1']; simpl;
      try (right; tauto); try (left; done).
    - pose proof (IH1 T1'). pose proof (IH2 U'). apply _.
    - pose proof (IH1 T1'). pose proof (IH2 U'). apply _.
    - pose proof (IH1 T1'). pose proof (IH2 U'). apply _.
    - assert (Decision (match k with 0 => eqT sequiv U U' | S _ => U = U' end)).
      { destruct k; [apply IH|apply _]. }
      apply _.
    - apply _.
    - pose proof (IH T1'). apply _.
  Defined.

  Global Instance lb_lower_dec W Γ n C lb lb' T : Decision (lb_lower W Γ n C lb lb' T).
  Proof. unfold lb_lower. apply _. Defined.

  Local Instance box_res_dec k U U' :
    Decision (match k with 0 => teq U U' | S _ => U = U' ∨ (teq U U' ∧ tcontr U ∧ tcontr U') end).
  Proof. destruct k; apply _. Defined.

  Local Ltac no := right; inversion 1; subst; tauto.

  (** Subtyping, decided by recursion on one side. Arguments are
      contravariant, so the recursion decides both orientations. *)
  Lemma tsub_dec_both W T : (∀ Γ T', Decision (tsub W Γ T T')) * (∀ Γ T', Decision (tsub W Γ T' T)).
  Proof.
    induction T as [|ub lb c T1 IH1 U IH2 a|T1 IH1 U IH2|T1 IH1 U IH2|n k C ub c U _|s x a mt|lb n C T1 IH] using ty_rect;
      split; intros Γ [|ub' lb' c' T1' U' a'|T1' U'|T1' U'|n' k' C' ub' c' U'|s' x' a' mt'|lb' n' C' T1'];
      try (right; inversion 1; fail).
    - left. constructor.
    - left. constructor.
    - destruct (decide (ub = ub' ∧ lb = lb' ∧ fle c c' ∧ fle a' a)) as [(<-&<-&?&?)|?]; [|no].
      destruct (snd IH1 Γ T1'); [|no]. destruct (fst IH2 Γ U'); [|no].
      left. by constructor.
    - destruct (decide (ub' = ub ∧ lb' = lb ∧ fle c' c ∧ fle a a')) as [(<-&<-&?&?)|?]; [|no].
      destruct (fst IH1 Γ T1'); [|no]. destruct (snd IH2 Γ U'); [|no].
      left. by constructor.
    - destruct (fst IH1 Γ T1'); [|no]. destruct (fst IH2 Γ U'); [|no]. left. by constructor.
    - destruct (snd IH1 Γ T1'); [|no]. destruct (snd IH2 Γ U'); [|no]. left. by constructor.
    - destruct (fst IH1 Γ T1'); [|no]. destruct (fst IH2 Γ U'); [|no]. left. by constructor.
    - destruct (snd IH1 Γ T1'); [|no]. destruct (snd IH2 Γ U'); [|no]. left. by constructor.
    - destruct (decide (n = n' ∧ k = k' ∧ C = C' ∧ ub = ub' ∧ fle c c' ∧
        match k with 0 => teq U U' | S _ => U = U' ∨ (teq U U' ∧ tcontr U ∧ tcontr U') end))
        as [(<-&<-&<-&<-&?&?)|?]; [|no].
      left. by constructor.
    - destruct (decide (n' = n ∧ k' = k ∧ C' = C ∧ ub' = ub ∧ fle c' c ∧
        match k' with 0 => teq U' U | S _ => U' = U ∨ (teq U' U ∧ tcontr U' ∧ tcontr U) end))
        as [(<-&<-&<-&<-&?&?)|?]; [|no].
      left. by constructor.
    - destruct (decide (ssub s s' ∧ fle a' a ∧ x = x' ∧ mt = mt')) as [(?&?&<-&<-)|?]; [|no].
      left. by constructor.
    - destruct (decide (ssub s' s ∧ fle a a' ∧ x' = x ∧ mt' = mt)) as [(?&?&<-&<-)|?]; [|no].
      left. by constructor.
    - destruct (decide (n = n' ∧ hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C') (ids n) ∧
        lb_lower W Γ n C lb lb' T1)) as [(<-&?&?)|?]; [|no].
      destruct (fst IH (hc_open n C Γ) T1'); [|no]. left. by constructor.
    - destruct (decide (n' = n ∧ hold_at W (hc_open n' C' Γ) (bcs_inst (pshift n') C) (ids n') ∧
        lb_lower W Γ n' C' lb' lb T1')) as [(<-&?&?)|?]; [|no].
      destruct (snd IH (hc_open n' C' Γ) T1'); [|no]. left. by constructor.
  Defined.

  Global Instance tsub_dec W Γ T T' : Decision (tsub W Γ T T').
  Proof. apply (fst (tsub_dec_both W T)). Defined.
End oracles.
