(** * Fork-join with replies

      main = let (w, w′) = new in spawn (λu. (force wk) w′); close w
      wk   = !(λw. let (c1, c1′) = new in let (c2, c2′) = new in
                   spawn (λu. close c1′); spawn (λu. close c2′);
                   close c1; close c2; close w)

    One round of binary fork-join. The worker waits for the replies of
    its two children and then answers its parent. main creates w at a
    fresh root ρ and keeps the end at ρ. The worker holds w′ at ι = ρ‾
    and creates both child channels at the fields ι·0 and ι·1 by
    E-New-Field. It keeps the ends at the fields and closes them first,
    so readiness asks ι·0 ≺ (ι·1)‾ and ι·0 ≺ ῑ for the first close and
    ι·1 ≺ ῑ for the second. These three facts are the box hypothesis H.
    The laws of ρ state H at ρ‾, so main forces the box there.

    - [fj_dftyped], [fj_term]: main types, and P-Term types the closed
      program over the empty world.
    - [fj_deadlock_free]: deadlock freedom by [soundness].
    - [close_close_needs]: every typing of close a; close b at any bound
      asks the point of a below the head of b. In the recursive worker
      the child's end sits at the dual of the parent's, so the recursive
      force needs H at an instance whose dual lies below ῑ. That is the
      descent that no box admits (docs/redesign/check-general-new.md,
      Proposition 7). The recursive version does not type.

    The channels carry no data, so "recv-or-close" is close throughout. *)

From GV Require Export examples.Tools.
From GV Require Import static.FundamentalProc examples.SemBranch.

Abbreviation ρ := (pvar 0).

(** ** The box hypothesis, over ι = 0 *)

Definition fj_P (g : fact) : Prop :=
  g = FLt (ρ·0) (ρ·1)‾ ∨ g = FLt (ρ·0) ρ‾ ∨ g = FLt (ρ·1) ρ‾.
Definition fj_H : bcs := BCs [] fj_P.

(** The laws of the root of w, H at ρ‾. A field is the same from both
    ends, ρ‾·κ = ρ·κ. *)
Definition fj_L (g : fact) : Prop :=
  g = FLt (ρ·0) (ρ·1)‾ ∨ g = FLt (ρ·0) ρ ∨ g = FLt (ρ·1) ρ.

Lemma fj_wf_new : wf_new (bcs_of fj_L).
Proof.
  apply (wf_new_lex3 _ (λ x, (if decide (pt_depth x = 0) then 1 else 0, pt_fsum x, pt_off x))).
  - intros x y Hk. destruct Hk as [E|[E|E]]; injection E as -> ->; split; reflexivity.
  - intros x. unfold lex3, pt_depth, pt_fsum. simpl. destruct (decide _); lia.
  - intros x y Hk. destruct Hk as [E|[E|E]]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.
#[global] Hint Resolve fj_wf_new : wfnew.

(** ** The programs *)

Definition wk_arr : ty := TLolli UTop LNone None (TSess SEnd ρ None None) TUnit None.
Definition wk_box : ty := TBox 1 0 fj_H None None wk_arr.

Definition wk_body : expr :=
  LetP ENew (LetP ENew
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 3)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
    (LetU (EClose (Var 3))
    (LetU (EClose (Var 1))
          (EClose (Var 4))))))).

Definition wk : expr := EBox (Lam wk_body).

Definition fj_main : expr :=
  let_new (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce wk) (Var 1))))) (EClose (Var 1))).

(** ** The worker *)

Lemma fj_fact W Γ x y :
  (fj_H, ids 1) ∈ hc_hyps Γ → fj_P (FLt x y) → slt W Γ x y.
Proof.
  intros Hin Hf. eapply (slt_hyp _ _ fj_P (ids 1) (FLt x y)); [done|done| |].
  - destruct Hf as [E|[E|E]]; injection E as -> ->; simpl; lia.
  - destruct Hf as [E|[E|E]]; injection E as -> ->; fact_eq.
Qed.

Lemma wk_box_shift n :
  lenv_pinst (pshift 1) (Some wk_box :: nones n) = Some wk_box :: nones n.
Proof. unfold lenv_pinst. rewrite fmap_cons, fmap_replicate. reflexivity. Qed.

Section worker.
  Context (W : sworld) (Γ : hctx).
  Local Definition Γw : hctx := hc_open 1 fj_H Γ.

  Lemma fj_in : (fj_H, ids 1) ∈ hc_hyps Γw.
  Proof. unfold Γw, hc_open. simpl. apply elem_of_app. right. by left. Qed.

  Lemma wk_body_typed n :
    dftyped W ∅ Γw (Some (TSess SEnd ρ None None) :: Some wk_box :: nones n)
      (∅, None) wk_body TUnit.
  Proof.
    unfold wk_body.
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 0 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 1 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 3))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·0); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[->|[[]|[]]]]]];
          apply fj_fact; [apply fj_in|left; done|apply fj_in|right; left; done].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·1); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[[]|[]]]]].
        apply fj_fact; [apply fj_in|right; right; done].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := ρ); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End worker.

Lemma wk_typed W Γ n F : dftyped W ∅ Γ (nones n) F wk wk_box.
Proof.
  eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. repeat (apply Is_true_andb; split); done. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil, wk_box_shift.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  { done. }
  apply wk_body_typed.
Qed.

(** ** main *)

Definition Γm : hctx := hc_open 1 (bcs_of fj_L) hc_empty.

Lemma law_fact W x y : fj_L (FLt x y) → slt W Γm x y.
Proof.
  intros Hf. eapply (slt_hyp _ _ fj_L (ids 1) (FLt x y)); [unfold Γm, hc_open; simpl; by left|done| |].
  - destruct Hf as [E|[E|E]]; injection E as -> ->; simpl; lia.
  - destruct Hf as [E|[E|E]]; injection E as -> ->; fact_eq.
Qed.

(** The force of the worker at ρ‾, where the laws give H. *)
Lemma wk_force W n F :
  dftyped W ∅ Γm (nones n) F (EForce wk) (TLolli UTop LNone None (TSess SEnd ρ‾ None None) TUnit None).
Proof.
  assert (sinst_ty (slist []) (ty_inst [ρ‾] wk_arr) =
    TLolli UTop LNone None (TSess SEnd ρ‾ None None) TUnit None) as <-.
  { rewrite sinst_nil. reflexivity. }
  eapply d_force with (C := fj_H) (ub := None) (c := None);
    [done| |done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|apply wk_typed].
  apply hold_at_nil. intros f Hf _.
  destruct Hf as [->|[->| ->]]; simpl; apply law_fact; unfold fj_L.
  all: first [left; fact_eq | right; left; fact_eq | right; right; fact_eq].
Qed.

Theorem fj_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) fj_main TUnit.
Proof.
  unfold fj_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply fj_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γm.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
                 |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce wk) (Var 1))))) EUnit| |].
  - apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce wk) EUnit|done| |].
    + apply (wk_force _ 4).
    + eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

(** P-Term types the closed program over the empty world. *)
Theorem fj_term : ptyped None sw_empty ∅ (∅, {[+ fj_main +]}) TUnit.
Proof.
  apply (p_term None sw_empty ∅ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply pfree_empty.
  - intros o e He. by rewrite lookup_empty in He.
  - set_solver.
  - assert (tenv_of (fhalf None) ∅ ∪ ∅ = tenv_df ∅) as ->.
    { unfold tenv_of, tenv_df. by rewrite !fmap_empty, map_union_empty. }
    apply fj_dftyped.
  - apply sw_empty_ok.
Qed.

Theorem fj_deadlock_free : deadlock_free (∅, {[+ fj_main +]}).
Proof. exact (soundness sw_empty _ TUnit fj_term). Qed.

(** ** Why the recursion does not type

    In the recursive worker the parent closes its child's channel c and
    then w, so after the spawn it runs close c; close w. Every typing of
    that term, at any bound, world and context, asks the point p of c
    below the head ῑ of w. The child holds the other end at p‾ and forces
    the same box there, so it needs H at an instance ι′ = p‾ with
    ῑ′ = p ≺ ῑ. Proposition 7 of docs/redesign/check-general-new.md shows
    that W, Γ and H then have no common model, for a field creation and
    for a fresh root alike, so main cannot force the box. *)
Lemma fj_wait_needs W N Θ Γ Δ F c w T k ec ew :
  c ≠ w → typed W N Θ Γ Δ F (LetU (EClose (Chan c)) (EClose (Chan w))) T k →
  Θ !! c = Some ec → Θ !! w = Some ew → slt W Γ (te_pt ec) (te_pt ew)‾.
Proof. apply cl2_needs. Qed.

Print Assumptions fj_deadlock_free.
Print Assumptions fj_wait_needs.
