(** * cycle is lock free (stage S9)

    The program of examples/Cycle.v types at the bound N = 4, so every end has N/2 = 2 tickets. Each end
    is created with credit 2. The thunk loses 1 at the spawn and 1 more
    on d′ while it closes c′, and main loses 1 on d while it closes c.
    The world is a lock-free world by the measure (field sum,
    offset, depth). *)

From GV Require Export examples.LFTools examples.Cycle.

Lemma W_cy_wfworld : wfworld W_cy.
Proof.
  apply (wfworld_lex3 W_cy (λ x, (pt_fsum x, pt_off x, pt_depth x))); [intros f []| |].
  - intros x. unfold pt_fsum, pt_depth. simpl. lia.
  - intros ℓ g x y _ [E|E]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.

Lemma cy_typedN : ∃ c, typed W_cy (Some 4) ∅ hc_empty [] (∅, None) cy_main TUnit c.
Proof.
  eexists _.
  { unfold cy_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { apply (e_new' _ _ _ _ _ _ SEnd); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_cy 0).
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 1)) EUnit| | | ].
  { eapply (e_new_at _ _ _ _ _ _ _ 0 SEnd (pvar 0) _ _ SEnd); [|shelve]. eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn cy_thunk) EUnit| | | ].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 5)) EUnit| | | ].
    { eapply e_close with (S0 := SEnd) (x := (pvar 0)‾); [done| |eapply e_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy.
      rewrite pt_dual_dual. apply cy_law2. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := ((pvar 0)·0)‾); [done|apply ub_below_empty|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (EClose (Var 3)) EUnit| | | ].
  { eapply e_close with (S0 := SEnd) (x := pvar 0); [done| |eapply e_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. apply cy_law1. }
  lage_tac.
  eapply e_close with (S0 := SEnd) (x := (pvar 0)·0); [done|apply ub_below_empty|].
  eapply e_var'; [reflexivity|]. spare_tac. }
  Unshelve. all: first [exact None | simpl; lia].
Qed.

Lemma cy_guarded : ∅ ⊢▷ cy_main.
Proof. unfold cy_main, let_new, cy_thunk. guard_tac. Qed.

Theorem cy_lftyped : ∃ N, ∅ ⊩^N _ W_cy (∅, {[+ cy_main +]}) : TUnit.
Proof.
  destruct cy_typedN as (c & Ht). exists 4.
  eapply lf_main_typed; [apply strict_wfworld; [apply W_cy_wf|apply W_cy_wfworld]|constructor|exact Ht|apply cy_guarded].
Qed.

Theorem cy_lock_free : lock_free (∅, {[+ cy_main +]}).
Proof.
  destruct cy_typedN as (c & Ht).
  eapply lf_main; [apply (strict_wfworld _ W_cy_wf W_cy_wfworld)|apply W_cy_wfworld|constructor|exact Ht|apply cy_guarded].
Qed.
