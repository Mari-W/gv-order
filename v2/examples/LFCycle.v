(** * cycle is lock free (stage S9)

    The program of examples/Cycle.v types at the bound N = 4, so every end has N/2 = 2 tickets. Each end
    is created with credit 2. The thunk loses 1 at the spawn and 1 more
    on d′ while it closes c′, and main loses 1 on d while it closes c.
    The world is a lock-free world by the measure (field sum,
    offset, depth). *)

From GV Require Export examples.LFTools examples.Cycle.

Lemma cy_typedN : ∃ c, typed W_cy (Some 4) ∅ hc_empty [] (∅, None) cy_main TUnit c.
Proof.
  eexists _.
  { unfold cy_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { eapply (e_new' _ _ _ _ _ _ SEnd); [spare_tac|apply cy_wf_new|contr_tac]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew cy_L).
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Pair (Var 1) ENew) EUnit| | | ].
  { eapply (e_new_at' _ _ _ _ _ _ _ 0 SEnd (pvar 0) _ _ SEnd); [done|shelve|reflexivity| |contr_tac]. spare_tac. }
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

Theorem cy_lftyped : ∃ N, ∅ ⊩^N _ W_cy (∅, {[+ cy_main +]}) : TUnit.
Proof.
  destruct cy_typedN as (c & Ht). exists 4.
  eapply lf_main_typed; [apply W_cy_wf|constructor|exact Ht].
Qed.

Theorem cy_lock_free : excluded_middle → functional_choice → lock_free (∅, {[+ cy_main +]}).
Proof.
  intros EM FC. destruct cy_typedN as (c & Ht).
  eapply (lf_main EM FC); [apply W_cy_wf|constructor|exact Ht].
Qed.
