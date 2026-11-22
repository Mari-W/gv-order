(** * between is lock free (stage S9)

    The program of examples/FreshBetween.v types at the bound N = 4. main
    creates c with tickets 3 and 1, and e at the field of c with the same
    split, so c and e reach the force at credit 3 and the box after the
    force (cost 1) at credit 2. The box takes c and e with credit 2 each. In the body, e loses 1 while c
    closes and 1 while d closes, and the thunk loses 1 on d′ at the
    spawn. main forces the box last, so the call of cost ∞ ages nothing.
    The world is a lock-free world by the measure (field sum, offset,
    depth): every law ends at r·1 or rises in depth. *)

From GV Require Export examples.LFTools examples.FreshBetween.

Definition fbl_T : ty := TProd (TSess SEnd (pvar 0) (Some 2) (Some 3)) (TSess SEnd (pvar 1) (Some 2) (Some 3)).
Definition fbl_ty : ty := lbox 2 fb_C (Some (pvar 1)) fbl_T TUnit.

Section body.
  Context (W : sworld) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 fb_C (pvar 1) Γ).

  Lemma fbl_hyp x y : fbx_P (FLt x y) → fact_scoped 2 (FLt x y) → slt W Γb x y.
  Proof. intros Hf Hs. eapply (hyp_slt_ids _ _ fbx_P 2); [exact (Γbox_in 2 fb_C (pvar 1) Γ)|done|done]. Qed.

  Ltac fbf := apply fbl_hyp; [unfold fbx_P; fb_disj|simpl; lia].

  Lemma fbl_body : ∃ c,
    typed W (Some 4) ∅ Γb (Some fbl_T :: Some fbl_ty :: nones n) (∅, Some (RAbove (pvar 1))) (LetP (Var 0) (LetP (Pair (Var 1) ENew) (LetP (Var 0)
        (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
        (LetU (EClose (Var 3)) (LetU (EClose (Var 1)) (EClose (Var 4)))))))) TUnit c.
  Proof.
    eexists _.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Pair (Var 1) ENew) EUnit| | | ].
    { eapply (e_new_at' _ _ _ _ _ _ _ 0 SEnd (pvar 0) _ _ SEnd); [done|shelve|reflexivity| |contr_tac]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| | | ].
    { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
      eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_close with (S0 := SEnd) (x := fbd‾); [done|apply ub_below_empty|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 3)) EUnit| | | ].
    { eapply e_close with (S0 := SEnd) (x := pvar 0); [done| |eapply e_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _); [bot_false| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 1)) EUnit| | | ].
    { eapply e_close with (S0 := SEnd) (x := fbd); [done| |eapply e_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _); [bot_false| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := pvar 1); [done| |eapply e_var'; [reflexivity|spare_tac]].
    apply (ub_below_var _ _ _ (pvar 1) _); [set_solver|by left]. }
    Unshelve. all: first [exact None | simpl; lia | simpl; done].
  Qed.
End body.

Lemma fbl_box_typed W Γ n F : typed W (Some 4) ∅ Γ (nones n) F fb_box fbl_ty (Some 0).
Proof.
  destruct (fbl_body W Γ n) as (c & Hb).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

Lemma fbl_hold : hold_at W_fb (Γnew fb_L) fb_C fb_xs.
Proof.
  apply hold_at_nil. intros f Hf _.
  destruct (fact_map (pt_inst (plist fb_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as <- <-; simpl; lia.
Qed.

Lemma fbl_typedN : ∃ c, typed W_fb (Some 4) ∅ hc_empty [] (∅, None) fb_main TUnit c.
Proof.
  eexists _.
  { unfold fb_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { eapply (e_new_tk _ _ _ _ _ _ SEnd (Some 3) (Some 1)); [spare_tac|apply fb_wf_new|unfold tsum_ok; simpl; lia|contr_tac]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew fb_L).
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Pair (Var 1) ENew) EUnit| | | ].
  { eapply (e_new_at' _ _ _ _ _ _ _ 1 SEnd (pvar 0) _ _ SEnd); [done|shelve|reflexivity| |contr_tac]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 5))))) EUnit| | | ].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := (pvar 0)‾); [done|apply ub_below_empty|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| | | ].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := ((pvar 0)·1)‾); [done|apply ub_below_empty|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce fb_box) EUnit|apply ubu_below_empty| | | |shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 2 fb_C (Some (pvar 1)) fbl_T TUnit fb_xs _ (UPt ((pvar 0)·1)) (TProd (TSess SEnd (pvar 0) (Some 2) (Some 3)) (TSess SEnd ((pvar 0)·1) (Some 2) (Some 3))));
      [done|apply fbl_hold|done|done|done|].
    apply (fbl_box_typed _ _ 7). }
  lage_tac.
  eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  Unshelve. all: first [exact None | simpl; lia | simpl; done].
Qed.

Theorem fb_lftyped : ∃ N, ∅ ⊩^N _ W_fb (∅, {[+ fb_main +]}) : TUnit.
Proof.
  destruct fbl_typedN as (c & Ht). exists 4.
  eapply lf_main_typed; [apply W_fb_wf|constructor|exact Ht].
Qed.

Theorem fb_lock_free : excluded_middle → functional_choice → lock_free (∅, {[+ fb_main +]}).
Proof.
  intros EM FC. destruct fbl_typedN as (c & Ht).
  eapply (lf_main EM FC); [apply W_fb_wf|constructor|exact Ht].
Qed.
