(** * between is lock free (stage S9)

    The program of examples/FreshBetween.v types at the refill N = 2. The
    box takes c and e with credit 2 each. In the body, e loses 1 while c
    closes and 1 while d closes, and the thunk loses 1 on d′ at the
    spawn. main forces the box last, so the call of cost ∞ ages nothing.
    The world is a lock-free world by the measure (field sum, offset,
    depth): every law ends at r·1 or rises in depth. *)

From GV Require Export examples.LFTools examples.FreshBetween.

Lemma W_fb_wf : world_wf W_fb.
Proof.
  split; simpl; [done|]. intros ℓ x y _ (f & Hf & E).
  destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as -> ->; done.
Qed.

Lemma W_fb_wfworld : wfworld W_fb.
Proof.
  apply (wfworld_lex3 W_fb (λ x, (pt_fsum x, pt_off x, pt_depth x))); [intros f []| |].
  - intros x. unfold pt_fsum, pt_depth. simpl. lia.
  - intros ℓ g x y _ (f & Hf & E).
    destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.

Definition fbl_T : ty := TProd (TSess SEnd (pvar 0) (Some 2)) (TSess SEnd (pvar 1) (Some 2)).
Definition fbl_ty : ty := lbox 2 fb_C (Some (pvar 1)) fbl_T TUnit.

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 fb_C (pvar 1) Γ).

  Lemma fbl_hyp x y : fbx_P (FLt x y) → fact_scoped 2 (FLt x y) → slt W Γb x y.
  Proof. intros Hf Hs. eapply (hyp_slt_ids _ _ fbx_P 2); [exact (Γbox_in 2 fb_C (pvar 1) Γ)|done|done]. Qed.

  Ltac fbf := apply fbl_hyp; [unfold fbx_P; fb_disj|simpl; lia].

  Lemma fbl_body : ∃ c t,
    typed W (Some 2) ∅ Γb (Some fbl_T :: Some fbl_ty :: nones n) (∅, Some (FVar 1))
      (LetP (Var 0) (LetP (ENewAt 0 (Var 1)) (LetP (Var 0)
        (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
        (LetU (EClose (Var 3)) (LetU (EClose (Var 1)) (EClose (Var 4))))))))
      TUnit c t ∧ t.2 = Some 0.
  Proof.
    eexists _, _. split.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 1)) EUnit| | | |shelve].
    { eapply (e_new_at _ _ _ _ _ _ _ 0 SEnd (pvar 0) _ SEnd). eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| | | |shelve].
    { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
      eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_close with (S0 := SEnd) (x := fbd‾); [done|apply ub_below_empty|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 3)) EUnit| | | |shelve].
    { eapply e_close with (S0 := SEnd) (x := pvar 0); [done| |eapply e_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _ 1); [bot_false|apply Γbox_fv| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 1)) EUnit| | | |shelve].
    { eapply e_close with (S0 := SEnd) (x := fbd); [done| |eapply e_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _ 1); [bot_false|apply Γbox_fv| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := pvar 1); [done| |eapply e_var'; [reflexivity|spare_tac]].
    apply (ub_below_var _ _ _ (pvar 1) _ 1); [apply Γbox_fv|set_solver|by left]. }
    reflexivity.
    Unshelve. all: first [tok_tac | exact None | simpl; done].
  Qed.
End body.

Lemma fbl_box_typed W Γ n F : hc_fv Γ = ∅ →
  typed W (Some 2) ∅ Γ (nones n) F fb_box fbl_ty (Some 0) tid.
Proof.
  intros HΓ. destruct (fbl_body W Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

Lemma fbl_hold : hold_at W_fb (Γnew W_fb 0) fb_C fb_xs.
Proof.
  apply hold_at_nil. intros f Hf _.
  destruct (fact_map (pt_inst (plist fb_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as <- <-; simpl; lia.
Qed.

Lemma fbl_typedN : ∃ c ϑ, typed W_fb (Some 2) ∅ hc_empty [] (∅, None) fb_main TUnit c ϑ ∧ meets ϑ 0 0.
Proof.
  eexists _, _. split.
  { unfold fb_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | |shelve].
  { apply (e_new' _ _ _ _ _ _ SEnd); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_fb 0).
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ENewAt 1 (Var 1)) EUnit| | | |shelve].
  { eapply (e_new_at _ _ _ _ _ _ _ 1 SEnd (pvar 0) _ SEnd). eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 5))))) EUnit| | | |shelve].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := (pvar 0)‾); [done|apply ub_below_empty|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| | | |shelve].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := ((pvar 0)·1)‾); [done|apply ub_below_empty|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce fb_box) EUnit|apply ub_below_empty| | | |shelve|shelve|shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 2 fb_C (Some (pvar 1)) fbl_T TUnit fb_xs _ _
      (Some ((pvar 0)·1)) (TProd (TSess SEnd (pvar 0) (Some 2)) (TSess SEnd ((pvar 0)·1) (Some 2))));
      [done|apply fbl_hold|done|done|done|].
    apply (fbl_box_typed _ _ 7). done. }
  lage_tac.
  eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  meets_tac.
  Unshelve. all: first [tok_tac | exact None | simpl; done].
Qed.

Lemma fb_guarded : ∅ ⊢▷ fb_main.
Proof. unfold fb_main, fb_box, let_new. guard_tac. Qed.

Theorem fb_lftyped : ∃ N, ∅ ⊩^N _ W_fb (∅, {[+ fb_main +]}) : TUnit.
Proof.
  destruct fbl_typedN as (c & ϑ & Ht & Hm). exists 2.
  eapply lf_main_typed; [apply strict_wfworld; [apply W_fb_wf|apply W_fb_wfworld]|constructor|exact Ht|apply fb_guarded|exact Hm].
Qed.

Theorem fb_lock_free : lock_free (∅, {[+ fb_main +]}).
Proof.
  destruct fbl_typedN as (c & ϑ & Ht & Hm).
  eapply lf_main; [apply (strict_wfworld _ W_fb_wf W_fb_wfworld)|apply W_fb_wfworld|constructor|exact Ht|apply fb_guarded|exact Hm].
Qed.
