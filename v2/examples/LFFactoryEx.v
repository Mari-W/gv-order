(** * The factory is lock free (stage S9)

    The program of examples/FactoryEx.v types at the refill N = 2. mk₀
    returns c′ packed at credit 2 ([Tresl]), mk₁ takes p at credit 2 and
    returns p and c′ at credit 2. main holds q while it receives on p and
    closes it, so q loses 2. Each call is followed only by code that
    holds what the call returns, so the arrows may cost ∞. The world is a
    lock-free world by the measure (field sum, depth, offset): both laws
    rise in depth. *)

From GV Require Export examples.LFTools examples.FactoryEx.

Lemma W_fx_wfworld : wfworld W_fx.
Proof.
  apply (wfworld_lex3 W_fx (λ x, (pt_fsum x, pt_depth x, pt_off x))); [intros f []| |].
  - intros x. unfold pt_fsum, pt_depth. simpl. lia.
  - intros ℓ g x y _ [E|E]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.

Definition Tresl : ty := TEx LBot 1 (bcs_of (w_laws W_fx 0)) (TSess Sr (pvar 0)‾) (Some 2).
Definition mk0l_ty : ty := lbox 0 C0 None TUnit None Tresl (Some 0).
Definition mk1l_res : ty := TProd (TSess Sr (pvar 0)) (Some 2) (TSess Sr ((pvar 0)·0)‾) (Some 2).
Definition mk1l_ty : ty := lbox 1 mk1_C None (TSess Sr (pvar 0)) (Some 2) mk1l_res (Some 0).

(** The worker: send at x, close at x⁺, with no future. *)
Ltac lworker_tac pp j :=
  eapply e_spawn_lam; [apply thage_empty|lage_tac|]; unfold worker;
  eapply e_letu_; [lsplit_tac (Var 0) EUnit|eapply e_var'; [reflexivity|spare_tac]| | |shelve];
  [lage_tac|];
  eapply e_close with (S0 := SEnd) (x := pt_shift 1 pp); [done|apply ub_below_empty|];
  eapply e_send with (x := pp) (m := 0) (T := TUnit) (b := None) (S0 := Sd);
    [done|exact I|done|cbn; set_solver|apply ub_below_empty| |age_tac|shelve];
  eapply e_pair_; [lsplit_tac EUnit (Var j)|apply e_unit'; spare_tac| | | |shelve];
  [lage_tac|eapply e_var'; [reflexivity|spare_tac]|age_tac].

(** ** mk₀ *)

Lemma mk0l_body Γ n : ∃ c t,
  typed W_fx (Some 2) ∅ (hc_fvar 1 None (hc_fvar 0 None (hc_open 0 C0 Γ)))
    (Some (TUnit, None) :: Some (mk0l_ty, None) :: nones n) (∅, Some (FVar 1)) mk0_e Tresl (Some 0) c t
  ∧ t.2 = Some 0.
Proof.
  eexists _, _. split.
  { unfold mk0_e, let_new.
  eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_let_; [lsplit_tac (ENew 0) EUnit| | | |shelve].
  { apply (e_new' _ _ _ _ _ _ Sd); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_nil', !lenv_pinst_cons', lenv_pinst_nones.
  cbn [fmap option_fmap option_map insert list_insert].
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (worker 2)) EUnit| | | |shelve].
  { lworker_tac (pvar 0) 2. }
  lage_tac.
  (* pack c′ at the fresh root *)
  change (pinst_ty (pshift 1) Tresl) with Tresl. unfold Tresl.
  eapply e_pack with (xs := pvar 0 :: []); [done| |exact I|].
  - apply hold_at_nil. intros f Hf _. destruct Hf as [->| ->]; simpl.
    + eapply (hyp_slt_ids _ _ (w_laws W_fx 0) 1);
        [unfold hc_fvar, hc_open; cbn [hc_hyps]; apply elem_of_app; right; apply list_elem_of_here|by left|simpl; lia].
    + eapply (hyp_slt_ids _ _ (w_laws W_fx 0) 1);
        [unfold hc_fvar, hc_open; cbn [hc_hyps]; apply elem_of_app; right; apply list_elem_of_here|by right|simpl; lia].
  - eapply e_var'; [reflexivity|]. spare_tac. }
  reflexivity.
  Unshelve. all: first [tok_tac | apply tsub_refl | exact None].
Qed.

Lemma mk0l_typed Γ n F : hc_fv Γ = ∅ → typed W_fx (Some 2) ∅ Γ (nones n) F mk0 mk0l_ty None (Some 0) tid.
Proof.
  intros HΓ. destruct (mk0l_body Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

(** ** mk₁ *)

Lemma mk1l_body Γ n : ∃ c t,
  typed W_fx (Some 2) ∅ (hc_fvar 1 None (hc_fvar 0 None (hc_open 1 mk1_C Γ)))
    (Some (TSess Sr (pvar 0), Some 2) :: Some (mk1l_ty, None) :: nones n) (∅, Some (FVar 1))
    mk1_e mk1l_res (Some 0) c t ∧ t.2 = Some 0.
Proof.
  eexists _, _. split.
  { unfold mk1_e.
  eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 0)) EUnit| | | |shelve].
  { eapply (e_new_at _ _ _ _ _ _ _ 0 Sr (pvar 0) _ Sd). eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (worker 2)) EUnit| | | |shelve].
  { lworker_tac ((pvar 0)·0) 2. }
  lage_tac.
  eapply e_pair_; [lsplit_tac (Var 3) (Var 0)| | | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  reflexivity.
  Unshelve. all: first [tok_tac | apply tsub_refl | exact None].
Qed.

Lemma mk1l_typed Γ n F : hc_fv Γ = ∅ → typed W_fx (Some 2) ∅ Γ (nones n) F mk1 mk1l_ty None (Some 0) tid.
Proof.
  intros HΓ. destruct (mk1l_body Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

(** ** main *)

Lemma fxl_typedN : ∃ c ϑ, typed W_fx (Some 2) ∅ hc_empty [] (∅, None) fx_main TUnit None c ϑ ∧ meets ϑ 0 0.
Proof.
  eexists _, _. split.
  { unfold fx_main, elet.
  eapply e_let_; [apply lsplit_nil| | | |shelve].
  { (* the first call needs no point *)
    eapply e_app_; [apply lsplit_nil|apply ub_below_empty| | | |shelve|shelve|shelve].
    { eapply (lbox_force_eq _ _ _ _ _ _ 0 C0 None TUnit None Tresl (Some 0) [] _ _ _ None TUnit Tresl);
        [done| |done|done|done|].
      - intros x y (g0 & (f & Hf & _) & _). done.
      - by apply (mk0l_typed _ 0). }
    lage_tac.
    apply e_unit'. spare_tac. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_fx 0).
  eapply e_letp_; [lsplit_tac (App (EForce mk1) (Var 0)) EUnit| | | |shelve].
  { eapply e_app_; [lsplit_tac (EForce mk1) (Var 0)|apply ub_below_empty| | | |shelve|shelve|shelve].
    { eapply (lbox_force_eq _ _ _ _ _ _ 1 mk1_C None (TSess Sr (pvar 0)) (Some 2) mk1l_res (Some 0)
        ((pvar 0)‾ :: []) _ _ _ None (TSess Sr (pvar 0)‾)
        (TProd (TSess Sr (pvar 0)‾) (Some 2) (TSess Sr ((pvar 0)·0)‾) (Some 2)));
        [done| |done|done|done|].
      + apply hold_at_nil. intros f Hf _. destruct Hf as [->| ->]; simpl.
        * apply fx_law; [by left|simpl; lia].
        * apply fx_law; [by right|simpl; lia].
      + by apply (mk1l_typed _ 1). }
    lage_tac.
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (LetP (ERecv (Var 1)) (LetU (Var 1) (EClose (Var 0)))) EUnit| | | |shelve].
  { (* recvclose p while q is held *)
    eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | |shelve].
    { eapply e_recv with (x := (pvar 0)‾) (m := 0) (T := TUnit) (b := None) (S0 := Sr);
        [done|exact I| |eapply e_var'; [reflexivity|spare_tac]].
      apply ub_below_novar; [|reflexivity]. intros y Hy.
      cbn [sf_unionb sf_union fst snd lenv_bot hbot orb] in Hy. heads_cases Hy.
      apply fx_law; [by left|simpl; lia]. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := pt_shift 1 (pvar 0)‾); [done| |].
    + apply ub_below_novar; [|reflexivity]. intros y Hy.
      cbn [sf_unionb sf_union fst snd lenv_bot hbot orb] in Hy. heads_cases Hy.
      apply fx_law; [by right|simpl; lia].
    + eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ERecv (Var 0)) EUnit| | | |shelve].
  { eapply e_recv with (x := ((pvar 0)·0)‾) (m := 0) (T := TUnit) (b := None) (S0 := Sr);
      [done|exact I| |eapply e_var'; [reflexivity|spare_tac]].
    apply ub_below_novar; [|reflexivity]. intros y Hy.
    cbn [sf_unionb sf_union fst snd lenv_bot hbot orb] in Hy. heads_cases Hy. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_close with (S0 := SEnd) (x := pt_shift 1 ((pvar 0)·0)‾); [done|apply ub_below_empty|].
  eapply e_var'; [reflexivity|]. spare_tac. }
  meets_tac.
  Unshelve. all: first [tok_tac | exact None | simpl; lia | simpl; done].
Qed.

Lemma fx_guarded : ∅ ⊢▷ fx_main.
Proof. unfold fx_main, mk0, mk1, mk0_e, mk1_e, worker, let_new, elet. guard_tac. Qed.

Theorem fx_lftyped : ∃ N, ∅ ⊩^N _ W_fx (∅, {[+ fx_main +]}) : TUnit.
Proof.
  destruct fxl_typedN as (c & ϑ & Ht & Hm). exists 2.
  eapply lf_main_typed; [constructor|exact Ht|apply fx_guarded|exact Hm].
Qed.

Theorem fx_lock_free : lock_free (∅, {[+ fx_main +]}).
Proof.
  destruct fxl_typedN as (c & ϑ & Ht & Hm).
  eapply lf_main; [apply (strict_wfworld _ W_fx_wf W_fx_wfworld)|apply W_fx_wfworld|constructor|exact Ht|apply fx_guarded|exact Hm].
Qed.
