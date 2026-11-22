(** * many is lock free (stage S9)

    The program of examples/FreshMany.v types at the bound N = 8. main
    creates c with tickets 5 and 3, and e at the field of c with the same
    split, so c and e reach the box after the force (cost 1) at credit 4.
    The box takes c and e with credit 4 each. In the body, e loses 1 while c
    closes and 3 while d sends twice and closes. Each send and receive
    returns its end at credit 4, so the thunk needs no more than the
    refill. main forces the box last. The world is a lock-free world by
    the measure (field sum, offset, depth). *)

From GV Require Export examples.LFTools examples.FreshMany.

Definition fml_T : ty := TProd (TSess SEnd (pvar 0) (Some 4) (Some 5)) (TSess SEnd (pvar 1) (Some 4) (Some 5)).
Definition fml_ty : ty := lbox 2 fm_C (Some (pvar 1)) fml_T TUnit.

Section body.
  Context (W : sworld) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 fm_C (pvar 1) Γ).

  Lemma fml_hyp x y : fmx_P (FLt x y) → fact_scoped 2 (FLt x y) → slt W Γb x y.
  Proof. intros Hf Hs. eapply (hyp_slt_ids _ _ fmx_P 2); [exact (Γbox_in 2 fm_C (pvar 1) Γ)|done|done]. Qed.

  Ltac fmf := apply fml_hyp; [unfold fmx_P; fm_disj|simpl; lia].

  Ltac normF :=
    cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; unfold fml_ty, lbox;
    cbn [hbot orb sf_unionb fst snd].

  Ltac fut x :=
    apply (ub_below_gen _ _ x (pvar 1));
      [ let y := fresh "y" in let Hy := fresh "Hy" in
        intros y Hy; revert Hy; normF; intros Hy; heads_cases Hy; fmf
      | normF; reflexivity  | right; fmf ].

  Lemma fml_body : ∃ c,
    typed W (Some 8) ∅ Γb (Some fml_T :: Some fml_ty :: nones n) (∅, Some (RAbove (pvar 1))) fm_e TUnit c.
  Proof.
    eexists _.
    { unfold fm_e.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Pair (Var 1) ENew) EUnit| | | ].
    { eapply (e_new_at' _ _ _ _ _ _ _ 0 SEnd (pvar 0) _ _ Sdd); [done|shelve|reflexivity| |contr_tac]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (ESpawn fm_thunk) EUnit| | | ].
    { (* the thunk receives twice on d′ and closes it *)
      eapply e_spawn_lam; [apply thage_empty|lage_tac|]. unfold fm_thunk.
      eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | ].
      { eapply e_recv with (x := (fmd 0)‾) (m := 0) (T := TUnit) (S0 := dual Sdd);
          [done|exact I| |eapply e_var'; [reflexivity|spare_tac]].
        apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. }
      lage_tac.
      eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_letp_; [lsplit_tac (ERecv (Var 0)) EUnit| | | ].
      { eapply e_recv with (x := pt_shift 1 (fmd 0)‾) (m := 0) (T := TUnit) (S0 := dual Sd1);
          [done|exact I| |eapply e_var'; [reflexivity|spare_tac]].
        apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. }
      lage_tac.
      eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_close with (S0 := SEnd) (x := pt_shift 1 (pt_shift 1 (fmd 0)‾)); [done|apply ub_below_empty|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 3)) EUnit| | | ].
    { eapply e_close with (S0 := SEnd) (x := pvar 0); [done|fut (pvar 0)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (ESend (Pair EUnit (ESend (Pair EUnit (Var 1)))))) EUnit| | | ].
    { eapply e_close with (S0 := SEnd) (x := pt_shift 1 (pt_shift 1 (fmd 0))); [done|fut (fmd 2)|].
      eapply e_send with (x := pt_shift 1 (fmd 0)) (m := 0) (T := TUnit) (Tp := TUnit) (S0 := Sd1);
        [done|exact I|split; [done|cbn; set_solver]|fut (fmd 1)| |age_tac|shelve].
      eapply e_pair_; [lsplit_tac EUnit (ESend (Pair EUnit (Var 1)))| | | | ].
      { apply e_unit'. spare_tac. }
      lage_tac.
      { eapply e_send with (x := fmd 0) (m := 0) (T := TUnit) (Tp := TUnit) (S0 := Sdd);
          [done|exact I|split; [done|cbn; set_solver]|fut (fmd 0)| |age_tac|shelve].
        eapply e_pair_; [lsplit_tac EUnit (Var 1)| | | | ].
        { apply e_unit'. spare_tac. }
        lage_tac.
        { eapply e_var'; [reflexivity|]. spare_tac. }
        age_tac. }
      age_tac. }
    lage_tac.
    eapply e_close with (S0 := SEnd) (x := pvar 1); [done| |eapply e_var'; [reflexivity|spare_tac]].
    apply (ub_below_var _ _ _ (pvar 1) _); [set_solver|by left]. }
    Unshelve. all: first [apply tsub_refl | exact None | simpl; lia].
  Qed.
End body.

Lemma fml_box_typed W Γ n F : typed W (Some 8) ∅ Γ (nones n) F fm_box fml_ty (Some 0).
Proof.
  destruct (fml_body W Γ n) as (c & Hb).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

Lemma fml_hold : hold_at W_fm (Γnew fm_L) fm_C fm_xs.
Proof.
  apply hold_at_nil. intros f Hf _.
  destruct (fact_map (pt_inst (plist fm_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct Hf as [->|[->|[->|(k & [->| ->])]]]; simpl in E; injection E as <- <-; simpl; lia.
Qed.

Lemma fml_typedN : ∃ c, typed W_fm (Some 8) ∅ hc_empty [] (∅, None) fm_main TUnit c.
Proof.
  eexists _.
  { unfold fm_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { eapply (e_new_tk _ _ _ _ _ _ SEnd (Some 5) (Some 3)); [spare_tac|apply fm_wf_new|unfold tsum_ok; simpl; lia|contr_tac]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew fm_L).
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
  eapply e_app_; [lsplit_tac (EForce fm_box) EUnit|apply ubu_below_empty| | | |shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 2 fm_C (Some (pvar 1)) fml_T TUnit fm_xs _ (UPt ((pvar 0)·1)) (TProd (TSess SEnd (pvar 0) (Some 4) (Some 5)) (TSess SEnd ((pvar 0)·1) (Some 4) (Some 5))));
      [done|apply fml_hold|done|done|done|].
    apply (fml_box_typed _ _ 7). }
  lage_tac.
  eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  Unshelve. all: first [apply tsub_refl | exact None | simpl; lia | simpl; done].
Qed.

Theorem fm_lftyped : ∃ N, ∅ ⊩^N _ (swrestrict W_fm (iface ∅ TUnit)) (∅, {[+ fm_main +]}) : TUnit.
Proof.
  destruct fml_typedN as (c & Ht). exists 8.
  eapply lf_main_typed; [apply W_fm_wf|constructor|exact Ht].
Qed.

Theorem fm_lock_free : excluded_middle → functional_choice → lock_free (∅, {[+ fm_main +]}).
Proof.
  intros EM FC. destruct fml_typedN as (c & Ht).
  eapply (lf_main EM FC); [apply W_fm_wf|constructor|exact Ht].
Qed.
