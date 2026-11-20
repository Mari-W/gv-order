(** * The growing ring is lock free (stage S9)

    The program of examples/GrowRing.v types at the refill N = 4 once the
    payload of Sch carries credit 2 ([Schl]); at credit ∞ no end of
    finite credit can be sent. The box takes ⟨x, y⟩ at credits 0 and 1.
    In the body, the payload z arrives at credit 2, loses 1 while x
    closes and 1 at the spawn, and a′, b, b′ arrive at credit 4 and lose
    1 at the receive, 1 at the close and 1 at the spawn. The calls get
    their arguments at credits (0, 1) and (1, 1), which fall to (0, 1)
    by subtyping. Each call is the last step of its thread.

    The world is a lock-free world by the measure (depth, offset): every
    law rises in depth, because the two points of a reachable pair have
    the same depth ([rreach_depth]). *)

From GV Require Export examples.LFTools examples.GrowRing.

(** ** The world *)

Lemma rreach_root X Y : rreach (pvar 0) (pvar 1) X Y →
  (pt_root X = NVar 0 ∨ pt_root X = NVar 1) ∧ (pt_root Y = NVar 0 ∨ pt_root Y = NVar 1).
Proof.
  induction 1 as [|X Y _ [IH1 IH2]|X Y _ [IH1 IH2]]; [auto|..];
    rewrite ?pt_root_dual, !pt_root_field; auto.
Qed.

Lemma rreach_depth X Y : rreach (pvar 0) (pvar 1) X Y → pt_depth X = pt_depth Y.
Proof. induction 1; unfold pt_depth in *; simpl in *; lia. Qed.

Lemma pn_depth_inst σ p : (∀ a, pt_depth (σ a) = 0) → pn_depth (pt_name (pn_inst σ p)) = pn_depth p.
Proof. intros Hσ. induction p as [| |a|p IH b κ]; simpl; auto. apply Hσ. Qed.

Lemma pt_depth_inst σ x : (∀ a, pt_depth (σ a) = 0) → pt_depth (pt_inst σ x) = pt_depth x.
Proof. intros Hσ. unfold pt_inst, pt_depth. destruct (pt_pol x); simpl; by apply pn_depth_inst. Qed.

Lemma rg_xs_depth a : pt_depth (plist rg_xs a) = 0.
Proof. by destruct a as [|[|a]]. Qed.

Lemma W_rg_wf : world_wf W_rg.
Proof.
  split; simpl; [done|]. intros ℓ x y _ (f & (X & Y & HR & HF) & E).
  destruct (rreach_root X Y HR) as [HX HY].
  assert (∀ u, pt_root u = pt_root X ∨ pt_root u = pt_root Y →
            pt_root (pt_inst (plist rg_xs) u) = NVar 0) as Hr.
  { intros u Hu. rewrite pt_root_inst_var.
    destruct Hu as [->| ->]; [destruct HX as [->| ->]|destruct HY as [->| ->]]; done. }
  unfold rg_F in HF. repeat destruct HF as [HF|HF]; subst f; simpl in E; injection E as -> ->;
    split; apply Hr; rewrite ?pt_root_shift, ?pt_root_dual, ?pt_root_field; auto.
Qed.

Lemma W_rg_wfworld : wfworld W_rg.
Proof.
  apply (wfworld_lex3 W_rg (λ x, (pt_depth x, pt_off x, 0))); [intros f []| |].
  - intros x. unfold pt_depth. simpl. lia.
  - intros ℓ g x y _ (f & (X & Y & HR & HF) & E).
    pose proof (rreach_depth X Y HR) as HD.
    cbv beta iota delta [lex3]. left. unfold law_inst.
    unfold rg_F in HF. repeat destruct HF as [HF|HF]; subst f; simpl in E; injection E as -> ->;
      rewrite !pt_depth_inst by (done || apply rg_xs_depth);
      unfold pt_depth in *; simpl; lia.
Qed.

(** ** Types at a finite refill *)

Definition Schl : sty := SMu (SSeq (SRcv 1 (TSess (SVar 0) (pvar 0) (Some 2))) SEnd).

Lemma unfold_Schl : unfoldS Schl = SSeq (SRcv 1 (TSess Schl (pvar 0) (Some 2))) SEnd.
Proof. done. Qed.
Lemma unfold_dSchl : unfoldS (dual Schl) = SSeq (SSnd 1 (TSess Schl (pvar 0) (Some 2))) SEnd.
Proof. done. Qed.
Lemma pscoped_SchlT : pscoped 1 (TSess Schl (pvar 0) (Some 2)).
Proof. simpl. split_and?; try done; intros a Ha; injection Ha as <-; lia. Qed.

Definition rgl_T : ty := TProd (TSess Schl (pvar 0) (Some 0)) (TSess (dual Schl) (pvar 1) (Some 1)).
Definition rgl_ty : ty := lbox 2 rg_C (Some (sh 1 (pvar 0))) rgl_T TUnit.

Ltac tsub_tac := first [apply tsub_refl | apply sub_sess; [apply sequiv_refl|simpl; lia]].

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 rg_C (sh 1 (pvar 0)) Γ).

  Ltac rgf := apply rg_hyp; exists (pvar 0), (pvar 1); split; [apply rr_root|unfold rg_F; rg_disj].

  (** A recursive call at a pair reachable in one step. *)
  Lemma rgl_call Δ F e X1 Y1 c0 t0 :
    rreach (pvar 0) (pvar 1) X1 Y1 →
    typed W (Some 4) ∅ Γb Δ F e rgl_ty c0 t0 →
    typed W (Some 4) ∅ Γb Δ F (EForce e)
      (TLolli (Some (sh 1 X1)) None None tz (Some 0) (TProd (TSess Schl X1 (Some 0)) (TSess (dual Schl) Y1 (Some 1))) TUnit None) (fadd c0 (Some 0)) (tseq t0 tid).
  Proof.
    intros HR H.
    eapply (lbox_force_eq _ _ _ _ _ _ 2 rg_C (Some (sh 1 (pvar 0))) rgl_T TUnit (X1 :: Y1 :: []));
      [done| | | |done|exact H].
    - apply hold_at_nil. intros f Hf _.
      destruct (fact_map (pt_inst (plist (X1 :: Y1 :: []))) f) as [x y] eqn:E.
      apply rg_hyp. rewrite <-E. by apply rg_inst.
    - cbn [fmap option_fmap option_map]. by rewrite pt_inst_shift, pt_inst_pvar_at.
    - unfold ty_inst, rgl_T. cbn [pinst_ty]. by rewrite !pt_inst_pvar_at.
  Qed.

  Ltac normF :=
    cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; unfold rgl_ty, lbox;
    cbn [hbot orb sf_unionb fst snd fs_var fs_bot].

  Ltac fut x :=
    apply (ub_below_gen _ _ x (sh 1 (pvar 0)) 1);
      [ let y := fresh "y" in let Hy := fresh "Hy" in
        intros y Hy; revert Hy; normF; unfold payload_at, ty_inst; cbn [pinst_ty]; intros Hy; heads_cases Hy;
        first [rgf | eapply sl_trans; [apply sl_po|rgf]]
      | normF; reflexivity | apply Γbox_fv
      | first [by left | right; apply sl_po] | normF; reflexivity ].

  Lemma rgl_body : ∃ c t,
    typed W (Some 4) ∅ Γb (Some rgl_T :: Some rgl_ty :: nones n) (∅, Some (FVar 1))
      rg_e TUnit c t ∧ t.2 = Some 0.
  Proof.
    eexists _, _. split.
    { unfold rg_e.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    (* a at Y·0 *)
    eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 0)) EUnit| | | |shelve].
    { eapply (e_new_at _ _ _ _ _ _ _ 0 (dual Schl) (pvar 1) _ Schl). eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    (* the y-thread sends a on y *)
    eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (ESend (Pair (Var 2) (Var 4))))))) EUnit
                    | | | |shelve].
    { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
      eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_close with (S0 := SEnd) (x := sh 1 (pvar 1)); [done|apply ub_below_empty|].
      eapply e_send with (x := pvar 1) (m := 1) (T := TSess Schl (pvar 0) (Some 2)) (S0 := dual Schl);
        [exact unfold_dSchl|exact pscoped_SchlT|done| |apply ub_below_empty| | |].
      { intros y Hy. cbn in Hy. apply elem_of_singleton in Hy as ->. rgf. }
      { eapply e_pair_; [lsplit_tac (Var 2) (Var 4)| | | | |shelve].
        { eapply e_var'; [reflexivity|]. spare_tac. }
        lage_tac.
        { eapply e_var'; [reflexivity|]. spare_tac. }
        age_tac. }
      age_tac.
      tsub_tac. }
    lage_tac.
    (* b at X·1, before the receive *)
    eapply e_letp_; [lsplit_tac (ENewAt 1 (Var 5)) EUnit| | | |shelve].
    { eapply (e_new_at _ _ _ _ _ _ _ 1 Schl (pvar 0) _ Schl). eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (ERecv (Var 3)) EUnit| | | |shelve].
    { eapply e_recv with (x := pvar 0) (m := 1) (T := TSess Schl (pvar 0) (Some 2)) (S0 := Schl);
        [exact unfold_Schl|exact pscoped_SchlT|fut (pvar 0)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (EClose (Var 0)) EUnit| | | |shelve].
    { eapply e_close with (S0 := SEnd) (x := sh 1 (pvar 0)); [done|fut (sh 1 (pvar 0))|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 14)) (Pair (Var 2) (Var 3))))))
                       EUnit| | | |shelve].
    { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
      eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_app_; [lsplit_tac (EForce (Var 14)) (Pair (Var 2) (Var 3))|apply ub_below_empty| | | |shelve|shelve|shelve].
      { eapply rgl_call; [eapply rr_l, rr_root|]. eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      eapply e_sub_sess2; [|shelve|shelve].
      eapply e_pair_; [lsplit_tac (Var 2) (Var 3)| | | | |shelve].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce (Var 14)) (Pair (Var 4) (Var 7))|apply ub_below_empty| | | |shelve|shelve|shelve].
    { eapply rgl_call; [eapply rr_r, rr_root|]. eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 4) (Var 7)| | | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    reflexivity.
    Unshelve. all: first [tok_tac | age_tac | tsub_tac | exact None | simpl; lia | simpl; done].
  Qed.
End body.

Lemma ringl_typed W Γ n F : hc_fv Γ = ∅ → typed W (Some 4) ∅ Γ (nones n) F ring rgl_ty (Some 0) tid.
Proof.
  intros HΓ. destruct (rgl_body W Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

(** ** main *)

Lemma rgl_hold : hold_at W_rg (Γnew W_rg 0) rg_C rg_xs.
Proof.
  apply hold_at_nil. intros f Hf Hs.
  destruct (fact_map (pt_inst (plist rg_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct f as [u v]. destruct Hs as [Hu Hv]. simpl in E. injection E as <- <-. split.
  - eapply pt_vb_inst; [exact Hu|]. intros [|[|a]] Ha; unfold rg_xs, plist in *; simpl in *; lia.
  - eapply pt_vb_inst; [exact Hv|]. intros [|[|a]] Ha; unfold rg_xs, plist in *; simpl in *; lia.
Qed.

Lemma rgl_typedN : ∃ c ϑ, typed W_rg (Some 4) ∅ hc_empty [] (∅, None) rg_main TUnit c ϑ ∧ meets ϑ 0 0.
Proof.
  eexists _, _. split.
  { unfold rg_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | |shelve].
  { apply (e_new' _ _ _ _ _ _ Schl); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_rg 0).
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce ring) EUnit|apply ub_below_empty| | | |shelve|shelve|shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 2 rg_C (Some (sh 1 (pvar 0))) rgl_T TUnit rg_xs _ _
      (Some (sh 1 (pvar 0))) (TProd (TSess Schl (pvar 0) (Some 0)) (TSess (dual Schl) (pvar 0)‾ (Some 1))));
      [done|apply rgl_hold|done|done|done|].
    apply (ringl_typed _ _ 3). done. }
  lage_tac.
  eapply e_sub_sess2; [|shelve|shelve].
  eapply e_pair_; [lsplit_tac (Var 1) EUnit| | | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  meets_tac.
  Unshelve. all: first [tok_tac | exact None | simpl; lia | simpl; done].
Qed.

Lemma rg_guarded : ∅ ⊢▷ rg_main.
Proof. unfold rg_main, ring, rg_e, let_new. guard_tac. Qed.

Theorem rg_lftyped : ∃ N, ∅ ⊩^N _ W_rg (∅, {[+ rg_main +]}) : TUnit.
Proof.
  destruct rgl_typedN as (c & ϑ & Ht & Hm). exists 4.
  eapply lf_main_typed; [apply strict_wfworld; [apply W_rg_wf|apply W_rg_wfworld]|constructor|exact Ht|apply rg_guarded|exact Hm].
Qed.

Theorem rg_lock_free : lock_free (∅, {[+ rg_main +]}).
Proof.
  destruct rgl_typedN as (c & ϑ & Ht & Hm).
  eapply lf_main; [apply (strict_wfworld _ W_rg_wf W_rg_wfworld)|apply W_rg_wfworld|constructor|exact Ht|apply rg_guarded|exact Hm].
Qed.
