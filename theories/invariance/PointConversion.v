(** * Point conversion of types and environments (§10)

    Aliased points are interchangeable. T ≈_W T′ gives V, E and P at T
    iff at T′ ([rel_tconv]), and Θ ≈_W Θ′ gives V and E at Θ iff at Θ′
    ([rel_econv]). For types, ≈_W is ≈ with ground points compared up
    to ≡_W ([teqW]). For environments it keeps channels and ends and
    relates each end by ≈ and ≡_W ([tconv]). *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export invariance.Monotonicity.

(** ** Types up to aliases *)

Section teqW.
  Context (W : world) (HW : world_wf W).

  Lemma pteqW_eq x y : pteqW W x y → w_eq W x y.
  Proof. intros [->|(_ & _ & H)]; [apply HW|done]. Qed.

  Lemma pteqW_refl x : pteqW W x x.
  Proof. by left. Qed.

  Lemma pteqW_sym x y : pteqW W x y → pteqW W y x.
  Proof. intros [->|(? & ? & ?)]; [by left|right; split_and!; auto using wf_eq_sym]. Qed.

  Lemma pteqW_trans x y z : pteqW W x y → pteqW W y z → pteqW W x z.
  Proof.
    intros [->|(? & ? & ?)] [->|(? & ? & ?)]; [by left|by right..|].
    right. split_and!; [done|done|]. by eapply wf_eq_trans.
  Qed.

  (** In a well-formed world only ground points have proper aliases. *)
  Lemma w_eq_pteqW x y : w_eq W x y → pteqW W x y.
  Proof.
    intros H. destruct (wf_eq_supp _ HW x y H) as [->|[Hx Hy]]; [by left|right].
    destruct (wf_names_const _ HW _ Hx) as [a Ha].
    destruct (wf_names_const _ HW _ Hy) as [b Hb].
    split_and!; [by exists a|by exists b|done].
  Qed.

  Lemma opt_rel_refl o : opt_rel (pteqW W) o o.
  Proof. destruct o; simpl; [apply pteqW_refl|done]. Qed.

  Lemma opt_rel_sym o o' : opt_rel (pteqW W) o o' → opt_rel (pteqW W) o' o.
  Proof. destruct o, o'; simpl; try done. apply pteqW_sym. Qed.

  Lemma opt_rel_trans o o' o'' :
    opt_rel (pteqW W) o o' → opt_rel (pteqW W) o' o'' → opt_rel (pteqW W) o o''.
  Proof. destruct o, o', o''; simpl; try done. apply pteqW_trans. Qed.

  Lemma fact_rel_refl g : fact_rel (pteqW W) g g.
  Proof. destruct g; simpl; split; apply pteqW_refl. Qed.

  Lemma fact_rel_sym g g' : fact_rel (pteqW W) g g' → fact_rel (pteqW W) g' g.
  Proof. destruct g, g'; simpl; try done; intros [? ?]; split; by apply pteqW_sym. Qed.

  Lemma fact_rel_trans g g' g'' :
    fact_rel (pteqW W) g g' → fact_rel (pteqW W) g' g'' → fact_rel (pteqW W) g g''.
  Proof.
    destruct g, g', g''; simpl; try done; intros [? ?] [? ?]; split; by eapply pteqW_trans.
  Qed.

  Lemma bcs_rel_refl n C : bcs_rel (pteqW W) n C C.
  Proof. split; intros g Hg; exists g; split; auto using fact_rel_refl. Qed.

  Lemma bcs_rel_sym n C C' : bcs_rel (pteqW W) n C C' → bcs_rel (pteqW W) n C' C.
  Proof.
    intros [H1 H2]. split; intros g Hg.
    - destruct (H2 g Hg) as (g' & ? & ?). exists g'. split; [done|by apply fact_rel_sym].
    - destruct (H1 g Hg) as (g' & ? & ?). exists g'. split; [done|by apply fact_rel_sym].
  Qed.

  Lemma bcs_rel_trans n C C' C'' :
    bcs_rel (pteqW W) n C C' → bcs_rel (pteqW W) n C' C'' → bcs_rel (pteqW W) n C C''.
  Proof.
    intros [H1 H2] [H3 H4]. split; intros g Hg.
    - destruct (H1 g Hg) as (g' & Hg' & ?). destruct (H3 g' Hg') as (g'' & ? & ?).
      exists g''. split; [done|by eapply fact_rel_trans].
    - destruct (H4 g Hg) as (g' & Hg' & ?). destruct (H2 g' Hg') as (g'' & ? & ?).
      exists g''. split; [done|by eapply fact_rel_trans].
  Qed.

  Lemma teqW_refl T : teqW W T T.
  Proof.
    induction T; simpl; repeat match goal with |- _ ∧ _ => split end;
      auto using opt_rel_refl, pteqW_refl, seq_refl, bcs_rel_refl.
  Qed.

  Lemma teqW_sym T : ∀ U, teqW W T U → teqW W U T.
  Proof.
    induction T; intros [] H; simpl in *; try done; try naive_solver.
    - destruct H as (? & ? & ? & ?). split_and!; auto using opt_rel_sym.
    - destruct H as (<- & ? & ?). split_and!; auto using bcs_rel_sym.
    - destruct H as [? ?]. split; [by apply pteqW_sym|by apply seq_sym].
    - destruct H as (? & <- & ? & ?). split_and!; auto using opt_rel_sym, bcs_rel_sym.
  Qed.

  Lemma teqW_trans T : ∀ U V, teqW W T U → teqW W U V → teqW W T V.
  Proof.
    induction T; intros [] [] H1 H2; simpl in *; try done; try naive_solver.
    - destruct H1 as (? & ? & ? & ?), H2 as (? & ? & ? & ?).
      split_and!; eauto using opt_rel_trans.
    - destruct H1 as (<- & ? & ?), H2 as (<- & ? & ?).
      split_and!; eauto using bcs_rel_trans.
    - destruct H1 as [? ?], H2 as [? ?]. split; [by eapply pteqW_trans|by eapply seq_trans].
    - destruct H1 as (? & <- & ? & ?), H2 as (? & <- & ? & ?).
      split_and!; eauto using opt_rel_trans, bcs_rel_trans.
  Qed.

  Lemma pteqW_shift n x y : pteqW W x y → pteqW W (pt_shift n x) (pt_shift n y).
  Proof.
    intros H. apply w_eq_pteqW. apply wf_eq_shift_n; [done|]. by apply pteqW_eq.
  Qed.

  Lemma pteqW_slot x y i : pteqW W x y → pteqW W (pt_slot x i) (pt_slot y i).
  Proof.
    intros H. apply w_eq_pteqW. apply (wf_eq_slot _ HW). by apply pteqW_eq.
  Qed.

  (** A ground point is fixed by instantiation. *)
  Lemma pn_inst_ground σ p a : pn_root p = NConst a → pn_inst σ p = Pt p 0.
  Proof.
    induction p; simpl; intros H; try done. rewrite IHp by done.
    unfold pt_slot, pt_shift. simpl. by rewrite ?Nat.add_0_l.
  Qed.

  Lemma pt_inst_ground σ x : pt_ground x → pt_inst σ x = x.
  Proof.
    intros [a Ha]. destruct x as [p o]. unfold pt_inst. simpl.
    rewrite (pn_inst_ground σ p a Ha). unfold pt_shift. simpl. by rewrite ?Nat.add_0_l.
  Qed.

  Lemma pteqW_inst_r ρ x y : pteqW W x y → pteqW W (pt_inst ρ x) (pt_inst ρ y).
  Proof.
    intros [->|(Hx & Hy & H)]; [by left|right].
    by rewrite !pt_inst_ground.
  Qed.

  Lemma pteqW_inst_l σ τ x :
    (∀ i, pteqW W (σ i) (τ i)) → pteqW W (pt_inst σ x) (pt_inst τ x).
  Proof.
    intros H. destruct x as [p o]. unfold pt_inst. simpl. apply pteqW_shift.
    induction p; simpl; [by left|apply H|]. apply pteqW_slot, pteqW_shift, IHp.
  Qed.

  Lemma pup_pteqW m σ τ :
    (∀ i, pteqW W (σ i) (τ i)) → ∀ i, pteqW W (pup m σ i) (pup m τ i).
  Proof. intros H i. unfold pup. case_decide; [by left|]. by apply pteqW_inst_r. Qed.

  Lemma bcs_rel_inst_l n σ τ C :
    (∀ i, pteqW W (σ i) (τ i)) → bcs_rel (pteqW W) n (bcs_inst σ C) (bcs_inst τ C).
  Proof.
    intros H. assert (∀ g, fact_rel (pteqW W) (fact_map (pt_inst (pup n σ)) g)
                                    (fact_map (pt_inst (pup n τ)) g)) as Hf.
    { intros []; simpl; split; apply pteqW_inst_l, pup_pteqW, H. }
    split; intros g Hg; apply bcs_open_inst in Hg as (g0 & Hg0 & ->).
    - exists (fact_map (pt_inst (pup n τ)) g0). split; [apply bcs_open_inst; by exists g0|apply Hf].
    - exists (fact_map (pt_inst (pup n σ)) g0). split; [apply bcs_open_inst; by exists g0|apply Hf].
  Qed.

  Lemma bcs_rel_inst_r n ρ C C' :
    bcs_rel (pteqW W) n C C' → bcs_rel (pteqW W) n (bcs_inst ρ C) (bcs_inst ρ C').
  Proof.
    intros [H1 H2]. assert (∀ g g', fact_rel (pteqW W) g g' →
      fact_rel (pteqW W) (fact_map (pt_inst (pup n ρ)) g) (fact_map (pt_inst (pup n ρ)) g')) as Hf.
    { intros [] []; simpl; try done; intros [? ?]; split; by apply pteqW_inst_r. }
    split; intros g Hg; apply bcs_open_inst in Hg as (g0 & Hg0 & ->).
    - destruct (H1 g0 Hg0) as (g1 & ? & ?). exists (fact_map (pt_inst (pup n ρ)) g1).
      split; [apply bcs_open_inst; by exists g1|by apply Hf].
    - destruct (H2 g0 Hg0) as (g1 & ? & ?). exists (fact_map (pt_inst (pup n ρ)) g1).
      split; [apply bcs_open_inst; by exists g1|by apply Hf].
  Qed.

  (** Instantiating with aliased points gives types up to aliases. *)
  Lemma teqW_pinst_l T : ∀ σ τ,
    (∀ i, pteqW W (σ i) (τ i)) → teqW W (pinst_ty σ T) (pinst_ty τ T).
  Proof.
    induction T; intros σ τ H; simpl; repeat match goal with |- _ ∧ _ => split end;
      auto using seq_refl.
    - destruct ub; simpl; [by apply pteqW_inst_l|done].
    - destruct lb; simpl; [by apply pteqW_inst_l|done].
    - by apply bcs_rel_inst_l.
    - apply IHT. by apply pup_pteqW.
    - by apply pteqW_inst_l.
    - destruct lb; simpl; [by apply pteqW_inst_l|done].
    - by apply bcs_rel_inst_l.
    - apply IHT. by apply pup_pteqW.
  Qed.

  Lemma teqW_pinst_r T : ∀ U σ, teqW W T U → teqW W (pinst_ty σ T) (pinst_ty σ U).
  Proof.
    induction T; intros [] σ H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done. by apply pteqW_inst_r.
      + destruct lb, lb0; simpl in *; try done. by apply pteqW_inst_r.
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as (<- & HC & ?). split_and!; [done|by apply bcs_rel_inst_r|by apply IHT].
    - destruct H as [? ?]. split; [by apply pteqW_inst_r|done].
    - destruct H as (Hl & <- & HC & ?). split_and!; [|done|by apply bcs_rel_inst_r|auto].
      destruct lb, lb0; simpl in *; try done. by apply pteqW_inst_r.
  Qed.

  Lemma teqW_ty_inst xs T U : teqW W T U → teqW W (ty_inst xs T) (ty_inst xs U).
  Proof. apply teqW_pinst_r. Qed.

  Lemma teqW_payload m U x y : w_eq W x y → teqW W (payload_at m U x) (payload_at m U y).
  Proof.
    intros H. apply teqW_pinst_l. intros i. unfold plist, slots.
    rewrite !list_lookup_fmap, !length_fmap, length_seq.
    destruct (List.seq 0 m !! i); simpl; [|by left].
    apply pteqW_slot. by apply w_eq_pteqW.
  Qed.
End teqW.

Lemma lb_below_conv W lb lb' H :
  world_wf W → opt_rel (pteqW W) lb lb' → lb_below W lb H → lb_below W lb' H.
Proof.
  intros HW Hr. destruct lb as [x|], lb' as [x'|]; simpl in *; try done.
  intros Hb y Hy. apply pteqW_eq in Hr; [|done].
  destruct (Hb y Hy) as [He|Hl]; [left|right].
  - eapply (wf_eq_trans _ HW); [|exact He]. by apply (wf_eq_sym _ HW).
  - eapply (wf_lt_eq _ HW); [| exact Hl|apply HW]. by apply (wf_eq_sym _ HW).
Qed.

Lemma ub_below_conv W ub ub' F :
  world_wf W → opt_rel (pteqW W) ub ub' → ub_below W ub F → ub_below W ub' F.
Proof.
  intros HW Hr. destruct ub as [x|], ub' as [x'|]; simpl in *; try done.
  intros Hb y Hy. apply pteqW_eq in Hr; [|done].
  eapply (wf_lt_eq _ HW); [|apply Hb, Hy|apply HW]. by apply (wf_eq_sym _ HW).
Qed.

Lemma wext_wf W W' : wext W W' → world_wf W'.
Proof. by intros (_ & _ & _ & [? _]). Qed.

Lemma wext_eq W W' x y : wext W W' → w_eq W x y → w_eq W' x y.
Proof. intros (_ & He & _). auto. Qed.

(** A box constraint up to aliases holds when the other one does (65). *)
Lemma bcs_hold_conv_sub W W' C C' xs :
  world_wf W → world_wf W' → (∀ x y, w_eq W x y → w_eq W' x y) →
  bcs_rel (pteqW W) (length xs) C C' →
  bcs_hold (w_eq W') (w_lt W') C' xs → bcs_hold (w_eq W') (w_lt W') C xs.
Proof.
  intros HW HW' HWW' [HC _] H g Hg.
  assert (∀ z z', pteqW W z z' → w_eq W' (pt_inst (plist xs) z) (pt_inst (plist xs) z')) as Hz.
  { intros z z' Hzz. apply HWW'. apply (pteqW_eq _ HW).
    by apply pteqW_inst_r. }
  destruct (HC g Hg) as (g' & Hg' & Hr). specialize (H g' Hg').
  destruct g as [x y|x y], g' as [x' y'|x' y']; simpl in *; try done; destruct Hr as [H1 H2].
  - eapply (wf_lt_eq _ HW'); [apply Hz, H1|exact H|apply (wf_eq_sym _ HW'), Hz, H2].
  - eapply (wf_eq_trans _ HW'); [apply Hz, H1|].
    eapply (wf_eq_trans _ HW'); [exact H|apply (wf_eq_sym _ HW'), Hz, H2].
Qed.

Lemma bcs_hold_conv W W' C C' xs :
  world_wf W → wext W W' → bcs_rel (pteqW W) (length xs) C C' →
  bcs_hold (w_eq W') (w_lt W') C' xs → bcs_hold (w_eq W') (w_lt W') C xs.
Proof.
  intros HW HWW'. apply bcs_hold_conv_sub; [done|by eapply wext_wf|]. intros. by eapply wext_eq.
Qed.

(** ** The relations are invariant *)

Lemma rel_tconv n :
  (∀ W Θ T T' v, world_wf W → teqW W T T' → Vrel n W Θ T v → Vrel n W Θ T' v) ∧
  (∀ W Θ T T' F e, world_wf W → teqW W T T' →
     Erel n W Θ T F e → Erel n W Θ T' F e) ∧
  (∀ W Σ T T' p, world_wf W → teqW W T T' → Prel n W Σ T p → Prel n W Σ T' p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ ub lb T1 T2 T' v, world_wf W → teqW W (TLolli ub lb T1 T2) T' →
            Vrel n W Θ (TLolli ub lb T1 T2) v → Vrel n W Θ T' v) as Hfun.
  { intros W Θ ub lb T1 T2 [|ub' lb' T1' T2'| | | | |] v HW Ht HVv; simpl in Ht; try done.
      destruct Ht as (Hu & Hl & Ht1 & Ht2).
      apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hsup & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!; [done|done| |].
        { by eapply lb_below_conv. }
        intros W' j Θ' Θ'' w F HW' Hj Hc HVw Hub.
        pose proof (wext_wf _ _ HW') as HW'f.
        eapply (proj1 (proj2 (IHn j Hj))); [done| |].
        { eapply teqW_mono; [|exact Ht2]. intros. by eapply wext_eq. }
        apply (HL W' j Θ' Θ'' w F); [done|done|done| |].
        * eapply (proj1 (IHn j Hj)); [done| |exact HVw].
          apply teqW_sym; [done|]. eapply teqW_mono; [|exact Ht1].
          intros. by eapply wext_eq.
        * eapply ub_below_conv; [done| |exact Hub].
          apply opt_rel_sym; [done|]. destruct ub, ub'; simpl in *; try done.
          destruct Hu as [->|(? & ? & ?)]; [by left|right; split_and!; auto].
          by eapply wext_eq.
      + apply Vrel_lolli_iff. right. exists k, T0. split_and!; [done|done|done|].
        eapply teqW_trans; [done|exact Ht|]. simpl. by split_and!. }
  assert (∀ W Θ T T' v, world_wf W → teqW W T T' →
            Vrel n W Θ T v → Vrel n W Θ T' v) as HV.
  { intros W Θ T. revert W Θ.
    induction T as [|ub lb T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2
                   |m C0 T1 IHT1|s x|lb m C0 T1 IHT1] using ty_ind_ex;
      intros W Θ [|ub' lb' T1' T2'|T1' T2'|T1' T2'|m' C0' T1'|s' x'|lb' m' C0' T1'] v HW Ht HVv;
      simpl in Ht; try done.
    - by eapply Hfun.
    - destruct Ht as [Ht1 Ht2].
      apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      apply Vrel_prod_iff. exists v1, v2, Θ1, Θ2. split_and!; [done|done|by eapply IHT1|by eapply IHT2].
    - destruct Ht as [Ht1 Ht2].
      apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; [split; [done|by eapply IHT1]|split; [done|by eapply IHT2]].
    - destruct Ht as (<- & HC & Ht).
      apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply Vrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros W' xs HW' Hxs HCx HKx. pose proof (wext_wf _ _ HW') as HW'f.
      eapply (IHT1 (plist xs)); [done| |].
      + apply teqW_ty_inst. eapply teqW_mono; [|exact Ht]. intros. by eapply wext_eq.
      + apply HK; [done..| |done].
        eapply (bcs_hold_conv W W' C0 C0'); [done|done| |done]. by rewrite Hxs.
    - destruct Ht as [Hx Hs].
      apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs0 & Hk).
      apply Vrel_sess_iff. exists c, s0, k. split_and!; [done|done| |].
      + by eapply seq_trans.
      + eapply (wf_eq_trans _ HW); [exact Hk|]. by apply pteqW_eq.
    - destruct Ht as (Hl & <- & HC & Ht).
      apply Vrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HCx & H)].
      apply Vrel_ex_iff. split; [by eapply lb_below_conv|]. exists xs. split_and!; [done..| |].
      + eapply (bcs_hold_conv_sub W W C0' C0); [done|done|done| |done].
        rewrite Hxs. by apply bcs_rel_sym.
      + eapply (IHT1 (plist xs)); [done| |exact H]. by apply teqW_ty_inst. }
  split_and!; [exact HV| |].
  - destruct n as [|n']; [intros; apply Erel_0|].
    intros W Θ T T' F e HW Ht HE. revert T' HW Ht.
    induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
    intros T' HW Ht.
    assert (∀ j W0 Θ0 F0 e0, j ≤ n' → world_wf W0 →
              (∀ x y, w_eq W x y → w_eq W0 x y) →
              Erel j W0 Θ0 T F0 e0 → Erel j W0 Θ0 T' F0 e0) as HEj.
    { intros j W0 Θ0 F0 e0 Hj HW0 Hsub.
      apply (proj1 (proj2 (IHn j ltac:(lia)))); [done|].
      by eapply teqW_mono. }
    apply Erel_S_iff. split_and!; [|done|].
    { intros Hirr. eapply HV; [done|exact Ht|]. by apply Hval. }
    intros α e' Hst. specialize (Hstep α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
    + by eapply HEj.
    + destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists Θ1, m, U, s, k. split; [done|].
      intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hc HVw.
      eapply HEj; [lia|by eapply wext_wf| |by apply (H W' j Θ2 Θ1c Θ')].
      intros. by eapply wext_eq.
    + destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done. exact (proj2 HE' T' HW Ht).
    + destruct Hstep as (Θ1 & k & Hhd & HE').
      exists Θ1, k. split; [done|]. exact (proj2 HE' T' HW Ht).
    + destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & ? & ? & ? & ? & HE').
      exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. exact (proj2 HE' T' HW Ht).
    + (* O-New: rename the new point away from the points of T' *)
      intros Hc. destruct (Hstep Hc) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
      destruct (fresh_const (w_names W ∪ tenv_roots Θ ∪ ty_roots T ∪ ty_roots T'
                             ∪ frame_roots F)) as [a1 Ha1].
      destruct (Erel_new_rename _ _ _ _ _ _ _ c s s' a a1 HW Hfr Ha
                  ltac:(set_solver) HE') as (W1' & Hfr' & HE1).
      exists a1, (stysw a a1 s), (stysw a a1 s'), W1'. split_and!.
      * set_solver.
      * by apply sdual_sw.
      * done.
      * eapply HEj; [lia| | |exact HE1].
        -- by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
        -- intros. destruct Hfr' as ((_ & He & _) & _). auto.
    + destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
      exists Θ1, Θ2, ub, lb. split_and!; [done|done|]. by eapply HEj.
  - destruct n as [|n']; [intros; apply Prel_0|].
    intros W Σ T T' p HW Ht HP. revert T' HW Ht.
    induction HP as [W Σ T p Hirr Hrdy Hstep] using Prel_S_ind.
    intros T' HW Ht.
    assert (∀ j W0 Σ0 p0, j ≤ n' → world_wf W0 →
              (∀ x y, w_eq W x y → w_eq W0 x y) →
              Prel j W0 Σ0 T p0 → Prel j W0 Σ0 T' p0) as HPj.
    { intros j W0 Σ0 p0 Hj HW0 Hsub.
      apply (proj2 (proj2 (IHn j ltac:(lia)))); [done|].
      by eapply teqW_mono. }
    apply Prel_S_iff. split_and!; [|done|].
    { intros Hp. destruct (Hirr Hp) as (v & E & -> & ? & HVv & ?).
      exists v, E. split_and!; [done|done| |done]. by eapply HV. }
    intros π q Hst. specialize (Hstep π q Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* Q-Tau: rename the placed points away from the points of T' *)
      destruct Hstep as [Htau Hlink]. split.
      2: { intros Hl Hd. exact (proj2 (Hlink Hl Hd) T' HW Ht). }
      intros Hd. destruct (Htau Hd) as (N & W1 & HN & Hfr & HP').
      destruct (Prel_tau_rename n' (ty_roots T') _ W N W1 Σ T q eq_refl HW Hfr HN HP')
        as (N' & W1' & HN'T & HN' & Hfr' & HP1).
      exists N', W1'. split_and!; [set_solver|done|].
      eapply HPj; [lia| | |exact HP1].
      * by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
      * intros. destruct Hfr' as ((_ & He & _) & _). auto.
    + destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists Σ1, m, U, s, k. split_and!; [done|done|].
      intros W' j Θ2 HW' Hj Hfr Hok HVw.
      eapply HPj; [lia|by eapply wext_wf| |by apply H].
      intros. by eapply wext_eq.
    + destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         ? & ? & ? & ? & ? & ? & HVw & HP').
      exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done. exact (proj2 HP' T' HW Ht).
    + destruct Hstep as (Σ1 & k & Hhd & ? & HP').
      exists Σ1, k. split_and!; [done|done|]. exact (proj2 HP' T' HW Ht).
    + destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & ? & -> & ? & ? & ? & ? & HP').
      exists c, d, Σ1, sc, sd, kc, kd. split_and!; [done..|]. exact (proj2 HP' T' HW Ht).
Qed.

Lemma Vrel_tconv n W Θ T T' v :
  world_wf W → teqW W T T' → Vrel n W Θ T v → Vrel n W Θ T' v.
Proof. apply (proj1 (rel_tconv n)). Qed.

Lemma Erel_tconv n W Θ T T' F e :
  world_wf W → teqW W T T' → Erel n W Θ T F e → Erel n W Θ T' F e.
Proof. apply (proj1 (proj2 (rel_tconv n))). Qed.

Lemma Prel_tconv n W Σ T T' p :
  world_wf W → teqW W T T' → Prel n W Σ T p → Prel n W Σ T' p.
Proof. apply (proj2 (proj2 (rel_tconv n))). Qed.

(** The compositionality lemma for E-Conv up to aliases: semantic
    typing transports along ≈_W, which persists into every later world
    (sharp edges 67). *)
Lemma sem_typed_tconv W Θ Δ F e T T' :
  teqW W T T' → sem_typed W Θ Δ F e T → sem_typed W Θ Δ F e T'.
Proof.
  intros Ht He n W' Θ' Θ'' γ HW Hd Hg. eapply Erel_tconv; [apply HW| |by apply (He n W' Θ')].
  eapply teqW_mono; [|exact Ht]. intros x y. by apply wext_eq.
Qed.

(** A payload typed at P[x] is typed at P[y] for every alias y of x. *)
Lemma Vrel_payload n W Θ m U x y v :
  world_wf W → w_eq W x y → Vrel n W Θ (payload_at m U x) v →
  Vrel n W Θ (payload_at m U y) v.
Proof. intros HW Hxy. apply Vrel_tconv; [done|]. by apply teqW_payload. Qed.

(** ** Environments up to aliases

    Θ ≈_W Θ′: the same channels with the same ends, each end's session
    type up to ≈ and its point up to ≡_W. Composition reads ≡_W already
    (sharp edges 40), so composing commutes with ≈_W. *)

Definition entry_conv (W : world) (e e' : sty * point) : Prop :=
  seq e.1 e'.1 ∧ w_eq W e.2 e'.2.

Definition ends_conv (W : world) (o o' : ends) : Prop :=
  match o, o' with
  | One e, One e' => entry_conv W e e'
  | Both e1 e2, Both e1' e2' => entry_conv W e1 e1' ∧ entry_conv W e2 e2'
  | _, _ => False
  end.

Definition oconv (W : world) (o o' : option ends) : Prop :=
  match o, o' with
  | Some a, Some b => ends_conv W a b
  | None, None => True
  | _, _ => False
  end.

Definition tconv (W : world) (Θ Θ' : tenv) : Prop := ∀ c, oconv W (Θ !! c) (Θ' !! c).

(** Finite choice for maps: a pointwise choice that is [None] outside a
    finite set of keys gives a map. *)
Lemma map_choice2 {A B} (P : chan → option A → option B → Prop) (D : gset chan) :
  (∀ c, ∃ o1 o2, P c o1 o2) → (∀ c, c ∉ D → P c None None) →
  ∃ (m1 : gmap chan A) (m2 : gmap chan B), ∀ c, P c (m1 !! c) (m2 !! c).
Proof.
  revert P. induction D as [|c0 D Hc0 IH] using set_ind_L; intros P Hall Hout.
  { exists ∅, ∅. intros c. rewrite !lookup_empty. apply Hout. set_solver. }
  destruct (Hall c0) as (o1 & o2 & H0).
  set (P' := λ c a b, if decide (c = c0) then a = None ∧ b = None else P c a b).
  destruct (IH P') as (m1 & m2 & Hm).
  { intros c. unfold P'. case_decide; [by exists None, None|apply Hall]. }
  { intros c Hc. unfold P'. case_decide; [done|]. apply Hout. set_solver. }
  exists (match o1 with Some a => <[c0 := a]> m1 | None => delete c0 m1 end),
         (match o2 with Some b => <[c0 := b]> m2 | None => delete c0 m2 end).
  intros c. destruct (decide (c = c0)) as [->|Hne].
  - destruct o1, o2; rewrite ?lookup_insert_eq, ?lookup_delete_eq; done.
  - specialize (Hm c). unfold P' in Hm. rewrite decide_False in Hm by done.
    destruct o1, o2; rewrite ?lookup_insert_ne, ?lookup_delete_ne by done; done.
Qed.

Section tconv.
  Context (W : world) (HW : world_wf W).

  Lemma entry_conv_refl e : entry_conv W e e.
  Proof. split; [apply seq_refl|apply HW]. Qed.

  Lemma entry_conv_sym e e' : entry_conv W e e' → entry_conv W e' e.
  Proof. intros [? ?]. split; [by apply seq_sym|by apply (wf_eq_sym _ HW)]. Qed.

  Lemma ends_conv_refl o : ends_conv W o o.
  Proof. destruct o; simpl; auto using entry_conv_refl. Qed.

  Lemma ends_conv_sym o o' : ends_conv W o o' → ends_conv W o' o.
  Proof. destruct o, o'; simpl; naive_solver eauto using entry_conv_sym. Qed.

  Lemma tconv_refl Θ : tconv W Θ Θ.
  Proof. intros c. destruct (Θ !! c); simpl; auto using ends_conv_refl. Qed.

  Lemma tconv_sym Θ Θ' : tconv W Θ Θ' → tconv W Θ' Θ.
  Proof.
    intros H c. specialize (H c). destruct (Θ !! c), (Θ' !! c); simpl in *; try done.
    by apply ends_conv_sym.
  Qed.

  Lemma tconv_dom Θ Θ' : tconv W Θ Θ' → dom Θ = dom Θ'.
  Proof.
    intros H. apply set_eq. intros c. rewrite !elem_of_dom. specialize (H c).
    destruct (Θ !! c), (Θ' !! c); simpl in *; naive_solver.
  Qed.

  Lemma tconv_empty Θ' : tconv W ∅ Θ' → Θ' = ∅.
  Proof.
    intros H. apply map_empty. intros c. specialize (H c).
    rewrite lookup_empty in H. by destruct (Θ' !! c).
  Qed.

  Lemma tconv_insert Θ Θ' c o o' :
    tconv W Θ Θ' → ends_conv W o o' → tconv W (<[c := o]> Θ) (<[c := o']> Θ').
  Proof.
    intros H Ho d. destruct (decide (d = c)) as [->|Hne].
    - by rewrite !lookup_insert_eq.
    - rewrite !lookup_insert_ne by done. apply H.
  Qed.

  Lemma tconv_entry Θ Θ' k e :
    tconv W Θ Θ' → tenv_entry Θ k = Some e →
    ∃ e', tenv_entry Θ' k = Some e' ∧ entry_conv W e e'.
  Proof.
    intros H He. destruct k as [c b]. unfold tenv_entry in *. simpl in *.
    specialize (H c). destruct (Θ !! c) as [[]|], (Θ' !! c) as [[]|], b;
      simpl in *; simplify_eq; try done; naive_solver.
  Qed.

  Lemma tconv_entry_none Θ Θ' k :
    tconv W Θ Θ' → tenv_entry Θ k = None → tenv_entry Θ' k = None.
  Proof.
    intros H He. destruct k as [c b]. unfold tenv_entry in *. simpl in *.
    specialize (H c). destruct (Θ !! c) as [[]|], (Θ' !! c) as [[]|], b;
      simpl in *; simplify_eq; try done.
  Qed.

  Lemma tconv_heads Θ Θ' y' :
    tconv W Θ Θ' → y' ∈ tenv_heads Θ' → ∃ y, y ∈ tenv_heads Θ ∧ w_eq W y y'.
  Proof.
    intros H Hy. apply elem_of_tenv_heads in Hy as (c & o' & Hc & Hy).
    specialize (H c). rewrite Hc in H. destruct (Θ !! c) as [o|] eqn:Ho; [|done].
    destruct o as [e|e1 e2], o' as [e'|e1' e2']; simpl in *; try done.
    - apply elem_of_singleton in Hy as ->. exists e.2.
      split; [apply elem_of_tenv_heads; exists c, (One e); split; [done|];
              simpl; set_solver|apply H].
    - destruct H as [[_ H1] [_ H2]].
      apply elem_of_union in Hy as [->%elem_of_singleton| ->%elem_of_singleton].
      + exists e1.2. split; [|done]. apply elem_of_tenv_heads.
        exists c, (Both e1 e2). split; [done|]. simpl. set_solver.
      + exists e2.2. split; [|done]. apply elem_of_tenv_heads.
        exists c, (Both e1 e2). split; [done|]. simpl. set_solver.
  Qed.

  (** Selection reads only the heads of the session types, which ≈
      keeps. *)
  Lemma selects_conv Θ Θ' σ k : tconv W Θ Θ' → selects Θ σ k → selects Θ' σ k.
  Proof.
    intros H. destruct σ as [c v|c v|c|cd]; simpl.
    - intros [Hk (e & m & T & s & He & Hu)]. split; [done|].
      destruct (tconv_entry _ _ _ _ H He) as (e' & He' & [Hs _]).
      destruct (seq_rcv_inv e'.1 e.1 m T s) as (U & s' & Hu' & _); [by apply seq_sym|done|].
      eauto 10.
    - intros [Hk (e & m & T & s & He & Hu)]. split; [done|].
      destruct (tconv_entry _ _ _ _ H He) as (e' & He' & [Hs _]).
      destruct (seq_snd_inv e'.1 e.1 m T s) as (U & s' & Hu' & _); [by apply seq_sym|done|].
      eauto 10.
    - intros [Hk (e & He & Hu & Ht)]. split; [done|].
      destruct (tconv_entry _ _ _ _ H He) as (e' & He' & [Hs _]).
      exists e'. split_and!; [done| |].
      + apply (seq_end_inv _ e.1); [by apply seq_sym|done].
      + intros Hk2 f' Hf' Hf'u.
        destruct (tenv_entry Θ (c, false)) as [f|] eqn:Ef.
        * destruct (tconv_entry _ _ _ _ H Ef) as (f'' & Hf'' & [Hsf _]).
          rewrite Hf' in Hf''. injection Hf'' as <-.
          apply (Ht Hk2 f eq_refl). by apply (seq_end_inv _ f'.1).
        * apply (tconv_entry_none _ _ _ H) in Ef. congruence.
    - intros [Hk [e He]]. split; [done|].
      destruct (tconv_entry _ _ _ _ H He) as (e' & He' & _). by eexists.
  Qed.

  Lemma offered_t_conv Θ Θ' t k :
    tconv W Θ Θ' → offered_t Θ t k ↔ offered_t Θ' t k.
  Proof.
    intros H. split; intros (σ & t' & Hs & Hk); exists σ, t'; split; try done.
    - by eapply selects_conv.
    - eapply selects_conv; [by apply tconv_sym|done].
  Qed.

  Lemma ready_t_conv Θ Θ' F t : tconv W Θ Θ' → ready_t W Θ F t → ready_t W Θ' F t.
  Proof.
    intros H Hr Hs. destruct (Hr Hs) as [Hv Ha]. split.
    - intros Hno. apply Hv. intros k Hk. apply (Hno k). by apply (offered_t_conv Θ).
    - destruct Ha as [?|Ha]; [by left|right]. intros k e' Ho He'.
      pose proof (proj2 (offered_t_conv Θ Θ' t k H) Ho) as Ho0.
      destruct (tconv_entry _ _ _ _ (tconv_sym _ _ H) He') as (e & He & [_ Hee]).
      destruct (Ha k e Ho0 He) as [H1 H2]. split.
      + intros k' f' Hf' Hn.
        destruct (tconv_entry _ _ _ _ (tconv_sym _ _ H) Hf') as (f & Hf & [_ Hff]).
        assert (¬ offered_t Θ t k') as Hn0.
        { intros Ho'. apply Hn. by apply (offered_t_conv Θ). }
        pose proof (H1 k' f Hf Hn0) as Hlt.
        unfold entry_head in *. eapply (wf_lt_eq _ HW); [|exact Hlt|];
          first [done|by apply (wf_eq_sym _ HW)].
      + intros y Hy. pose proof (H2 y Hy) as Hlt.
        unfold entry_head in *. eapply (wf_lt_eq _ HW); [|exact Hlt|apply (wf_eq_refl _ HW)].
        first [done|by apply (wf_eq_sym _ HW)].
  Qed.

  Lemma insert_over (Θ : tenv) c o o2 :
    Θ !! c = Some o → <[c := o]> (<[c := o2]> Θ) = Θ.
  Proof.
    intros H. apply map_eq. intros d. destruct (decide (d = c)) as [->|Hne].
    - by rewrite lookup_insert_eq.
    - by rewrite !lookup_insert_ne.
  Qed.

  (** Taking one end off, and putting one on. *)
  Lemma tconv_unext Θm c e Θ Θ' :
    tconv W Θ Θ' → tenv_ext Θm c e Θ →
    ∃ e' Θm', tenv_ext Θm' c e' Θ' ∧ entry_conv W e e' ∧ tconv W Θm Θm'.
  Proof.
    intros H [[Hm ->]|(f & Hm & [-> | ->])]; pose proof (H c) as Hc;
      rewrite lookup_insert_eq in Hc; destruct (Θ' !! c) as [o'|] eqn:Ho'; try done.
    - destruct o' as [e'|]; simpl in Hc; try done.
      exists e', (delete c Θ'). split_and!; [|done|].
      + left. split; [apply lookup_delete_eq|]. by rewrite insert_delete_id.
      + intros d. destruct (decide (d = c)) as [->|Hne].
        * by rewrite Hm, lookup_delete_eq.
        * rewrite lookup_delete_ne by done. specialize (H d).
          by rewrite lookup_insert_ne in H.
    - destruct o' as [|e' f']; simpl in Hc; try done. destruct Hc as [He Hf].
      exists e', (<[c := One f']> Θ'). split_and!; [|done|].
      + right. exists f'. split; [apply lookup_insert_eq|]. left.
        by rewrite insert_over.
      + intros d. destruct (decide (d = c)) as [->|Hne].
        * by rewrite Hm, lookup_insert_eq.
        * rewrite lookup_insert_ne by done. specialize (H d).
          by rewrite lookup_insert_ne in H.
    - destruct o' as [|f' e']; simpl in Hc; try done. destruct Hc as [Hf He].
      exists e', (<[c := One f']> Θ'). split_and!; [|done|].
      + right. exists f'. split; [apply lookup_insert_eq|]. right.
        by rewrite insert_over.
      + intros d. destruct (decide (d = c)) as [->|Hne].
        * by rewrite Hm, lookup_insert_eq.
        * rewrite lookup_insert_ne by done. specialize (H d).
          by rewrite lookup_insert_ne in H.
  Qed.

  Lemma tconv_ext Θm Θm' c e e' Θ :
    tconv W Θm Θm' → entry_conv W e e' → tenv_ext Θm c e Θ →
    ∃ Θ', tenv_ext Θm' c e' Θ' ∧ tconv W Θ Θ'.
  Proof.
    intros H He [[Hm ->]|(f & Hm & [-> | ->])]; pose proof (H c) as Hc;
      rewrite Hm in Hc; destruct (Θm' !! c) as [o'|] eqn:Ho'; try done.
    - exists (<[c := One e']> Θm'). split; [by left|]. by apply tconv_insert.
    - destruct o' as [f'|]; simpl in Hc; try done.
      exists (<[c := Both e' f']> Θm'). split; [right; exists f'; by split; [|left]|].
      apply tconv_insert; [done|]. by split.
    - destruct o' as [f'|]; simpl in Hc; try done.
      exists (<[c := Both f' e']> Θm'). split; [right; exists f'; by split; [|right]|].
      apply tconv_insert; [done|]. by split.
  Qed.
End tconv.

Lemma ends_join_cases a b c :
  ends_join a b c →
  (a = None ∧ b = None ∧ c = None) ∨ (∃ o, a = Some o ∧ b = None ∧ c = Some o) ∨
  (∃ o, a = None ∧ b = Some o ∧ c = Some o) ∨
  (∃ e1 e2, a = Some (One e1) ∧ b = Some (One e2) ∧
     (c = Some (Both e1 e2) ∨ c = Some (Both e2 e1))).
Proof. destruct 1; [left|right; left|right; right; left|right; right; right..]; eauto 10. Qed.

Section tconv_comp.
  Context (W : world) (HW : world_wf W).

  Lemma entry_conv_dual e1 e2 e1' e2' :
    entry_conv W e1 e1' → entry_conv W e2 e2' →
    w_eq W e1.2 e2.2 ∧ sdual e1.1 e2.1 → w_eq W e1'.2 e2'.2 ∧ sdual e1'.1 e2'.1.
  Proof.
    intros [Hs1 Hx1] [Hs2 Hx2] [Hx Hs]. split.
    - eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|].
      by eapply (wf_eq_trans _ HW).
    - eapply sdual_seq_l; [exact Hs1|]. by eapply sdual_seq_r.
  Qed.

  (** Splitting a composition along ≈. *)
  Lemma tconv_comp_split Θ Θ1 Θ2 Θ' :
    tenv_comp (w_eq W) Θ Θ1 Θ2 → tconv W Θ Θ' →
    ∃ Θ1' Θ2', tenv_comp (w_eq W) Θ' Θ1' Θ2' ∧ tconv W Θ1 Θ1' ∧ tconv W Θ2 Θ2'.
  Proof.
    intros [Hj Hd] H.
    destruct (map_choice2 (λ c o1 o2, ends_join o1 o2 (Θ' !! c) ∧
                oconv W (Θ1 !! c) o1 ∧ oconv W (Θ2 !! c) o2) (dom Θ'))
      as (Θ1' & Θ2' & HP).
    { intros c. specialize (H c).
      destruct (ends_join_cases _ _ _ (Hj c)) as
        [(-> & -> & E)|[(o & -> & -> & E)|[(o & -> & -> & E)|(e1 & e2 & -> & -> & [E|E])]]];
        rewrite E in H; destruct (Θ' !! c) as [o'|]; try done.
      - exists None, None. split_and!; [constructor|done|done].
      - exists (Some o'), None. split_and!; [constructor|done|done].
      - exists None, (Some o'). split_and!; [constructor|done|done].
      - destruct o' as [|e1' e2']; [done|]. destruct H as [H1 H2].
        exists (Some (One e1')), (Some (One e2')). split_and!; [constructor|done|done].
      - destruct o' as [|e2' e1']; [done|]. destruct H as [H2 H1].
        exists (Some (One e1')), (Some (One e2')). split_and!; [constructor|done|done]. }
    { intros c Hc. apply not_elem_of_dom in Hc. rewrite Hc.
      specialize (H c). rewrite Hc in H.
      destruct (ends_join_cases _ _ _ (Hj c)) as
        [(-> & -> & E)|[(o & -> & -> & E)|[(o & -> & -> & E)|(e1 & e2 & -> & -> & [E|E])]]];
        rewrite E in H; try done. split_and!; [constructor|done|done]. }
    exists Θ1', Θ2'. split_and!.
    - split; [intros c; apply HP|].
      intros c e1' e2' H1' H2'. destruct (HP c) as (_ & Hc1 & Hc2).
      rewrite H1' in Hc1. rewrite H2' in Hc2.
      destruct (Θ1 !! c) as [[e1|]|] eqn:E1; try done.
      destruct (Θ2 !! c) as [[e2|]|] eqn:E2; try done.
      apply (entry_conv_dual e1 e2); [done|done|]. by apply (Hd c).
    - intros c. apply HP.
    - intros c. apply HP.
  Qed.

  (** Joining with a converted part. *)
  Lemma tconv_comp_join Θ1 Θ1' Θ2 Θ12' :
    tenv_comp (w_eq W) Θ12' Θ1' Θ2 → tconv W Θ1 Θ1' →
    ∃ Θ12, tenv_comp (w_eq W) Θ12 Θ1 Θ2 ∧ tconv W Θ12 Θ12'.
  Proof.
    intros [Hj Hd] H.
    destruct (map_choice2 (B := unit) (λ c o _, ends_join (Θ1 !! c) (Θ2 !! c) o ∧
                oconv W o (Θ12' !! c)) (dom Θ12')) as (Θ12 & _ & HP).
    { intros c. specialize (H c).
      destruct (ends_join_cases _ _ _ (Hj c)) as
        [(E1 & -> & ->)|[(o & E1 & -> & ->)|[(o & E1 & -> & ->)|(e1' & e2 & E1 & -> & [->| ->])]]];
        rewrite E1 in H; destruct (Θ1 !! c) as [o1|]; try done.
      - exists None, None. split; [constructor|done].
      - exists (Some o1), None. split; [constructor|done].
      - exists (Some o), None. split; [constructor|]. apply (ends_conv_refl W HW).
      - destruct o1 as [e1|]; [|done].
        exists (Some (Both e1 e2)), None. split; [constructor|].
        split; [done|apply (entry_conv_refl W HW)].
      - destruct o1 as [e1|]; [|done].
        exists (Some (Both e2 e1)), None. split; [constructor|].
        split; [apply (entry_conv_refl W HW)|done]. }
    { intros c Hc. apply not_elem_of_dom in Hc. rewrite Hc.
      specialize (H c).
      destruct (ends_join_cases _ _ _ (Hj c)) as
        [(E1 & -> & E)|[(o & E1 & -> & E)|[(o & E1 & -> & E)|(e1' & e2 & E1 & -> & [E|E])]]];
        rewrite Hc in E; try done. rewrite E1 in H. destruct (Θ1 !! c); [done|].
      split; [constructor|done]. }
    exists Θ12. split.
    - split; [intros c; apply HP|].
      intros c e1 e2 H1 H2. specialize (H c). rewrite H1 in H.
      destruct (Θ1' !! c) as [[e1'|]|] eqn:E1'; try done.
      apply (entry_conv_dual e1' e2); [by apply entry_conv_sym|apply entry_conv_refl; done|].
      by apply (Hd c).
    - intros c. apply HP.
  Qed.
End tconv_comp.

Lemma tconv_mono W W' Θ Θ' :
  (∀ x y, w_eq W x y → w_eq W' x y) → tconv W Θ Θ' → tconv W' Θ Θ'.
Proof.
  intros Hm H c. specialize (H c).
  destruct (Θ !! c) as [[]|], (Θ' !! c) as [[]|]; simpl in *; try done;
    unfold entry_conv in *; naive_solver.
Qed.

Lemma tconv_singleton_inv W c o Θ' :
  tconv W {[c := o]} Θ' → ∃ o', Θ' = {[c := o']} ∧ ends_conv W o o'.
Proof.
  intros H. pose proof (H c) as Hc. rewrite lookup_singleton_eq in Hc.
  destruct (Θ' !! c) as [o'|] eqn:Ho'; [|done]. exists o'. split; [|done].
  apply map_eq. intros d. destruct (decide (d = c)) as [->|Hne].
  - by rewrite Ho', lookup_singleton_eq.
  - rewrite lookup_singleton_ne by done. specialize (H d).
    rewrite lookup_singleton_ne in H by done. by destruct (Θ' !! d).
Qed.

Lemma teq_teqW W T U : teq T U → teqW W T U.
Proof.
  unfold teq. revert U. induction T; intros [] H; simpl in *; try done.
  - destruct H as (-> & -> & ? & ?). split_and!; [apply opt_rel_refl..|auto|auto].
  - destruct H. split; auto.
  - destruct H. split; auto.
  - destruct H as (<- & <- & ?). split_and!; [done|apply bcs_rel_refl|auto].
  - destruct H as [<- ?]. split; [by left|done].
  - destruct H as (<- & <- & <- & ?). split_and!; [apply opt_rel_refl|done|apply bcs_rel_refl|auto].
Qed.

(** ** Environments up to ≈ leave V and E unchanged (Entry conversion) *)

Lemma rel_econv n :
  (∀ W Θ Θ' T v, world_wf W → tconv W Θ Θ' → Vrel n W Θ T v → Vrel n W Θ' T v) ∧
  (∀ W Θ Θ' T F e, world_wf W → tconv W Θ Θ' →
     Erel n W Θ T F e → Erel n W Θ' T F e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ Θ' T v, world_wf W → tconv W Θ Θ' →
            Vrel n W Θ T v → Vrel n W Θ' T v) as HV.
  { intros W Θ Θ' T. revert Θ Θ'.
    assert (∀ Θ Θ' lb, world_wf W → tconv W Θ Θ' → lb_below W lb (tenv_heads Θ) →
              lb_below W lb (tenv_heads Θ')) as Hlbc.
    { intros Θ Θ' lb HW Hc Hlb. destruct lb as [x|]; simpl in *.
      - intros y' Hy'. destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & Hyy).
        destruct (Hlb y Hy) as [He|Hl]; [left|right].
        + by eapply (wf_eq_trans _ HW).
        + eapply (wf_lt_eq _ HW); [apply HW|exact Hl|exact Hyy].
      - apply set_eq. intros y'. split; [|set_solver]. intros Hy'.
        destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & _). set_solver. }
    induction T as [|ub lb T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2
                   |m C0 T1 IHT1|s x|lb m C0 T1 IHT1] using ty_ind_ex;
      intros Θ Θ' v HW Hc HVv.
    - apply Vrel_unit_iff in HVv as [-> ->]. apply Vrel_unit_iff.
      split; [by apply (tconv_empty W)|done].
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hsup & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!; [done| | |].
        * by rewrite <-(tconv_dom W Θ Θ').
        * destruct lb as [x|]; simpl in *.
          -- intros y' Hy'. destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & Hyy).
             destruct (Hlb y Hy) as [He|Hl]; [left|right].
             ++ by eapply (wf_eq_trans _ HW).
             ++ eapply (wf_lt_eq _ HW); [apply HW|exact Hl|exact Hyy].
          -- apply set_eq. intros y'. split; [|set_solver]. intros Hy'.
             destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & _). set_solver.
        * intros W' j Θa Θ'' w F HW' Hj Hcomp HVw Hub.
          assert (world_wf W') as HW'f by (by eapply wext_wf).
          destruct (tconv_comp_join W' HW'f Θ Θ' Θa Θ'' Hcomp) as (Θ0 & Hc0 & Hconv).
          { eapply tconv_mono; [|exact Hc]. intros. by eapply wext_eq. }
          eapply (proj2 (IHn j Hj)); [done|exact Hconv|].
          by apply (HL W' j Θa Θ0 w F).
      + apply (tconv_empty W) in Hc as ->. apply Vrel_lolli_iff. right.
        by exists k, T0.
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      destruct (tconv_comp_split W HW Θ Θ1 Θ2 Θ' Hsp Hc) as (Θ1' & Θ2' & Hsp' & Hc1 & Hc2).
      apply Vrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; eauto.
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; eauto.
    - apply Vrel_box_iff in HVv as (-> & HB).
      apply (tconv_empty W) in Hc as ->. by apply Vrel_box_iff.
    - apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs0 & Hk).
      destruct (tconv_singleton_inv W c _ Θ' Hc) as ([[s0' k']|] & -> & Ho); [|done].
      destruct Ho as [Hs Hkk]. simpl in *.
      apply Vrel_sess_iff. exists c, s0', k'. split_and!; [done|done| |].
      + eapply seq_trans; [by apply seq_sym|exact Hs0].
      + eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|exact Hk].
    - apply Vrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HCx & H)].
      apply Vrel_ex_iff. split; [by eapply Hlbc|]. exists xs. split_and!; [done..|].
      by apply (IHT1 (plist xs) Θ Θ'). }
  split; [exact HV|].
  destruct n as [|n']; [intros; apply Erel_0|].
  intros W Θ Θ' T F e HW Hc HE. revert Θ' HW Hc.
  induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
  intros Θ' HW Hc.
  assert (∀ j W0 Θ0 Θ0' e0, j ≤ n' → world_wf W0 → tconv W0 Θ0 Θ0' →
            Erel j W0 Θ0 T F e0 → Erel j W0 Θ0' T F e0) as HEj.
  { intros j ? ? ? ? Hj. apply (proj2 (IHn j ltac:(lia))). }
  apply Erel_S_iff. split_and!.
  { intros Hirr. eapply HV; [done|exact Hc|]. by apply Hval. }
  { intros Hirr. eapply ready_t_conv; [done|exact Hc|]. by apply Hrdy. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
  - by eapply HEj.
  - (* O-Recv *)
    destruct Hstep as (Θ1 & m & U & s & k & (s0 & Hext & Hu) & H).
    destruct (tconv_unext W Θ1 c (s0, k) Θ Θ' Hc Hext)
      as ([s0' k'] & Θ1' & Hext' & [Hs Hkk] & Hc1). simpl in Hs, Hkk.
    destruct (seq_rcv_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
      [by apply seq_sym|done|].
    exists Θ1', m, U', s'', k'. split; [by exists s0'|].
    intros W' j Θ2 Θ1c' Θ'' HW' Hj HextT Hcomp HVw.
    assert (world_wf W') as HW'f by (by eapply wext_wf).
    assert (∀ x y, w_eq W x y → w_eq W' x y) as Hsub by (intros; by eapply wext_eq).
    destruct (tconv_ext W' Θ1' Θ1 c (s'', pt_shift 1 k') (s, pt_shift 1 k) Θ1c')
      as (Θ1c & Hext1 & Hc1c).
    { apply (tconv_sym W' HW'f). by eapply tconv_mono. }
    { split; simpl; [done|]. apply Hsub. apply (wf_eq_shift _ HW).
      by apply (wf_eq_sym _ HW). }
    { done. }
    destruct (tconv_comp_join W' HW'f Θ1c Θ1c' Θ2 Θ'' Hcomp) as (Θ0 & Hc0 & Hconv);
      [by apply (tconv_sym W' HW'f)|].
    assert (Vrel j W' Θ2 (payload_at m U k) w) as HVw0.
    { eapply Vrel_tconv; [done| |exact HVw].
      eapply teqW_trans; [done|apply teq_teqW, teq_ty_inst, HU|].
      apply teqW_payload; [done|]. apply Hsub. by apply (wf_eq_sym _ HW). }
    pose proof (H W' j Θ2 Θ1c Θ0 HW' Hj Hext1 Hc0 HVw0) as HE'.
    eapply HEj; [lia|done|exact Hconv|exact HE'].
  - (* O-Send *)
    destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & ΘS & (s0 & Hext & Hu) &
                       Hsp & HVw & Hext1 & HE').
    destruct (tconv_unext W Θr c (s0, k) Θ Θ' Hc Hext)
      as ([s0' k'] & Θr' & Hext' & [Hs Hkk] & Hcr). simpl in Hs, Hkk.
    destruct (seq_snd_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
      [by apply seq_sym|done|].
    destruct (tconv_comp_split W HW Θr Θ1 Θ2 Θr' Hsp Hcr) as (Θ1' & Θ2' & Hsp' & Hc1 & Hc2).
    destruct (tconv_ext W Θ1 Θ1' c (s, pt_shift 1 k) (s'', pt_shift 1 k') ΘS Hc1)
      as (Θ''' & Hext3 & Hc3); [|done|].
    { split; simpl; [by apply seq_sym|]. by apply (wf_eq_shift _ HW). }
    exists Θr', Θ1', Θ2', m, U', s'', k', Θ'''. split_and!.
    + by exists s0'.
    + done.
    + eapply Vrel_tconv; [done| |by eapply HV].
      eapply teqW_trans; [done|apply teqW_payload; [done|exact Hkk]|].
      apply teq_teqW, teq_ty_inst. by apply teq_sym.
    + done.
    + exact (proj2 HE' _ HW Hc3).
  - (* O-Close *)
    destruct Hstep as (Θ1 & k & (s0 & Hext & Hu) & HE').
    destruct (tconv_unext W Θ1 c (s0, k) Θ Θ' Hc Hext)
      as ([s0' k'] & Θ1' & Hext' & [Hs Hkk] & Hc1). simpl in Hs, Hkk.
    exists Θ1', k'. split.
    + exists s0'. split; [done|]. apply (seq_end_inv _ s0); [by apply seq_sym|done].
    + exact (proj2 HE' _ HW Hc1).
  - (* O-Link *)
    destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd & -> & Hext1 & Hext2 &
                       Hdu & Hal & HE').
    destruct (tconv_unext W Θm c (sc, kc) Θ Θ' Hc Hext2)
      as ([sc' kc'] & Θm' & Hext2' & [Hsc Hkc] & Hcm). simpl in Hsc, Hkc.
    destruct (tconv_unext W Θ1 d (sd, kd) Θm Θm' Hcm Hext1)
      as ([sd' kd'] & Θ1' & Hext1' & [Hsd Hkd] & Hc1). simpl in Hsd, Hkd.
    exists c, d, Θ1', Θm', sc', sd', kc', kd'. split_and!; [done|done|done| | |].
    + eapply sdual_seq_l; [exact Hsd|]. by eapply sdual_seq_r.
    + eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|].
      eapply (wf_eq_trans _ HW); [exact Hal|exact Hkd].
    + exact (proj2 HE' _ HW Hc1).
  - (* O-New: rename the new point away from the points of Θ' *)
    intros Hc0. rewrite <-(tconv_dom W Θ Θ' Hc) in Hc0.
    destruct (Hstep Hc0) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
    destruct (fresh_const (w_names W ∪ tenv_roots Θ ∪ tenv_roots Θ' ∪ ty_roots T
                           ∪ frame_roots F)) as [a1 Ha1].
    destruct (Erel_new_rename _ _ _ _ _ _ _ c s s' a a1 HW Hfr Ha
                ltac:(set_solver) HE') as (W1' & Hfr' & HE1).
    exists a1, (stysw a a1 s), (stysw a a1 s'), W1'. split_and!.
    + set_solver.
    + by apply sdual_sw.
    + done.
    + assert (world_wf W1') as HW1 by (by destruct Hfr' as ((_ & _ & _ & [? _]) & _)).
      eapply HEj; [lia|done| |exact HE1].
      apply (tconv_insert W1'); [|apply (ends_conv_refl W1' HW1)].
      eapply tconv_mono; [|exact Hc]. intros. destruct Hfr' as ((_ & He & _) & _). auto.
  - (* O-Spawn *)
    destruct Hstep as (Θ1 & Θ2 & ub & lb & Hsp & HVw & HE').
    destruct (tconv_comp_split W HW Θ Θ1 Θ2 Θ' Hsp Hc) as (Θ1' & Θ2' & Hsp' & Hc1 & Hc2).
    exists Θ1', Θ2', ub, lb. split_and!; [done|by eapply HV|].
    eapply HEj; [lia|done|exact Hc2|exact HE'].
Qed.

Lemma Vrel_econv n W Θ Θ' T v :
  world_wf W → tconv W Θ Θ' → Vrel n W Θ T v → Vrel n W Θ' T v.
Proof. apply (proj1 (rel_econv n)). Qed.

Lemma Erel_econv n W Θ Θ' T F e :
  world_wf W → tconv W Θ Θ' → Erel n W Θ T F e → Erel n W Θ' T F e.
Proof. apply (proj2 (rel_econv n)). Qed.

(** ** Interfaces up to aliases leave P unchanged (Entry conversion for P) *)

Definition sconv (W : world) (Σ Σ' : senv) : Prop :=
  ∀ c, match Σ !! c, Σ' !! c with
       | Some e, Some e' => entry_conv W e e'
       | None, None => True
       | _, _ => False
       end.

Section sconv.
  Context (W : world) (HW : world_wf W).

  Lemma sconv_tconv Σ Σ' : sconv W Σ Σ' → tconv W (tenv_of Σ) (tenv_of Σ').
  Proof.
    intros H c. specialize (H c). unfold tenv_of. rewrite !lookup_fmap.
    destruct (Σ !! c), (Σ' !! c); simpl in *; done.
  Qed.

  Lemma sconv_dom Σ Σ' : sconv W Σ Σ' → dom Σ = dom Σ'.
  Proof.
    intros H. apply set_eq. intros c. rewrite !elem_of_dom. specialize (H c).
    destruct (Σ !! c), (Σ' !! c); naive_solver.
  Qed.

  Lemma sconv_refl Σ : sconv W Σ Σ.
  Proof. intros c. destruct (Σ !! c); [apply (entry_conv_refl W HW)|done]. Qed.

  Lemma sconv_insert Σ Σ' c e e' :
    sconv W Σ Σ' → entry_conv W e e' → sconv W (<[c := e]> Σ) (<[c := e']> Σ').
  Proof.
    intros H He d. destruct (decide (d = c)) as [->|Hne].
    - by rewrite !lookup_insert_eq.
    - rewrite !lookup_insert_ne by done. apply H.
  Qed.

  Lemma sconv_union Σ1 Σ1' Σ2 Σ2' :
    sconv W Σ1 Σ1' → sconv W Σ2 Σ2' → sconv W (Σ1 ∪ Σ2) (Σ1' ∪ Σ2').
  Proof.
    intros H1 H2 c. specialize (H1 c). specialize (H2 c). rewrite !lookup_union.
    destruct (Σ1 !! c), (Σ1' !! c), (Σ2 !! c), (Σ2' !! c); simpl in *; done.
  Qed.

  Lemma sconv_difference Σ1 Σ1' Σ2 :
    sconv W Σ1 Σ1' → sconv W (Σ1 ∖ Σ2) (Σ1' ∖ Σ2).
  Proof.
    intros H c. specialize (H c). rewrite !lookup_difference.
    destruct (Σ2 !! c), (Σ1 !! c), (Σ1' !! c); simpl in *; done.
  Qed.

  Lemma difference_sconv Σ Σ2 Σ2' :
    sconv W Σ2 Σ2' → Σ ∖ Σ2 = Σ ∖ Σ2'.
  Proof.
    intros H. apply map_eq. intros c. specialize (H c). rewrite !lookup_difference.
    destruct (Σ2 !! c), (Σ2' !! c); simpl in *; done.
  Qed.

  (** Reading a head off a converted interface. *)
  Lemma sconv_hd Σ Σ' c u k Σ1 :
    sconv W Σ Σ' → senv_hd Σ c u k Σ1 → c ∉ dom Σ1 →
    ∃ s s' k' Σ1', Σ = <[c := (s, k)]> Σ1 ∧ Σ' = <[c := (s', k')]> Σ1' ∧
      unfoldS s = u ∧ seq s s' ∧ w_eq W k k' ∧ sconv W Σ1 Σ1' ∧ c ∉ dom Σ1'.
  Proof.
    intros H (s & -> & Hu) Hc. pose proof (H c) as Hcc. rewrite lookup_insert_eq in Hcc.
    destruct (Σ' !! c) as [[s' k']|] eqn:E; [|done]. destruct Hcc as [Hs Hk].
    exists s, s', k', (delete c Σ'). split_and!; try done.
    - by rewrite insert_delete_id.
    - intros d. destruct (decide (d = c)) as [->|Hne].
      + rewrite lookup_delete_eq. by apply not_elem_of_dom in Hc as ->.
      + rewrite lookup_delete_ne by done. specialize (H d).
        by rewrite lookup_insert_ne in H.
    - by rewrite dom_delete_L; set_solver.
  Qed.

  Lemma senv_dual_on_conv Σ1 Σ1' Σ2 :
    sconv W Σ1 Σ1' → senv_dual_on (w_eq W) Σ1' Σ2 → senv_dual_on (w_eq W) Σ1 Σ2.
  Proof.
    intros H Hd c e1 e2 H1 H2. specialize (H c). rewrite H1 in H.
    destruct (Σ1' !! c) as [e1'|] eqn:E; [|done].
    apply (entry_conv_dual W HW e1' e2); [by apply entry_conv_sym|apply entry_conv_refl; done|].
    by apply (Hd c).
  Qed.

  Lemma recv_ok_conv Σr Σr' Θ2 : sconv W Σr Σr' → recv_ok W Σr' Θ2 → recv_ok W Σr Θ2.
  Proof.
    intros H (H1 & H2 & H3). split_and!; [by eapply senv_dual_on_conv|done|].
    by rewrite (sconv_dom Σr Σr').
  Qed.

  Lemma recv_back_conv Σr Σr' Θ2 : sconv W Σr Σr' → recv_back Σr Θ2 = recv_back Σr' Θ2.
  Proof. intros H. unfold recv_back. by rewrite (sconv_dom Σr Σr'). Qed.

  Lemma recv_env_conv Σr Σr' Θ2 :
    sconv W Σr Σr' → sconv W (recv_env Σr Θ2) (recv_env Σr' Θ2).
  Proof.
    intros H. unfold recv_env. rewrite (difference_sconv (tenv_ones Θ2) Σr Σr' H).
    apply sconv_union; [by apply sconv_difference|apply sconv_refl].
  Qed.

  Lemma above_offered_conv Σ Σ' off :
    sconv W Σ Σ' → above_offered W (tenv_of Σ) off → above_offered W (tenv_of Σ') off.
  Proof.
    intros H Ha k e' He' Hk. apply sconv_tconv in H.
    destruct (tconv_entry _ _ _ _ _ (tconv_sym W HW _ _ H) He') as (e & He & [_ Hee]).
    destruct (Ha k e He Hk) as (k' & f & Ho & Hf & Hlt).
    destruct (tconv_entry _ _ _ _ _ H Hf) as (f' & Hf' & [_ Hff]).
    exists k', f'. split_and!; [done|done|].
    unfold entry_head in *. eapply (wf_lt_eq _ HW);
      [by apply (wf_eq_sym _ HW)|exact Hlt|by apply (wf_eq_sym _ HW)].
  Qed.

  Lemma offered_p_conv Σ Σ' p k : sconv W Σ Σ' → offered_p Σ p k ↔ offered_p Σ' p k.
  Proof.
    intros H. apply sconv_tconv in H. unfold offered_p.
    split; intros (σ & p' & Hs & Hk); exists σ, p'; split; try done.
    - by eapply selects_conv.
    - eapply selects_conv; [by apply tconv_sym|done].
  Qed.

  Lemma ready_p_conv Σ Σ' p : sconv W Σ Σ' → ready_p W Σ p → ready_p W Σ' p.
  Proof.
    intros H Hr Hs. destruct (Hr Hs) as [?|[Hv Ha]]; [by left|right]. split.
    - intros Hno. apply Hv. intros k Hk. apply (Hno k). by apply (offered_p_conv Σ).
    - eapply above_offered_conv; [exact H|].
      intros k e He Hk. destruct (Ha k e He) as (k' & f & Ho & Hf & Hlt).
      { intros Ho. apply Hk. by apply (offered_p_conv Σ). }
      exists k', f. split_and!; [by apply (offered_p_conv Σ)|done|done].
  Qed.
End sconv.

Lemma sconv_mono W W' Σ Σ' :
  (∀ x y, w_eq W x y → w_eq W' x y) → sconv W Σ Σ' → sconv W' Σ Σ'.
Proof.
  intros Hm H c. specialize (H c). destruct (Σ !! c), (Σ' !! c); try done.
  destruct H. split; auto.
Qed.

Lemma tconv_union W Θ1 Θ1' Θ2 Θ2' :
  tconv W Θ1 Θ1' → tconv W Θ2 Θ2' → tconv W (Θ1 ∪ Θ2) (Θ1' ∪ Θ2').
Proof.
  intros H1 H2 c. specialize (H1 c). specialize (H2 c). rewrite !lookup_union.
  destruct (Θ1 !! c), (Θ1' !! c), (Θ2 !! c), (Θ2' !! c); simpl in *; done.
Qed.

Definition senv_restrict (Σ : senv) (D : gset chan) : senv :=
  filter (λ kv, kv.1 ∈ D) Σ.

Lemma lookup_senv_restrict Σ D c :
  senv_restrict Σ D !! c = if decide (c ∈ D) then Σ !! c else None.
Proof.
  unfold senv_restrict. destruct (Σ !! c) eqn:E.
  - case_decide.
    + apply map_lookup_filter_Some. naive_solver.
    + apply map_lookup_filter_None. right. intros ? Hx. simplify_eq. done.
  - case_decide; apply map_lookup_filter_None; by left.
Qed.

(** Splitting a converted union along the doms of the parts. *)
Lemma sconv_split W Σ0 Σv Σ' :
  Σ0 ##ₘ Σv → sconv W (Σ0 ∪ Σv) Σ' →
  ∃ Σ0' Σv', Σ' = Σ0' ∪ Σv' ∧ Σ0' ##ₘ Σv' ∧ sconv W Σ0 Σ0' ∧ sconv W Σv Σv' ∧
    dom Σ0' = dom Σ0 ∧ dom Σv' = dom Σv.
Proof.
  intros Hd H.
  exists (senv_restrict Σ' (dom Σ0)), (senv_restrict Σ' (dom Σv)).
  assert (∀ c, c ∈ dom Σ0 → Σv !! c = None) as Hn0.
  { intros c Hc. apply elem_of_dom in Hc as [e He]. specialize (Hd c).
    rewrite He in Hd. by destruct (Σv !! c). }
  assert (sconv W Σ0 (senv_restrict Σ' (dom Σ0))) as H0.
  { intros c. rewrite lookup_senv_restrict. specialize (H c). rewrite lookup_union in H.
    case_decide as Hc.
    - rewrite (Hn0 c Hc) in H. apply elem_of_dom in Hc as [e He]. rewrite He in H |- *.
      by destruct (Σ' !! c).
    - apply not_elem_of_dom in Hc. by rewrite Hc. }
  assert (sconv W Σv (senv_restrict Σ' (dom Σv))) as Hv.
  { intros c. rewrite lookup_senv_restrict. specialize (H c). rewrite lookup_union in H.
    case_decide as Hc.
    - apply elem_of_dom in Hc as [e He]. rewrite He in H |- *.
      assert (Σ0 !! c = None) as E0.
      { specialize (Hd c). rewrite He in Hd. by destruct (Σ0 !! c). }
      rewrite E0 in H. by destruct (Σ' !! c).
    - apply not_elem_of_dom in Hc. by rewrite Hc. }
  split_and!.
  - apply map_eq. intros c. rewrite lookup_union, !lookup_senv_restrict.
    specialize (H c). rewrite lookup_union in H.
    case_decide as A; case_decide as B.
    + exfalso. assert (Σv !! c = None) as N by (by apply Hn0).
      apply elem_of_dom in B as [? ?]. congruence.
    + by destruct (Σ' !! c).
    + by destruct (Σ' !! c).
    + apply not_elem_of_dom in A, B. rewrite A, B in H. by destruct (Σ' !! c).
  - intros c. rewrite !lookup_senv_restrict. case_decide as A; case_decide as B; try done.
    + assert (Σv !! c = None) as N by (by apply Hn0). apply elem_of_dom in B as [? ?].
      congruence.
    + by destruct (Σ' !! c).
    + by destruct (Σ' !! c).
  - done.
  - done.
  - apply set_eq. intros c. rewrite !elem_of_dom. specialize (H0 c).
    destruct (Σ0 !! c), (senv_restrict Σ' (dom Σ0) !! c); naive_solver.
  - apply set_eq. intros c. rewrite !elem_of_dom. specialize (Hv c).
    destruct (Σv !! c), (senv_restrict Σ' (dom Σv) !! c); naive_solver.
Qed.

Lemma Prel_sconv n : ∀ W Σ Σ' T p,
  world_wf W → sconv W Σ Σ' → Prel n W Σ T p → Prel n W Σ' T p.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros W Σ Σ' T p HW Hc HP.
  destruct n as [|n']; [apply Prel_0|].
  revert Σ' HW Hc.
  induction HP as [W Σ T p Hirr Hrdy Hstep] using Prel_S_ind.
  intros Σ' HW Hc.
  assert (∀ j W0 Σ0 Σ0' p0, j ≤ n' → world_wf W0 → sconv W0 Σ0 Σ0' →
            Prel j W0 Σ0 T p0 → Prel j W0 Σ0' T p0) as HPj.
  { intros j ? ? ? ? Hj. apply IHn. lia. }
  apply Prel_S_iff. split_and!.
  { intros Hp. destruct (Hirr Hp) as (v & E & -> & ? & HVv & ?).
    exists v, E. split_and!; [done|done| |done].
    eapply Vrel_econv; [done|by apply sconv_tconv|exact HVv]. }
  { intros Hp. eapply (ready_p_conv W HW); [exact Hc|]. by apply Hrdy. }
  intros π q Hst. specialize (Hstep π q Hst).
  destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
  - (* Q-Tau *)
    destruct Hstep as [Htau Hlink]. split.
    2: { intros Hl Hd. rewrite <-(sconv_dom W Σ Σ' Hc) in Hd.
         exact (proj2 (Hlink Hl Hd) Σ' HW Hc). }
    intros Hd. rewrite <-(sconv_dom W Σ Σ' Hc) in Hd.
    destruct (Htau Hd) as (N & W1 & HN & Hfr & HP').
    destruct (Prel_tau_rename n' (senv_roots Σ') _ W N W1 Σ T q eq_refl HW Hfr HN HP')
      as (N' & W1' & HN'X & HN' & Hfr' & HP1).
    exists N', W1'. split_and!; [set_solver|done|].
    assert (world_wf W1') as HW1 by (by destruct Hfr' as ((_ & _ & _ & [? _]) & _)).
    eapply HPj; [lia|done| |exact HP1].
    eapply sconv_mono; [|exact Hc]. intros. destruct Hfr' as ((_ & He & _) & _). auto.
  - (* Q-Recv *)
    destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc1 & H).
    destruct (sconv_hd W HW Σ Σ' c _ k Σ1 Hc Hhd Hc1)
      as (s0 & s0' & k' & Σ1' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
    destruct (seq_rcv_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
      [by apply seq_sym|done|].
    exists Σ1', m, U', s'', k'. split_and!; [by exists s0'|done|].
    intros W' j Θ2 HW' Hj Hfr Hok HVw.
    assert (world_wf W') as HW'f by (by eapply wext_wf).
    assert (∀ x y, w_eq W x y → w_eq W' x y) as Hsub by (intros; by eapply wext_eq).
    assert (sconv W' (<[c := (s, pt_shift 1 k)]> Σ1) (<[c := (s'', pt_shift 1 k')]> Σ1'))
      as Hcr.
    { apply sconv_insert; [by eapply sconv_mono|].
      split; simpl; [by apply seq_sym|]. apply Hsub. by apply (wf_eq_shift _ HW). }
    assert (Vrel j W' Θ2 (payload_at m U k) w) as HVw0.
    { eapply Vrel_tconv; [done| |exact HVw].
      eapply teqW_trans; [done|apply teq_teqW, teq_ty_inst, HU|].
      apply teqW_payload; [done|]. apply Hsub. by apply (wf_eq_sym _ HW). }
    pose proof (H W' j Θ2 HW' Hj Hfr (recv_ok_conv W' HW'f _ _ _ Hcr Hok) HVw0) as HP1.
    rewrite (recv_back_conv W' _ _ Θ2 Hcr) in HP1.
    eapply HPj; [lia|done| |exact HP1]. by apply (recv_env_conv W' HW'f).
  - (* Q-Send *)
    destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd & Hd0v & Hc0 & Hcv &
                       Hdom & Hsplit & HdΣ & HVw & HP').
    destruct (sconv_hd W HW Σ Σ' c _ k (Σ0 ∪ Σv) Hc Hhd ltac:(rewrite dom_union_L; set_solver))
      as (s0 & s0' & k' & Σ01' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
    destruct (seq_snd_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
      [by apply seq_sym|done|].
    destruct (sconv_split W Σ0 Σv Σ01' Hd0v Hc1') as
      (Σ0' & Σv' & -> & Hd0v' & Hc0' & Hcv' & Hdom0 & Hdomv).
    exists Σ0', Σv', m, U', s'', k', Σe, Θe. split_and!.
    + by exists s0'.
    + done.
    + by rewrite Hdom0.
    + by rewrite Hdomv.
    + done.
    + done.
    + by rewrite <-(sconv_dom W Σ Σ' Hc).
    + eapply Vrel_tconv; [done| |].
      { eapply teqW_trans; [done|apply teqW_payload; [done|exact Hk]|].
        apply teq_teqW, teq_ty_inst. by apply teq_sym. }
      eapply Vrel_econv; [done| |exact HVw].
      apply tconv_union; [by apply sconv_tconv|apply tconv_refl; done].
    + apply (proj2 HP'); [done|].
      apply sconv_insert; [apply sconv_union; [done|apply (sconv_refl W HW)]|].
      split; simpl; [by apply seq_sym|]. by apply (wf_eq_shift _ HW).
  - (* Q-Close *)
    destruct Hstep as (Σ1 & k & Hhd & Hc1 & HP').
    destruct (sconv_hd W HW Σ Σ' c _ k Σ1 Hc Hhd Hc1)
      as (s0 & s0' & k' & Σ1' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
    exists Σ1', k'. split_and!; [|done|].
    + exists s0'. split; [done|]. apply (seq_end_inv _ s0); [by apply seq_sym|done].
    + exact (proj2 HP' _ HW Hc1').
  - (* Q-Link *)
    destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd & -> & Hne & HΣ & Hc1 & Hd1 &
                       Hdu & Hal & HP').
    pose proof (Hc c) as Hcc. pose proof (Hc d) as Hdd. rewrite HΣ in Hcc, Hdd.
    rewrite lookup_insert_eq in Hcc. rewrite lookup_insert_ne, lookup_insert_eq in Hdd by done.
    destruct (Σ' !! c) as [[sc' kc']|] eqn:Ec; [|done].
    destruct (Σ' !! d) as [[sd' kd']|] eqn:Ed; [|done].
    destruct Hcc as [Hsc Hkc], Hdd as [Hsd Hkd]. simpl in *.
    exists c, d, (delete c (delete d Σ')), sc', sd', kc', kd'. split_and!.
    + done.
    + done.
    + apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
      { by rewrite lookup_insert_eq. }
      rewrite lookup_insert_ne by done. destruct (decide (x = d)) as [->|Hxd].
      { by rewrite lookup_insert_eq. }
      by rewrite lookup_insert_ne, lookup_delete_ne, lookup_delete_ne.
    + rewrite dom_delete_L. set_solver.
    + rewrite !dom_delete_L. set_solver.
    + eapply sdual_seq_l; [exact Hsd|]. by eapply sdual_seq_r.
    + eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|].
      eapply (wf_eq_trans _ HW); [exact Hal|exact Hkd].
    + apply (proj2 HP'); [done|].
      intros x. destruct (decide (x = c)) as [->|Hxc].
      { rewrite lookup_delete_eq. by apply not_elem_of_dom in Hc1 as ->. }
      rewrite lookup_delete_ne by done. destruct (decide (x = d)) as [->|Hxd].
      { rewrite lookup_delete_eq. by apply not_elem_of_dom in Hd1 as ->. }
      rewrite lookup_delete_ne by done. specialize (Hc x). rewrite HΣ in Hc.
      by rewrite !lookup_insert_ne in Hc.
Qed.
