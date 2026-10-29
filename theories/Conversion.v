(** * Type point conversion (§10)

    Aliased points are interchangeable in types:

      T ≈_W T′  ⇒  V, E, P at T ⇔ V, E, P at T′       ([rel_tconv])

    where ≈_W is ≈ with ground points compared up to ≡_W ([teqW]). In
    particular a payload type P[x] may be read at any alias y of x
    ([teqW_payload]), which P-Connect needs when the two ends of a cut
    channel sit at aliased points. Environments need no conversion:
    every overlap condition already reads ≡_W (sharp edges 40). *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Monotone.

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

  Lemma teqW_refl T : teqW W T T.
  Proof.
    induction T; simpl; repeat split; auto using opt_rel_refl, pteqW_refl, seq_refl.
  Qed.

  Lemma teqW_sym T : ∀ U, teqW W T U → teqW W U T.
  Proof.
    induction T; intros [] H; simpl in *; try done; try naive_solver.
    - destruct H as (? & ? & ? & ?). split_and!; auto using opt_rel_sym.
    - destruct H as [? ?]. split; [by apply pteqW_sym|by apply seq_sym].
  Qed.

  Lemma teqW_trans T : ∀ U V, teqW W T U → teqW W U V → teqW W T V.
  Proof.
    induction T; intros [] [] H1 H2; simpl in *; try done; try naive_solver.
    - destruct H1 as (? & ? & ? & ?), H2 as (? & ? & ? & ?).
      split_and!; eauto using opt_rel_trans.
    - destruct H1 as [? ?], H2 as [? ?]. split; [by eapply pteqW_trans|by eapply seq_trans].
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

  (** Instantiating with aliased points gives types up to aliases. *)
  Lemma teqW_pinst_l T : ∀ σ τ,
    (∀ i, pteqW W (σ i) (τ i)) → teqW W (pinst_ty σ T) (pinst_ty τ T).
  Proof.
    induction T; intros σ τ H; simpl; repeat split; auto using seq_refl.
    - destruct ub; simpl; [by apply pteqW_inst_l|done].
    - destruct lb; simpl; [by apply pteqW_inst_l|done].
    - apply IHT. by apply pup_pteqW.
    - by apply pteqW_inst_l.
  Qed.

  Lemma teqW_pinst_r T : ∀ U σ, teqW W T U → teqW W (pinst_ty σ T) (pinst_ty σ U).
  Proof.
    induction T; intros [] σ H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done. by apply pteqW_inst_r.
      + destruct lb, lb0; simpl in *; try done. by apply pteqW_inst_r.
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as [<- ?]. split; [done|]. by apply IHT.
    - destruct H as [? ?]. split; [by apply pteqW_inst_r|done].
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

Lemma teqW_mono' W W' T U :
  (∀ x y, w_eq W x y → w_eq W' x y) → teqW W T U → teqW W' T U.
Proof. apply teqW_mono. Qed.

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

(** ** The relations are invariant *)

Lemma rel_tconv n :
  (∀ W Θ T T' v, world_wf W → teqW W T T' → Vrel n W Θ T v → Vrel n W Θ T' v) ∧
  (∀ W Θ T T' F e, world_wf W → teqW W T T' →
     Erel n W Θ T F e → Erel n W Θ T' F e) ∧
  (∀ W Σ T T' p, world_wf W → teqW W T T' → Prel n W Σ T p → Prel n W Σ T' p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ T T' v, world_wf W → teqW W T T' →
            Vrel n W Θ T v → Vrel n W Θ T' v) as HV.
  { intros W Θ T. revert Θ.
    induction T as [|ub lb T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2
                   |m T1 IHT1|s x];
      intros Θ [|ub' lb' T1' T2'|T1' T2'|T1' T2'|m' T1'|s' x'] v HW Ht HVv;
      simpl in Ht; try done.
    - (* ⊸ *)
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
        eapply teqW_trans; [done|exact Ht|]. simpl. by split_and!.
    - destruct Ht as [Ht1 Ht2].
      apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      apply Vrel_prod_iff. exists v1, v2, Θ1, Θ2. split_and!; eauto.
    - destruct Ht as [Ht1 Ht2].
      apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; eauto.
    - destruct Ht as [<- Ht].
      apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply Vrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros W' j xs HW' Hj Hxs. eapply (proj1 (proj2 (IHn j Hj))).
      + by eapply wext_wf.
      + apply teqW_ty_inst. eapply teqW_mono; [|exact Ht]. intros. by eapply wext_eq.
      + by apply HK.
    - destruct Ht as [Hx Hs].
      apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs0 & Hk).
      apply Vrel_sess_iff. exists c, s0, k. split_and!; [done|done| |].
      + by eapply seq_trans.
      + eapply (wf_eq_trans _ HW); [exact Hk|]. by apply pteqW_eq. }
  split_and!; [exact HV| |].
  - intros W Θ T T' F e HW Ht HE.
    destruct n as [|n']; [apply Erel_0|].
    assert (∀ j W0 Θ0 F0 e0, j ≤ n' → world_wf W0 →
              (∀ x y, w_eq W x y → w_eq W0 x y) →
              Erel j W0 Θ0 T F0 e0 → Erel j W0 Θ0 T' F0 e0) as HEj.
    { intros j W0 Θ0 F0 e0 Hj HW0 Hsub.
      apply (proj1 (proj2 (IHn j ltac:(lia)))); [done|].
      by eapply teqW_mono. }
    apply Erel_S_iff in HE as (Hval & Hrdy & Hstep).
    apply Erel_S_iff. split_and!; [|done|].
    { intros Hirr. eapply HV; [done|exact Ht|]. by apply Hval. }
    intros α e' Hst. specialize (Hstep α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
    + by eapply HEj.
    + destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists Θ1, m, U, s, k. split; [done|].
      intros W' j Θ2 Θ12 HW' Hj Hc HVw.
      destruct (H W' j Θ2 Θ12 HW' Hj Hc HVw) as (Θ' & Hext & HE').
      exists Θ'. split; [done|]. eapply HEj; [lia|by eapply wext_wf| |exact HE'].
      intros. by eapply wext_eq.
    + destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done. by eapply HEj.
    + destruct Hstep as (Θ1 & k & Hhd & HE').
      exists Θ1, k. split; [done|]. by eapply HEj.
    + destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & ? & ? & ? & ? & HE').
      exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. by eapply HEj.
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
  - intros W Σ T T' p HW Ht HP.
    destruct n as [|n']; [apply Prel_0|].
    assert (∀ j W0 Σ0 p0, j ≤ n' → world_wf W0 →
              (∀ x y, w_eq W x y → w_eq W0 x y) →
              Prel j W0 Σ0 T p0 → Prel j W0 Σ0 T' p0) as HPj.
    { intros j W0 Σ0 p0 Hj HW0 Hsub.
      apply (proj2 (proj2 (IHn j ltac:(lia)))); [done|].
      by eapply teqW_mono. }
    apply Prel_S_iff in HP as (Hirr & Hrdy & Hstep).
    apply Prel_S_iff. split_and!; [|done|].
    { intros Hp. destruct (Hirr Hp) as (v & E & -> & ? & HVv & ?).
      exists v, E. split_and!; [done|done| |done]. by eapply HV. }
    intros π q Hst. specialize (Hstep π q Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* Q-Tau: rename the placed points away from the points of T' *)
      destruct Hstep as (N & W1 & HN & Hfr & HP').
      destruct (Prel_tau_rename n' (ty_roots T') _ W N W1 Σ T q eq_refl HW Hfr HN HP')
        as (N' & W1' & HN'T & HN' & Hfr' & HP1).
      exists N', W1'. split_and!; [set_solver|done|].
      eapply HPj; [lia| | |exact HP1].
      * by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
      * intros. destruct Hfr' as ((_ & He & _) & _). auto.
    + destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists Σ1, m, U, s, k. split_and!; [done|done|].
      intros W' j Θ2 HW' Hj Hok HVw.
      eapply HPj; [lia|by eapply wext_wf| |by apply H].
      intros. by eapply wext_eq.
    + destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         ? & ? & ? & ? & ? & ? & HVw & HP').
      exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done. by eapply HPj.
    + destruct Hstep as (Σ1 & k & Hhd & ? & HP').
      exists Σ1, k. split_and!; [done|done|]. by eapply HPj.
    + destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & ? & -> & ? & ? & ? & ? & HP').
      exists c, d, Σ1, sc, sd, kc, kd. split_and!; [done..|]. by eapply HPj.
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

(** A payload typed at P[x] is typed at P[y] for every alias y of x. *)
Lemma Vrel_payload n W Θ m U x y v :
  world_wf W → w_eq W x y → Vrel n W Θ (payload_at m U x) v →
  Vrel n W Θ (payload_at m U y) v.
Proof. intros HW Hxy. apply Vrel_tconv; [done|]. by apply teqW_payload. Qed.
