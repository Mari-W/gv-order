(** * The soup along a synchronization (stage S8)

    P-Act-Msg, P-Act-Close and P-Act-Choice: two threads act on the two
    ends of one channel. Their obligations in E[live] and in FuelE give
    the continuations, and the soup's pairing gives the duality of the
    two session types (up to annotations) and of the two protocols (up
    to ≈), so the payload of a message is in V and in FV at the
    receiver's types, and the continuations are paired again. *)

From stdpp Require Import relations.
From GV Require Export soup.SoupStep soup.SyncMaps.

Section sync.
  Context (N n : nat) (W : world) (T : ty) (C : gset chan) (Mq : gmap nat expr) (K : own)
    (tk : nat → nat) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N (S n) W ∅ T (LFState (C, Mq) K tk) A Π U).

  Local Lemma owner_of t o v : kres K t A !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

  Local Lemma owner_ofΠ t o v : kres K t Π !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

  Local Lemma inA t o v : kres K t A !! o = Some v → A !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  Local Lemma inΠ t o v : kres K t Π !! o = Some v → Π !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  Local Lemma ctrs_some t o : o ∈ dom (kth K t) → ∃ f, ctrs K t !! o = Some f.
  Proof. intros (h & Hh & Ht)%elem_of_dom_kth. exists h.(h_ctr). apply lookup_ctrs. eauto. Qed.

  (** The owner of every held end is a thread, and a held end is held at
      a point of A, a protocol of Π and a counter. *)
  Local Lemma held_all o h : K !! o = Some h →
    (∃ S x, A !! o = Some (S, x) ∧ x = h.(h_pt)) ∧ ∃ P, Π !! o = Some P.
  Proof.
    intros Ho. split.
    - pose proof (s_pts _ _ _ _ _ _ _ _ Hs o) as Hp. cbn [s_K] in Hp. rewrite Ho in Hp.
      destruct (A !! o) as [[S x]|]; simpl in Hp; simplify_eq. eauto.
    - assert (o ∈ dom Π) as HΠ by (rewrite (s_dom _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Ho).
      by apply elem_of_dom in HΠ.
  Qed.
  Local Ltac pw := apply map_eq_some; intros o0 v0.

  (** P-Act-Msg. *)
  Lemma step_msg i j e e' f f' o Mv w :
    i ≠ j → Mq !! i = Some e → Mq !! j = Some f →
    tstep e (LSess (SSend o Mv w)) e' → tstep f (LSess (SRecv (edual o) w)) f' →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K tk) (EvMsg i j o Mv) (C, <[j := f']> (<[i := e']> Mq))) A' Π' U.
  Proof.
    intros Hij He Hf Hst Hst'.
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HEi HFi].
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs j f _ f' Hf Hst') as [HEj HFj].
    cbn [Eobl Fobl] in HEi, HFi, HEj, HFj. unfold o_send in HEi. unfold o_recv in HEj.
    unfold f_send in HFi. unfold f_recv in HFj.
    destruct HEi as (S0 & x & m & U0 & b & S & ΘM & Θr & Ho & Hu & Hd & HΘ & HM & HV & HE').
    destruct HEj as (S0' & x' & m' & U0' & b' & S' & Ho' & Hu' & HR).
    destruct HFi as (_ & P0 & m2 & T2 & b2 & P & HPo & HPu & HMφ & _ & HVf & HF').
    destruct HFj as (_ & P0' & m3 & T3 & b3 & P' & HPo' & HPu' & HRf).
    destruct (owner_of i o _ Ho) as (hi & Khi & Ehi).
    destruct (owner_of j (edual o) _ Ho') as (hj & Khj & Ehj).
    pose proof (inA _ _ _ Ho) as HA. pose proof (inA _ _ _ Ho') as HA'.
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S0' x' HA HA') as [-> Hsd].
    destruct (sdual_snd _ _ _ _ _ _ _ _ _ _ Hsd Hu Hu') as (-> & HU & HSS').
    pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o P0 P0' (inΠ _ _ _ HPo) (inΠ _ _ _ HPo')) as Hpd.
    destruct (pdual_snd _ _ _ _ _ _ _ _ _ _ Hpd HPu HPu') as (-> & -> & HT & HPP').
    destruct (split_mres _ _ _ _ Hd HΘ HM) as [-> ->].
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x HA) as Hkx. cbn [s_K] in Hkx.
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs (edual o) S0' (pt_dual x) HA') as Hkx'. cbn [s_K] in Hkx'.
    assert (HMi : ∀ o1, o1 ∈ Mv → ∃ h, K !! o1 = Some h ∧ h.(h_th) = i ∧ o1 ≠ o).
    { intros o1 Ho1. rewrite <-HM, dom_mres, dom_delete_L in Ho1.
      apply elem_of_intersection in Ho1 as [Ho1 _]. apply elem_of_difference in Ho1 as [Ho1 Hne].
      apply elem_of_dom in Ho1 as [v1 Hv1]. destruct (owner_of i o1 v1 Hv1) as (h & ? & ?).
      exists h. set_solver. }
    assert (Hoo : o ≠ edual o) by (destruct o; discriminate).
    assert (HoM : edual o ∉ Mv).
    { intros Hin. destruct (HMi _ Hin) as (h & Hh & Ht & _). rewrite Khj in Hh. simplify_eq; congruence. }
    (* the receiver *)
    assert (HVr : Vrel live n W (mres Mv (delete o (kres K i A))) (payload_at m U0' (pt_dual x)) w).
    { rewrite payload_at_dual. apply (Vrel_teq live _ _ _ _ _ _ (payload_teq m U0 U0' x HU)).
      eapply at_cost_V_live; [|exact HV]. cbn; lia. }
    assert (Hdisj : kres K j A ##ₘ mres Mv (delete o (kres K i A))).
    { apply map_disjoint_spec. intros o1 v1 v2 H1 H2. apply lookup_mres_Some in H2 as [H2 _].
      apply lookup_delete_Some in H2 as [_ H2].
      destruct (owner_of _ _ _ H1) as (h1 & Hh1 & Ht1). destruct (owner_of _ _ _ H2) as (h2 & Hh2 & Ht2).
      simplify_eq; congruence. }
    pose proof (HR n _ ltac:(cbn; lia) Hdisj HVr) as HEr.
    assert (HVfr : Vfuel (Some N) n (RTy T3 b2) (mres Mv (kres K i Π)) (fhand Mv (ctrs K i)) w).
    { apply (Vfuel_teq n (Some N) T2 T3); [by apply teq_sym|exact HVf]. }
    assert (Hd1 : mres Mv (kres K i Π) ##ₘ <[edual o := P']> (kres K j Π)).
    { apply map_disjoint_spec. intros o1 v1 v2 H1 H2. apply lookup_mres_Some in H1 as [H1 Hin].
      destruct (owner_ofΠ _ _ _ H1) as (h1 & Hh1 & Ht1).
      apply lookup_insert_Some in H2 as [[<- _]|[_ H2]]; [done|].
      destruct (owner_ofΠ _ _ _ H2) as (h2 & Hh2 & Ht2). simplify_eq; congruence. }
    assert (Hd2 : fhand Mv (ctrs K i) ##ₘ refill (Some N) (edual o) (ctrs K j)).
    { apply map_disjoint_spec. intros o1 v1 v2 H1 H2. unfold fhand, refill in *.
      apply lookup_fmap_Some in H1 as (f1 & _ & H1). apply lookup_mres_Some in H1 as [H1 Hin].
      apply lookup_ctrs in H1 as (h1 & Hh1 & Ht1 & _).
      apply lookup_insert_Some in H2 as [[<- _]|[_ H2]]; [done|].
      apply lookup_fmap_Some in H2 as (f2 & _ & H2). apply lookup_delete_Some in H2 as [_ H2].
      apply lookup_ctrs in H2 as (h2 & Hh2 & Ht2 & _). simplify_eq; congruence. }
    pose proof (HRf n _ _ (Nat.le_refl _) Hd1 Hd2 HVfr) as HFr.
    eexists (<[o := (S, pt_shift 1 x)]> (<[edual o := (S', pt_shift 1 (pt_dual x))]> A)), (<[o := P]> (<[edual o := P']> Π)).
    unfold lf_next. cbn [tk_next s_K s_tk s_q].
    assert (Hoi : ∃ h, K !! o = Some h ∧ h.(h_th) = i) by eauto.
    assert (Hoj : ∃ h, K !! edual o = Some h ∧ h.(h_th) = j) by eauto.
    pose proof (λ Y, @msg_kres_i N K i j o Mv Hij Hoi Hoj HMi Hoo Y) as Ki.
    pose proof (λ Y, @msg_kres_i' N K i j o Mv Hij Hoi Hoj HMi Hoo Y) as Ki'.
    pose proof (λ Y, @msg_kres_j N K i j o Mv Hij Hoi Hoj HMi Hoo Y) as Kj.
    pose proof (λ Y, @msg_kres_j' N K i j o Mv Hij Hoi Hoj HMi Hoo Y) as Kj'.
    pose proof (λ Y, @msg_kres_other N K i j o Mv Hij Hoi Hoj HMi Hoo Y) as Kt.
    pose proof (msg_ctrs_i N K i j o Mv Hij Hoi Hoj HMi Hoo) as Ci.
    pose proof (msg_ctrs_j N K i j o Mv Hij Hoi Hoj HMi Hoo) as Cj.
    pose proof (msg_ctrs_other N K i j o Mv Hij Hoi Hoj HMi Hoo) as Ct.
    assert (HK' : ∀ o0, own_next N (EvMsg i j o Mv) K !! o0 =
      if decide (o0 = o) then Some (Hold i (pt_shift 1 x) (Some N))
      else if decide (o0 = edual o) then Some (Hold j (pt_shift 1 (pt_dual x)) (Some N))
      else (λ h, if decide (o0 ∈ Mv) then Hold j h.(h_pt) (ftick h.(h_ctr))
                 else if decide (h.(h_th) = i ∨ h.(h_th) = j) then htick h else h) <$> K !! o0).
    { intros o0. by rewrite lookup_msg, Hkx, Hkx'. }
    assert (HdK : dom (own_next N (EvMsg i j o Mv) K) = dom K).
    { apply set_eq. intros o0. rewrite !elem_of_dom, HK'.
      destruct (decide (o0 = o)) as [->|]; [split; intros _; [by eexists|done]|].
      destruct (decide (o0 = edual o)) as [->|]; [split; intros _; [by eexists|done]|].
      by rewrite fmap_is_Some. }
    assert (HCh : ∀ o0, o0 ∈ ({[o]} ∪ {[edual o]} : gset cend) ↔ edual o0 ∈ ({[o]} ∪ {[edual o]} : gset cend)).
    { intros o0. rewrite !elem_of_union, !elem_of_singleton. split.
      - intros [-> | ->]; [right|left]; [done|apply edual_edual].
      - intros [H|H]; [right; by rewrite <-H, edual_edual|left; by apply edual_inj]. }
    unfold ftick in HF', HFr. rewrite fsub_inf in HF', HFr.
    apply (soup_build _ _ _ _ _ _ _ _ _ _ _ Hs).
    - intros t e1 He1. apply lookup_insert_Some in He1 as [[<- <-]|[Htj He1]].
      + rewrite Kj, Kj', Cj. split_and!; [exact HEr|exact (s_ty Hs j f Hf)|exact HFr].
      + apply lookup_insert_Some in He1 as [[<- <-]|[Hti He1]].
        * rewrite Ki, Ki', Ci. split_and!; [|exact (s_ty Hs i e He)|exact HF'].
          eapply at_cost_E_live; [|exact HE']. cbn; lia.
        * rewrite !Kt, Ct by done. destruct (s_other _ _ _ _ _ _ _ _ _ _ _ Hs t e1 He1) as [H1 H2].
          split_and!; [done|exact (s_ty Hs t e1 He1)|done].
    - apply map_eq. intros o0. rewrite !lookup_fmap, HK'.
      pose proof (s_pts _ _ _ _ _ _ _ _ Hs o0) as Hp. cbn [s_K] in Hp.
      destruct (decide (o0 = o)) as [->|]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done.
      destruct (decide (o0 = edual o)) as [->|]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done. rewrite Hp.
      destruct (K !! o0); simpl; [|done]. by own_cases.
    - rewrite HdK, !dom_insert_L, (s_dom _ _ _ _ _ _ _ _ Hs). cbn [s_K].
      apply elem_of_dom_2 in Khi, Khj. clear - Khi Khj. set_solver.
    - intros o0 h0 Ho0. rewrite HK' in Ho0. rewrite !lookup_insert_is_Some'.
      destruct (decide (o0 = o)); [simplify_eq; simpl; by right; left|].
      destruct (decide (o0 = edual o)); [simplify_eq; simpl; by left|].
      apply fmap_Some in Ho0 as (h1 & Ho1 & ->). pose proof (s_threads _ _ _ _ _ _ _ _ _ _ _ Hs o0 h1 Ho1).
      own_cases; simpl; auto.
    - intros o0. rewrite HdK. apply (s_closed _ _ _ _ _ _ _ _ Hs).
    - intros o0. rewrite HdK. apply (s_pair _ _ _ _ _ _ _ _ Hs).
    - intros o0 S1 x1 S2 x2 H3 H4.
      refine (pair_frame (λ _ (v v' : sty * point), v'.2 = pt_dual v.2 ∧ sdual v.1 v'.1) _ _
        ({[o]} ∪ {[edual o]}) HCh _ _ _ o0 (S1, x1) (S2, x2) H3 H4).
      + intros o1 Ho1. rewrite !lookup_insert_ne by (clear - Ho1; set_solver). done.
      + intros o1 [S5 x5] [S6 x6] H5 H6. exact (s_sdual _ _ _ _ _ _ _ _ Hs o1 S5 x5 S6 x6 H5 H6).
      + intros o1 [S5 x5] [S6 x6] Ho1 H5 H6. simpl.
        apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_singleton in Ho1 as ->.
        * rewrite lookup_insert_eq in H5. rewrite lookup_insert_ne, lookup_insert_eq in H6 by done.
          simplify_eq. split; [by rewrite pt_dual_shift|done].
        * rewrite edual_edual, lookup_insert_eq in H6. rewrite lookup_insert_ne, lookup_insert_eq in H5 by done.
          simplify_eq. split; [by rewrite pt_dual_shift, pt_dual_dual|by apply sdual_sym].
    - intros o0 P1 P2 H3 H4.
      refine (pair_frame (λ _ v v', sequiv v' (dual v)) _ _ ({[o]} ∪ {[edual o]}) HCh _ _ _ o0 P1 P2 H3 H4).
      + intros o1 Ho1. rewrite !lookup_insert_ne by (clear - Ho1; set_solver). done.
      + intros o1 P5 P6 H5 H6. exact (s_pdual _ _ _ _ _ _ _ _ Hs o1 P5 P6 H5 H6).
      + intros o1 P5 P6 Ho1 H5 H6.
        apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_singleton in Ho1 as ->.
        * rewrite lookup_insert_eq in H5. rewrite lookup_insert_ne, lookup_insert_eq in H6 by done.
          simplify_eq. done.
        * rewrite edual_edual, lookup_insert_eq in H6. rewrite lookup_insert_ne, lookup_insert_eq in H5 by done.
          simplify_eq. by apply pdual_sym.
  Qed.
End sync.
