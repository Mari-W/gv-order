(** * The soup along a synchronization (stage S8)

    P-Act-Msg, P-Act-Close and P-Act-Choice: two threads act on the two
    ends of one channel. Their obligations in E[live] and in FuelE give
    the continuations, and the soup's pairing gives the duality of the
    two session types (up to annotations) and of the two protocols (up
    to ≈), so the payload of a message is in V and in FV at the
    receiver's types, and the continuations are paired again. *)

From stdpp Require Import relations.
From GV Require Export soup.SoupStep soup.SyncMaps.
From GV Require Import compat.Redex.

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

  Local Ltac pw := apply map_eq_some; intros o0 v0.

  (** P-Act-Msg. *)
  Lemma step_msg i j e e' f f' o w :
    i ≠ j → Mq !! i = Some e → Mq !! j = Some f →
    tstep e (LSess (SSend o w)) e' → tstep f (LSess (SRecv (edual o) w)) f' →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K tk) (EvMsg i j o w) (C, <[j := f']> (<[i := e']> Mq))) A' Π' U.
  Proof.
    intros Hij He Hf Hst Hst'.
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HEi HFi].
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs j f _ f' Hf Hst') as [HEj HFj].
    cbn [Eobl Fobl] in HEi, HFi, HEj, HFj. unfold o_send in HEi. unfold o_recv in HEj.
    unfold f_send in HFi. unfold f_recv in HFj.
    destruct HEi as (S0 & x & m & U0 & b & S & ΘM & Θr & Ho & Hu & Hd & HΘ & HV & HE').
    assert (HM : dom ΘM = fends w).
    { destruct (decide (c_give live = 0)) as [Hc|Hc];
        [exact (Vrel_exact _ _ _ _ _ _ (proj1 HV Hc))|exact (Vrel_exact _ _ _ _ _ _ (proj2 HV Hc))]. }
    destruct HEj as (S0' & x' & m' & U0' & b' & S' & Ho' & Hu' & HR).
    destruct HFi as (_ & P0 & m2 & T2 & b2 & P & HPo & HPu & HMφ & _ & HVf & HF').
    destruct HFj as (_ & P0' & m3 & T3 & b3 & P' & HPo' & HPu' & HRf).
    destruct (owner_of i o _ Ho) as (hi & Khi & Ehi).
    destruct (owner_of j (edual o) _ Ho') as (hj & Khj & Ehj).
    pose proof (inA _ _ _ Ho) as HA. pose proof (inA _ _ _ Ho') as HA'.
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S0' x' HA HA') as [-> Hsd].
    destruct (sdual_snd_both _ _ _ _ _ _ _ _ _ _ Hsd Hu Hu') as (-> & HU & HSS').
    pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o P0 P0' (inΠ _ _ _ HPo) (inΠ _ _ _ HPo')) as Hpd.
    destruct (pdual_snd _ _ _ _ _ _ _ _ _ _ Hpd HPu HPu') as (-> & -> & HT & HPP').
    destruct (split_mres _ _ _ _ Hd HΘ HM) as [-> ->].
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x HA) as Hkx. cbn [s_K] in Hkx.
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs (edual o) S0' (pt_dual x) HA') as Hkx'. cbn [s_K] in Hkx'.
    assert (HMi : ∀ o1, o1 ∈ (fends w) → ∃ h, K !! o1 = Some h ∧ h.(h_th) = i ∧ o1 ≠ o).
    { intros o1 Ho1. rewrite <-HM, dom_mres, dom_delete_L in Ho1.
      apply elem_of_intersection in Ho1 as [Ho1 _]. apply elem_of_difference in Ho1 as [Ho1 Hne].
      apply elem_of_dom in Ho1 as [v1 Hv1]. destruct (owner_of i o1 v1 Hv1) as (h & ? & ?).
      exists h. set_solver. }
    assert (Hoo : o ≠ edual o) by (destruct o; discriminate).
    assert (HoM : edual o ∉ (fends w)).
    { intros Hin. destruct (HMi _ Hin) as (h & Hh & Ht & _). rewrite Khj in Hh. simplify_eq; congruence. }
    (* the receiver *)
    assert (HVr : Vrel live n W (mres (fends w) (delete o (kres K i A))) (payload_at m U0' (pt_dual x)) w).
    { rewrite payload_at_dual. apply (Vrel_teq live _ _ _ _ _ _ (payload_teq m U0 U0' x HU)).
      eapply at_cost_V_live; [|exact HV]. cbn; lia. }
    assert (Hdisj : kres K j A ##ₘ mres (fends w) (delete o (kres K i A))).
    { apply map_disjoint_spec. intros o1 v1 v2 H1 H2. apply lookup_mres_Some in H2 as [H2 _].
      apply lookup_delete_Some in H2 as [_ H2].
      destruct (owner_of _ _ _ H1) as (h1 & Hh1 & Ht1). destruct (owner_of _ _ _ H2) as (h2 & Hh2 & Ht2).
      simplify_eq; congruence. }
    pose proof (HR n _ ltac:(cbn; lia) Hdisj HVr) as HEr.
    assert (HVfr : Vfuel (Some N) n (RTy T3 b2) (mres (fends w) (kres K i Π)) (fhand (fends w) (ctrs K i)) w).
    { apply (Vfuel_teq n (Some N) T2 T3); [by apply teq_sym|exact HVf]. }
    assert (Hd1 : mres (fends w) (kres K i Π) ##ₘ <[edual o := P']> (kres K j Π)).
    { apply map_disjoint_spec. intros o1 v1 v2 H1 H2. apply lookup_mres_Some in H1 as [H1 Hin].
      destruct (owner_ofΠ _ _ _ H1) as (h1 & Hh1 & Ht1).
      apply lookup_insert_Some in H2 as [[<- _]|[_ H2]]; [done|].
      destruct (owner_ofΠ _ _ _ H2) as (h2 & Hh2 & Ht2). simplify_eq; congruence. }
    assert (Hd2 : fhand (fends w) (ctrs K i) ##ₘ refill (Some N) (edual o) (ctrs K j)).
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
    pose proof (λ Y, @sync_kres_i N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo Y) as Ki.
    pose proof (λ Y, @sync_kres_i' N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo Y) as Ki'.
    pose proof (λ Y, @sync_kres_j N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo Y) as Kj.
    pose proof (λ Y, @sync_kres_j' N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo Y) as Kj'.
    pose proof (λ Y, @sync_kres_other N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo Y) as Kt.
    pose proof (sync_ctrs_i N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo) as Ci.
    pose proof (sync_ctrs_j N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo) as Cj.
    pose proof (sync_ctrs_other N K i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) Hij Hoi Hoj HMi Hoo) as Ct.
    cbn [own_next]. rewrite Hkx, Hkx'.
    assert (HK' : ∀ o0, ksync N i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) K !! o0 =
      if decide (o0 = o) then Some (Hold i (pt_shift 1 x) (Some N))
      else if decide (o0 = edual o) then Some (Hold j (pt_shift 1 (pt_dual x)) (Some N))
      else (λ h, if decide (o0 ∈ (fends w)) then Hold j h.(h_pt) (ftick h.(h_ctr))
                 else if decide (h.(h_th) = i ∨ h.(h_th) = j) then htick h else h) <$> K !! o0).
    { intros o0. by rewrite lookup_ksync. }
    assert (HdK : dom (ksync N i j o (pt_shift 1 x) (pt_shift 1 (pt_dual x)) (fends w) K) = dom K).
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
    - apply kfin_ksync. exact (sp_fin _ _ _ _ _ _ _ _ Hs).
  Qed.

  (** P-Act-Close. *)
  Lemma step_close i j e e' f f' o :
    i ≠ j → Mq !! i = Some e → Mq !! j = Some f →
    tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose (edual o))) f' →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K tk) (EvClose i j o) (C ∖ {[ech o]}, <[j := f']> (<[i := e']> Mq))) A' Π' U.
  Proof.
    intros Hij He Hf Hst Hst'.
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HEi HFi].
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs j f _ f' Hf Hst') as [HEj HFj].
    cbn [Eobl Fobl] in HEi, HFi, HEj, HFj. unfold o_close in HEi, HEj. unfold f_close in HFi, HFj.
    destruct HEi as (S0 & x & Ho & _ & HE1). destruct HEj as (S0' & x' & Ho' & _ & HE2).
    destruct HFi as (_ & P0 & _ & _ & HF1). destruct HFj as (_ & P0' & _ & _ & HF2).
    destruct (owner_of i o _ Ho) as (hi & Khi & Ehi).
    destruct (owner_of j (edual o) _ Ho') as (hj & Khj & Ehj).
    assert (Hoi : ∃ h, K !! o = Some h ∧ h.(h_th) = i) by eauto.
    assert (Hoj : ∃ h, K !! edual o = Some h ∧ h.(h_th) = j) by eauto.
    assert (Hoo : o ≠ edual o) by (destruct o; discriminate).
    pose proof (λ Y, @close_kres_i K i j o Hij Hoi Hoj Hoo Y) as Ki.
    pose proof (λ Y, @close_kres_j K i j o Hij Hoi Hoj Hoo Y) as Kj.
    pose proof (λ Y, @close_kres_other K i j o Hij Hoi Hoj Hoo Y) as Kt.
    pose proof (close_ctrs_i K i j o Hij Hoi Hoj Hoo) as Ci.
    pose proof (close_ctrs_j K i j o Hij Hoi Hoj Hoo) as Cj.
    pose proof (close_ctrs_other K i j o Hij Hoi Hoj Hoo) as Ct.
    pose proof (lookup_kclose K i j o Hij Hoi Hoj Hoo) as HK'.
    unfold ftick in HF1, HF2. rewrite fsub_inf in HF1, HF2. fold ftick in HF1, HF2.
    exists (delete o (delete (edual o) A)), (delete o (delete (edual o) Π)).
    unfold lf_next. cbn [own_next tk_next s_K s_tk s_q].
    assert (HdK : ∀ o0, o0 ∈ dom (ktick i j ∅ (delete o (delete (edual o) K))) ↔
                        o0 ∈ dom K ∧ ¬ (o0 = o ∨ o0 = edual o)).
    { apply (dom_kclose K i j o Hij Hoi Hoj Hoo). }
    apply (soup_build _ _ _ _ _ _ _ _ _ _ _ Hs).
    - intros t e1 He1. apply lookup_insert_Some in He1 as [[<- <-]|[Htj He1]].
      + rewrite Kj, Kj, Cj. split_and!; [|exact (s_ty Hs j f Hf)|exact HF2].
        eapply at_cost_E_live; [|exact HE2]. cbn; lia.
      + apply lookup_insert_Some in He1 as [[<- <-]|[Hti He1]].
        * rewrite Ki, Ki, Ci. split_and!; [|exact (s_ty Hs i e He)|exact HF1].
          eapply at_cost_E_live; [|exact HE1]. cbn; lia.
        * rewrite !Kt, Ct by done. destruct (s_other _ _ _ _ _ _ _ _ _ _ _ Hs t e1 He1) as [H1 H2].
          split_and!; [done|exact (s_ty Hs t e1 He1)|done].
    - apply map_eq. intros o0. rewrite !lookup_fmap, HK'.
      pose proof (s_pts _ _ _ _ _ _ _ _ Hs o0) as Hp. cbn [s_K] in Hp.
      case_decide as Hc.
      + destruct Hc as [-> | ->]; [by rewrite lookup_delete_eq|by rewrite lookup_delete_ne, lookup_delete_eq].
      + rewrite !lookup_delete_ne by (intros ?; subst; apply Hc; auto).
        rewrite Hp. destruct (K !! o0); simpl; [|done]. by own_cases.
    - apply set_eq. intros o0. rewrite HdK, !dom_delete_L, (s_dom _ _ _ _ _ _ _ _ Hs). cbn [s_K].
      rewrite !elem_of_difference, !elem_of_singleton. split.
      + intros [[H0 H5] H6]. split; [done|]. intros [?|?]; contradiction.
      + intros [H0 Hn]. split_and!; [done|intros ->; apply Hn; auto|intros ->; apply Hn; auto].
    - intros o0 h0 Ho0. rewrite HK' in Ho0. case_decide; [done|].
      apply fmap_Some in Ho0 as (h1 & Ho1 & ->). pose proof (s_threads _ _ _ _ _ _ _ _ _ _ _ Hs o0 h1 Ho1).
      rewrite !lookup_insert_is_Some'. own_cases; simpl; auto.
    - intros o0 Ho0. apply HdK in Ho0 as [Ho0 Hne]. apply elem_of_difference.
      split; [exact (s_closed _ _ _ _ _ _ _ _ Hs o0 Ho0)|]. rewrite elem_of_singleton.
      intros Hc. destruct (ech_eq _ _ Hc) as [Hc'|Hc']; apply Hne; [left; done|right; rewrite Hc'; symmetry; apply edual_edual].
    - intros o0 Ho0. apply HdK in Ho0 as [Ho0 Hne]. apply HdK. split; [exact (s_pair _ _ _ _ _ _ _ _ Hs o0 Ho0)|].
      intros [Hc|Hc]; apply Hne; [right; by rewrite <-Hc, edual_edual|left; by apply edual_inj].
    - intros o0 S1 x1 S2 x2 H3 H4. apply lookup_delete_Some in H3 as [_ H3]. apply lookup_delete_Some in H3 as [_ H3].
      apply lookup_delete_Some in H4 as [_ H4]. apply lookup_delete_Some in H4 as [_ H4].
      exact (s_sdual _ _ _ _ _ _ _ _ Hs o0 S1 x1 S2 x2 H3 H4).
    - intros o0 P1 P2 H3 H4. apply lookup_delete_Some in H3 as [_ H3]. apply lookup_delete_Some in H3 as [_ H3].
      apply lookup_delete_Some in H4 as [_ H4]. apply lookup_delete_Some in H4 as [_ H4].
      exact (s_pdual _ _ _ _ _ _ _ _ Hs o0 P1 P2 H3 H4).
    - apply kfin_ktick, kfin_delete, kfin_delete. exact (sp_fin _ _ _ _ _ _ _ _ Hs).
  Qed.

  (** P-Act-Choice. *)
  Lemma step_choice i j e e' f f' o b :
    i ≠ j → Mq !! i = Some e → Mq !! j = Some f →
    tstep e (LSess (SSel o b)) e' → tstep f (LSess (SBra (edual o) b)) f' →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K tk) (EvChoice i j o b) (C, <[j := f']> (<[i := e']> Mq))) A' Π' U.
  Proof.
    intros Hij He Hf Hst Hst'.
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HEi HFi].
    destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs j f _ f' Hf Hst') as [HEj HFj].
    cbn [Eobl Fobl] in HEi, HFi, HEj, HFj. unfold o_select in HEi. unfold o_branch in HEj.
    unfold f_select in HFi. unfold f_branch in HFj.
    destruct HEi as (S0 & x & S1 & S2 & Ho & Hu & HE1).
    destruct HEj as (S0' & x' & S1' & S2' & Ho' & Hu' & HE2).
    destruct HFi as (_ & P0 & P1 & P2 & HPo & HPu & HF1).
    destruct HFj as (_ & P0' & P1' & P2' & HPo' & HPu' & HF2).
    destruct (owner_of i o _ Ho) as (hi & Khi & Ehi).
    destruct (owner_of j (edual o) _ Ho') as (hj & Khj & Ehj).
    pose proof (inA _ _ _ Ho) as HA. pose proof (inA _ _ _ Ho') as HA'.
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S0' x' HA HA') as [-> Hsd].
    destruct (sdual_plus_both _ _ _ _ _ _ Hsd Hu Hu') as [Hd1 Hd2].
    pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o P0 P0' (inΠ _ _ _ HPo) (inΠ _ _ _ HPo')) as Hpd.
    destruct (pdual_plus _ _ _ _ _ _ Hpd HPu HPu') as [Hq1 Hq2].
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x HA) as Hkx. cbn [s_K] in Hkx.
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs (edual o) S0' (pt_dual x) HA') as Hkx'. cbn [s_K] in Hkx'.
    assert (HMi : ∀ o1, o1 ∈ (∅ : gset cend) → ∃ h, K !! o1 = Some h ∧ h.(h_th) = i ∧ o1 ≠ o)
      by (intros o1 Ho1; by apply elem_of_empty in Ho1).
    assert (Hoo : o ≠ edual o) by (destruct o; discriminate).
    unfold ftick in HF1, HF2. rewrite fsub_inf in HF1, HF2.
    set (y := sel_pt x b). set (y' := bra_pt (pt_dual x) b).
    exists (<[o := (bsel b S1 S2, y)]> (<[edual o := (bsel b S1' S2', y')]> A)),
      (<[o := if b then P2 else P1]> (<[edual o := if b then P2' else P1']> Π)).
    unfold lf_next. cbn [own_next tk_next s_K s_tk s_q]. rewrite Hkx, Hkx'. fold y y'.
    assert (Hoi : ∃ h, K !! o = Some h ∧ h.(h_th) = i) by eauto.
    assert (Hoj : ∃ h, K !! edual o = Some h ∧ h.(h_th) = j) by eauto.
    pose proof (λ Y, @sync_kres_i' N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo Y) as Ki'.
    pose proof (λ Y, @sync_kres_j' N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo Y) as Kj'.
    pose proof (λ Y, @sync_kres_other N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo Y) as Kt.
    pose proof (sync_ctrs_i N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo) as Ci.
    pose proof (sync_ctrs_j N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo) as Cj.
    pose proof (sync_ctrs_other N K i j o y y' ∅ Hij Hoi Hoj HMi Hoo) as Ct.
    rewrite mrem_empty in Ci. rewrite fhand_empty, map_union_empty in Cj.
    assert (HK' : ∀ o0, ksync N i j o y y' ∅ K !! o0 =
      if decide (o0 = o) then Some (Hold i y (Some N))
      else if decide (o0 = edual o) then Some (Hold j y' (Some N))
      else (λ h, if decide (o0 ∈ (∅ : gset cend)) then Hold j h.(h_pt) (ftick h.(h_ctr))
                 else if decide (h.(h_th) = i ∨ h.(h_th) = j) then htick h else h) <$> K !! o0).
    { intros o0. by rewrite lookup_ksync. }
    assert (HdK : dom (ksync N i j o y y' ∅ K) = dom K).
    { apply set_eq. intros o0. rewrite !elem_of_dom, HK'.
      destruct (decide (o0 = o)) as [->|]; [split; intros _; [by eexists|done]|].
      destruct (decide (o0 = edual o)) as [->|]; [split; intros _; [by eexists|done]|].
      by rewrite fmap_is_Some. }
    assert (HCh : ∀ o0, o0 ∈ ({[o]} ∪ {[edual o]} : gset cend) ↔ edual o0 ∈ ({[o]} ∪ {[edual o]} : gset cend)).
    { intros o0. rewrite !elem_of_union, !elem_of_singleton. split.
      - intros [-> | ->]; [right|left]; [done|apply edual_edual].
      - intros [H|H]; [right; by rewrite <-H, edual_edual|left; by apply edual_inj]. }
    apply (soup_build _ _ _ _ _ _ _ _ _ _ _ Hs).
    - intros t e1 He1. apply lookup_insert_Some in He1 as [[<- <-]|[Htj He1]].
      + rewrite Kj', Kj', Cj, !mres_empty, !map_union_empty. split_and!; [|exact (s_ty Hs j f Hf)|exact HF2].
        eapply at_cost_E_live; [|exact HE2]. cbn; lia.
      + apply lookup_insert_Some in He1 as [[<- <-]|[Hti He1]].
        * rewrite Ki', Ki', Ci, !mrem_empty. split_and!; [|exact (s_ty Hs i e He)|exact HF1].
          eapply at_cost_E_live; [|exact HE1]. cbn; lia.
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
    - intros o0 S5 x5 S6 x6 H3 H4.
      refine (pair_frame (λ _ (v v' : sty * point), v'.2 = pt_dual v.2 ∧ sdual v.1 v'.1) _ _
        ({[o]} ∪ {[edual o]}) HCh _ _ _ o0 (S5, x5) (S6, x6) H3 H4).
      + intros o1 Ho1. rewrite !lookup_insert_ne by (clear - Ho1; set_solver). done.
      + intros o1 [S7 x7] [S8 x8] H5 H6. exact (s_sdual _ _ _ _ _ _ _ _ Hs o1 S7 x7 S8 x8 H5 H6).
      + assert (y' = pt_dual y) as Hy.
        { unfold y, y', sel_pt, bra_pt. by rewrite pt_field_dual, pt_dual_dual. }
        intros o1 [S7 x7] [S8 x8] Ho1 H5 H6. simpl.
        apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_singleton in Ho1 as ->.
        * rewrite lookup_insert_eq in H5. rewrite lookup_insert_ne, lookup_insert_eq in H6 by done.
          simplify_eq. split; [done|by apply sdual_bsel].
        * rewrite edual_edual, lookup_insert_eq in H6. rewrite lookup_insert_ne, lookup_insert_eq in H5 by done.
          simplify_eq. split; [by rewrite Hy, pt_dual_dual|by apply sdual_sym, sdual_bsel].
    - intros o0 Q1 Q2 H3 H4.
      refine (pair_frame (λ _ v v', sequiv v' (dual v)) _ _ ({[o]} ∪ {[edual o]}) HCh _ _ _ o0 Q1 Q2 H3 H4).
      + intros o1 Ho1. rewrite !lookup_insert_ne by (clear - Ho1; set_solver). done.
      + intros o1 Q5 Q6 H5 H6. exact (s_pdual _ _ _ _ _ _ _ _ Hs o1 Q5 Q6 H5 H6).
      + intros o1 Q5 Q6 Ho1 H5 H6.
        apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_singleton in Ho1 as ->.
        * rewrite lookup_insert_eq in H5. rewrite lookup_insert_ne, lookup_insert_eq in H6 by done.
          simplify_eq. by destruct b.
        * rewrite edual_edual, lookup_insert_eq in H6. rewrite lookup_insert_ne, lookup_insert_eq in H5 by done.
          simplify_eq. apply pdual_sym. by destruct b.
    - apply kfin_ksync. exact (sp_fin _ _ _ _ _ _ _ _ Hs).
  Qed.
End sync.
