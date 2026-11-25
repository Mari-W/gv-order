(** * The soup along a link (stage S8)

    P-Act-Link: thread i links o1 and o2, which it holds at dual points
    and dual session types. The channel of o1 goes, and every thread is
    renamed by [csub o1 o2], so the dual end of o1 now holds o2. The
    linker's obligations remove both ends, and its fuel gives the
    tickets of the link ([lok]). Every other thread keeps its term,
    renamed ([Erel_rename], [FuelE_rename]), and the dual ends of o1 and
    o2 form one channel ([link_pair]), whose tickets meet the bound
    ([link_tsum]). No counter changes. *)

From stdpp Require Import relations.
From GV Require Export soup.SoupSync soup.LinkMaps.

Lemma pair_set_eq (o1 o2 p1 p2 : cend) :
  ({[o1]} ∪ {[o2]} : gset cend) = {[p1]} ∪ {[p2]} → p1 ≠ p2 →
  (p1 = o1 ∧ p2 = o2) ∨ (p1 = o2 ∧ p2 = o1).
Proof.
  intros Heq Hne.
  assert (p1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as H1 by (rewrite Heq; set_solver).
  assert (p2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as H2 by (rewrite Heq; set_solver).
  assert (o1 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as H3 by (rewrite <-Heq; set_solver).
  assert (o2 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as H4 by (rewrite <-Heq; set_solver).
  set_solver.
Qed.

Lemma kdel2_notown {Y : Type} (K : own) t (m : gmap cend Y) o1 o2 :
  (¬ ∃ h, K !! o1 = Some h ∧ h.(h_th) = t) → (¬ ∃ h, K !! o2 = Some h ∧ h.(h_th) = t) →
  kdel2 o1 o2 (kres K t m) = kres K t m.
Proof.
  intros H1 H2.
  assert (kres K t m !! o1 = None) by (apply lookup_kres_None; by right).
  assert (kres K t m !! o2 = None) by (apply lookup_kres_None; by right).
  unfold kdel2. rewrite (delete_id (kres K t m) o2) by done. by rewrite delete_id.
Qed.

Lemma ctrs_notown (K : own) t o1 o2 :
  (¬ ∃ h, K !! o1 = Some h ∧ h.(h_th) = t) → (¬ ∃ h, K !! o2 = Some h ∧ h.(h_th) = t) →
  kdel2 o1 o2 (ctrs K t) = ctrs K t.
Proof.
  intros H1 H2.
  assert (ctrs K t !! o1 = None) by (by apply lookup_ctrs_None).
  assert (ctrs K t !! o2 = None) by (by apply lookup_ctrs_None).
  unfold kdel2. rewrite (delete_id (ctrs K t) o2) by done. by rewrite delete_id.
Qed.

Section link.
  Context (N : nat) (n lv : Ix) (Hlv : olt lv n) (W : world) (T : ty) (C : gset chan) (Mq : gmap nat expr) (K : own) (Ws : world)
    (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W ∅ T (LFState (C, Mq) K Ws) A Π U).

  Local Lemma owner_of' t o v : kres K t A !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

  Local Lemma inA' t o v : kres K t A !! o = Some v → A !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  Local Lemma inΠ' t o v : kres K t Π !! o = Some v → Π !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  (** The linker's obligations, in the order of the event. *)
  Lemma link_obl i e o1 o2 e' :
    Mq !! i = Some e → tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' →
    o1 ≠ o2 ∧
    (∃ h, K !! o1 = Some h ∧ h.(h_th) = i) ∧ (∃ h, K !! o2 = Some h ∧ h.(h_th) = i) ∧
    (∃ Sa Sb xa, A !! o1 = Some (Sa, xa) ∧ A !! o2 = Some (Sb, pt_dual xa) ∧ sdual Sa Sb) ∧
    (∃ Pa Pb, Π !! o1 = Some Pa ∧ Π !! o2 = Some Pb ∧ ssub Pa (dual Pb)) ∧
    e' ∈ E[live]^W _ lv⟦kdel2 o1 o2 (kres K i A) ⊢ U i⟧^∅ ∧
    lok (Some N) (ctrs K i) ({[o1]} ∪ {[o2]}) ∧
    e' ∈ F^(Some N) _ lv⟦RThread ▷ None⟧(kdel2 o1 o2 (kres K i Π), kdel2 o1 o2 (ctrs K i)).
  Proof.
    intros He Hst. destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HE HF].
    cbn [Eobl Fobl] in HE, HF. unfold o_link in HE. unfold f_link in HF.
    destruct HE as (p1 & p2 & S1 & S2 & x & Hos & Hp12 & Hp1 & Hp2 & Hsd & HE').
    destruct HF as (Hpl & _ & Htk & HF'). specialize (HF' lv Hlv).
    rewrite mrem_kdel2, mrem_kdel2 in HF'.
    destruct Hpl as (q1 & q2 & P1 & P2 & Hqs & Hq12 & Hq1 & Hq2 & Hqd).
    destruct (owner_of' _ _ _ Hp1) as (h1 & Kh1 & Eh1). destruct (owner_of' _ _ _ Hp2) as (h2 & Kh2 & Eh2).
    pose proof (inA' _ _ _ Hp1) as HA1. pose proof (inA' _ _ _ Hp2) as HA2.
    pose proof (inΠ' _ _ _ Hq1) as HB1. pose proof (inΠ' _ _ _ Hq2) as HB2.
    assert (Hdel : kdel2 p1 p2 (kres K i A) = kdel2 o1 o2 (kres K i A)).
    { destruct (pair_set_eq _ _ _ _ Hos Hp12) as [[-> ->]|[-> ->]]; [done|apply kdel2_comm]. }
    unfold kdel2 in Hdel. rewrite Hdel in HE'.
    destruct (pair_set_eq _ _ _ _ Hos Hp12) as [[-> ->]|[-> ->]];
      (split; [done|]); (split; [eauto|]); (split; [eauto|]); split_and!.
    - exists S1, S2, x. done.
    - destruct (pair_set_eq _ _ _ _ Hqs Hq12) as [[-> ->]|[-> ->]]; [by exists P1, P2|].
      exists P2, P1. split_and!; [done|done|by apply plink_sym].
    - eapply at_cost_E_live; [|exact HE'|exact Hlv]. cbn; lia.
    - done.
    - exact HF'.
    - exists S2, S1, (pt_dual x). split_and!; [done|by rewrite pt_dual_dual|by apply sdual_sym].
    - destruct (pair_set_eq _ _ _ _ Hqs Hq12) as [[-> ->]|[-> ->]]; [by exists P1, P2|].
      exists P2, P1. split_and!; [done|done|by apply plink_sym].
    - eapply at_cost_E_live; [|exact HE'|exact Hlv]. cbn; lia.
    - done.
    - exact HF'.
  Qed.

  Lemma dom_kdel2_eq {Y Z : Type} (m : gmap cend Y) (m' : gmap cend Z) o1 o2 :
    dom m = dom m' → dom (kdel2 o1 o2 m) = dom (kdel2 o1 o2 m').
  Proof. intros H. unfold kdel2. by rewrite !dom_delete_L, H. Qed.

  (** P-Act-Link. *)
  Lemma step_link tc i e o1 o2 e' :
    Mq !! i = Some e → tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' →
    ∃ A' Π', soup_inv N lv W ∅ T
      (lf_next tc (LFState (C, Mq) K Ws) (EvSolo i (LSess (SLink ({[o1]} ∪ {[o2]}))) (PickLink o1 o2))
        (C ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> Mq))) A' Π' U.
  Proof.
    intros He Hst.
    destruct (link_obl i e o1 o2 e' He Hst) as (H12 & Ho1 & Ho2 & (Sa & Sb & xa & HA1 & HA2 & Hsab) &
      (Pa & Pb & HB1 & HB2 & Hpab) & HE & Hlok & HF).
    exists (kmapr (csub o1 o2) (kdel2 o1 o2 A)), (kmapr (csub o1 o2) (kdel2 o1 o2 Π)).
    unfold lf_next. cbn [own_next s_K s_q].
    change (delete o1 (delete o2 K)) with (kdel2 o1 o2 K).
    pose proof (kinj_csub o1 o2 K) as HkK.
    pose proof (s_domA _ _ _ _ _ _ _ _ Hs) as HdA. cbn [s_K] in HdA.
    pose proof (s_dom _ _ _ _ _ _ _ _ Hs) as HdΠ. cbn [s_K] in HdΠ.
    assert (HdA0 : dom (kdel2 o1 o2 A) ⊆ dom (kdel2 o1 o2 K)) by (by rewrite (dom_kdel2_eq A K)).
    assert (HdΠ0 : dom (kdel2 o1 o2 Π) ⊆ dom (kdel2 o1 o2 K)) by (by rewrite (dom_kdel2_eq Π K)).
    destruct Ho1 as (h1 & Kh1 & Eh1). destruct Ho2 as (h2 & Kh2 & Eh2).
    assert (Hown : ∀ t, t ≠ i → (¬ ∃ h, K !! o1 = Some h ∧ h.(h_th) = t) ∧ (¬ ∃ h, K !! o2 = Some h ∧ h.(h_th) = t)).
    { intros t Hti. split; intros (h & Hh & Ht); simplify_eq; congruence. }
    apply (soup_build _ _ _ _ _ _ _ _ _ _ _ _ Hs).
    - intros t e1 He1. apply lookup_fmap_Some in He1 as (e0 & <- & He0).
      rewrite (kres_kmapr _ _ t), (kres_kmapr _ _ t), ctrs_kmapr, kres_kdel2, kres_kdel2, ctrs_kdel2 by done.
      apply lookup_insert_Some in He0 as [[<- <-]|[Hti He0]].
      + split_and!.
        * rewrite <-kren_kmapr. apply Erel_rename; [apply kinj_csub|exact HE].
        * exact (s_ty Hs i e He).
        * eapply (FuelE_rename _ _ _ _ _ _ _ (csub o1 o2)); [apply kinj_csub|apply kinj_csub|
            apply kmapr_renk, kinj_csub|apply kmapr_renk, kinj_csub|exact HF].
      + destruct (Hown t (not_eq_sym Hti)) as [Hn1 Hn2].
        destruct (s_other _ _ _ Hlv _ _ _ _ _ _ _ _ _ Hs t e0 He0) as [H1 H2].
        rewrite <-(kdel2_notown K t A o1 o2 Hn1 Hn2) in H1.
        rewrite <-(kdel2_notown K t Π o1 o2 Hn1 Hn2), <-(ctrs_notown K t o1 o2 Hn1 Hn2) in H2.
        split_and!.
        * rewrite <-kren_kmapr. apply Erel_rename; [apply kinj_csub|exact H1].
        * exact (s_ty Hs t e0 He0).
        * eapply (FuelE_rename _ _ _ _ _ _ _ (csub o1 o2)); [apply kinj_csub|apply kinj_csub|
            apply kmapr_renk, kinj_csub|apply kmapr_renk, kinj_csub|exact H2].
    - rewrite !fmap_kmapr by apply kinj_csub. f_equal. unfold kdel2. rewrite !fmap_delete. f_equal. f_equal.
      apply (sp_pts _ _ _ _ _ _ _ _ _ _ Hs).
    - rewrite !dom_kmapr by apply kinj_csub. f_equal. by apply dom_kdel2_eq.
    - intros o' h Ho'. apply kmapr_lookup_inv in Ho' as (a & -> & Ha). apply lookup_kdel2 in Ha as (_ & _ & Ha).
      pose proof (s_threads _ _ _ _ _ _ _ _ _ _ _ Hs a h Ha) as Ht.
      rewrite lookup_fmap, fmap_is_Some, lookup_insert_is_Some'.
      destruct (decide (i = h.(h_th))); [by left|by right].
    - apply (link_dom_closed K C o1 o2 H12); [by apply elem_of_dom_2 in Kh2|].
      intros a Ha. exact (s_closed _ _ _ _ _ _ _ _ Hs a Ha).
    - destruct (decide (o2 = edual o1)) as [->|Hns].
      + intros o' Ho'. rewrite kmapr_id_ext in Ho' |- * by apply csub_self.
        apply elem_of_dom_kdel2 in Ho' as (Ha1 & Ha2 & Ha). apply elem_of_dom_kdel2. split_and!.
        * intros Hx. apply Ha2. by rewrite <-Hx, edual_edual.
        * intros Hx. apply Ha1. by apply edual_inj.
        * exact (s_pair _ _ _ _ _ _ _ _ Hs o' Ha).
      + apply link_dom_pair; [done|done| |by apply elem_of_dom_2 in Kh1|by apply elem_of_dom_2 in Kh2].
        intros a Ha. exact (s_pair _ _ _ _ _ _ _ _ Hs a Ha).
    - intros o' S1 x1 S2 x2 H3 H4. destruct (decide (o2 = edual o1)) as [->|Hns].
      + rewrite kmapr_id_ext in H3, H4 by apply csub_self.
        apply lookup_kdel2 in H3 as (_ & _ & H3). apply lookup_kdel2 in H4 as (_ & _ & H4).
        exact (s_sdual _ _ _ _ _ _ _ _ Hs o' S1 x1 S2 x2 H3 H4).
      + refine (link_pair (λ v v' : sty * point, v'.2 = pt_dual v.2 ∧ sdual v.1 v'.1) A o1 o2 H12 Hns
          _ _ _ o' (S1, x1) (S2, x2) H3 H4).
        * intros [S5 x5] [S6 x6] [Hx Hd]. simpl in *. split; [by rewrite Hx, pt_dual_dual|by apply sdual_sym].
        * intros a [S5 x5] [S6 x6] H5 H6. exact (s_sdual _ _ _ _ _ _ _ _ Hs a S5 x5 S6 x6 H5 H6).
        * intros [R1 y1] [R2 y2] H5 H6. simpl.
          destruct (s_sdual _ _ _ _ _ _ _ _ Hs o1 Sa xa R1 y1 HA1 H5) as [-> Hd1].
          destruct (s_sdual _ _ _ _ _ _ _ _ Hs o2 Sb (pt_dual xa) R2 y2 HA2 H6) as [-> Hd2].
          split; [done|]. exact (sdual_link Sa Sb R1 R2 Hsab Hd1 Hd2).
    - intros o' Q1 Q2 H3 H4. destruct (decide (o2 = edual o1)) as [->|Hns].
      + rewrite kmapr_id_ext in H3, H4 by apply csub_self.
        apply lookup_kdel2 in H3 as (_ & _ & H3). apply lookup_kdel2 in H4 as (_ & _ & H4).
        exact (s_pdual _ _ _ _ _ _ _ _ Hs o' Q1 Q2 H3 H4).
      + refine (link_pair (λ v v', ssub (dual v) v') Π o1 o2 H12 Hns _ _ _ o' Q1 Q2 H3 H4).
        * intros P P' HP. by apply pdual_sym.
        * intros a P P' H5 H6. exact (s_pdual _ _ _ _ _ _ _ _ Hs a P P' H5 H6).
        * intros R1 R2 H5 H6.
          pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o1 Pa R1 HB1 H5) as Hd1.
          pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o2 Pb R2 HB2 H6) as Hd2.
          exact (pdual_link Pa Pb R1 R2 Hpab Hd1 Hd2).
    - apply kfin_kmapr. unfold kdel2. apply kfin_delete, kfin_delete. exact (sp_fin _ _ _ _ _ _ _ _ _ _ Hs).
    - intros o' h Ho'. apply kmapr_lookup_inv in Ho' as (a & -> & Ha). apply lookup_kdel2 in Ha as (_ & _ & Ha).
      exact (s_kcap_ok _ _ _ _ _ _ _ _ _ _ _ Hs a h Ha).
    - intros o' h h' H3 H4. destruct (decide (o2 = edual o1)) as [->|Hns].
      + rewrite kmapr_id_ext in H3, H4 by apply csub_self.
        apply lookup_kdel2 in H3 as (_ & _ & H3). apply lookup_kdel2 in H4 as (_ & _ & H4).
        exact (s_ktsum_ok _ _ _ _ _ _ _ _ _ _ _ Hs o' h h' H3 H4).
      + refine (link_pair (λ v v' : hold, tsum_ok (Some N) v.(h_cap) v'.(h_cap)) K o1 o2 H12 Hns
          _ _ _ o' h h' H3 H4).
        * intros v v' Hv. by apply tsum_ok_comm.
        * intros a v v' H5 H6. exact (s_ktsum_ok _ _ _ _ _ _ _ _ _ _ _ Hs a v v' H5 H6).
        * intros r1 r2 H5 H6.
          assert (ctrs K i !! o1 = Some (hctr h1)) as G1 by (apply lookup_ctrs; by exists h1).
          assert (ctrs K i !! o2 = Some (hctr h2)) as G2 by (apply lookup_ctrs; by exists h2).
          destruct (Hlok o1 o2 _ _ eq_refl H12 G1 G2) as [L1 _]. simpl in L1.
          exact (link_tsum N _ _ _ _ _ L1 (proj1 (s_kcap_ok _ _ _ _ _ _ _ _ _ _ _ Hs o1 h1 Kh1))
                   (s_ktsum_ok _ _ _ _ _ _ _ _ _ _ _ Hs o1 h1 r1 Kh1 H5)
                   (s_ktsum_ok _ _ _ _ _ _ _ _ _ _ _ Hs o2 h2 r2 Kh2 H6)).
  Qed.
End link.
