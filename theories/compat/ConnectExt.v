(** * P-Connect, external steps of the composite (stage S4)

    An external step of the composite is an external step of the
    component of its thread on an interface end. Close, select, branch
    and link change the interface of that component only. *)

From GV Require Export compat.ConnectTau.
From GV Require Import fuel.FuelMono.

Lemma conn_del_iface1 Σ1 ΣC C1 Σ2 ΣD C2 o :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → conn (delete o Σ1) ΣC C1 Σ2 ΣD C2.
Proof.
  intros [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
  assert (chans_of (delete o Σ1) ⊆ chans_of Σ1) as Hs by (apply chans_of_mono; rewrite dom_delete_L; set_solver).
  constructor; try done.
  - by apply map_disjoint_delete_l.
  - apply (pfree_sub _ Σ1); [rewrite dom_delete_L; set_solver|done].
  - clear -Hs H12. set_solver.
  - clear -Hs H1C. set_solver.
  - clear -Hs HC1. set_solver.
  - clear -Hs HC2. set_solver.
Qed.

Lemma conn_del_iface2 Σ1 ΣC C1 Σ2 ΣD C2 o :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → conn Σ1 ΣC C1 (delete o Σ2) ΣD C2.
Proof. intros Hc. apply conn_sym, conn_del_iface1, conn_sym, Hc. Qed.

Lemma conn_retype2 Σ1 ΣC C1 Σ2 ΣD C2 o v :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → o ∈ dom Σ2 → conn Σ1 ΣC C1 (<[o := v]> Σ2) ΣD C2.
Proof. intros Hc Ho. apply conn_sym, conn_retype1; [by apply conn_sym|done]. Qed.

Section ext.
  Context (κ : ctable) (n : Ix) (W1 : world) (T : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (CC : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Let HT := cc_HT CC. Let Hc := cc_Hc CC.
  Let H1 := cc_H1 CC. Let H2 := cc_H2 CC. Let L := cc_L CC.
  Let X1P := cc_X1P CC. Let X2P := cc_X2P CC. Let HP1 := cc_HP1 CC. Let HP2 := cc_HP2 CC.
  Let G1 := cc_G1 CC. Let G2 := cc_G2 CC.
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma Hq1e M1 : soup M1 = q1.2 → erase (q1.1, M1) = q1.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q1. Qed.
  Local Lemma Hq2e M2 : soup M2 = q2.2 → erase (q2.1, M2) = q2.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q2. Qed.
  Local Lemma side (M1 M2 : gmap nat expr) i e : (M1 ∪ M2) !! i = Some e → M1 !! i = Some e ∨ M2 !! i = Some e.
  Proof. intros [H|[_ H]]%lookup_union_Some_raw; auto. Qed.

  (** A step of p1 that changes only its interface. *)
  Lemma ext_comp1 c Σ1' p1' :
    at_cost_P n c (Prel κ) X1 W1 (Σ1' ∪ ΣC) T p1' → conn Σ1' ΣC p1'.1 Σ2 ΣD q2.1 →
    at_cost_P n c (Prel κ) (Prel κ n) W1 (Σ1' ∪ Σ2) T (pconn p1' q2 K).
  Proof.
    intros [A0 A1] Hc'. split.
    - intros Hz. pose proof (G1 p1' _ id ∅ Σ1' ΣC Σ2 ΣD q2 (A0 Hz) (fuse_ok_id _ _)) as HG.
      rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in HG. apply HG; [done| |done].
      pose proof (HP2 id ∅ (fuse_ok_id _ _)) as P. by rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in P.
    - intros Hz j Hj. apply (L j (oadd_lt _ _ _ Hz Hj) Σ1' ΣC Σ2 ΣD); [by apply A1| |done].
      pose proof (HP2 id ∅ (fuse_ok_id _ _)) as P. rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in P.
      eapply Prel_down; [|exact P]. exact (olt_ole _ _ (oadd_lt _ _ _ Hz Hj)).
  Qed.

  (** A step of p2 that changes only its interface. *)
  Lemma ext_comp2 c Σ2' p2' :
    at_cost_P n c (Prel κ) X2 W1 (Σ2' ∪ ΣD) TUnit p2' → conn Σ1 ΣC q1.1 Σ2' ΣD p2'.1 →
    at_cost_P n c (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2') T (pconn q1 p2' K).
  Proof.
    intros [A0 A1] Hc'. split.
    - intros Hz. pose proof (G2 p2' _ id ∅ Σ1 ΣC Σ2' ΣD id ∅ (A0 Hz) (fuse_ok_id _ _)) as HG.
      rewrite !sdrop_empty, !kren_id_map, !pfuse_empty, !pmap_id in HG. apply HG; [done|apply fuse_ok_id|done|done].
    - intros Hz j Hj. apply (L j (oadd_lt _ _ _ Hz Hj) Σ1 ΣC Σ2' ΣD); [|by apply A1|done].
      pose proof (HP1 id ∅ (fuse_ok_id _ _)) as P. rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in P.
      eapply Prel_down; [|exact P]. exact (olt_ole _ _ (oadd_lt _ _ _ Hz Hj)).
  Qed.

  Local Lemma iface1 o v : (Σ1 ∪ ΣC) !! o = Some v → ech o ∉ K → Σ1 !! o = Some v ∧ o ∈ dom Σ1.
  Proof.
    intros H Hn. destruct (lookup_1C _ _ _ _ H) as [[A B]|[A B]]; [done|]. exfalso. apply Hn. by apply elem_of_chans_of.
  Qed.

  Local Lemma iface2 o v : (Σ2 ∪ ΣD) !! o = Some v → ech o ∉ K → Σ2 !! o = Some v ∧ o ∈ dom Σ2.
  Proof.
    intros H Hn. destruct (lookup_1C _ _ _ _ H) as [[A B]|[A B]]; [done|]. exfalso. apply Hn.
    rewrite <-(cut_dual_chans ΣC ΣD) by (by destruct Hc). by apply elem_of_chans_of.
  Qed.

  Local Lemma lk12 o v : Σ1 !! o = Some v → (Σ1 ∪ Σ2) !! o = Some v.
  Proof. apply lookup_union_Some_l. Qed.
  Local Lemma lk21 o v : Σ2 !! o = Some v → (Σ1 ∪ Σ2) !! o = Some v.
  Proof.
    intros H. apply lookup_union_Some_raw. right. split; [|done]. apply not_elem_of_dom. intros D.
    destruct (cls_2 _ _ _ _ _ _ o Hc ltac:(by eapply elem_of_dom_2)) as (_ & ? & _). done.
  Qed.

  Local Lemma del1 o : o ∈ dom Σ1 → delete o (Σ1 ∪ ΣC) = delete o Σ1 ∪ ΣC ∧ delete o (Σ1 ∪ Σ2) = delete o Σ1 ∪ Σ2.
  Proof.
    intros D. pose proof (cls_1 _ _ _ _ _ _ Hc o D) as Co. rewrite !delete_union.
    rewrite (delete_id ΣC o), (delete_id Σ2 o); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto].
  Qed.
  Local Lemma del2 o : o ∈ dom Σ2 → delete o (Σ2 ∪ ΣD) = delete o Σ2 ∪ ΣD ∧ delete o (Σ1 ∪ Σ2) = Σ1 ∪ delete o Σ2.
  Proof.
    intros D. pose proof (cls_2 _ _ _ _ _ _ o Hc D) as Co. rewrite !delete_union.
    rewrite (delete_id ΣD o), (delete_id Σ1 o); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto].
  Qed.
  Local Lemma ins1 o v : o ∈ dom Σ1 → <[o := v]> (Σ1 ∪ ΣC) = <[o := v]> Σ1 ∪ ΣC ∧ <[o := v]> (Σ1 ∪ Σ2) = <[o := v]> Σ1 ∪ Σ2.
  Proof. intros D. by rewrite !insert_union_l. Qed.
  Local Lemma ins2 o v : o ∈ dom Σ2 → <[o := v]> (Σ2 ∪ ΣD) = <[o := v]> Σ2 ∪ ΣD ∧ <[o := v]> (Σ1 ∪ Σ2) = Σ1 ∪ <[o := v]> Σ2.
  Proof.
    intros D. pose proof (cls_2 _ _ _ _ _ _ o Hc D) as Co. rewrite insert_union_l. split; [done|].
    apply insert_union_r. apply not_elem_of_dom. tauto.
  Qed.

  Local Lemma soup1 M1 M2 i e e' : M1 ##ₘ M2 → M1 !! i = Some e →
    soup (<[i := e']> (M1 ∪ M2)) = soup (<[i := e']> M1) ⊎ soup M2.
  Proof.
    intros Hd Hi. assert (M2 !! i = None) as Hi2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    rewrite insert_union_l, soup_union; [done|]. apply map_disjoint_insert_l. by split.
  Qed.
  Local Lemma soup2 M1 M2 i e e' : M1 ##ₘ M2 → M2 !! i = Some e →
    soup (<[i := e']> (M1 ∪ M2)) = soup M1 ⊎ soup (<[i := e']> M2).
  Proof.
    intros Hd Hi. assert (M1 !! i = None) as Hi1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    rewrite insert_union_r by done. rewrite soup_union; [done|]. apply map_disjoint_insert_r. by split.
  Qed.

  (** The external step of the composite as a step of a component. *)
  Local Lemma ext_split q i σ q' : erase q = pc → istep q (EvOffer i σ) q' →
    ∃ M1 M2 e e', M1 ##ₘ M2 ∧ soup M1 = q1.2 ∧ soup M2 = q2.2 ∧ tstep e (LSess σ) e' ∧
      subjs σ ## q1.1 ∪ q2.1 ∪ K ∧
      ((M1 !! i = Some e ∧ istep (q1.1, M1) (EvOffer i σ) (q1.1 ∖ sentc σ, <[i := e']> M1) ∧
         erase q' = ((q1.1 ∪ q2.1 ∪ K) ∖ sentc σ, soup (<[i := e']> M1) ⊎ q2.2)) ∨
       (M2 !! i = Some e ∧ istep (q2.1, M2) (EvOffer i σ) (q2.1 ∖ sentc σ, <[i := e']> M2) ∧
         erase q' = ((q1.1 ∪ q2.1 ∪ K) ∖ sentc σ, q1.2 ⊎ soup (<[i := e']> M2)))).
  Proof.
    intros Hq Hst. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
    inversion Hst; subst. exists M1, M2, e, e'. split_and!; try done.
    match goal with H : (_ ∪ _) !! i = Some _ |- _ => destruct (side _ _ _ _ H) as [Hi|Hi] end; [left|right]; split_and!; try done.
    - eapply p_act_session; [exact Hi|done|cc_set_solver].
    - unfold erase. simpl. by rewrite soup1 with (e := e), HM2.
    - eapply p_act_session; [exact Hi|done|cc_set_solver].
    - unfold erase. simpl. by rewrite soup2 with (e := e), HM1.
  Qed.
  Local Lemma pc1 M1 i e' σ : sentc σ = ∅ →
    ((q1.1 ∪ q2.1 ∪ K) ∖ sentc σ, soup (<[i := e']> M1) ⊎ q2.2) = pconn (erase (q1.1 ∖ sentc σ, <[i := e']> M1)) q2 K.
  Proof. intros E. unfold pconn, erase. simpl. rewrite E, !difference_empty_L. done. Qed.
  Local Lemma pc2 M2 i e' σ : sentc σ = ∅ →
    ((q1.1 ∪ q2.1 ∪ K) ∖ sentc σ, q1.2 ⊎ soup (<[i := e']> M2)) = pconn q1 (erase (q2.1 ∖ sentc σ, <[i := e']> M2)) K.
  Proof. intros E. unfold pconn, erase. simpl. rewrite E, !difference_empty_L. done. Qed.

  (** Q-Close of the composite. *)
  Lemma ext_close q i o q' : erase q = pc → istep q (EvOffer i (SClose o)) q' →
    ∃ S0 x, (Σ1 ∪ Σ2) !! o = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
      at_cost_P n (c_give κ) (Prel κ) (Prel κ n) W1 (delete o (Σ1 ∪ Σ2)) T (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      simpl in Hsub; assert (ech o ∉ K) as HnK by (clear -Hsub; cc_set_solver); rewrite Eq.
    - destruct H1 as (_ & _ & (_ & _ & _ & C1 & _)). destruct (C1 _ _ _ _ (Hq1e M1 HM1) Hs) as (S0 & x & Lo & Uo & A).
      destruct (iface1 _ _ Lo HnK) as [Lo' D]. exists S0, x. split_and!; [by apply lk12|done|].
      destruct (del1 o D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc1 by done.
      apply ext_comp1; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_del_iface1.
    - destruct H2 as (_ & _ & (_ & _ & _ & C2 & _)). destruct (C2 _ _ _ _ (Hq2e M2 HM2) Hs) as (S0 & x & Lo & Uo & A).
      destruct (iface2 _ _ Lo HnK) as [Lo' D]. exists S0, x. split_and!; [by apply lk21|done|].
      destruct (del2 o D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc2 by done.
      apply ext_comp2; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_del_iface2.
  Qed.

  (** Q-Select of the composite. *)
  Lemma ext_select q i o b q' : erase q = pc → istep q (EvOffer i (SSel o b)) q' →
    ∃ S0 x S1 S2, (Σ1 ∪ Σ2) !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
      at_cost_P n (c_give κ) (Prel κ) (Prel κ n) W1 (<[o := (bsel b S1 S2, sel_pt x b)]> (Σ1 ∪ Σ2)) T (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      simpl in Hsub; assert (ech o ∉ K) as HnK by (clear -Hsub; cc_set_solver); rewrite Eq.
    - destruct H1 as (_ & _ & (_ & _ & _ & _ & C1 & _)). destruct (C1 _ _ _ _ _ (Hq1e M1 HM1) Hs) as (S0 & x & S1 & S2 & Lo & Uo & A).
      destruct (iface1 _ _ Lo HnK) as [Lo' D]. exists S0, x, S1, S2. split_and!; [by apply lk12|done|].
      destruct (ins1 o (bsel b S1 S2, sel_pt x b) D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc1 by done.
      apply ext_comp1; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_retype1.
    - destruct H2 as (_ & _ & (_ & _ & _ & _ & C2 & _)). destruct (C2 _ _ _ _ _ (Hq2e M2 HM2) Hs) as (S0 & x & S1 & S2 & Lo & Uo & A).
      destruct (iface2 _ _ Lo HnK) as [Lo' D]. exists S0, x, S1, S2. split_and!; [by apply lk21|done|].
      destruct (ins2 o (bsel b S1 S2, sel_pt x b) D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc2 by done.
      apply ext_comp2; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_retype2.
  Qed.

  (** Q-Branch of the composite. *)
  Lemma ext_branch q i o b q' : erase q = pc → istep q (EvOffer i (SBra o b)) q' →
    ∃ S0 x S1 S2, (Σ1 ∪ Σ2) !! o = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
      at_cost_P n (c_take κ) (Prel κ) (Prel κ n) W1 (<[o := (bsel b S1 S2, bra_pt x b)]> (Σ1 ∪ Σ2)) T (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      simpl in Hsub; assert (ech o ∉ K) as HnK by (clear -Hsub; cc_set_solver); rewrite Eq.
    - destruct H1 as (_ & _ & (_ & _ & _ & _ & _ & C1 & _)). destruct (C1 _ _ _ _ _ (Hq1e M1 HM1) Hs) as (S0 & x & S1 & S2 & Lo & Uo & A).
      destruct (iface1 _ _ Lo HnK) as [Lo' D]. exists S0, x, S1, S2. split_and!; [by apply lk12|done|].
      destruct (ins1 o (bsel b S1 S2, bra_pt x b) D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc1 by done.
      apply ext_comp1; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_retype1.
    - destruct H2 as (_ & _ & (_ & _ & _ & _ & _ & C2 & _)). destruct (C2 _ _ _ _ _ (Hq2e M2 HM2) Hs) as (S0 & x & S1 & S2 & Lo & Uo & A).
      destruct (iface2 _ _ Lo HnK) as [Lo' D]. exists S0, x, S1, S2. split_and!; [by apply lk21|done|].
      destruct (ins2 o (bsel b S1 S2, bra_pt x b) D) as [E1 E2]. rewrite E1 in A. rewrite E2, pc2 by done.
      apply ext_comp2; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_retype2.
  Qed.

  (** Q-Link of the composite. *)
  Lemma ext_link q i os q' : erase q = pc → istep q (EvOffer i (SLink os)) q' →
    ∃ o1 o2 S1 S2 x, os = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧
      (Σ1 ∪ Σ2) !! o1 = Some (S1, x) ∧ (Σ1 ∪ Σ2) !! o2 = Some (S2, x‾) ∧ sdual S1 S2 ∧
      at_cost_P n (c_link κ) (Prel κ) (Prel κ n) W1 (delete o1 (delete o2 (Σ1 ∪ Σ2))) T (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      cbn [subjs] in Hsub; rewrite Eq.
    - destruct H1 as (_ & _ & (_ & _ & _ & _ & _ & _ & C1)). destruct (C1 _ _ _ _ (Hq1e M1 HM1) Hs) as (o1 & o2 & S1 & S2 & x & -> & Ne & L1 & L2 & Hs12 & A).
      rewrite set_map_union_L, !set_map_singleton_L in Hsub.
      assert (ech o1 ∉ K ∧ ech o2 ∉ K) as [N1 N2] by (clear -Hsub; split; intros Hk; [apply (Hsub (ech o1))|apply (Hsub (ech o2))]; cc_set_solver).
      destruct (iface1 _ _ L1 N1) as [L1' D1]. destruct (iface1 _ _ L2 N2) as [L2' D2].
      exists o1, o2, S1, S2, x. split_and!; [done|done|by apply lk12|by apply lk12|done|].
      pose proof (cls_1 _ _ _ _ _ _ Hc o1 D1) as Co1. pose proof (cls_1 _ _ _ _ _ _ Hc o2 D2) as Co2.
      assert (delete o1 (delete o2 (Σ1 ∪ ΣC)) = delete o1 (delete o2 Σ1) ∪ ΣC) as E1.
      { rewrite !delete_union, (delete_id ΣC o2), (delete_id ΣC o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      assert (delete o1 (delete o2 (Σ1 ∪ Σ2)) = delete o1 (delete o2 Σ1) ∪ Σ2) as E2.
      { rewrite !delete_union, (delete_id Σ2 o2), (delete_id Σ2 o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      rewrite E1 in A. rewrite E2, pc1 by done.
      apply ext_comp1; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_del_iface1, conn_del_iface1.
    - destruct H2 as (_ & _ & (_ & _ & _ & _ & _ & _ & C2)). destruct (C2 _ _ _ _ (Hq2e M2 HM2) Hs) as (o1 & o2 & S1 & S2 & x & -> & Ne & L1 & L2 & Hs12 & A).
      rewrite set_map_union_L, !set_map_singleton_L in Hsub.
      assert (ech o1 ∉ K ∧ ech o2 ∉ K) as [N1 N2] by (clear -Hsub; split; intros Hk; [apply (Hsub (ech o1))|apply (Hsub (ech o2))]; cc_set_solver).
      destruct (iface2 _ _ L1 N1) as [L1' D1]. destruct (iface2 _ _ L2 N2) as [L2' D2].
      exists o1, o2, S1, S2, x. split_and!; [done|done|by apply lk21|by apply lk21|done|].
      pose proof (cls_2 _ _ _ _ _ _ o1 Hc D1) as Co1. pose proof (cls_2 _ _ _ _ _ _ o2 Hc D2) as Co2.
      assert (delete o1 (delete o2 (Σ2 ∪ ΣD)) = delete o1 (delete o2 Σ2) ∪ ΣD) as E1.
      { rewrite !delete_union, (delete_id ΣD o2), (delete_id ΣD o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      assert (delete o1 (delete o2 (Σ1 ∪ Σ2)) = Σ1 ∪ delete o1 (delete o2 Σ2)) as E2.
      { rewrite !delete_union, (delete_id Σ1 o2), (delete_id Σ1 o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      rewrite E1 in A. rewrite E2, pc2 by done.
      apply ext_comp2; [exact A|]. simpl. rewrite difference_empty_L. by apply conn_del_iface2, conn_del_iface2.
  Qed.
End ext.
