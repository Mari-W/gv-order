(** * P-Connect, the step clause of the composite (stage S4)

    One lemma per kind of step of the composite, over the clauses of the
    two components (compat/Connect.v). *)

From GV Require Export compat.ConnectCtx.
From GV Require Import fuel.FuelMono.

(** ** The step clause of the composite *)

Section core.
  Context (κ : ctable) (n : nat) (W1 : world) (T : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (CC : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Let HS := cc_HS CC. Let HT := cc_HT CC. Let Hc := cc_Hc CC.
  Let H1 := cc_H1 CC. Let H2 := cc_H2 CC. Let L := cc_L CC.
  Let X1P := cc_X1P CC. Let X2P := cc_X2P CC. Let HP1 := cc_HP1 CC. Let HP2 := cc_HP2 CC.
  Let G1 := cc_G1 CC. Let G2 := cc_G2 CC.
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma Hq1e M1 : soup M1 = q1.2 → erase (q1.1, M1) = q1.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q1. Qed.
  Local Lemma Hq2e M2 : soup M2 = q2.2 → erase (q2.1, M2) = q2.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q2. Qed.

  Local Lemma HP2r g : dcomm g → (∀ o, pheld (Σ2 ∪ ΣD) q2 o → g o = o) →
    ∀ j, j ≤ S n → Prel κ j W1 (Σ2 ∪ ΣD) TUnit (pmap g q2).
  Proof.
    intros Hd Hid j Hj. destruct (ren_held_id g _ _ Hd Hid) as (Hok & Hk & _).
    pose proof (HP2 g ∅ (pren_fuse_ok _ _ _ Hok)) as H. rewrite sdrop_empty, Hk, pfuse_empty in H.
    by eapply Prel_down.
  Qed.

  Local Lemma HP1r g : dcomm g → (∀ o, pheld (Σ1 ∪ ΣC) q1 o → g o = o) →
    ∀ j, j ≤ S n → Prel κ j W1 (Σ1 ∪ ΣC) T (pmap g q1).
  Proof.
    intros Hd Hid j Hj. destruct (ren_held_id g _ _ Hd Hid) as (Hok & Hk & _).
    pose proof (HP1 g ∅ (pren_fuse_ok _ _ _ Hok)) as H. rewrite sdrop_empty, Hk, pfuse_empty in H.
    by eapply Prel_down.
  Qed.

  Local Lemma ev_ren_ok1 ev : (match ev with EvLink _ o1 _ => ech o1 ∈ q1.1 | _ => True end) →
    dcomm (ev_ren ev) ∧ ∀ o, pheld (Σ2 ∪ ΣD) q2 o → ev_ren ev o = o.
  Proof.
    destruct ev; simpl; intros Hl; try (split; [done|done]).
    split; [apply csub_dcomm_all|]. apply csub_held_id.
    destruct Hc as [_ _ Hcut _ _ _ _ _ _ HCC HC1 _]. rewrite chans_of_union, (cut_dual_chans _ _ Hcut). cc_set_solver.
  Qed.

  (** A τ step that p1 takes alone. *)
  Lemma tau_l1 M1 M2 ev q' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    istep (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) ev q' → ev_tau ev → ev_local q1.1 M1 ev →
    q'.1 ## chans_of (Σ1 ∪ Σ2) →
    at_cost_P (S n) (ev_cost κ ev) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T (erase q').
  Proof.
    intros Hd HM1 HM2 Hst Hτ Hloc Hfr.
    assert (q1.1 ## q2.1 ∪ K) as HC12 by (destruct Hc; cc_set_solver).
    destruct (istep_local _ _ _ _ _ _ _ Hd HC12 Hst Hloc) as (q1' & Hst1 & -> & Hsub & Hdj & Hd').
    destruct (ev_ren_ok1 ev) as [Hgd Hgid].
    { destruct ev; simpl; try done. by destruct Hloc as [_ ?]. }
    destruct H1 as (_ & _ & Ht1 & _).
    destruct (Ht1 (q1.1, M1) ev q1' (Hq1e M1 HM1) Hst1 Hτ) as [A0 A1].
    { rewrite chans_of_union. simpl in Hfr. rewrite chans_of_union in Hfr. unfold erase. simpl. cc_set_solver. }
    assert (erase (q1'.1 ∪ q2.1 ∪ K, q1'.2 ∪ (emap (ev_ren ev) <$> M2)) =
      pconn (erase q1') (pmap (ev_ren ev) q2) K) as He.
    { unfold erase, pconn, pmap. simpl. rewrite soup_union; [|apply map_disjoint_dom; rewrite dom_fmap_L; by apply map_disjoint_dom].
      rewrite soup_fmap, HM2. destruct (ren_held_id _ _ _ Hgd Hgid) as (_ & _ & E). unfold pmap in E. simpl in E.
      by rewrite E. }
    rewrite He.
    assert (conn Σ1 ΣC (erase q1').1 Σ2 ΣD (pmap (ev_ren ev) q2).1) as Hc'.
    { destruct (ren_held_id _ _ _ Hgd Hgid) as (_ & _ & ->). apply (conn_C1 _ _ q1.1); [done| |].
      - unfold erase. simpl. cc_set_solver.
      - unfold erase. simpl. rewrite chans_of_union in Hfr. simpl in Hfr. cc_set_solver. }
    split.
    - intros Hc0. pose proof (A0 Hc0) as HX.
      pose proof (G1 (erase q1') (Σ1 ∪ ΣC) id ∅ Σ1 ΣC Σ2 ΣD (pmap (ev_ren ev) q2) HX (fuse_ok_id _ _)) as HG.
      rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in HG.
      apply HG; [done|by apply HP2r|done].
    - intros Hc0. apply (L (S n - ev_cost κ ev) ltac:(lia) Σ1 ΣC Σ2 ΣD); [by apply A1|apply HP2r; [done|done|lia]|done].
  Qed.

  Local Lemma ev_ren_ok2 ev : (match ev with EvLink _ o1 _ => ech o1 ∈ q2.1 | _ => True end) →
    dcomm (ev_ren ev) ∧ ∀ o, pheld (Σ1 ∪ ΣC) q1 o → ev_ren ev o = o.
  Proof.
    destruct ev; simpl; intros Hl; try (split; [done|done]).
    split; [apply csub_dcomm_all|]. apply csub_held_id.
    destruct Hc as [_ _ Hcut _ _ _ _ _ _ HCC _ HC2]. rewrite chans_of_union. cc_set_solver.
  Qed.

  (** A τ step that p2 takes alone. *)
  Lemma tau_l2 M1 M2 ev q' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    istep (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) ev q' → ev_tau ev → ev_local q2.1 M2 ev →
    q'.1 ## chans_of (Σ1 ∪ Σ2) →
    at_cost_P (S n) (ev_cost κ ev) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T (erase q').
  Proof.
    intros Hd HM1 HM2 Hst Hτ Hloc Hfr.
    assert (q2.1 ## q1.1 ∪ K) as HC21 by (destruct Hc; cc_set_solver).
    assert ((q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) = (q2.1 ∪ q1.1 ∪ K, M2 ∪ M1)) as Esw.
    { f_equal; [cc_set_solver|by apply map_union_comm]. }
    rewrite Esw in Hst.
    destruct (istep_local _ _ _ _ _ _ _ (map_disjoint_sym _ _ Hd) HC21 Hst Hloc) as (q2' & Hst2 & -> & Hsub & Hdj & Hd').
    destruct (ev_ren_ok2 ev) as [Hgd Hgid].
    { destruct ev; simpl; try done. by destruct Hloc as [_ ?]. }
    destruct H2 as (_ & _ & Ht2 & _).
    destruct (Ht2 (q2.1, M2) ev q2' (Hq2e M2 HM2) Hst2 Hτ) as [A0 A1].
    { rewrite chans_of_union. simpl in Hfr. rewrite chans_of_union in Hfr. unfold erase. simpl.
      rewrite (cut_dual_chans ΣC ΣD) by (by destruct Hc). cc_set_solver. }
    destruct (ren_held_id _ _ _ Hgd Hgid) as (Hok & Hk & E1).
    assert (erase (q2'.1 ∪ q1.1 ∪ K, q2'.2 ∪ (emap (ev_ren ev) <$> M1)) =
      pconn (pmap (ev_ren ev) q1) (erase q2') K) as He.
    { unfold erase, pconn. simpl. unfold pmap in E1. simpl in E1. rewrite E1.
      rewrite soup_union; [|apply map_disjoint_dom; rewrite dom_fmap_L; apply map_disjoint_dom, Hd'].
      rewrite soup_fmap, HM1. f_equal; [cc_set_solver|apply (comm_L (⊎))]. }
    rewrite He.
    assert (conn Σ1 ΣC (pmap (ev_ren ev) q1).1 Σ2 ΣD (erase q2').1) as Hc'.
    { rewrite E1. apply (conn_C2 _ _ _ _ _ q2.1); [done| |].
      - unfold erase. simpl. cc_set_solver.
      - unfold erase. simpl. rewrite chans_of_union in Hfr. simpl in Hfr. cc_set_solver. }
    split.
    - intros Hc0. pose proof (A0 Hc0) as HX.
      pose proof (G2 (erase q2') (Σ2 ∪ ΣD) id ∅ Σ1 ΣC Σ2 ΣD (ev_ren ev) ∅ HX (fuse_ok_id _ _)) as HG.
      rewrite !sdrop_empty, !pfuse_empty, kren_id_map, pmap_id, Hk in HG.
      apply HG; [done|by apply pren_fuse_ok|done|done].
    - intros Hc0. apply (L (S n - ev_cost κ ev) ltac:(lia) Σ1 ΣC Σ2 ΣD); [apply HP1r; [done|done|lia]|by apply A1|done].
  Qed.

  Local Lemma at_cost_down c Σ T' p j : at_cost_P (S n) c (Prel κ) (λ W Σ T p, X1 W Σ T p ∨ X2 W Σ T p) W1 Σ T' p →
    j ≤ S n - c → Prel κ j W1 Σ T' p.
  Proof.
    intros [A0 A1] Hj. destruct (decide (c = 0)) as [->|Hcz].
    - destruct (A0 eq_refl) as [?|?]; eapply Prel_down; [|by apply X1P| |by apply X2P]; lia.
    - eapply Prel_down; [|by apply A1]. lia.
  Qed.

  Local Lemma at_cost_or1 c Σ T' p : at_cost_P (S n) c (Prel κ) X1 W1 Σ T' p →
    at_cost_P (S n) c (Prel κ) (λ W Σ T p, X1 W Σ T p ∨ X2 W Σ T p) W1 Σ T' p.
  Proof. intros [A0 A1]. split; [intros; left; by apply A0|done]. Qed.
  Local Lemma at_cost_or2 c Σ T' p : at_cost_P (S n) c (Prel κ) X2 W1 Σ T' p →
    at_cost_P (S n) c (Prel κ) (λ W Σ T p, X1 W Σ T p ∨ X2 W Σ T p) W1 Σ T' p.
  Proof. intros [A0 A1]. split; [intros; right; by apply A0|done]. Qed.

  Local Lemma lookup_cut o S x : (Σ1 ∪ ΣC) !! o = Some (S, x) → ech o ∈ K → ΣC !! o = Some (S, x).
  Proof.
    intros H Ho. destruct (lookup_union_cases _ _ _ _ H) as [H'|[_ H']]; [|done].
    exfalso. destruct Hc as [_ _ _ _ _ _ _ H1C _ _ _ _]. apply (H1C (ech o)); [|done].
    apply elem_of_chans_of. by eapply elem_of_dom_2.
  Qed.

  Local Lemma lookup_cut2 o S x : (Σ2 ∪ ΣD) !! o = Some (S, x) → ech o ∈ K → ΣD !! o = Some (S, x).
  Proof.
    intros H Ho. destruct (lookup_union_cases _ _ _ _ H) as [H'|[_ H']]; [|done].
    exfalso. destruct Hc as [_ _ _ _ _ _ _ _ H2C _ _ _]. apply (H2C (ech o)); [|done].
    apply elem_of_chans_of. by eapply elem_of_dom_2.
  Qed.

  Local Lemma chans_of_delete_pf (Σ : senv) o : pfree Σ → o ∈ dom Σ → chans_of (delete o Σ) = chans_of Σ ∖ {[ech o]}.
  Proof.
    intros Hf Ho. unfold chans_of. rewrite dom_delete_L. apply set_eq. intros c. rewrite elem_of_difference, !elem_of_map.
    split.
    - intros (o' & -> & Ho'). apply elem_of_difference in Ho' as [Ho1 Ho2]. split; [eauto|].
      intros He%elem_of_singleton. apply ech_eq in He as [->| ->]; [cc_set_solver|]. apply (Hf _ Ho). by rewrite edual_edual.
    - intros [(o' & -> & Ho') Hn]. exists o'. split; [done|]. apply elem_of_difference. split; [done|].
      intros ->%elem_of_singleton. by apply Hn, elem_of_singleton.
  Qed.

  Lemma conn_delete o :
    o ∈ dom ΣC → conn Σ1 (delete o ΣC) q1.1 Σ2 (delete (edual o) ΣD) q2.1 ∧
      chans_of (delete o ΣC) = K ∖ {[ech o]}.
  Proof.
    intros Ho. destruct Hc as [Hd1 Hd2 [Hcd Hct] Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (chans_of (delete o ΣC) = K ∖ {[ech o]}) as HK by (by apply chans_of_delete_pf).
    split; [|done]. constructor.
    - by apply map_disjoint_delete_r.
    - by apply map_disjoint_delete_r.
    - split.
      + intros o'. rewrite !dom_delete_L, !elem_of_difference, Hcd, !elem_of_singleton.
        split; intros [? Hn]; split; try done; intros E; apply Hn; [by rewrite <-E, edual_edual|by rewrite E, edual_edual].
      + intros o' S x Hl. apply lookup_delete_Some in Hl as [Hne Hl]. destruct (Hct _ _ _ Hl) as (S' & ? & ?).
        exists S'. split; [|done]. rewrite lookup_delete_ne; [done|]. intros E. by apply Hne, edual_inj.
    - done.
    - done.
    - intros o' Ho'. rewrite !dom_delete_L in Ho' |- *. cc_set_solver.
    - done.
    - rewrite HK. clear -H1C H2C HC1 HC2. cc_set_solver.
    - rewrite HK. clear -H1C H2C HC1 HC2. cc_set_solver.
    - done.
    - rewrite HK. clear -H1C H2C HC1 HC2. cc_set_solver.
    - rewrite HK. clear -H1C H2C HC1 HC2. cc_set_solver.
  Qed.

  (** A close across the cut. *)
  Lemma tau_close M1 M2 i j o e e' f f' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    M1 !! i = Some e → M2 !! j = Some f →
    tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose (edual o))) f' → ech o ∈ q1.1 ∪ q2.1 ∪ K →
    at_cost_P (S n) (c_give κ + c_take κ) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o]}, <[j := f']> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi Hj He Hf HoC.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    destruct H1 as (_ & _ & (_ & _ & _ & S1c & _)). destruct H2 as (_ & _ & (_ & _ & _ & S2c & _)).
    assert (istep (q1.1, M1) (EvSess i (SClose o)) (q1.1 ∖ sentc (SClose o), <[i := e']> M1) → ech o ∉ q1.1 →
      ∃ S0 x, (Σ1 ∪ ΣC) !! o = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
        at_cost_P (S n) (c_give κ) (Prel κ) X1 W1 (delete o (Σ1 ∪ ΣC)) T (erase (q1.1 ∖ sentc (SClose o), <[i := e']> M1))) as C1.
    { intros Hs _. exact (S1c _ _ _ _ (Hq1e M1 HM1) Hs). }
    assert (istep (q2.1, M2) (EvSess j (SClose (edual o))) (q2.1 ∖ sentc (SClose (edual o)), <[j := f']> M2) →
      ∃ S0 x, (Σ2 ∪ ΣD) !! edual o = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
        at_cost_P (S n) (c_give κ) (Prel κ) X2 W1 (delete (edual o) (Σ2 ∪ ΣD)) TUnit (erase (q2.1 ∖ sentc (SClose (edual o)), <[j := f']> M2))) as C2.
    { intros Hs. exact (S2c _ _ _ _ (Hq2e M2 HM2) Hs). }
    assert (ech o ∉ q1.1) as Hn1.
    { intros Ho. destruct C2 as (S0 & x & Hl & _).
      { eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; cc_set_solver]. }
      apply (HC1 (ech o) Ho). apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, HKD, ech_edual in Hl. cc_set_solver. }
    assert (ech o ∉ q2.1) as Hn2.
    { intros Ho. destruct C1 as (S0 & x & Hl & _); [eapply p_act_session; [exact Hi|exact He|simpl; cc_set_solver]|done|].
      apply (HC2 (ech o) Ho). apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union in Hl. cc_set_solver. }
    assert (ech o ∈ K) as HoK by cc_set_solver.
    destruct C1 as (S0 & x & L1 & U1 & A1); [eapply p_act_session; [exact Hi|exact He|simpl; cc_set_solver]|done|].
    destruct C2 as (S0' & x' & L2 & U2 & A2); [eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; cc_set_solver]|].
    unfold erase in A1, A2. simpl in A1, A2. rewrite difference_empty_L in A1, A2.
    apply lookup_cut in L1; [|done]. apply lookup_cut2 in L2; [|by rewrite ech_edual].
    assert (o ∈ dom ΣC) as HoC' by (by eapply elem_of_dom_2).
    destruct (conn_delete o HoC') as [Hc' HK'].
    assert (delete o (Σ1 ∪ ΣC) = Σ1 ∪ delete o ΣC) as E1.
    { rewrite delete_union, (delete_id Σ1); [done|]. apply eq_None_not_Some. intros [? ?].
      eapply (disj_lookup Σ1 ΣC); [done|eassumption|done]. }
    assert (delete (edual o) (Σ2 ∪ ΣD) = Σ2 ∪ delete (edual o) ΣD) as E2.
    { rewrite delete_union, (delete_id Σ2); [done|]. apply eq_None_not_Some. intros [? ?].
      eapply (disj_lookup Σ2 ΣD); [done|eassumption|done]. }
    rewrite E1 in A1. rewrite E2 in A2.
    assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o]}, <[j := f']> (<[i := e']> (M1 ∪ M2))) =
      pconn (q1.1, soup (<[i := e']> M1)) (q2.1, soup (<[j := f']> M2)) (chans_of (delete o ΣC))) as Ee.
    { assert (M2 !! i = None) as Hi2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      assert (M1 !! j = None) as Hj1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      unfold erase, pconn. simpl. rewrite HK'. f_equal; [cc_set_solver|].
      rewrite insert_union_l, insert_union_r by (by rewrite lookup_insert_ne by (intros ->; congruence)).
      rewrite soup_union; [done|]. apply map_disjoint_insert_l. split; [by rewrite lookup_insert_ne by (intros ->; congruence)|].
      apply map_disjoint_insert_r. split; [done|done]. }
    rewrite Ee. split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _.
    apply (L (S n - (c_give κ + c_take κ)) ltac:(pose proof (c_take_pos κ) as Ht; lia) Σ1 (delete o ΣC) Σ2 (delete (edual o) ΣD)).
    - eapply at_cost_down; [apply at_cost_or1, A1|lia].
    - eapply at_cost_down; [apply at_cost_or2, A2|lia].
    - done.
  Qed.

  Lemma conn_update o S y S' :
    o ∈ dom ΣC → sdual S S' →
    conn Σ1 (<[o := (S, y)]> ΣC) q1.1 Σ2 (<[edual o := (S', y‾)]> ΣD) q2.1 ∧
      chans_of (<[o := (S, y)]> ΣC) = K.
  Proof.
    intros Ho Hs. destruct Hc as [Hd1 Hd2 [Hcd Hct] Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (edual o ∈ dom ΣD) as Ho' by (apply Hcd; by rewrite edual_edual).
    assert (chans_of (<[o := (S, y)]> ΣC) = K) as HK.
    { unfold chans_of. rewrite dom_insert_L. clear -Ho. cc_set_solver. }
    split; [|done]. constructor.
    - apply map_disjoint_insert_r. split; [|done]. apply eq_None_not_Some. intros [? ?].
      apply elem_of_dom in Ho as [? ?]. eapply (disj_lookup Σ1 ΣC); eassumption.
    - apply map_disjoint_insert_r. split; [|done]. apply eq_None_not_Some. intros [? ?].
      apply elem_of_dom in Ho' as [? ?]. eapply (disj_lookup Σ2 ΣD); eassumption.
    - split.
      + intros o'. rewrite !dom_insert_L, !elem_of_union, !elem_of_singleton, Hcd.
        split; intros [E|E]; try (right; done); left; [rewrite E; by rewrite edual_edual|by rewrite <-E, edual_edual].
      + intros o' S0 x0 Hl. destruct (decide (o' = o)) as [->|Hne].
        * rewrite lookup_insert_eq in Hl. injection Hl as <- <-. exists S'. by rewrite lookup_insert_eq.
        * rewrite lookup_insert_ne in Hl by done. destruct (Hct _ _ _ Hl) as (S1 & ? & ?).
          exists S1. rewrite lookup_insert_ne; [done|]. intros E. by apply Hne, edual_inj.
    - done.
    - done.
    - intros o' Ho1. rewrite dom_insert_L in Ho1 |- *. apply elem_of_union in Ho1 as [Ho1%elem_of_singleton|Ho1].
      + subst. intros [E|E]%elem_of_union.
        * apply elem_of_singleton in E. by apply (edual_ne o).
        * by apply (HfC _ Ho).
      + intros [E|E]%elem_of_union; [|by apply (HfC _ Ho1)].
        apply elem_of_singleton in E. apply (HfC _ Ho). rewrite <-E, edual_edual. done.
    - done.
    - by rewrite HK.
    - by rewrite HK.
    - done.
    - by rewrite HK.
    - by rewrite HK.
  Qed.

  (** A choice across the cut, p1 selecting. *)
  Lemma tau_choice12 M1 M2 i j o b e e' f f' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    M1 !! i = Some e → M2 !! j = Some f →
    tstep e (LSess (SSel o b)) e' → tstep f (LSess (SBra (edual o) b)) f' →
    at_cost_P (S n) (c_give κ + c_take κ) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T
      (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi Hj He Hf.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    destruct H1 as (_ & _ & (_ & _ & _ & _ & S1c & _)). destruct H2 as (_ & _ & (_ & _ & _ & _ & _ & S2c & _)).
    assert (ech o ∉ q1.1 → ∃ S0 x S1 S2, (Σ1 ∪ ΣC) !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
        at_cost_P (S n) (c_give κ) (Prel κ) X1 W1 (<[o := (bsel b S1 S2, sel_pt x b)]> (Σ1 ∪ ΣC)) T
          (erase (q1.1 ∖ sentc (SSel o b), <[i := e']> M1))) as C1.
    { intros Hn. eapply (S1c _ _ _ _ _ (Hq1e M1 HM1)). eapply p_act_session; [exact Hi|exact He|simpl; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q2.1 → ∃ S0 x S1 S2, (Σ2 ∪ ΣD) !! edual o = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
        at_cost_P (S n) (c_take κ) (Prel κ) X2 W1 (<[edual o := (bsel b S1 S2, bra_pt x b)]> (Σ2 ∪ ΣD)) TUnit
          (erase (q2.1 ∖ sentc (SBra (edual o) b), <[j := f']> M2))) as C2.
    { intros Hn. eapply (S2c _ _ _ _ _ (Hq2e M2 HM2)). eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q1.1) as Hn1.
    { intros Ho. destruct C2 as (S0 & x & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, HKD, ech_edual in Hl.
      clear -Ho Hl HC1. cc_set_solver. }
    assert (ech o ∉ q2.1) as Hn2.
    { intros Ho. destruct C1 as (S0 & x & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union in Hl. clear -Ho Hl HC2. cc_set_solver. }
    destruct C1 as (S0 & x & S1 & S2 & L1 & U1 & A1); [done|].
    destruct C2 as (S0' & x' & S1' & S2' & L2 & U2 & A2); [done|].
    assert (ech o ∈ K) as HoK.
    { destruct (lookup_union_cases _ _ _ _ L1) as [Lc|[_ Lc]]; [|by apply elem_of_dom_2, elem_of_chans_of in Lc].
      exfalso. apply elem_of_dom_2, elem_of_chans_of in Lc. apply elem_of_dom_2, elem_of_chans_of in L2.
      rewrite chans_of_union, HKD, ech_edual in L2. clear -Lc L2 H12 H1C. cc_set_solver. }
    apply lookup_cut in L1; [|done]. apply lookup_cut2 in L2; [|by rewrite ech_edual].
    destruct (proj2 Hcut _ _ _ L1) as (S0'' & L2' & Hdu). rewrite L2 in L2'. injection L2' as -> ->.
    destruct (sdual_plus _ _ _ _ Hdu U1) as (T1 & T2 & U2' & D1 & D2). rewrite U2 in U2'. injection U2' as -> ->.
    assert (o ∈ dom ΣC) as HoC' by (by eapply elem_of_dom_2).
    destruct (conn_update o (bsel b S1 S2) (sel_pt x b) (bsel b T1 T2) HoC' (sdual_bsel b _ _ _ _ D1 D2)) as [Hc' HK'].
    rewrite sel_bra_pt in Hc'.
    unfold erase in A1, A2. simpl in A1, A2. rewrite difference_empty_L in A1, A2.
    rewrite insert_union_r in A1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup Σ1 ΣC); eassumption).
    rewrite insert_union_r in A2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup Σ2 ΣD); eassumption).
    assert (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2))) =
      pconn (q1.1, soup (<[i := e']> M1)) (q2.1, soup (<[j := f']> M2)) (chans_of (<[o := (bsel b S1 S2, sel_pt x b)]> ΣC))) as Ee.
    { assert (M2 !! i = None) as Hi2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      assert (M1 !! j = None) as Hj1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      unfold erase, pconn. simpl. rewrite HK'. f_equal.
      rewrite insert_union_l, insert_union_r by (by rewrite lookup_insert_ne by (intros ->; congruence)).
      rewrite soup_union; [done|]. apply map_disjoint_insert_l. split; [by rewrite lookup_insert_ne by (intros ->; congruence)|].
      apply map_disjoint_insert_r. split; [done|done]. }
    rewrite Ee. split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _.
    apply (L (S n - (c_give κ + c_take κ)) ltac:(pose proof (c_take_pos κ) as Ht; lia) Σ1 (<[o := (bsel b S1 S2, sel_pt x b)]> ΣC) Σ2 (<[edual o := (bsel b T1 T2, bra_pt (x‾) b)]> ΣD)); [| |exact Hc'].
    - eapply at_cost_down; [apply at_cost_or1, A1|lia].
    - eapply at_cost_down; [apply at_cost_or2, A2|lia].
  Qed.
  (** A choice across the cut, p2 selecting. *)
  Lemma tau_choice21 M1 M2 i j o b e e' f f' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    M2 !! i = Some e → M1 !! j = Some f →
    tstep e (LSess (SSel o b)) e' → tstep f (LSess (SBra (edual o) b)) f' →
    at_cost_P (S n) (c_give κ + c_take κ) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T
      (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi Hj He Hf.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    destruct H1 as (_ & _ & (_ & _ & _ & _ & _ & S1c & _)). destruct H2 as (_ & _ & (_ & _ & _ & _ & S2c & _)).
    assert (ech o ∉ q2.1 → ∃ S0 x S1 S2, (Σ2 ∪ ΣD) !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
        at_cost_P (S n) (c_give κ) (Prel κ) X2 W1 (<[o := (bsel b S1 S2, sel_pt x b)]> (Σ2 ∪ ΣD)) TUnit
          (erase (q2.1 ∖ sentc (SSel o b), <[i := e']> M2))) as C2.
    { intros Hn. eapply (S2c _ _ _ _ _ (Hq2e M2 HM2)). eapply p_act_session; [exact Hi|exact He|simpl; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q1.1 → ∃ S0 x S1 S2, (Σ1 ∪ ΣC) !! edual o = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
        at_cost_P (S n) (c_take κ) (Prel κ) X1 W1 (<[edual o := (bsel b S1 S2, bra_pt x b)]> (Σ1 ∪ ΣC)) T
          (erase (q1.1 ∖ sentc (SBra (edual o) b), <[j := f']> M1))) as C1.
    { intros Hn. eapply (S1c _ _ _ _ _ (Hq1e M1 HM1)). eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q1.1) as Hn1.
    { intros Ho. destruct C2 as (S0 & x & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, HKD in Hl.
      clear -Ho Hl HC1. cc_set_solver. }
    assert (ech o ∉ q2.1) as Hn2.
    { intros Ho. destruct C1 as (S0 & x & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, ech_edual in Hl. clear -Ho Hl HC2. cc_set_solver. }
    destruct C2 as (S0 & x & S1 & S2 & L2 & U2 & A2); [done|].
    destruct C1 as (S0' & x' & S1' & S2' & L1 & U1 & A1); [done|].
    assert (ech o ∈ K) as HoK.
    { destruct (lookup_union_cases _ _ _ _ L1) as [Lc|[_ Lc]]; [|by apply elem_of_dom_2, elem_of_chans_of in Lc; rewrite ech_edual in Lc].
      exfalso. apply elem_of_dom_2, elem_of_chans_of in Lc. apply elem_of_dom_2, elem_of_chans_of in L2.
      rewrite ech_edual in Lc. rewrite chans_of_union, HKD in L2. clear -Lc L2 H12 H1C. cc_set_solver. }
    apply lookup_cut in L1; [|by rewrite ech_edual]. apply lookup_cut2 in L2; [|done].
    destruct (proj2 Hcut _ _ _ L1) as (S0'' & L2' & Hdu). rewrite edual_edual, L2 in L2'. injection L2' as -> ->.
    destruct (sdual_with _ _ _ _ Hdu U1) as (T1 & T2 & U2' & D1 & D2). rewrite U2 in U2'. injection U2' as <- <-.
    assert (edual o ∈ dom ΣC) as HoC' by (by eapply elem_of_dom_2).
    destruct (conn_update (edual o) (bsel b S1' S2') (bra_pt x' b) (bsel b S1 S2) HoC' (sdual_bsel b _ _ _ _ D1 D2)) as [Hc' HK'].
    rewrite bra_sel_pt, edual_edual in Hc'.
    unfold erase in A1, A2. simpl in A1, A2. rewrite difference_empty_L in A1, A2.
    rewrite insert_union_r in A1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup Σ1 ΣC); eassumption).
    rewrite insert_union_r in A2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup Σ2 ΣD); eassumption).
    assert (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2))) =
      pconn (q1.1, soup (<[j := f']> M1)) (q2.1, soup (<[i := e']> M2)) (chans_of (<[edual o := (bsel b S1' S2', bra_pt x' b)]> ΣC))) as Ee.
    { assert (M1 !! i = None) as Hi1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      assert (M2 !! j = None) as Hj2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
      unfold erase, pconn. simpl. rewrite HK'. f_equal.
      rewrite insert_union_r, insert_union_l by (by rewrite ?lookup_insert_ne by (intros ->; congruence)).
      rewrite soup_union; [done|]. apply map_disjoint_insert_l. split; [by rewrite lookup_insert_ne by (intros ->; congruence)|].
      apply map_disjoint_insert_r. split; [done|done]. }
    rewrite Ee. split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _.
    apply (L (S n - (c_give κ + c_take κ)) ltac:(pose proof (c_take_pos κ) as Ht; lia) Σ1 (<[edual o := (bsel b S1' S2', bra_pt x' b)]> ΣC) Σ2 (<[o := (bsel b S1 S2, sel_pt (x'‾) b)]> ΣD)); [| |exact Hc'].
    - eapply at_cost_down; [apply at_cost_or1, A1|lia].
    - eapply at_cost_down; [apply at_cost_or2, A2|lia].
  Qed.
End core.
