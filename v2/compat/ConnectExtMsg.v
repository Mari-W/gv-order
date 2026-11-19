(** * P-Connect, external messages of the composite (stage S4)

    Q-Send and Q-Recv of the composite. A send of a component can move
    cut ends, whose partners in the other component then join the
    interface. A receive can bring ends whose partners lie in the other
    component, and they become cut ends. Both re-split the cut by the
    composite's new interface (compat/ConnectSendEnv.v). *)

From GV Require Export compat.ConnectExt compat.ConnectSendEnv.
From GV Require Import fuel.FuelMono.

Section extmsg.
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
  Local Lemma side (M1 M2 : gmap nat expr) i e : (M1 ∪ M2) !! i = Some e → M1 !! i = Some e ∨ M2 !! i = Some e.
  Proof. intros [H|[_ H]]%lookup_union_Some_raw; auto. Qed.

  Local Lemma iface1 o v : (Σ1 ∪ ΣC) !! o = Some v → ech o ∉ K → Σ1 !! o = Some v ∧ o ∈ dom Σ1.
  Proof.
    intros H Hn. destruct (lookup_1C _ _ _ _ H) as [[A B]|[A B]]; [done|]. exfalso. apply Hn. by apply elem_of_chans_of.
  Qed.

  Local Lemma iface2 o v : (Σ2 ∪ ΣD) !! o = Some v → ech o ∉ K → Σ2 !! o = Some v ∧ o ∈ dom Σ2.
  Proof.
    intros H Hn. destruct (lookup_1C _ _ _ _ H) as [[A B]|[A B]]; [done|]. exfalso. apply Hn.
    rewrite <-(cut_dual_chans ΣC ΣD) by (by destruct Hc). by apply elem_of_chans_of.
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
  Local Lemma lk12 o v : Σ1 !! o = Some v → (Σ1 ∪ Σ2) !! o = Some v.
  Proof. apply lookup_union_Some_l. Qed.

  Local Lemma HΣ12 : Σ1 ∪ Σ2 = Σ2 ∪ Σ1.
  Proof. apply map_union_comm, chans_disj_map. by destruct Hc. Qed.

  Local Lemma HKD : chans_of ΣD = K.
  Proof. apply cut_dual_chans. by destruct Hc. Qed.

  Local Lemma HP1id j : j ≤ S n → Prel κ j W1 (Σ1 ∪ ΣC) T q1.
  Proof.
    intros Hj. pose proof (HP1 id ∅ (fuse_ok_id _ _)) as P. rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in P.
    eapply Prel_down; [|exact P]. lia.
  Qed.
  Local Lemma HP2id j : j ≤ S n → Prel κ j W1 (Σ2 ∪ ΣD) TUnit q2.
  Proof.
    intros Hj. pose proof (HP2 id ∅ (fuse_ok_id _ _)) as P. rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in P.
    eapply Prel_down; [|exact P]. lia.
  Qed.

  (** A step of p1 after which the cut is re-split. *)
  Lemma ext_comp1' c E1 Σ1' ΣC' Σ2' ΣD' p1' :
    at_cost_P (S n) c (Prel κ) X1 W1 E1 T p1' → E1 = Σ1' ∪ ΣC' → Σ2 ∪ ΣD = Σ2' ∪ ΣD' →
    conn Σ1' ΣC' p1'.1 Σ2' ΣD' q2.1 →
    at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W1 (Σ1' ∪ Σ2') T (pconn p1' q2 (chans_of ΣC')).
  Proof.
    intros [A0 A1] -> E2 Hc'. split.
    - intros Hz. pose proof (G1 p1' _ id ∅ Σ1' ΣC' Σ2' ΣD' q2 (A0 Hz) (fuse_ok_id _ _)) as HG.
      rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in HG. apply HG; [done| |done].
      rewrite <-E2. by apply HP2id.
    - intros Hz. apply (L (S n - c) ltac:(lia) Σ1' ΣC' Σ2' ΣD'); [by apply A1| |done].
      rewrite <-E2. apply HP2id. lia.
  Qed.

  (** A step of p2 after which the cut is re-split. *)
  Lemma ext_comp2' c E2 Σ1' ΣC' Σ2' ΣD' p2' :
    at_cost_P (S n) c (Prel κ) X2 W1 E2 TUnit p2' → E2 = Σ2' ∪ ΣD' → Σ1 ∪ ΣC = Σ1' ∪ ΣC' →
    conn Σ1' ΣC' q1.1 Σ2' ΣD' p2'.1 →
    at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W1 (Σ1' ∪ Σ2') T (pconn q1 p2' (chans_of ΣC')).
  Proof.
    intros [A0 A1] -> E1 Hc'. split.
    - intros Hz. pose proof (G2 p2' _ id ∅ Σ1' ΣC' Σ2' ΣD' id ∅ (A0 Hz) (fuse_ok_id _ _)) as HG.
      rewrite !sdrop_empty, !kren_id_map, !pfuse_empty, !pmap_id in HG.
      apply HG; [done|apply fuse_ok_id|by rewrite E1|done].
    - intros Hz. apply (L (S n - c) ltac:(lia) Σ1' ΣC' Σ2' ΣD'); [|by apply A1|done].
      rewrite <-E1. apply HP1id. lia.
  Qed.

  (** Q-Send of the composite. *)
  Lemma ext_send q i o w q' : erase q = pc → istep q (EvOffer i (SSend o w)) q' →
    q_send κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T pc o w (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      simpl in Hsub; assert (ech o ∉ K) as HnK by (clear -Hsub; cc_set_solver); rewrite Eq.
    - destruct H1 as (_ & _ & (_ & S1 & _)).
      destruct (S1 _ _ _ _ _ (Hq1e M1 HM1) Hs) as (S0 & x & m & U & b & Sc & Σv1 & Σr1 & Θe1 & Σe1 & Lo & Uo & Dvr & Edel & HΘ1 & Hss & AV & AP).
      assert (fends w = dom Σv1 ∪ dom Θe1) as HM
        by (rewrite <-dom_union_L; symmetry; exact (at_cost_V_exact κ _ _ _ _ _ _ _ AV)).
      destruct (iface1 _ _ Lo HnK) as [Lo' Do].
      assert (∀ o', o' ∈ dom Θe1 → ech o' ∈ q1.1) as HΘe by (intros o' Ho'; by apply HΘ1).
      destruct (snd_moved Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺) (fends w) HΘ1 HM) as [HΘ HM'].
      pose proof (snd_conn Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hc'.
      pose proof (snd_iface Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hif.
      pose proof (snd_chans Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hch.
      eexists S0, x, m, U, b, Sc, _, _, _, _. split_and!.
      + by apply lk12.
      + done.
      + apply (snd_vr Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + apply (snd_del Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + exact HΘ.
      + apply (snd_split Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + rewrite (snd_payload Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)). exact AV.
      + simpl in AP |- *. unfold fchans in AP |- *. rewrite HM in AP. rewrite <-Hif.
        set (E1 := <[o := (Sc, x⁺)]> (Σr1 ∪ Σe1)) in *.
        match type of Hif with _ = ?S => set (Σ' := S) in * end.
        pose proof (ext_comp1' _ _ _ _ _ _ _ AP (eq_sym (fin_fout Σ' E1)) (eq_sym (fin_fout Σ' (Σ2 ∪ ΣD)))) as R.
        unfold erase in R at 2. simpl in R. specialize (R Hc').
        refine (eq_rect _ (λ p, at_cost_P (S n) (c_give κ) (Prel κ) (Prel κ (S n)) W1 _ T p) R _ _).
        unfold pconn, erase. simpl. unfold fchans. rewrite HM, Hch. f_equal.
    - rewrite HΣ12. pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs.
      destruct H2 as (_ & _ & (_ & S2 & _)).
      destruct (S2 _ _ _ _ _ (Hq2e M2 HM2) Hs) as (S0 & x & m & U & b & Sc & Σv1 & Σr1 & Θe1 & Σe1 & Lo & Uo & Dvr & Edel & HΘ1 & Hss & AV & AP).
      assert (fends w = dom Σv1 ∪ dom Θe1) as HM
        by (rewrite <-dom_union_L; symmetry; exact (at_cost_V_exact κ _ _ _ _ _ _ _ AV)).
      destruct (iface2 _ _ Lo HnK) as [Lo' Do].
      assert (∀ o', o' ∈ dom Θe1 → ech o' ∈ q2.1) as HΘe by (intros o' Ho'; by apply HΘ1).
      destruct (snd_moved Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺) (fends w) HΘ1 HM) as [HΘ HM'].
      pose proof (snd_conn Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hc'.
      pose proof (snd_iface Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hif.
      pose proof (snd_chans Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)) as Hch.
      eexists S0, x, m, U, b, Sc, _, _, _, _. split_and!.
      + by apply lookup_union_Some_l.
      + done.
      + apply (snd_vr Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + apply (snd_del Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + intros o'. rewrite (HΘ o'). simpl. rewrite HKD. clear. cc_set_solver.
      + apply (snd_split Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)).
      + rewrite (snd_payload Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o Do Σv1 Σr1 Θe1 Σe1 Dvr Edel HΘe Hss (Sc, x⁺)). exact AV.
      + simpl in AP |- *. unfold fchans in AP |- *. rewrite HM in AP. rewrite <-Hif.
        set (E2 := <[o := (Sc, x⁺)]> (Σr1 ∪ Σe1)) in *.
        match type of Hif with _ = ?S => set (Σ' := S) in * end.
        pose proof (conn_sym _ _ _ _ _ _ Hc') as Hc''.
        pose proof Hc' as Hc3. destruct Hc3 as [_ _ Hcut3 _ _ _ H123 _ _ _ _ _].
        pose proof (cut_dual_chans _ _ Hcut3) as Hch'.
        pose proof (ext_comp2' _ _ _ _ _ _ _ AP (eq_sym (fin_fout Σ' E2)) (eq_sym (fin_fout Σ' (Σ1 ∪ ΣC)))) as R.
        unfold erase in R at 2. simpl in R. specialize (R Hc'').
        rewrite map_union_comm by (apply chans_disj_map; clear -H123; cc_set_solver).
        refine (eq_rect _ (λ p, at_cost_P (S n) (c_give κ) (Prel κ) (Prel κ (S n)) W1 _ T p) R _ _).
        unfold pconn, erase. simpl. unfold fchans. rewrite HM, Hch'. f_equal.
        rewrite <-HKD. assert (q1.1 ∪ q2.1 ∪ chans_of ΣD = q2.1 ∪ q1.1 ∪ chans_of ΣD) as -> by (clear; cc_set_solver).
        rewrite Hch. clear. cc_set_solver.
  Qed.

  (** Q-Recv of the composite. *)
  Lemma ext_recv q i o w q' : erase q = pc → istep q (EvOffer i (SRecv o w)) q' →
    q_recv κ (S n) (Vrel κ) (Prel κ) W1 (Σ1 ∪ Σ2) T pc o w (erase q').
  Proof.
    intros Hq Hst. destruct (ext_split _ _ _ _ Hq Hst) as (M1 & M2 & e & e' & Hd & HM1 & HM2 & He & Hsub & [(Hi & Hs & Eq)|(Hi & Hs & Eq)]);
      simpl in Hsub; assert (ech o ∉ K) as HnK by (clear -Hsub; cc_set_solver); rewrite Eq.
    - destruct H1 as (_ & _ & (_ & _ & R1 & _)).
      destruct (R1 _ _ _ _ _ (Hq1e M1 HM1) Hs) as (S0 & x & m & U & b & Sc & Lo & Uo & AR).
      destruct (iface1 _ _ Lo HnK) as [Lo' Do].
      exists S0, x, m, U, b, Sc. split_and!; [by apply lk12|done|]. intros j Θ2 Hj Hdj Hok HV.
      pose proof (c_take_pos κ) as Ht.
      pose proof (conn_retype1 _ _ _ _ _ _ o (Sc, x⁺) Hc Do) as Hc1.
      rewrite insert_union_l in Hok |- *. rewrite insert_union_l in AR.
      assert (set_map ech (dom Θ2) ## q1.1 ∪ q2.1 ∪ chans_of ΣC) as HΘ by exact Hdj.
      pose proof (rcv_ok1 _ ΣC Σ2 ΣD q1.1 q2.1 Hc1 Θ2 HΘ Hok) as Hok1.
      pose proof (AR j Θ2 Hj ltac:(clear -HΘ; cc_set_solver) Hok1 HV) as P1.
      pose proof (rcv_conn _ ΣC Σ2 ΣD q1.1 q2.1 Hc1 Θ2 HΘ Hok) as Hc'.
      pose proof (rcv_iface _ ΣC Σ2 ΣD q1.1 q2.1 Hc1 Θ2 HΘ Hok) as Hif.
      pose proof (rcv_chans _ ΣC Σ2 ΣD q1.1 q2.1 Hc1 Θ2 HΘ Hok) as Hch.
      match type of Hif with _ = ?S => set (Σ' := S) in * end.
      set (E1 := recv_env (<[o := (Sc, x⁺)]> Σ1 ∪ ΣC) Θ2) in *.
      unfold erase in P1. simpl in P1. rewrite difference_empty_L in P1.
      rewrite <-(fin_fout Σ' E1) in P1.
      pose proof (HP2id j ltac:(lia)) as P2. rewrite <-(fin_fout Σ' (Σ2 ∪ ΣD)) in P2.
      pose proof (L j ltac:(lia) _ _ _ _ _ _ P1 P2 Hc') as HL. rewrite Hif in HL.
      refine (eq_rect _ (λ p, Prel κ j W1 Σ' T p) HL _ _).
      unfold pconn, erase. simpl. rewrite !difference_empty_L. f_equal. rewrite <-Hch. done.
    - rewrite HΣ12. pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs.
      destruct H2 as (_ & _ & (_ & _ & R2 & _)).
      destruct (R2 _ _ _ _ _ (Hq2e M2 HM2) Hs) as (S0 & x & m & U & b & Sc & Lo & Uo & AR).
      destruct (iface2 _ _ Lo HnK) as [Lo' Do].
      exists S0, x, m, U, b, Sc. split_and!; [by apply lookup_union_Some_l|done|]. intros j Θ2 Hj Hdj Hok HV.
      pose proof (c_take_pos κ) as Ht.
      pose proof (conn_retype1 _ _ _ _ _ _ o (Sc, x⁺) Hcs Do) as Hc1.
      rewrite insert_union_l in Hok |- *. rewrite insert_union_l in AR.
      assert (set_map ech (dom Θ2) ## q2.1 ∪ q1.1 ∪ chans_of ΣD) as HΘ.
      { rewrite HKD. simpl in Hdj. clear -Hdj. cc_set_solver. }
      pose proof (rcv_ok1 _ ΣD Σ1 ΣC q2.1 q1.1 Hc1 Θ2 HΘ Hok) as Hok1.
      pose proof (AR j Θ2 Hj ltac:(clear -HΘ; cc_set_solver) Hok1 HV) as P2.
      pose proof (rcv_conn _ ΣD Σ1 ΣC q2.1 q1.1 Hc1 Θ2 HΘ Hok) as Hc'.
      pose proof (rcv_iface _ ΣD Σ1 ΣC q2.1 q1.1 Hc1 Θ2 HΘ Hok) as Hif.
      pose proof (rcv_chans _ ΣD Σ1 ΣC q2.1 q1.1 Hc1 Θ2 HΘ Hok) as Hch.
      match type of Hif with _ = ?S => set (Σ' := S) in * end.
      set (E2 := recv_env (<[o := (Sc, x⁺)]> Σ2 ∪ ΣD) Θ2) in *.
      pose proof (conn_sym _ _ _ _ _ _ Hc') as Hc''.
      pose proof Hc' as Hc3. destruct Hc3 as [_ _ Hcut3 _ _ _ H123 _ _ _ _ _].
      pose proof (cut_dual_chans _ _ Hcut3) as Hch'.
      unfold erase in P2. simpl in P2. rewrite difference_empty_L in P2.
      rewrite <-(fin_fout Σ' E2) in P2.
      pose proof (HP1id j ltac:(lia)) as P1. rewrite <-(fin_fout Σ' (Σ1 ∪ ΣC)) in P1.
      pose proof (L j ltac:(lia) _ _ _ _ _ _ P1 P2 Hc'') as HL.
      rewrite map_union_comm in HL by (apply chans_disj_map; clear -H123; cc_set_solver).
      rewrite Hif in HL.
      refine (eq_rect _ (λ p, Prel κ j W1 Σ' T p) HL _ _).
      unfold pconn, erase. simpl. rewrite !difference_empty_L, Hch'. f_equal.
      rewrite <-HKD. assert (q1.1 ∪ q2.1 ∪ chans_of ΣD = q2.1 ∪ q1.1 ∪ chans_of ΣD) as -> by (clear; cc_set_solver).
      rewrite Hch. clear. cc_set_solver.
  Qed.

  (** The clauses of P for the composite. *)
  Lemma pc_clauses : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T pc.
  Proof.
    split_and!.
    - intros Hi. exact (pc_stop κ n W1 HS T TUnit X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2 HT tfree_unit eq_refl Hi).
    - intros _. exact (pc_ready κ n W1 HS T TUnit X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2 HT tfree_unit eq_refl).
    - split_and!.
      + intros q ev q' Hq Hst Hτ Hfr. eapply tau_all; eassumption.
      + intros q i o w q' Hq Hst. by eapply ext_send.
      + intros q i o w q' Hq Hst. by eapply ext_recv.
      + intros q i o q' Hq Hst. eapply ext_close; eassumption.
      + intros q i o b q' Hq Hst. eapply ext_select; eassumption.
      + intros q i o b q' Hq Hst. eapply ext_branch; eassumption.
      + intros q i os q' Hq Hst. eapply ext_link; eassumption.
  Qed.
End extmsg.
