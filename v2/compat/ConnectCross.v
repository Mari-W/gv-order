(** * P-Connect, messages across the cut (stage S4)

    The step clause of the composite for a message on a cut channel,
    over the clauses of the two components, in the context of
    compat/ConnectSteps.v. The cut is re-split by compat/ConnectMsg.v. *)

From GV Require Export compat.ConnectSteps compat.ConnectMsg.
From GV Require Import fuel.FuelMono compat.Blind.

Section cross.
  Context (κ : ctable) (n : Ix) (W1 : world) (T : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (CC : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Let HS := cc_HS CC. Let HT := cc_HT CC. Let Hc := cc_Hc CC.
  Let H1 := cc_H1 CC. Let H2 := cc_H2 CC. Let L := cc_L CC.
  Let X1P := cc_X1P CC. Let X2P := cc_X2P CC. Let HP1 := cc_HP1 CC. Let HP2 := cc_HP2 CC.
  Let G1 := cc_G1 CC. Let G2 := cc_G2 CC.
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma Hq1e' M1 : soup M1 = q1.2 → erase (q1.1, M1) = q1.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q1. Qed.
  Local Lemma Hq2e' M2 : soup M2 = q2.2 → erase (q2.1, M2) = q2.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q2. Qed.

  Local Lemma at_cost_lvl {X : prel} (XP : ∀ W Σ T p, X W Σ T p → Prel κ n W Σ T p) c Σ T' p j :
    at_cost_P n c (Prel κ) X W1 Σ T' p → ole (oadd j c) n → Prel κ j W1 Σ T' p.
  Proof.
    intros [A0 A1] Hj. destruct (decide (c = 0)) as [->|Hcz].
    - eapply Prel_down; [exact Hj|by apply XP, A0].
    - by apply A1.
  Qed.

  Local Lemma at_cost_V_lvl c Θ U v j :
    at_cost_V n c (Vrel κ) (Vrel κ n) W1 Θ U v → ole (oadd j c) n → Vrel κ j W1 Θ U v.
  Proof.
    intros [A0 A1] Hj. destruct (decide (c = 0)) as [->|Hcz].
    - eapply Vrel_down; [exact Hj|by apply A0].
    - apply A1; [done|exact (oadd_lt _ _ _ Hcz Hj)|by left].
  Qed.

  Local Lemma soup_two M1 M2 i j e' f' :
    M1 ##ₘ M2 → is_Some (M1 !! i) → is_Some (M2 !! j) →
    soup (<[j := f']> (<[i := e']> (M1 ∪ M2))) = soup (<[i := e']> M1) ⊎ soup (<[j := f']> M2).
  Proof.
    intros Hd [e Hi] [f Hj].
    assert (M2 !! i = None) as Hi2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    assert (M1 !! j = None) as Hj1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    rewrite insert_union_l, insert_union_r by (by rewrite lookup_insert_ne by (intros ->; congruence)).
    rewrite soup_union; [done|]. apply map_disjoint_insert_l. split; [by rewrite lookup_insert_ne by (intros ->; congruence)|].
    apply map_disjoint_insert_r. split; [done|done].
  Qed.

  (** A message across the cut, p1 sending. *)
  Lemma tau_msg12 M1 M2 i j o w e e' f f' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    M1 !! i = Some e → M2 !! j = Some f →
    tstep e (LSess (SSend o w)) e' → tstep f (LSess (SRecv (edual o) w)) f' →
    at_cost_P n (c_give κ + c_take κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi Hj He Hf.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    destruct H1 as (_ & _ & (_ & S1s & _)). destruct H2 as (_ & _ & (_ & _ & S2r & _)).
    assert (ech o ∉ q1.1 → ∃ S0 x m U Sc Σv Σr Θe Σe, (Σ1 ∪ ΣC) !! o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SSnd m U) Sc ∧ Σv ##ₘ Σr ∧ delete o (Σ1 ∪ ΣC) = Σv ∪ Σr ∧
        (∀ o', o' ∈ dom Θe ↔ o' ∈ (fends w) ∧ ech o' ∈ q1.1) ∧
        send_split (Σ1 ∪ ΣC) Σe Θe ∧
        at_cost_V n (c_give κ) (Vrel κ) (Vrel κ n) W1 (Σv ∪ Θe) (payload_at m U x) w ∧
        at_cost_P n (c_give κ) (Prel κ) X1 W1 (<[o := (Sc, x⁺)]> (Σr ∪ Σe)) T
          (erase (q1.1 ∖ sentc (SSend o w), <[i := e']> M1))) as C1.
    { intros Hn. eapply (S1s _ _ _ _ _ (Hq1e' M1 HM1)). eapply p_act_session; [exact Hi|exact He|simpl; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q2.1 → ∃ S0 x m U Sc, (Σ2 ∪ ΣD) !! edual o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SRcv m U) Sc ∧
        ∀ jl Θ2, ole (oadd jl (c_take κ)) n → set_map ech (dom Θ2) ## q2.1 →
          recv_ok (<[edual o := (Sc, x⁺)]> (Σ2 ∪ ΣD)) Θ2 → Vrel κ jl W1 Θ2 (payload_at m U x) w →
          Prel κ jl W1 (recv_env (<[edual o := (Sc, x⁺)]> (Σ2 ∪ ΣD)) Θ2) TUnit
            ((erase (q2.1 ∖ sentc (SRecv (edual o) w), <[j := f']> M2)).1 ∪ recv_back (<[edual o := (Sc, x⁺)]> (Σ2 ∪ ΣD)) Θ2,
             (erase (q2.1 ∖ sentc (SRecv (edual o) w), <[j := f']> M2)).2)) as C2.
    { intros Hn. eapply (S2r _ _ _ _ _ (Hq2e' M2 HM2)). eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q1.1) as Hn1.
    { intros Ho. destruct C2 as (S0 & x & ? & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, HKD, ech_edual in Hl.
      clear -Ho Hl HC1. cc_set_solver. }
    assert (ech o ∉ q2.1) as Hn2.
    { intros Ho. destruct C1 as (S0 & x & ? & ? & ? & ? & ? & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union in Hl. clear -Ho Hl HC2. cc_set_solver. }
    destruct C1 as (S0 & x & m & U & Sc & Σv & Σr & Θe & Σe & L1 & U1 & Dvr & Edel & HΘe & Hss & AV & AP); [done|].
    destruct C2 as (S0' & x' & m' & U' & Sc' & L2 & U2 & AR); [done|].
    assert (ech o ∈ K) as HoK.
    { destruct (lookup_union_cases _ _ _ _ L1) as [Lc|[_ Lc]]; [|by apply elem_of_dom_2, elem_of_chans_of in Lc].
      exfalso. apply elem_of_dom_2, elem_of_chans_of in Lc. apply elem_of_dom_2, elem_of_chans_of in L2.
      rewrite chans_of_union, HKD, ech_edual in L2. clear -Lc L2 H12 H1C. cc_set_solver. }
    assert (ΣC !! o = Some (S0, x)) as Lc.
    { destruct (lookup_union_cases _ _ _ _ L1) as [Lc|[_ Lc]]; [|done]. exfalso.
      apply elem_of_dom_2, elem_of_chans_of in Lc. clear -Lc HoK H1C. cc_set_solver. }
    assert (ΣD !! edual o = Some (S0', x')) as Ld.
    { destruct (lookup_union_cases _ _ _ _ L2) as [Ld|[_ Ld]]; [|done]. exfalso.
      apply elem_of_dom_2, elem_of_chans_of in Ld. rewrite ech_edual in Ld. clear -Ld HoK H2C. cc_set_solver. }
    destruct (proj2 Hcut _ _ _ Lc) as (S0'' & Ld' & Hdu). rewrite Ld in Ld'. injection Ld' as <- ->.
    destruct (sdual_snd _ _ _ _ _ Hdu U1) as (U'' & S'' & U2' & Hteq & HdS).
    rewrite U2 in U2'. injection U2' as -> <- <-.
    rewrite (pt_dual_shift 1 x) in AR.
    assert (∀ o', o' ∈ dom Θe → ech o' ∈ q1.1) as HΘe' by (intros o' Ho'; by apply HΘe).
    split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _ jj Hjj.
    destruct (oadd_le_part jj _ _ _ Hjj) as [Hjg Hjt].
    assert (Vrel κ jj W1 (Σv ∪ Θe) (payload_at m U' x‾) w) as HV.
    { rewrite payload_at_dual. apply (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x Hteq)).
      eapply at_cost_V_lvl; [exact AV|exact Hjg]. }
    pose proof (msg_recv_ok Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o S0 x Lc Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hok.
    pose proof (msg_recv_disj Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o S0 x Lc Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hdj.
    pose proof (AR jj (Σv ∪ Θe) Hjt Hdj Hok HV) as P2.
    unfold erase in P2. simpl in P2. rewrite difference_empty_L in P2.
    assert (Prel κ jj W1 (<[o := (Sc, x⁺)]> (Σr ∪ Σe)) T (erase (q1.1 ∖ set_map ech (dom Σv ∪ dom Θe), <[i := e']> M1))) as P1.
    { assert (fends w = dom Σv ∪ dom Θe) as HMv by (by rewrite <-(Vrel_exact κ _ _ _ _ _ HV), dom_union_L).
      simpl in AP. unfold fchans in AP. rewrite HMv in AP. eapply (at_cost_lvl X1P); [exact AP|exact Hjg]. }
    pose proof (msg_conn Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o S0 x Lc Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hc'.
    pose proof (msg_iface Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o S0 x Lc Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hif.
    pose proof (msg_chans Σ1 ΣC Σ2 ΣD q1.1 q2.1 Hc o S0 x Lc Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hch.
    rewrite <-(fin_fout (Σ1 ∪ Σ2) (<[o := (Sc, x⁺)]> (Σr ∪ Σe))) in P1.
    rewrite <-(fin_fout (Σ1 ∪ Σ2) (recv_env (<[edual o := (Sc', (x⁺)‾)]> (Σ2 ∪ ΣD)) (Σv ∪ Θe))) in P2.
    pose proof (L jj (sync_lt κ jj n Hjj) _ _ _ _ _ _ P1 P2 Hc') as HL.
    rewrite Hif in HL. refine (eq_rect _ (λ p, Prel κ jj W1 (Σ1 ∪ Σ2) T p) HL _ _).
    unfold pconn, erase. simpl. f_equal; [|symmetry; apply soup_two; eauto].
    rewrite Hch. clear. cc_set_solver.
  Qed.
  (** A message across the cut, p2 sending. *)
  Lemma tau_msg21 M1 M2 i j o w e e' f f' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    M2 !! i = Some e → M1 !! j = Some f →
    tstep e (LSess (SSend o w)) e' → tstep f (LSess (SRecv (edual o) w)) f' →
    at_cost_P n (c_give κ + c_take κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase (q1.1 ∪ q2.1 ∪ K, <[j := f']> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi Hj He Hf.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD. pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs.
    destruct H1 as (_ & _ & (_ & _ & S1r & _)). destruct H2 as (_ & _ & (_ & S2s & _)).
    assert (ech o ∉ q2.1 → ∃ S0 x m U Sc Σv Σr Θe Σe, (Σ2 ∪ ΣD) !! o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SSnd m U) Sc ∧ Σv ##ₘ Σr ∧ delete o (Σ2 ∪ ΣD) = Σv ∪ Σr ∧
        (∀ o', o' ∈ dom Θe ↔ o' ∈ (fends w) ∧ ech o' ∈ q2.1) ∧
        send_split (Σ2 ∪ ΣD) Σe Θe ∧
        at_cost_V n (c_give κ) (Vrel κ) (Vrel κ n) W1 (Σv ∪ Θe) (payload_at m U x) w ∧
        at_cost_P n (c_give κ) (Prel κ) X2 W1 (<[o := (Sc, x⁺)]> (Σr ∪ Σe)) TUnit
          (erase (q2.1 ∖ sentc (SSend o w), <[i := e']> M2))) as C2.
    { intros Hn. eapply (S2s _ _ _ _ _ (Hq2e' M2 HM2)). eapply p_act_session; [exact Hi|exact He|simpl; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q1.1 → ∃ S0 x m U Sc, (Σ1 ∪ ΣC) !! edual o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SRcv m U) Sc ∧
        ∀ jl Θ2, ole (oadd jl (c_take κ)) n → set_map ech (dom Θ2) ## q1.1 →
          recv_ok (<[edual o := (Sc, x⁺)]> (Σ1 ∪ ΣC)) Θ2 → Vrel κ jl W1 Θ2 (payload_at m U x) w →
          Prel κ jl W1 (recv_env (<[edual o := (Sc, x⁺)]> (Σ1 ∪ ΣC)) Θ2) T
            ((erase (q1.1 ∖ sentc (SRecv (edual o) w), <[j := f']> M1)).1 ∪ recv_back (<[edual o := (Sc, x⁺)]> (Σ1 ∪ ΣC)) Θ2,
             (erase (q1.1 ∖ sentc (SRecv (edual o) w), <[j := f']> M1)).2)) as C1.
    { intros Hn. eapply (S1r _ _ _ _ _ (Hq1e' M1 HM1)). eapply p_act_session; [exact Hj|exact Hf|simpl; rewrite ech_edual; clear -Hn; cc_set_solver]. }
    assert (ech o ∉ q2.1) as Hn2.
    { intros Ho. destruct C1 as (S0 & x & ? & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, ech_edual in Hl.
      clear -Ho Hl HC2. cc_set_solver. }
    assert (ech o ∉ q1.1) as Hn1.
    { intros Ho. destruct C2 as (S0 & x & ? & ? & ? & ? & ? & ? & ? & Hl & _); [clear -Ho HCC; cc_set_solver|].
      apply elem_of_dom_2, elem_of_chans_of in Hl. rewrite chans_of_union, HKD in Hl. clear -Ho Hl HC1. cc_set_solver. }
    destruct C2 as (S0 & x & m & U & Sc & Σv & Σr & Θe & Σe & L2 & U2 & Dvr & Edel & HΘe & Hss & AV & AP); [done|].
    destruct C1 as (S0' & x' & m' & U' & Sc' & L1 & U1 & AR); [done|].
    assert (ech o ∈ K) as HoK.
    { destruct (lookup_union_cases _ _ _ _ L2) as [Lc|[_ Lc]]; [|by apply elem_of_dom_2, elem_of_chans_of in Lc; rewrite HKD in Lc].
      exfalso. apply elem_of_dom_2, elem_of_chans_of in Lc. apply elem_of_dom_2, elem_of_chans_of in L1.
      rewrite chans_of_union, ech_edual in L1. clear -Lc L1 H12 H2C. cc_set_solver. }
    assert (ΣD !! o = Some (S0, x)) as Ld.
    { destruct (lookup_union_cases _ _ _ _ L2) as [Ld|[_ Ld]]; [|done]. exfalso.
      apply elem_of_dom_2, elem_of_chans_of in Ld. clear -Ld HoK H2C. cc_set_solver. }
    assert (ΣC !! edual o = Some (S0', x')) as Lc.
    { destruct (lookup_union_cases _ _ _ _ L1) as [Lc|[_ Lc]]; [|done]. exfalso.
      apply elem_of_dom_2, elem_of_chans_of in Lc. rewrite ech_edual in Lc. clear -Lc HoK H1C. cc_set_solver. }
    destruct (proj2 (cut_dual_sym _ _ HfC Hcut) _ _ _ Ld) as (S0'' & Lc' & Hdu). rewrite Lc in Lc'. injection Lc' as <- ->.
    destruct (sdual_snd _ _ _ _ _ Hdu U2) as (U'' & S'' & U1' & Hteq & HdS).
    rewrite U1 in U1'. injection U1' as -> <- <-.
    rewrite (pt_dual_shift 1 x) in AR.
    assert (∀ o', o' ∈ dom Θe → ech o' ∈ q2.1) as HΘe' by (intros o' Ho'; by apply HΘe).
    split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _ jj Hjj.
    destruct (oadd_le_part jj _ _ _ Hjj) as [Hjg Hjt].
    assert (Vrel κ jj W1 (Σv ∪ Θe) (payload_at m U' x‾) w) as HV.
    { rewrite payload_at_dual. apply (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x Hteq)).
      eapply at_cost_V_lvl; [exact AV|exact Hjg]. }
    pose proof (msg_recv_ok Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o S0 x Ld Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hok.
    pose proof (msg_recv_disj Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o S0 x Ld Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hdj.
    pose proof (AR jj (Σv ∪ Θe) Hjt Hdj Hok HV) as P1.
    unfold erase in P1. simpl in P1. rewrite difference_empty_L in P1.
    assert (Prel κ jj W1 (<[o := (Sc, x⁺)]> (Σr ∪ Σe)) TUnit (erase (q2.1 ∖ set_map ech (dom Σv ∪ dom Θe), <[i := e']> M2))) as P2.
    { assert (fends w = dom Σv ∪ dom Θe) as HMv by (by rewrite <-(Vrel_exact κ _ _ _ _ _ HV), dom_union_L).
      simpl in AP. unfold fchans in AP. rewrite HMv in AP. eapply (at_cost_lvl X2P); [exact AP|exact Hjg]. }
    pose proof (msg_conn Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o S0 x Ld Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hc'.
    pose proof (msg_iface Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o S0 x Ld Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hif.
    pose proof (msg_chans Σ2 ΣD Σ1 ΣC q2.1 q1.1 Hcs o S0 x Ld Σv Σr Θe Σe Dvr Edel HΘe' Hss Sc Sc' (x⁺) HdS) as Hch.
    pose proof Hc' as Hc3. destruct Hc3 as [_ _ Hcut3 _ _ _ _ _ _ _ _ _]. pose proof (cut_dual_chans _ _ Hcut3) as Hch'.
    pose proof (conn_sym _ _ _ _ _ _ Hc') as Hc''.
    set (E1 := <[o := (Sc, x⁺)]> (Σr ∪ Σe)) in *.
    set (E2 := recv_env (<[edual o := (Sc', (x⁺)‾)]> (Σ1 ∪ ΣC)) (Σv ∪ Θe)) in *.
    rewrite <-(fin_fout (Σ2 ∪ Σ1) E1) in P2. rewrite <-(fin_fout (Σ2 ∪ Σ1) E2) in P1.
    pose proof (L jj (sync_lt κ jj n Hjj) _ _ _ _ _ _ P1 P2 Hc'') as HL.
    assert (ConnectSplit.fin (Σ2 ∪ Σ1) E2 ∪ ConnectSplit.fin (Σ2 ∪ Σ1) E1 = Σ1 ∪ Σ2) as Hif'.
    { rewrite map_union_comm, Hif; [apply map_union_comm, chans_disj_map; clear -H12; cc_set_solver|].
      apply chans_disj_map. destruct Hc''. clear -cn_12. cc_set_solver. }
    rewrite Hif' in HL. refine (eq_rect _ (λ p, Prel κ jj W1 (Σ1 ∪ Σ2) T p) HL _ _).
    assert (i ≠ j) as Hij by (intros ->; eapply (disj_lookup_n M1 M2); eassumption).
    unfold pconn, erase. simpl. f_equal.
    - rewrite Hch', <-HKD. assert (q2.1 ∪ q1.1 ∪ chans_of ΣD = q1.1 ∪ q2.1 ∪ chans_of ΣD) as E by (clear; cc_set_solver).
      rewrite <-E, Hch. clear. cc_set_solver.
    - rewrite (insert_insert_ne _ j i) by done. rewrite (soup_two M1 M2 j i f' e'); [done|done|eauto|eauto].
  Qed.
End cross.
