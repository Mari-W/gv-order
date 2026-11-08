(** * Environments up to ≈ for the live relation (invariance/PointConversion.v)

    [LVrel_econv], [LErel_econv]: V and E transport along Θ ≈_W Θ′, the
    same ends with session types up to ≈. [LPrel_sconv]: P transports
    along Σ ≈_W Σ′. The environment lemmas are reused from
    PointConversion.v. New and the process τ need no renaming of
    points: their fresh names are cofinite, and the caller adds the
    roots of the converted environment to the set to avoid. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveFuse.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

Lemma lb_below_tconv W Θ Θ' lb :
  world_wf W → tconv W Θ Θ' → lb_below W lb (tenv_heads Θ) → lb_below W lb (tenv_heads Θ').
Proof.
  intros HW Hc Hlb. destruct lb as [x|]; simpl in *.
  - intros y' Hy'. destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & Hyy).
    destruct (Hlb y Hy) as [He|Hl]; [left|right].
    + by eapply (wf_eq_trans _ HW).
    + eapply (wf_lt_eq _ HW); [reflexivity|exact Hl|exact Hyy].
  - apply set_eq. intros y'. split; [|set_solver]. intros Hy'.
    destruct (tconv_heads W HW Θ Θ' y' Hc Hy') as (y & Hy & _). set_solver.
Qed.

Lemma lbx_below_tconv W Θ Θ' lb :
  world_wf W → tconv W Θ Θ' → lbx_below W lb (tenv_heads Θ) false →
  lbx_below W lb (tenv_heads Θ') false.
Proof.
  intros HW Hc Hlb. destruct lb as [| |x]; simpl in *; [|done|].
  - destruct Hlb as [Hlb _]. split; [|done]. by apply (lb_below_tconv W Θ Θ' None).
  - destruct Hlb as [Hlb _]. split; [|done]. by apply (lb_below_tconv W Θ Θ' (Some x)).
Qed.

Lemma wext_r_wf W W1 : world_wf W → wext_r W W1 → world_wf W1.
Proof. intros HW [->|H]; [done|by eapply wext_wf]. Qed.

Lemma wext_r_eq W W1 x y : wext_r W W1 → w_eq W x y → w_eq W1 x y.
Proof. intros [->|H] Hxy; [done|by eapply wext_eq]. Qed.

Section econv.
  Context (n : nat).
  Context (IHn : ∀ j, j < n →
    (∀ W Θ Θ' T v, world_wf W → tconv W Θ Θ' → LVrel j W Θ T v → LVrel j W Θ' T v) ∧
    (∀ W Θ Θ' T F e, world_wf W → tconv W Θ Θ' → LErel j W Θ T F e → LErel j W Θ' T F e)).

  Lemma LErel_econv_at T :
    (∀ W Θ Θ' v, world_wf W → tconv W Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T v) →
    ∀ W Θ Θ' F e, world_wf W → tconv W Θ Θ' → LErel n W Θ T F e → LErel n W Θ' T F e.
  Proof.
    intros HVT W Θ Θ' F e HW Hc HE.
    destruct n as [|n']; [apply LErel_0|].
    assert (HEj : ∀ j W0 Θ0 Θ0' T F e0, j ≤ n' → world_wf W0 → tconv W0 Θ0 Θ0' →
              LErel j W0 Θ0 T F e0 → LErel j W0 Θ0' T F e0).
    { intros j ? ? ? ? ? ? Hj. apply (proj2 (IHn j ltac:(lia))). }
    assert (HVj : ∀ j W0 Θ0 Θ0' T v, j ≤ n' → world_wf W0 → tconv W0 Θ0 Θ0' →
              LVrel j W0 Θ0 T v → LVrel j W0 Θ0' T v).
    { intros j ? ? ? ? ? Hj. apply (proj1 (IHn j ltac:(lia))). }
    clear IHn.
    revert W Θ T F e HE HVT Θ' HW Hc.
    refine (LErel_S_ind n' (λ W Θ T F e,
      (∀ W Θ Θ' v, world_wf W → tconv W Θ Θ' → LVrel (S n') W Θ T v → LVrel (S n') W Θ' T v) →
      ∀ Θ', world_wf W → tconv W Θ Θ' → LErel (S n') W Θ' T F e) _).
    intros W0 Θ T F e H HVT Θ' HW0 Hc0.
    apply LErel_S_iff. intros W HW1.
    assert (world_wf W) as HW by (by eapply wext_r_wf).
    assert (tconv W Θ Θ') as Hc.
    { eapply tconv_mono; [|exact Hc0]. intros. by eapply wext_r_eq. }
    destruct (H W HW1) as (Hval & Hrdy & Hb & Hnew & Hsp & Hσ & Hlk).
    clear H HW0 Hc0 HW1.
    assert (HVu : ∀ W Θ Θ' v, world_wf W → tconv W Θ Θ' →
              LVrel (S n') W Θ TUnit v → LVrel (S n') W Θ' TUnit v).
    { intros W2 Θ2 Θ2' v HW2 Hc2 [-> ->]%LVrel_unit_iff.
      apply (tconv_empty W2) in Hc2 as ->. by apply LVrel_unit_iff. }
    split_and!.
    - intros Hirr. eapply HVT; [done|exact Hc|]. by apply Hval.
    - intros Hirr. eapply ready_t_conv; [done|exact Hc|]. by apply Hrdy.
    - intros e' Hst. destruct (Hb e' Hst) as [_ HΦ]. by apply HΦ.
    - intros c e' Hst Hc' L.
      rewrite <-(tconv_dom W Θ Θ' Hc) in Hc'.
      destruct (Hnew c e' Hst Hc' (L ∪ tenv_roots Θ')) as (x & s & s' & W' & Hpl & Hdu & _ & HΦ).
      exists x, s, s', W'. split_and!; [eapply new_place_sub; [|exact Hpl]; set_solver|done|].
      assert (world_wf W' ∧ ∀ x y, w_eq W x y → w_eq W' x y) as [HW' HeW'].
      { destruct Hpl as [(a & -> & Ha & Hfr)|(_ & ->)]; [|done].
        pose proof (proj1 Hfr) as Hx. split; [by eapply wext_wf|intros; by eapply wext_eq]. }
      apply (HΦ HVT); [done|]. apply (tconv_insert W'); [|apply (ends_conv_refl W' HW')].
      by eapply tconv_mono.
    - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & Hsp' & Hv & _ & HΦ).
      destruct (tconv_comp_split W HW Θ Θ1 Θ2 Θ' Hsp' Hc) as (Θ1' & Θ2' & Hsp'' & Hc1 & Hc2).
      exists Θ1', Θ2', ub, lb. split_and!; [done| |by apply HΦ].
      destruct Hv as [(eb & -> & Hfc & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + left. exists eb. split_and!; [done|by rewrite <-(tconv_dom W Θ1 Θ1')|by eapply lb_below_tconv|].
        intros W' j Θa Θ'' w' F' HW' Hj Hcomp Hub.
        assert (world_wf W') as HW'f by (by eapply wext_wf).
        destruct (tconv_comp_join W' HW'f Θ1 Θ1' Θa Θ'' Hcomp) as (Θ0 & Hc0 & Hconv).
        { eapply tconv_mono; [|exact Hc1]. intros. by eapply wext_eq. }
        destruct (HL W' j Θa Θ0 w' F' HW' Hj Hc0 Hub) as [K1 K2]. split.
        * intros Hlt HVw. eapply HEj; [lia|done|exact Hconv|]. by apply K1.
        * intros Hjn HΘ Hw. destruct (K2 Hjn HΘ Hw) as [_ HΦ']. by apply HΦ'.
      + apply (tconv_empty W) in Hc1 as ->. right. by exists k, T0.
    - intros σ e' Hst. pose proof (Hσ σ e' Hst) as Hstep.
      destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LEobl pred] in Hstep |- *.
      + (* O-Recv *)
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
        assert (LVrel j W' Θ2 (payload_at m U k) w) as HVw0.
        { eapply LVrel_tconv; [done| |exact HVw].
          eapply teqW_trans; [done|apply teq_teqW, teq_ty_inst, HU|].
          apply teqW_payload; [done|]. apply Hsub. by apply (wf_eq_sym _ HW). }
        pose proof (H W' j Θ2 Θ1c Θ0 HW' Hj Hext1 Hc0 HVw0) as HE'.
        eapply HEj; [lia|done|exact Hconv|exact HE'].
      + (* O-Send *)
        destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & ΘS & (s0 & Hext & Hu) &
                           Hsp' & HVw & Hext1 & HE').
        destruct (tconv_unext W Θr c (s0, k) Θ Θ' Hc Hext)
          as ([s0' k'] & Θr' & Hext' & [Hs Hkk] & Hcr). simpl in Hs, Hkk.
        destruct (seq_snd_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
          [by apply seq_sym|done|].
        destruct (tconv_comp_split W HW Θr Θ1 Θ2 Θr' Hsp' Hcr) as (Θ1' & Θ2' & Hsp'' & Hc1 & Hc2).
        destruct (tconv_ext W Θ1 Θ1' c (s, pt_shift 1 k) (s'', pt_shift 1 k') ΘS Hc1)
          as (Θ''' & Hext3 & Hc3); [|done|].
        { split; simpl; [by apply seq_sym|]. by apply (wf_eq_shift _ HW). }
        exists Θr', Θ1', Θ2', m, U', s'', k', Θ'''. split_and!.
        * by exists s0'.
        * done.
        * eapply LVrel_tconv; [done| |by eapply HVj].
          eapply teqW_trans; [done|apply teqW_payload; [done|exact Hkk]|].
          apply teq_teqW, teq_ty_inst. by apply teq_sym.
        * done.
        * by eapply HEj.
      + (* O-Close *)
        destruct Hstep as (Θ1 & k & (s0 & Hext & Hu) & HE').
        destruct (tconv_unext W Θ1 c (s0, k) Θ Θ' Hc Hext)
          as ([s0' k'] & Θ1' & Hext' & [Hs Hkk] & Hc1). simpl in Hs, Hkk.
        exists Θ1', k'. split.
        * exists s0'. split; [done|]. apply (seq_end_inv _ s0); [by apply seq_sym|done].
        * by eapply HEj.
      + (* O-Link below *)
        exact I.
      + (* O-Select *)
        destruct Hstep as (Θr & s1 & s2 & k & ΘS & (s0 & Hext & Hu) & Hext1 & HE').
        destruct (tconv_unext W Θr c (s0, k) Θ Θ' Hc Hext)
          as ([s0' k'] & Θr' & Hext' & [Hs Hkk] & Hcr). simpl in Hs, Hkk.
        destruct (seq_plus_inv s0' s0 s1 s2) as (s1' & s2' & Hu' & Hs1 & Hs2);
          [by apply seq_sym|done|].
        destruct (tconv_ext W Θr Θr' c (sbranch i s1 s2, sel_pt k i)
                    (sbranch i s1' s2', sel_pt k' i) ΘS Hcr) as (Θ3 & Hext3 & Hc3); [|done|].
        { split; simpl; [destruct i; by apply seq_sym|].
          by apply (wf_eq_dual _ HW), (wf_eq_payload _ HW). }
        exists Θr', s1', s2', k', Θ3. split_and!; [by exists s0'|done|].
        by eapply HEj.
      + (* O-Branch *)
        destruct Hstep as (Θr & s1 & s2 & k & ΘS & (s0 & Hext & Hu) & Hext1 & HE').
        destruct (tconv_unext W Θr c (s0, k) Θ Θ' Hc Hext)
          as ([s0' k'] & Θr' & Hext' & [Hs Hkk] & Hcr). simpl in Hs, Hkk.
        destruct (seq_with_inv s0' s0 s1 s2) as (s1' & s2' & Hu' & Hs1 & Hs2);
          [by apply seq_sym|done|].
        destruct (tconv_ext W Θr Θr' c (sbranch i s1 s2, bra_pt k i)
                    (sbranch i s1' s2', bra_pt k' i) ΘS Hcr) as (Θ3 & Hext3 & Hc3); [|done|].
        { split; simpl; [destruct i; by apply seq_sym|]. by apply (wf_eq_payload _ HW). }
        exists Θr', s1', s2', k', Θ3. split_and!; [by exists s0'|done|].
        eapply HEj; [lia|done|exact Hc3|exact HE'].
    - (* O-Link, at the index *)
      intros cd e' Hst.
      destruct (Hlk cd e' Hst) as (c & d & Θ1 & Θm & sc & sd & kc & kd & -> & Hext1 & Hext2 &
                                   Hdu & Hal & [_ HΦ]).
      destruct (tconv_unext W Θm c (sc, kc) Θ Θ' Hc Hext2)
        as ([sc' kc'] & Θm' & Hext2' & [Hsc Hkc] & Hcm). simpl in Hsc, Hkc.
      destruct (tconv_unext W Θ1 d (sd, kd) Θm Θm' Hcm Hext1)
        as ([sd' kd'] & Θ1' & Hext1' & [Hsd Hkd] & Hc1). simpl in Hsd, Hkd.
      exists c, d, Θ1', Θm', sc', sd', kc', kd'. split_and!; [done|done|done| | |].
      * eapply sdual_seq_l; [exact Hsd|]. by eapply sdual_seq_r.
      * eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|].
        eapply (wf_eq_trans _ HW); [exact Hal|by apply (wf_eq_dual _ HW)].
      * exact (HΦ HVT Θ1' HW Hc1).
  Qed.

  Lemma LVrel_econv_size k :
    ∀ W Θ Θ' T v, tsize T ≤ k → world_wf W → tconv W Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T v.
  Proof.
    induction k as [k IHk] using lt_wf_ind.
    intros W Θ Θ' T v Hk HW Hc HVv.
    assert (∀ W Θ Θ' T F e, tsize T < k → world_wf W → tconv W Θ Θ' →
              LErel n W Θ T F e → LErel n W Θ' T F e) as HE.
    { intros W0 Θ0 Θ0' T0 F e Hs. apply LErel_econv_at.
      intros W1 Θ1 Θ1' v1. apply (IHk (tsize T0)); [lia|lia]. }
    destruct T as [|ub lb T1 T2|T1 T2|T1 T2|m kk C0 T1|s x|lb m C0 T1]; simpl in Hk.
    - apply LVrel_unit_iff in HVv as [-> ->]. apply LVrel_unit_iff.
      split; [by apply (tconv_empty W)|done].
    - apply LVrel_lolli_iff in HVv
        as [(eb & -> & Hsup & Hlb & HL)|(kc & T0 & -> & -> & Hkc & Ht)].
      + apply LVrel_lolli_iff. left. exists eb. split_and!; [done| | |].
        * by rewrite <-(tconv_dom W Θ Θ').
        * by eapply lb_below_tconv.
        * intros W' j Θa Θ'' w F HW' Hj Hcomp Hub HVw.
          assert (world_wf W') as HW'f by (by eapply wext_wf).
          destruct (tconv_comp_join W' HW'f Θ Θ' Θa Θ'' Hcomp) as (Θ0 & Hc0 & Hconv).
          { eapply tconv_mono; [|exact Hc]. intros. by eapply wext_eq. }
          destruct (decide (j < n)) as [Hlt|Hge].
          -- eapply (proj2 (IHn j Hlt)); [done|exact Hconv|].
             by apply (HL W' j Θa Θ0 w F).
          -- assert (j = n) as -> by lia.
             eapply (HE _ _ _ T2); [lia|done|exact Hconv|].
             by apply (HL W' n Θa Θ0 w F).
      + apply (tconv_empty W) in Hc as ->. apply LVrel_lolli_iff. right.
        by exists kc, T0.
    - apply LVrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      destruct (tconv_comp_split W HW Θ Θ1 Θ2 Θ' Hsp Hc) as (Θ1' & Θ2' & Hsp' & Hc1 & Hc2).
      apply LVrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; [done|done| |].
      + eapply (IHk (tsize T1)); [lia|lia|done|exact Hc1|exact H1].
      + eapply (IHk (tsize T2)); [lia|lia|done|exact Hc2|exact H2].
    - apply LVrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply LVrel_sum_iff; [left|right]; exists v'; (split; [done|]).
      + eapply (IHk (tsize T1)); [lia|lia|done|exact Hc|exact H].
      + eapply (IHk (tsize T2)); [lia|lia|done|exact Hc|exact H].
    - apply LVrel_box_iff in HVv as (-> & HB).
      apply (tconv_empty W) in Hc as ->. by apply LVrel_box_iff.
    - apply LVrel_sess_iff in HVv as (c & s0 & kk & -> & -> & Hs0 & Hkk).
      destruct (tconv_singleton_inv W c _ Θ' Hc) as ([[s0' k']|] & -> & Ho); [|done].
      destruct Ho as [Hs Hk']. simpl in *.
      apply LVrel_sess_iff. exists c, s0', k'. split_and!; [done|done| |].
      + eapply seq_trans; [by apply seq_sym|exact Hs0].
      + eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|exact Hkk].
    - apply LVrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HCx & H)].
      apply LVrel_ex_iff. split; [by eapply lbx_below_tconv|]. exists xs. split_and!; [done..|].
      eapply (IHk (tsize T1)); [lia|unfold ty_inst; rewrite tsize_pinst; lia|done|exact Hc|exact H].
  Qed.
End econv.

Lemma lrel_econv n :
  (∀ W Θ Θ' T v, world_wf W → tconv W Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T v) ∧
  (∀ W Θ Θ' T F e, world_wf W → tconv W Θ Θ' → LErel n W Θ T F e → LErel n W Θ' T F e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ Θ' T v, world_wf W → tconv W Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T v) as HV.
  { intros W Θ Θ' T v. by apply (LVrel_econv_size n IHn (tsize T)). }
  split; [exact HV|].
  intros W Θ Θ' T F e. apply (LErel_econv_at n IHn). intros. by eapply HV.
Qed.

Lemma LVrel_econv n W Θ Θ' T v :
  world_wf W → tconv W Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T v.
Proof. apply (proj1 (lrel_econv n)). Qed.

Lemma LErel_econv n W Θ Θ' T F e :
  world_wf W → tconv W Θ Θ' → LErel n W Θ T F e → LErel n W Θ' T F e.
Proof. apply (proj2 (lrel_econv n)). Qed.

(** ** Interfaces up to ≈ *)

Lemma LPrel_sconv n : ∀ W Σ Σ' T p,
  world_wf W → sconv W Σ Σ' → LPrel n W Σ T p → LPrel n W Σ' T p.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros W Σ Σ' T p HW Hc HP.
  destruct n as [|n']; [apply LPrel_0|].
  assert (∀ j W0 Σ0 Σ0' T p0, j ≤ n' → world_wf W0 → sconv W0 Σ0 Σ0' →
            LPrel j W0 Σ0 T p0 → LPrel j W0 Σ0' T p0) as HPj.
  { intros j ? ? ? ? ? Hj. apply IHn. lia. }
  clear IHn.
  revert W Σ T p HP Σ' HW Hc.
  refine (LPrel_S_ind n' (λ W Σ T p, ∀ Σ', world_wf W → sconv W Σ Σ' → LPrel (S n') W Σ' T p) _).
  intros W0 Σ T p H Σ' HW0 Hc0.
  apply LPrel_S_iff. intros W HW1.
  assert (world_wf W) as HW by (by eapply wext_r_wf).
  assert (sconv W Σ Σ') as Hc.
  { eapply sconv_mono; [|exact Hc0]. intros. by eapply wext_r_eq. }
  destruct (H W HW1) as (Hirr & Hrdy & Had & Hcm & Hlk & Hstep).
  clear H HW0 Hc0 HW1.
  assert (Htau : ∀ X q, (∀ W' Σ0 Σ0' T q, world_wf W' → sconv W' Σ0 Σ0' → X W' Σ0 T q → X W' Σ0' T q) →
            LPtau_case X W Σ T q → LPtau_case X W Σ' T q).
  { intros X q HX Hq Hd L. rewrite <-(sconv_dom W Σ Σ' Hc) in Hd.
    destruct (Hq Hd (L ∪ senv_roots Σ')) as (N & W1 & HN & Hfr & HP').
    exists N, W1. split_and!; [set_solver|done|].
    assert (world_wf W1) as HW1 by (by destruct Hfr as ((_ & _ & _ & [? _]) & _)).
    eapply HX; [done| |exact HP'].
    eapply sconv_mono; [|exact Hc]. intros. destruct Hfr as ((_ & He & _) & _). auto. }
  split_and!.
  - intros Hp. destruct (Hirr Hp) as (v & E & -> & ? & HVv & ?).
    exists v, E. split_and!; [done|done| |done].
    eapply LVrel_econv; [done|by apply sconv_tconv|exact HVv].
  - intros Hp. eapply (ready_p_conv W HW); [exact Hc|]. by apply Hrdy.
  - intros q Hst Hd L. rewrite <-(sconv_dom W Σ Σ' Hc) in Hd.
    destruct (Had q Hst Hd (L ∪ senv_roots Σ')) as (N & W1 & HN & Hfr & _ & HΦ).
    exists N, W1. split_and!; [set_solver|done|].
    assert (world_wf W1) as HW1 by (by destruct Hfr as ((_ & _ & _ & [? _]) & _)).
    apply HΦ; [done|].
    eapply sconv_mono; [|exact Hc]. intros. destruct Hfr as ((_ & He & _) & _). auto.
  - intros q Hst. apply Htau; [|by apply Hcm]. intros. eapply HPj; [lia|done..].
  - (* Q-Link, at the index *)
    intros cd q Hst.
    destruct (Hlk cd q Hst) as (c & d & Σ1 & sc & sd & kc & kd & -> & Hne & HΣ & Hc1 & Hd1 &
                                Hdu & Hal & [_ HΦ]).
      pose proof (Hc c) as Hcc. pose proof (Hc d) as Hdd. rewrite HΣ in Hcc, Hdd.
      rewrite lookup_insert_eq in Hcc. rewrite lookup_insert_ne, lookup_insert_eq in Hdd by done.
      destruct (Σ' !! c) as [[sc' kc']|] eqn:Ec; [|done].
      destruct (Σ' !! d) as [[sd' kd']|] eqn:Ed; [|done].
      destruct Hcc as [Hsc Hkc], Hdd as [Hsd Hkd]. simpl in *.
      exists c, d, (delete c (delete d Σ')), sc', sd', kc', kd'. split_and!.
      * done.
      * done.
      * apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
        { by rewrite lookup_insert_eq. }
        rewrite lookup_insert_ne by done. destruct (decide (x = d)) as [->|Hxd].
        { by rewrite lookup_insert_eq. }
        by rewrite lookup_insert_ne, lookup_delete_ne, lookup_delete_ne.
      * rewrite dom_delete_L. set_solver.
      * rewrite !dom_delete_L. set_solver.
      * eapply sdual_seq_l; [exact Hsd|]. by eapply sdual_seq_r.
      * eapply (wf_eq_trans _ HW); [by apply (wf_eq_sym _ HW)|].
        eapply (wf_eq_trans _ HW); [exact Hal|by apply (wf_eq_dual _ HW)].
      * apply HΦ; [done|].
        intros x. destruct (decide (x = c)) as [->|Hxc].
        { rewrite lookup_delete_eq. by apply not_elem_of_dom in Hc1 as ->. }
        rewrite lookup_delete_ne by done. destruct (decide (x = d)) as [->|Hxd].
        { rewrite lookup_delete_eq. by apply not_elem_of_dom in Hd1 as ->. }
        rewrite lookup_delete_ne by done. specialize (Hc x). rewrite HΣ in Hc.
        by rewrite !lookup_insert_ne in Hc.
  - intros σ q Hst. specialize (Hstep σ q Hst).
    destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LPobl pred] in Hstep |- *.
    + (* Q-Recv *)
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
      assert (LVrel j W' Θ2 (payload_at m U k) w) as HVw0.
      { eapply LVrel_tconv; [done| |exact HVw].
        eapply teqW_trans; [done|apply teq_teqW, teq_ty_inst, HU|].
        apply teqW_payload; [done|]. apply Hsub. by apply (wf_eq_sym _ HW). }
      pose proof (H W' j Θ2 HW' Hj Hfr (recv_ok_conv W' HW'f _ _ _ Hcr Hok) HVw0) as HP1.
      rewrite (recv_back_conv W' _ _ Θ2 Hcr) in HP1.
      eapply HPj; [lia|done| |exact HP1]. by apply (recv_env_conv W' HW'f).
    + (* Q-Send *)
      destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd & Hd0v & Hc0 & Hcv &
                         Hdom & Hsplit & HdΣ & HVw & HP').
      destruct (sconv_hd W HW Σ Σ' c _ k (Σ0 ∪ Σv) Hc Hhd ltac:(rewrite dom_union_L; set_solver))
        as (s0 & s0' & k' & Σ01' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
      destruct (seq_snd_inv s0' s0 m U s) as (U' & s'' & Hu' & HU & Hs'');
        [by apply seq_sym|done|].
      destruct (sconv_split W Σ0 Σv Σ01' Hd0v Hc1') as
        (Σ0' & Σv' & -> & Hd0v' & Hc0' & Hcv' & Hdom0 & Hdomv).
      exists Σ0', Σv', m, U', s'', k', Σe, Θe. split_and!.
      * by exists s0'.
      * done.
      * by rewrite Hdom0.
      * by rewrite Hdomv.
      * done.
      * done.
      * by rewrite <-(sconv_dom W Σ Σ' Hc).
      * eapply LVrel_tconv; [done| |].
        { eapply teqW_trans; [done|apply teqW_payload; [done|exact Hk]|].
          apply teq_teqW, teq_ty_inst. by apply teq_sym. }
        eapply LVrel_econv; [done| |exact HVw].
        apply tconv_union; [by apply sconv_tconv|apply tconv_refl; done].
      * eapply HPj; [lia|done| |exact HP'].
        apply sconv_insert; [apply sconv_union; [done|apply (sconv_refl W HW)]|].
        split; simpl; [by apply seq_sym|]. by apply (wf_eq_shift _ HW).
    + (* Q-Close *)
      destruct Hstep as (Σ1 & k & Hhd & Hc1 & HP').
      destruct (sconv_hd W HW Σ Σ' c _ k Σ1 Hc Hhd Hc1)
        as (s0 & s0' & k' & Σ1' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
      exists Σ1', k'. split_and!; [|done|].
      * exists s0'. split; [done|]. apply (seq_end_inv _ s0); [by apply seq_sym|done].
      * eapply HPj; [lia|done|exact Hc1'|exact HP'].
    + (* Q-Link above *)
      exact I.
    + (* Q-Select *)
      destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc1 & HP').
      destruct (sconv_hd W HW Σ Σ' c _ k Σ1 Hc Hhd Hc1)
        as (s0 & s0' & k' & Σ1' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
      destruct (seq_plus_inv s0' s0 s1 s2) as (s1' & s2' & Hu' & Hs1 & Hs2);
        [by apply seq_sym|done|].
      exists Σ1', s1', s2', k'. split_and!; [by exists s0'|done|].
      eapply HPj; [lia|done| |exact HP']. apply sconv_insert; [done|].
      split; simpl; [destruct i; by apply seq_sym|].
      by apply (wf_eq_dual _ HW), (wf_eq_payload _ HW).
    + (* Q-Branch *)
      destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc1 & HP').
      destruct (sconv_hd W HW Σ Σ' c _ k Σ1 Hc Hhd Hc1)
        as (s0 & s0' & k' & Σ1' & HΣ & HΣ' & Hu & Hs & Hk & Hc1' & Hcd').
      destruct (seq_with_inv s0' s0 s1 s2) as (s1' & s2' & Hu' & Hs1 & Hs2);
        [by apply seq_sym|done|].
      exists Σ1', s1', s2', k'. split_and!; [by exists s0'|done|].
      eapply HPj; [lia|done| |exact HP']. apply sconv_insert; [done|].
      split; simpl; [destruct i; by apply seq_sym|]. by apply (wf_eq_payload _ HW).
Qed.
