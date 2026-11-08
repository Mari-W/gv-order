(** * Conversion of types up to aliases for the live relation (PointConversion.v)

    V, E and P transport along T ≈_W T'. The arrow of V at level n reads
    E at level n, so inside one level V and E are converted together by
    induction on [tsize], which ≈_W keeps ([teqW_tsize]). New and the
    process τ need no renaming, because they keep the world.

    The alias handling sits in the lemmas reused from
    invariance/PointConversion.v ([teqW_mono], [lb_below_conv],
    [ub_below_conv], [bcs_hold_conv], [pteqW_eq] and the teqW algebra).
    With equality for ≡_W they become rewriting. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveBind.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

Lemma teqW_tsize ρ W T : ∀ U, teqW_r ρ W T U → tsize T = tsize U.
Proof.
  induction T as [| ub lb T1 IH1 U1 IH2 | T1 IH1 U1 IH2 | T1 IH1 U1 IH2 | m k C T1 IH | s x
                 | lb m C T1 IH] in ρ |- *;
    intros [| ub' lb' T1' U1' | T1' U1' | T1' U1' | m' k' C' T1' | s' x' | lb' m' C' T1'] H;
    simpl in *; try done.
  - destruct H as (_ & _ & H1 & H2). by rewrite (IH1 _ _ H1), (IH2 _ _ H2).
  - destruct H as [H1 H2]. by rewrite (IH1 _ _ H1), (IH2 _ _ H2).
  - destruct H as [H1 H2]. by rewrite (IH1 _ _ H1), (IH2 _ _ H2).
  - destruct H as (<- & <- & _ & H). destruct k; by erewrite IH.
  - destruct H as (_ & _ & _ & H). by erewrite IH.
Qed.

Lemma wext_r_eq' W W1 x y : wext_r W W1 → w_eq W x y → w_eq W1 x y.
Proof. intros [->|(_ & He & _)] H; [done|by apply He]. Qed.

Section conv.
  Context (n : nat).
  Context (IHn : ∀ j, j < n →
    (∀ W Θ T T' v, world_wf W → teqW W T T' → LVrel j W Θ T v → LVrel j W Θ T' v) ∧
    (∀ W Θ T T' F e, world_wf W → teqW W T T' → LErel j W Θ T F e → LErel j W Θ T' F e) ∧
    (∀ W Σ T T' p, world_wf W → teqW W T T' → LPrel j W Σ T p → LPrel j W Σ T' p)).

  Lemma LErel_tconv_at (T T' : ty) :
    (∀ W Θ v, world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v) →
    ∀ W Θ F e, world_wf W → teqW W T T' → LErel n W Θ T F e → LErel n W Θ T' F e.
  Proof.
    intros HVT W Θ F e HW Ht HE.
    destruct n as [|n']; [apply LErel_0|].
    revert W Θ T F e HE HW Ht HVT.
    refine (LErel_S_ind n' (λ W Θ T F e, world_wf W → teqW W T T' →
              (∀ W Θ v, world_wf W → teqW W T T' → LVrel (S n') W Θ T v → LVrel (S n') W Θ T' v) →
              LErel (S n') W Θ T' F e) _).
    intros W Θ T F e H HW Ht HVT. apply LErel_S_iff. intros W1 HW1.
    assert (world_wf W1) as HW1f by (destruct HW1 as [->|HW1]; [done|by eapply wext_wf]).
    assert (teqW W1 T T') as Ht1.
    { eapply teqW_mono; [|exact Ht]. intros. by eapply wext_r_eq'. }
    destruct (H W1 HW1) as (Hs & Hr & Hb & Hnew & Hsp & Hσ & Hlk).
    split_and!.
    - intros Hirr. by apply HVT, Hs.
    - done.
    - intros e' Hst. destruct (Hb e' Hst) as [_ HΦ]. by apply HΦ.
    - intros c e' Hst Hc.
      destruct (Hnew c e' Hst Hc) as (x & s & s' & Hpl & Hdu & _ & HΦ).
      exists x, s, s'. split_and!; [done|done|]. by apply HΦ.
    - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & _ & HΦ).
      exists Θ1, Θ2, ub, lb. split_and!; [done| |by apply HΦ].
      eapply Vspawn_mono; [|exact Hv]. by intros ? ? ? ? [? _].
    - intros σ e' Hst. pose proof (Hσ σ e' Hst) as Hc.
      assert (∀ j W0 Θ0 F0 e0, j ≤ n' → world_wf W0 → (∀ x y, w_eq W1 x y → w_eq W0 x y) →
                LErel j W0 Θ0 T F0 e0 → LErel j W0 Θ0 T' F0 e0) as HEj.
      { intros j W0 Θ0 F0 e0 Hj HW0 Hsub.
        apply (proj1 (proj2 (IHn j ltac:(lia)))); [done|]. by eapply teqW_mono. }
      destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LEobl pred] in Hc |- *.
      + destruct Hc as (Θ1 & m & U & s & k & Hhd & H').
        exists Θ1, m, U, s, k. split; [done|].
        intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hc HVw.
        eapply HEj; [lia|by eapply wext_wf| |by apply (H' W' j Θ2 Θ1c Θ')].
        intros. by eapply wext_eq.
      + destruct Hc as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & ? & ? & ? & ? & HE').
        exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done. by eapply HEj.
      + destruct Hc as (Θ1 & k & ? & HE'). exists Θ1, k. split; [done|]. by eapply HEj.
      + done.
      + destruct Hc as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
        exists Θr, s1, s2, k, Θ'. split_and!; try done. by eapply HEj.
      + destruct Hc as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
        exists Θr, s1, s2, k, Θ'. split_and!; try done. by eapply HEj.
    - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)].
      intros ? [_ HΦ]. by apply HΦ.
  Qed.

  Lemma LVrel_tconv_size k :
    ∀ W Θ T T' v, tsize T ≤ k → world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v.
  Proof.
    induction k as [k IHk] using lt_wf_ind.
    intros W Θ T T' v Hk HW Ht HVv.
    assert (∀ W Θ T T' F e, tsize T < k → world_wf W → teqW W T T' →
              LErel n W Θ T F e → LErel n W Θ T' F e) as HE.
    { intros W0 Θ0 T0 T0' F e Hs HW0 Ht0. apply LErel_tconv_at; [|done|done].
      intros W1 Θ1 v1 HW1 Ht1. apply (IHk (tsize T0)); [lia|lia|done|done]. }
    destruct T as [|ub lb T1 T2|T1 T2|T1 T2|m kk C0 T1|s x|lb m C0 T1];
      destruct T' as [|ub' lb' T1' T2'|T1' T2'|T1' T2'|m' kk' C0' T1'|s' x'|lb' m' C0' T1'];
      simpl in Ht, Hk; try done.
    - destruct Ht as (Hu & Hl & Ht1 & Ht2).
      apply LVrel_lolli_iff in HVv as [(eb & -> & Hsup & Hlb & HL)|(kc & T0 & -> & -> & Hkc & Htc)].
      + apply LVrel_lolli_iff. left. exists eb. split_and!; [done|done| |].
        { by eapply lb_below_conv. }
        intros W' j Θ' Θ'' w F HW' Hj Hc Hub HVw.
        pose proof (wext_wf _ _ HW') as HW'f.
        assert (∀ x y, w_eq W x y → w_eq W' x y) as Hsub by (intros; by eapply wext_eq).
        assert (teqW W' T1' T1) as Ht1' by (apply teqW_sym; [done|]; by eapply teqW_mono).
        assert (teqW W' T2 T2') as Ht2' by (by eapply teqW_mono).
        assert (ub_below W' ub F) as Hub'.
        { eapply ub_below_conv; [done| |exact Hub].
          apply opt_rel_sym; [done|]. destruct ub, ub'; simpl in *; try done. }
        destruct (decide (j < n)) as [Hlt|Hge].
        * eapply (proj1 (proj2 (IHn j Hlt))); [done|exact Ht2'|].
          apply (HL W' j Θ' Θ'' w F); [done|done|done|done|].
          by eapply (proj1 (IHn j Hlt)).
        * assert (j = n) as -> by lia.
          apply (HE _ _ T2); [lia|done|exact Ht2'|].
          apply (HL W' n Θ' Θ'' w F); [done|done|done|done|].
          pose proof (teqW_tsize _ _ _ _ Ht1) as Hs1.
          apply (IHk (tsize T1') ltac:(lia) W' Θ' T1' T1 w); [lia|done|exact Ht1'|exact HVw].
      + apply LVrel_lolli_iff. right. exists kc, T0. split_and!; [done|done|done|].
        eapply teqW_trans; [done|exact Htc|]. simpl. by split_and!.
    - destruct Ht as [Ht1 Ht2].
      apply LVrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      apply LVrel_prod_iff. exists v1, v2, Θ1, Θ2.
      split_and!; [done|done|apply (IHk (tsize T1) ltac:(lia) W Θ1 T1 T1' v1); [lia|done|done|done]
                  |apply (IHk (tsize T2) ltac:(lia) W Θ2 T2 T2' v2); [lia|done|done|done]].
    - destruct Ht as [Ht1 Ht2].
      apply LVrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply LVrel_sum_iff; [left|right]; exists v'; (split; [done|]).
      + apply (IHk (tsize T1) ltac:(lia) W Θ T1 T1' v'); [lia|done|done|done].
      + apply (IHk (tsize T2) ltac:(lia) W Θ T2 T2' v'); [lia|done|done|done].
    - destruct Ht as (<- & <- & HC & Ht).
      apply LVrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply LVrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros W' xs ss HW' Hxs Hss Hsc HCx HKx. pose proof (wext_wf _ _ HW') as HW'f.
      eapply (IHk (tsize T1) ltac:(lia) W' ∅ (sinst_ty (slist ss) (ty_inst xs T1))); [unfold ty_inst; rewrite tsize_sinst, tsize_pinst; lia|done| |].
      + destruct kk as [|kk].
        * destruct ss; [|done]. rewrite !sinst_slist_nil.
          apply teqW_ty_inst. eapply teqW_mono; [|exact Ht]. intros. by eapply wext_eq.
        * eapply teqW_eq_r; try apply seq_refl; try done.
          eapply teqW_eq_sinst; try done. eapply teqW_r_pinst_r; try done.
          eapply teqW_r_mono; [|exact Ht]. intros. by eapply wext_eq.
      + apply HK; [done..| |done].
        eapply (bcs_hold_conv W W' C0 C0'); [done|done| |done]. by rewrite Hxs.
    - destruct Ht as [Hx Hs].
      apply LVrel_sess_iff in HVv as (c & s0 & kk & -> & -> & Hs0 & Hkk).
      apply LVrel_sess_iff. exists c, s0, kk. split_and!; [done|done| |].
      + by eapply seq_trans.
      + eapply (wf_eq_trans _ HW); [exact Hkk|]. by apply (pteqW_eq W HW).
    - destruct Ht as (Hl & <- & HC & Ht).
      apply LVrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HCx & H)].
      apply LVrel_ex_iff. split; [by eapply lbx_below_conv|]. exists xs. split_and!; [done..| |].
      + eapply (bcs_hold_conv_sub W W C0' C0); [done|done|done| |done].
        rewrite Hxs. by apply bcs_rel_sym.
      + eapply (IHk (tsize T1) ltac:(lia) W Θ (ty_inst xs T1)); [unfold ty_inst; rewrite tsize_pinst; lia|done| |exact H].
        by apply teqW_ty_inst.
  Qed.

  Lemma LPrel_tconv_at W Σ T T' p :
    world_wf W → teqW W T T' → LPrel n W Σ T p → LPrel n W Σ T' p.
  Proof.
    intros HW Ht HP.
    assert (∀ W Θ T T' v, world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v) as HV.
    { intros W0 Θ0 T0 T0' v0. by apply (LVrel_tconv_size (tsize T0)). }
    destruct n as [|n']; [apply LPrel_0|].
    revert W Σ T p HP HW Ht.
    refine (LPrel_S_ind n' (λ W Σ T p, world_wf W → teqW W T T' → LPrel (S n') W Σ T' p) _).
    intros W Σ T p H HW Ht. apply LPrel_S_iff. intros W1 HW1.
    assert (world_wf W1) as HW1f by (destruct HW1 as [->|HW1]; [done|by eapply wext_wf]).
    assert (teqW W1 T T') as Ht1.
    { eapply teqW_mono; [|exact Ht]. intros. by eapply wext_r_eq'. }
    destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
    assert (∀ j W0 Σ0 q, j ≤ n' → world_wf W0 → (∀ x y, w_eq W1 x y → w_eq W0 x y) →
              LPrel j W0 Σ0 T q → LPrel j W0 Σ0 T' q) as HPj.
    { intros j W0 Σ0 q Hj HW0 Hsub.
      apply (proj2 (proj2 (IHn j ltac:(lia)))); [done|]. by eapply teqW_mono. }
    split_and!.
    - intros Hp. destruct (Hs Hp) as (v & E & -> & ? & HVv & ?).
      exists v, E. split_and!; [done|done| |done]. by eapply HV.
    - done.
    - intros p' Hst Hd. destruct (Ha p' Hst Hd) as [_ HΦ]. by apply HΦ.
    - intros p' Hst Hd. eapply HPj; [lia|done|by intros|exact (Hc p' Hst Hd)].
    - intros cd p' Hst. eapply Plink_case_mono; [|exact (Hl cd p' Hst)].
      intros ? [_ HΦ]. by apply HΦ.
    - intros σ q Hst. pose proof (Hσ σ q Hst) as Hc'.
      destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LPobl pred] in Hc' |- *.
      + destruct Hc' as (Σ1 & m & U & s & k & Hhd & ? & H').
        exists Σ1, m, U, s, k. split_and!; [done|done|].
        intros W' j Θ2 HW' Hj Hfr Hok HVw.
        eapply HPj; [lia|by eapply wext_wf| |by apply H']. intros. by eapply wext_eq.
      + destruct Hc' as (Σ0 & Σv & m & U & s & k & Σe & Θe & ? & ? & ? & ? & ? & ? & ? & ? & HP').
        exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done. by eapply HPj.
      + destruct Hc' as (Σ1 & k & ? & ? & HP'). exists Σ1, k. split_and!; try done. by eapply HPj.
      + done.
      + destruct Hc' as (Σ1 & s1 & s2 & k & ? & ? & HP').
        exists Σ1, s1, s2, k. split_and!; try done. by eapply HPj.
      + destruct Hc' as (Σ1 & s1 & s2 & k & ? & ? & HP').
        exists Σ1, s1, s2, k. split_and!; try done. by eapply HPj.
  Qed.
End conv.

Lemma lrel_tconv n :
  (∀ W Θ T T' v, world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v) ∧
  (∀ W Θ T T' F e, world_wf W → teqW W T T' → LErel n W Θ T F e → LErel n W Θ T' F e) ∧
  (∀ W Σ T T' p, world_wf W → teqW W T T' → LPrel n W Σ T p → LPrel n W Σ T' p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ T T' v, world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v) as HV.
  { intros. by eapply (LVrel_tconv_size n IHn (tsize T)). }
  split_and!; [exact HV| |].
  - intros W Θ T T' F e HW Ht. apply (LErel_tconv_at n IHn); [|done|done].
    intros ? ? ? ? Ht'. by eapply HV.
  - intros. by eapply (LPrel_tconv_at n IHn).
Qed.

Lemma LVrel_tconv n W Θ T T' v : world_wf W → teqW W T T' → LVrel n W Θ T v → LVrel n W Θ T' v.
Proof. apply (proj1 (lrel_tconv n)). Qed.

Lemma LErel_tconv n W Θ T T' F e :
  world_wf W → teqW W T T' → LErel n W Θ T F e → LErel n W Θ T' F e.
Proof. apply (proj1 (proj2 (lrel_tconv n))). Qed.

Lemma LPrel_tconv n W Σ T T' p : world_wf W → teqW W T T' → LPrel n W Σ T p → LPrel n W Σ T' p.
Proof. apply (proj2 (proj2 (lrel_tconv n))). Qed.

(** A payload typed at P[x] is typed at P[y] for every alias y of x. *)
Lemma LVrel_payload n W Θ m U x y v :
  world_wf W → w_eq W x y → LVrel n W Θ (payload_at m U x) v → LVrel n W Θ (payload_at m U y) v.
Proof. intros HW Hxy. apply LVrel_tconv; [done|]. by apply teqW_payload. Qed.
