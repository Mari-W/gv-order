(** * Channel renaming for the live relation (invariance/ChannelRenaming.v)

    V, E and P are equivariant under a swap of two channel names. The
    environment lemmas and the readiness lemmas are reused from
    ChannelRenaming.v. Inside one level V and E are swapped together by
    induction on [tsize], as in LiveConv.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveConv invariance.ChannelRenaming.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

Section swap_steps.
  Context (a b : chan).

  Lemma tenv_fit_swap Θ e : tenv_fit Θ e → tenv_fit (tenvswap a b Θ) (eswap a b e).
  Proof.
    intros [Hf HB]. split.
    - by rewrite tenv_ends_swap, fends_eswap, Hf.
    - intros c e1 e2 H. rewrite lookup_tenvswap' in H. exact (HB _ _ _ H).
  Qed.

  Lemma padmin_pswap p p' : padmin p p' → padmin (pswap a b p) (pswap a b p').
  Proof.
    destruct 1 as [C E e e' Hst|C E e c x e' Hst HcC HcE Hce|C E e v e' Hst|C E e c bc d bd e' Hst HcC].
    4: { apply padmin_link, ptau_link_pswap. by exists C, E, e, c, bc, d, bd, e'. }
    all: unfold pswap; simpl; rewrite ?msswap_disj_union, ?msswap_singleton.
    - apply PABeta. by apply (tstep_eswap a b) in Hst.
    - rewrite gswap_union, gswap_singleton. eapply PANew.
      + by apply (tstep_eswap a b) in Hst.
      + by rewrite elem_of_gswap.
      + by rewrite echans_msswap, elem_of_gswap.
      + by rewrite fchans_eswap, elem_of_gswap.
    - apply PASpawn. by apply (tstep_eswap a b) in Hst.
  Qed.

  Lemma pcomm_pswap p p' : pcomm p p' → pcomm (pswap a b p) (pswap a b p').
  Proof.
    destruct 1 as [C E c bb v e e' f f' H1 H2|C E c bb e e' f f' H1 H2 HcC|C E c β i e e' f f' H1 H2];
      unfold pswap; simpl; rewrite ?msswap_disj_union, ?msswap_singleton.
    - eapply PCMsg; [by apply (tstep_eswap a b) in H1|by apply (tstep_eswap a b) in H2].
    - rewrite gswap_difference, gswap_singleton. eapply PCClose.
      + by apply (tstep_eswap a b) in H1.
      + by apply (tstep_eswap a b) in H2.
      + by rewrite elem_of_gswap.
    - eapply PCChoice; [by apply (tstep_eswap a b) in H1|by apply (tstep_eswap a b) in H2].
  Qed.

  Lemma padmin_pswap_inv p q : padmin (pswap a b p) q → padmin p (pswap a b q).
  Proof. intros H. apply (padmin_pswap) in H. by rewrite pswap_involutive in H. Qed.

  Lemma pcomm_pswap_inv p q : pcomm (pswap a b p) q → pcomm p (pswap a b q).
  Proof. intros H. apply (pcomm_pswap) in H. by rewrite pswap_involutive in H. Qed.

  Lemma ptau_link_pswap_inv p q : ptau_link (pswap a b p) q → ptau_link p (pswap a b q).
  Proof. intros H. apply (ptau_link_pswap a b) in H. by rewrite pswap_involutive in H. Qed.

  Lemma disj_pswap (p : proc) Σ : (pswap a b p).1 ## dom (senvswap a b Σ) → p.1 ## dom Σ.
  Proof.
    destruct p as [C E]; simpl. rewrite dom_senvswap. by apply gswap_disjoint_iff.
  Qed.
End swap_steps.

Section swap_obl.
  Context (a b : chan).

  Lemma LEobl_swap n Vl El W Θ T F σ e' :
    (∀ j, j ≤ pred n → ∀ W Θ T v, Vl j W Θ T v → Vl j W (tenvswap a b Θ) T (eswap a b v)) →
    (∀ j, j ≤ pred n → ∀ W Θ T F e, El j W Θ T F e → El j W (tenvswap a b Θ) T F (eswap a b e)) →
    LEobl Vl El n W Θ T F σ e' →
    LEobl Vl El n W (tenvswap a b Θ) T F (slswap a b σ) (eswap a b e').
  Proof.
    intros IHV IHE.
    destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; cbn [LEobl slswap oswap fst snd].
    - destruct 1 as (Θ1 & m & U & s & k & [Hhd Hp] & H).
      exists (tenvswap a b Θ1), m, U, s, k.
      split; [split; [by apply (tenv_hd_swap a b _ _ (SSeq (SRcv m U) s))|done]|].
      intros W' j Θ2 Θ1c Θ' Hx Hj Hext Hc HVw.
      apply (tenv_comp_swap a b) in Hc.
      apply (tenv_ext_swap a b) in Hext. rewrite tenvswap_involutive, cswap_involutive in Hext.
      apply (IHV j Hj) in HVw. rewrite eswap_involutive in HVw.
      pose proof (H _ _ _ _ _ Hx Hj Hext Hc HVw) as HE'.
      apply (IHE j Hj) in HE'. by rewrite tenvswap_involutive in HE'.
    - destruct 1 as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & [Hhd Hp] & Hc & HVw & Hext & HE').
      exists (tenvswap a b Θr), (tenvswap a b Θ1), (tenvswap a b Θ2), m, U, s, k, (tenvswap a b Θ').
      split_and!.
      + split; [by apply (tenv_hd_swap a b _ _ (SSeq (SSnd m U) s))|done].
      + by apply tenv_comp_swap.
      + by apply IHV.
      + by apply (tenv_ext_swap a b _ _ (s, pt_shift 1 k)).
      + by apply IHE.
    - destruct 1 as (Θ1 & k & [Hhd Hp] & HE'). exists (tenvswap a b Θ1), k. split.
      + split; [by apply (tenv_hd_swap a b _ _ SEnd)|done].
      + by apply IHE.
    - done.
    - destruct 1 as (Θr & s1 & s2 & k & Θ' & [Hhd Hp] & Hext & HE').
      exists (tenvswap a b Θr), s1, s2, k, (tenvswap a b Θ'). split_and!.
      + split; [by apply (tenv_hd_swap a b _ _ (SPlus s1 s2))|done].
      + by apply (tenv_ext_swap a b _ _ (sbranch i s1 s2, sel_pt k i)).
      + by apply IHE.
    - destruct 1 as (Θr & s1 & s2 & k & Θ' & [Hhd Hp] & Hext & HE').
      exists (tenvswap a b Θr), s1, s2, k, (tenvswap a b Θ'). split_and!.
      + split; [by apply (tenv_hd_swap a b _ _ (SWith s1 s2))|done].
      + by apply (tenv_ext_swap a b _ _ (sbranch i s1 s2, bra_pt k i)).
      + by apply IHE.
  Qed.

End swap_obl.

Section swap.
  Context (a b : chan) (n : nat).
  Context (IHn : ∀ j, j < n →
    (∀ W Θ T v, LVrel j W Θ T v → LVrel j W (tenvswap a b Θ) T (eswap a b v)) ∧
    (∀ W Θ T F e, LErel j W Θ T F e → LErel j W (tenvswap a b Θ) T F (eswap a b e)) ∧
    (∀ W Σ T p, LPrel j W Σ T p → LPrel j W (senvswap a b Σ) T (pswap a b p))).

  Lemma LErel_swap_at T :
    (∀ W Θ v, LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v)) →
    ∀ W Θ F e, LErel n W Θ T F e → LErel n W (tenvswap a b Θ) T F (eswap a b e).
  Proof.
    intros HVT W Θ F e HE.
    destruct n as [|n']; [apply LErel_0|].
    revert W Θ T F e HE HVT.
    refine (LErel_S_ind n' (λ W Θ T F e,
              (∀ W Θ v, LVrel (S n') W Θ T v → LVrel (S n') W (tenvswap a b Θ) T (eswap a b v)) →
              LErel (S n') W (tenvswap a b Θ) T F (eswap a b e)) _).
    intros W Θ T F e H HVT. apply LErel_S_iff. intros W1 HW1.
    destruct (H W1 HW1) as (Hs & Hr & Hb & Hnew & Hsp & Hσ & Hlk).
    assert (HVu : ∀ W Θ v, LVrel (S n') W Θ TUnit v →
              LVrel (S n') W (tenvswap a b Θ) TUnit (eswap a b v)).
    { intros W0 Θ0 v0 [-> ->]%LVrel_unit_iff. apply LVrel_unit_iff. by rewrite tenvswap_empty. }
    split_and!.
    - intros Hirr. apply HVT, Hs.
      apply (irred_swap a b) in Hirr. by rewrite eswap_involutive in Hirr.
    - intros Hirr. apply ready_t_swap, Hr.
      intros Hirr0. apply Hirr. by apply irred_swap.
    - intros e'' Hst. apply (tstep_eswap_inv' a b) in Hst. simpl in Hst.
      destruct (Hb _ Hst) as [_ HΦ]. specialize (HΦ HVT). by rewrite eswap_involutive in HΦ.
    - intros c x e'' Hst Hc. apply (tstep_eswap_inv' a b) in Hst. simpl in Hst.
      assert (cswap a b c ∉ dom Θ) as Hc0.
      { rewrite dom_tenvswap, elem_of_gswap' in Hc. done. }
      destruct (Hnew _ _ _ Hst Hc0) as (Hpl & s & s' & Hdu & _ & HΦ).
      split; [done|]. exists s, s'. split.
      + done.
      + specialize (HΦ HVT). by rewrite tenvswap_insert, cswap_involutive, eswap_involutive in HΦ.
    - intros w e'' Hst. apply (tstep_eswap_inv' a b) in Hst. simpl in Hst.
      destruct (Hsp _ _ Hst) as (Θ1 & Θ2 & ub & lb & Hc & Hv & _ & HΦ).
      exists (tenvswap a b Θ1), (tenvswap a b Θ2), ub, lb. split_and!.
      + by apply tenv_comp_swap.
      + destruct Hv as [(eb & Hw & Hfc & Hlb & HL)|(k & T0 & Hw & -> & Hk & Ht)].
        * left. exists (eswap a b eb). split_and!.
          { by rewrite <-(eswap_involutive a b w), Hw. }
          { by apply tenv_fit_swap. }
          { by rewrite tenv_heads_swap. }
          intros W' j Θ' Θ'' w' F' HW' Hj Hc' Hub.
          apply (tenv_comp_swap a b) in Hc'. rewrite tenvswap_involutive in Hc'.
          destruct (HL W' j (tenvswap a b Θ') (tenvswap a b Θ'') (eswap a b w') F' HW' Hj Hc' Hub)
            as [K1 K2].
          split.
          -- intros Hlt HVw. apply (proj1 (IHn j Hlt)) in HVw.
             specialize (K1 Hlt HVw). apply (proj1 (proj2 (IHn j Hlt))) in K1.
             by rewrite tenvswap_involutive, eswap_subst1, !eswap_involutive in K1.
          -- intros Hjn -> ->. rewrite tenvswap_empty in K2.
             destruct (K2 Hjn eq_refl eq_refl) as [_ HΦ'].
             specialize (HΦ' HVu).
             by rewrite tenvswap_involutive, eswap_subst1, eswap_involutive in HΦ'.
        * right. exists k, T0. split_and!; [|by rewrite tenvswap_empty|done|done].
          by rewrite <-(eswap_involutive a b w), Hw.
      + specialize (HΦ HVT). by rewrite eswap_involutive in HΦ.
    - intros σ e'' Hst. apply (tstep_eswap_inv' a b) in Hst. simpl in Hst.
      pose proof (Hσ _ _ Hst) as Hc.
      rewrite <-(slswap_involutive a b σ), <-(eswap_involutive a b e'').
      apply LEobl_swap; [| |exact Hc].
      + intros j Hj. apply (IHn j). simpl in Hj. lia.
      + intros j Hj. apply (IHn j). simpl in Hj. lia.
    - intros cd e'' Hst. apply (tstep_eswap_inv' a b) in Hst. simpl in Hst.
      destruct (Hlk _ _ Hst) as (c & d & Θ1 & Θm & sc & sd & kc & kd & Hcd & H1 & H2 & Hdu & Hal & [_ HΦ]).
      exists (cswap a b c), (cswap a b d), (tenvswap a b Θ1), (tenvswap a b Θm), sc, sd, kc, kd.
      split_and!.
      + by rewrite <-(goswap_involutive a b cd), Hcd, goswap_upair.
      + by apply (tenv_ext_swap a b _ _ (sd, kd)).
      + by apply (tenv_ext_swap a b _ _ (sc, kc)).
      + done.
      + done.
      + specialize (HΦ HVT). by rewrite eswap_involutive in HΦ.
  Qed.

  Lemma LVrel_swap_size k :
    ∀ W Θ T v, tsize T ≤ k → LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v).
  Proof.
    induction k as [k IHk] using lt_wf_ind.
    intros W Θ T v Hk HVv.
    assert (∀ W Θ T F e, tsize T < k → LErel n W Θ T F e →
              LErel n W (tenvswap a b Θ) T F (eswap a b e)) as HE.
    { intros W0 Θ0 T0 F e Hs. apply LErel_swap_at.
      intros W1 Θ1 v1. apply (IHk (tsize T0)); [lia|lia]. }
    destruct T as [|ub lb T1 U|T1 U|T1 U|m kk C0 T1|s x|lb m C0 T1|x]; simpl in Hk.
    - apply LVrel_unit_iff in HVv as [-> ->].
      apply LVrel_unit_iff. by rewrite tenvswap_empty.
    - apply LVrel_lolli_iff in HVv as [(eb & -> & Hfc & Hlb & H)|(kc & T0 & -> & -> & Hkc & Ht)].
      + apply LVrel_lolli_iff. left. exists (eswap a b eb). split_and!.
        * done.
        * by apply tenv_fit_swap.
        * by rewrite tenv_heads_swap.
        * intros W' j Θ' Θ'' w F Hx Hj Hc Hub HVw.
          apply (tenv_comp_swap a b) in Hc. rewrite tenvswap_involutive in Hc.
          destruct (decide (j < n)) as [Hlt|Hge].
          -- apply (proj1 (IHn j Hlt)) in HVw.
             specialize (H _ _ _ _ _ _ Hx Hj Hc Hub HVw).
             apply (proj1 (proj2 (IHn j Hlt))) in H.
             by rewrite tenvswap_involutive, eswap_subst1, eswap_involutive in H.
          -- assert (j = n) as -> by lia.
             apply (IHk (tsize T1) ltac:(lia) _ _ T1 _ ltac:(lia)) in HVw.
             specialize (H _ _ _ _ _ _ Hx Hj Hc Hub HVw).
             apply (HE _ _ U) in H; [|lia].
             by rewrite tenvswap_involutive, eswap_subst1, eswap_involutive in H.
      + apply LVrel_lolli_iff. right. exists kc, T0. split_and!; [done|by rewrite tenvswap_empty|done|done].
    - apply LVrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
      apply LVrel_prod_iff.
      exists (eswap a b v1), (eswap a b v2), (tenvswap a b Θ1), (tenvswap a b Θ2).
      split_and!; [done|by apply tenv_comp_swap|apply (IHk (tsize T1)); [lia|lia|done]
                  |apply (IHk (tsize U)); [lia|lia|done]].
    - apply LVrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply LVrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + apply (IHk (tsize T1)); [lia|lia|done].
      + apply (IHk (tsize U)); [lia|lia|done].
    - apply LVrel_box_iff in HVv as (-> & eb & -> & Hfc & H).
      apply LVrel_box_iff. rewrite tenvswap_empty. split; [done|].
      exists (eswap a b eb). split_and!; [done|by rewrite fchans_eswap, Hfc, gswap_empty|].
      intros W' xs ss Hx Hxs Hss Hsc HC HK.
      specialize (H _ xs ss Hx Hxs Hss Hsc HC HK).
      apply (IHk (tsize T1)) in H; [|lia|unfold ty_inst; rewrite tsize_sinst, tsize_pinst; lia].
      unfold thunk in H. simpl in H.
      by rewrite tenvswap_empty, eswap_rename, eswap_subst1 in H.
    - apply LVrel_sess_iff in HVv as (c & bb & s0 & kk & -> & -> & Hs & Hx & Hp).
      apply LVrel_sess_iff. exists (cswap a b c), bb, s0, kk.
      split_and!; [done|by rewrite tenvswap_singleton|done|done|done].
    - apply LVrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HC & H)].
      apply LVrel_ex_iff. split; [by rewrite tenv_heads_swap|].
      exists xs. split_and!; [done..|].
      apply (IHk (tsize T1)); [lia|unfold ty_inst; rewrite tsize_pinst; lia|done].
    - apply LVrel_pt_iff in HVv as (-> & -> & Hx). apply LVrel_pt_iff.
      by rewrite tenvswap_empty.
  Qed.

  Lemma LPrel_swap_at W Σ T p :
    LPrel n W Σ T p → LPrel n W (senvswap a b Σ) T (pswap a b p).
  Proof.
    intros HP.
    assert (∀ W Θ T v, LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v)) as HV.
    { intros W0 Θ0 T0 v0. by apply (LVrel_swap_size (tsize T0)). }
    destruct n as [|n']; [apply LPrel_0|].
    revert W Σ T p HP.
    refine (LPrel_S_ind n' (λ W Σ T p, LPrel (S n') W (senvswap a b Σ) T (pswap a b p)) _).
    intros W Σ T p H. apply LPrel_S_iff. intros W1 HW1.
    destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
    assert (IHP : ∀ j, j ≤ n' → ∀ W Σ T p, LPrel j W Σ T p →
              LPrel j W (senvswap a b Σ) T (pswap a b p)).
    { intros j Hj. apply (IHn j). lia. }
    split_and!.
    - intros Hpirr.
      destruct (Hs) as (v & E & -> & Hv & HVv & HE).
      { apply (pirred_swap a b) in Hpirr. by rewrite pswap_involutive in Hpirr. }
      unfold pswap; simpl.
      rewrite gswap_empty, msswap_disj_union, msswap_singleton.
      exists (eswap a b v), (msswap a b E). split_and!.
      + done.
      + by rewrite is_val_eswap.
      + apply HV in HVv. by rewrite tenvswap_of in HVv.
      + intros e He. apply msswap_elem in He as (e0 & -> & He0).
        by rewrite (HE e0 He0).
    - intros Hpirr. apply ready_p_swap.
      apply Hr. intros Hp0. apply Hpirr. by apply pirred_swap.
    - intros q Hst Hd. apply padmin_pswap_inv in Hst.
      rewrite <-(pswap_involutive a b q) in Hd. apply disj_pswap in Hd.
      destruct (Ha _ Hst Hd) as [_ HΦ].
      by rewrite pswap_involutive in HΦ.
    - intros q Hst Hd. apply pcomm_pswap_inv in Hst.
      rewrite <-(pswap_involutive a b q) in Hd. apply disj_pswap in Hd.
      pose proof (Hc _ Hst Hd) as HP'.
      apply IHP in HP'; [|lia]. by rewrite pswap_involutive in HP'.
    - intros cd q Hst. apply (proc_step_pswap_inv' a b) in Hst. simpl in Hst.
      destruct (Hl _ _ Hst) as (c & d & Σ1 & sc & sd & kc & kd &
                           Hcd & Hne & -> & Hc1 & Hd1 & Hdu & Hal & [_ HP']).
      exists (cswap a b c), (cswap a b d), (senvswap a b Σ1), sc, sd, kc, kd.
      split_and!.
      * by rewrite <-(goswap_involutive a b cd), Hcd, goswap_upair.
      * intros Heq. by apply cswap_inj in Heq.
      * by rewrite !senvswap_insert.
      * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
      * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
      * done.
      * done.
      * by rewrite pswap_involutive in HP'.
    - intros σ q Hst. apply (proc_step_pswap_inv' a b) in Hst. simpl in Hst.
      pose proof (Hσ _ _ Hst) as Hstep.
      rewrite <-(pswap_involutive a b q).
      set (q0 := pswap a b q) in *. clearbody q0.
      rewrite <-(slswap_involutive a b σ).
      destruct (slswap a b σ) as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i];
        cbn [LPobl slswap pred oswap fst snd] in Hstep |- *.
      + destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc0 & H').
        exists (senvswap a b Σ1), m, U, s, k.
        split_and!.
        * by apply (senv_hd_swap a b _ _ (SSeq (SRcv m U) s)).
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * intros W' j Θ2 Hx Hj Hfr Hok HVw.
          assert (dom (tenvswap a b Θ2) ## p.1) as Hfr'.
          { rewrite dom_tenvswap. destruct p as [C E]; simpl in *.
            rewrite <-(gswap_involutive a b C). by apply gswap_disjoint_iff. }
          assert (recv_ok W' (<[c := (s, pt_shift 1 k)]> Σ1) (tenvswap a b Θ2)) as Hok'.
          { apply (recv_ok_swap a b) in Hok.
            by rewrite senvswap_insert, senvswap_involutive, cswap_involutive in Hok. }
          apply (proj1 (IHn j ltac:(lia))) in HVw. rewrite eswap_involutive in HVw.
          specialize (H' _ _ _ Hx Hj Hfr' Hok' HVw).
          apply (IHP j ltac:(lia)) in H'.
          rewrite <-recv_env_swap, tenvswap_involutive, senvswap_insert in H'.
          unfold pswap in H'; simpl in H'.
          rewrite gswap_union, <-recv_back_swap, tenvswap_involutive,
            senvswap_insert in H'.
          exact H'.
      + destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                           Hd0v & Hc0 & Hcv & Hdom & Hsplit & HdΣ & HVw & HP').
        exists (senvswap a b Σ0), (senvswap a b Σv), m, U,
          s, k, (senvswap a b Σe), (tenvswap a b Θe).
        split_and!.
        * rewrite <-senvswap_union. by apply (senv_hd_swap a b _ _ (SSeq (SSnd m U) s)).
        * by apply senvswap_disjoint.
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * destruct p as [C E]; simpl in *.
          by rewrite dom_tenvswap, fchans_eswap, Hdom, gswap_intersection.
        * by apply send_split_swap.
        * rewrite dom_tenvswap, dom_senvswap. by apply gswap_disjoint_iff.
        * apply (proj1 (IHn n' ltac:(lia))) in HVw. by rewrite tenvswap_union, tenvswap_of in HVw.
        * apply (IHP n' ltac:(lia)) in HP'.
          by rewrite senvswap_insert, senvswap_union in HP'.
      + destruct Hstep as (Σ1 & k & Hhd & Hc0 & HP').
        exists (senvswap a b Σ1), k. split_and!.
        * by apply (senv_hd_swap a b _ _ SEnd).
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * by apply (IHP n' ltac:(lia)) in HP'.
      + done.
      + destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc0 & HP').
        exists (senvswap a b Σ1), s1, s2, k. split_and!.
        * by apply (senv_hd_swap a b _ _ (SPlus s1 s2)).
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * apply (IHP n' ltac:(lia)) in HP'. by rewrite senvswap_insert in HP'.
      + destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc0 & HP').
        exists (senvswap a b Σ1), s1, s2, k. split_and!.
        * by apply (senv_hd_swap a b _ _ (SWith s1 s2)).
        * rewrite dom_senvswap. simpl. by rewrite elem_of_gswap.
        * apply (IHP n' ltac:(lia)) in HP'. by rewrite senvswap_insert in HP'.
  Qed.
End swap.

Lemma lrel_swap a b n :
  (∀ W Θ T v, LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v)) ∧
  (∀ W Θ T F e, LErel n W Θ T F e → LErel n W (tenvswap a b Θ) T F (eswap a b e)) ∧
  (∀ W Σ T p, LPrel n W Σ T p → LPrel n W (senvswap a b Σ) T (pswap a b p)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ T v, LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v)) as HV.
  { intros W Θ T v. by apply (LVrel_swap_size a b n IHn (tsize T)). }
  split_and!; [exact HV| |].
  - intros W Θ T F e. apply (LErel_swap_at a b n IHn). intros. by apply HV.
  - intros. by apply (LPrel_swap_at a b n IHn).
Qed.

Lemma LVrel_swap a b n W Θ T v :
  LVrel n W Θ T v → LVrel n W (tenvswap a b Θ) T (eswap a b v).
Proof. apply (lrel_swap a b n). Qed.

Lemma LErel_swap a b n W Θ T F e :
  LErel n W Θ T F e → LErel n W (tenvswap a b Θ) T F (eswap a b e).
Proof. apply (lrel_swap a b n). Qed.

Lemma LPrel_swap a b n W Σ T p :
  LPrel n W Σ T p → LPrel n W (senvswap a b Σ) T (pswap a b p).
Proof. apply (lrel_swap a b n). Qed.

(** A process may rename names outside its interface. *)
Lemma LPrel_swap_restricted a b n W Σ T p :
  a ∉ dom Σ → b ∉ dom Σ → LPrel n W Σ T p → LPrel n W Σ T (pswap a b p).
Proof.
  intros Ha Hb HP. apply (LPrel_swap a b) in HP. by rewrite senvswap_fix in HP.
Qed.
