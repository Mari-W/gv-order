(** * P-Connect, continued: links across the cut *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Connect2.

(** Section lemmas take every section variable, so that both
    orientations of a configuration can be passed uniformly. *)
Set Default Proof Using "All".

Section steps3.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → conn_at j T).
  Context (m : nat) (IHi : conn_lt (S n') T m).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA TB : ty).
  Context (Hm : msize (E1 ⊎ E2) = m) (Hty : ctys TA TB T)
    (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : Prel (S n') W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2 : Prel (S n') W (Σ2 ∪ ΣC') TB (C2, E2)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).

  (** An external link of component 1, with the two ends named as in
      the label. *)
  Lemma ext_link_norm F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∉ C1 → d ∉ C1 →
    c ≠ d ∧ ∃ Σ1a sc sd kc kd,
      Σ1 ∪ ΣC = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ1a) ∧ c ∉ dom Σ1a ∧ d ∉ dom Σ1a ∧
      sdual sc sd ∧ w_eq W kc kd ∧ Prel (S n') W Σ1a TA (C1, F1 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc Hd.
    assert (proc_step (C1, E1) (PSess (SLink {[c; d]})) (C1 ∖ sentc (SLink {[c; d]}), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE; apply PStepSession; [done|simpl; clear -Hc Hd; set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hs1) as Hc1. simpl in Hc1.
    rewrite difference_empty_L in Hc1.
    destruct Hc1 as (c' & d' & Σ1a & sc & sd & kc & kd & Hcd' & Hne & HΣa & Hc1a & Hd1a & Hdu & Hal & HP1').
    assert (c ≠ d) as Hcd.
    { intros <-. assert (c' ∈ ({[c; c]} : gset chan)) as H1 by (rewrite Hcd'; set_solver).
      assert (d' ∈ ({[c; c]} : gset chan)) as H2 by (rewrite Hcd'; set_solver).
      apply Hne. set_solver. }
    split; [done|].
    destruct (upair_eq_inv c d c' d' Hcd' Hcd) as [[-> ->]|[-> ->]].
    - exists Σ1a, sc, sd, kc, kd. split_and!; try done. by apply sdual_sym.
    - exists Σ1a, sd, sc, kd, kc. split_and!; try done.
      + rewrite HΣa. by apply insert_insert_ne.
      + by apply (wf_eq_sym _ (proj1 (co_strict _ _ _ _ _ _ _ _ Hok))).
  Qed.
  (** The giving clause for a link of component 1 between its end of a
      cut channel c and an interface channel d: component 2's end of c
      is renamed to d. *)
  Lemma link_iface F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C0 → d ∈ dom Σ1 →
    Prel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst HcC0 HdΣ1.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply map_disjoint_dom in Hd12 as Hd12'.
    assert (c ∉ C1 ∧ d ∉ C1 ∧ c ∉ C2 ∧ d ∉ C2 ∧ d ∉ C0 ∧ d ∉ dom Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2)
      as (Hc1 & Hd1' & Hc2 & Hd2' & HdC0 & HdΣ2 & HcΣ1 & HcΣ2)
      by (clear -HcC0 HdΣ1 HC10 HC1Σ1 HC20 HC2Σ1 HΣ1C0 HΣ2C0 Hd12'; set_solver).
    destruct (ext_link_norm F1 e c d e' HE Hst Hc1 Hd1')
      as (Hcd & Σ1a & sc & sd & kc & kd & HΣa & Hc1a & Hd1a & Hdu & Hal & HP1').
    assert (ΣC !! c = Some (sc, kc)) as HCc.
    { pose proof (f_equal (lookup c) HΣa) as H. rewrite lookup_insert_eq, lookup_union in H.
      rewrite (not_elem_of_dom_1 _ _ HcΣ1), (left_id_L None (∪)) in H. done. }
    assert (Σ1 !! d = Some (sd, kd)) as H1d.
    { pose proof (f_equal (lookup d) HΣa) as H. rewrite lookup_insert_ne, lookup_insert_eq, lookup_union in H by done.
      assert (ΣC !! d = None) as HCd by (apply not_elem_of_dom; by rewrite HC0).
      rewrite HCd in H. destruct (Σ1 !! d); [by rewrite (right_id_L None (∪)) in H|done]. }
    assert (is_Some (ΣC' !! c)) as [[sc2 kc2] HC'c] by (apply elem_of_dom; by rewrite HC0').
    destruct (Hcut c _ _ HCc HC'c) as [Hkk Hdd]. simpl in Hkk, Hdd.
    (* component 2, its end of c renamed to d *)
    assert (Prel (S n') W (<[d := (sd, kd)]> Σ2 ∪ delete c ΣC') TB (C2, echsubst c d E2)) as HP2'.
    { pose proof (Prel_swap c d _ _ _ _ _ HP2) as H. unfold pswap in H. simpl in H.
      rewrite gswap_fresh in H by done.
      apply (Prel_junk _ _ _ _ _ _ c d) in H.
      - rewrite echsubst_msswap_same in H. eapply Prel_sconv; [apply HW'| |exact H].
        intros r. rewrite lookup_senvswap'.
        destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
        + rewrite cswap_l, !lookup_union. rewrite lookup_insert_ne by done. rewrite lookup_delete_eq.
          rewrite (not_elem_of_dom_1 _ _ HdΣ2), (not_elem_of_dom_1 _ _ HcΣ2).
          assert (ΣC' !! d = None) as -> by (apply not_elem_of_dom; by rewrite HC0').
          done.
        + rewrite cswap_r, !lookup_union, lookup_insert_eq, (not_elem_of_dom_1 _ _ HcΣ2), HC'c, (left_id_L None (∪)), union_Some_l.
          simpl. split; [eapply sdual_unique; [exact Hdd|exact Hdu]|].
          apply (wf_eq_trans _ (proj1 HW') _ kc); [by apply (wf_eq_sym _ (proj1 HW'))|done].
        + rewrite cswap_ne by done. rewrite !lookup_union, lookup_insert_ne, lookup_delete_ne by done.
          destruct (Σ2 !! r), (ΣC' !! r); simpl; try done; split; try apply seq_refl;
            apply (wf_eq_refl _ (proj1 HW')).
      - rewrite dom_senvswap, elem_of_gswap', cswap_l, dom_union_L, HC0'.
        clear -HdΣ2 HdC0. set_solver.
      - done.
      - done.
      - done. }
    assert (Prel (S n') W (delete d Σ1 ∪ delete c ΣC) TA (C1, echsubst c d (F1 ⊎ {[+ e' +]}))) as HP1''.
    { assert (Σ1a = delete d Σ1 ∪ delete c ΣC) as <-.
      { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
        destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
        - rewrite lookup_union, lookup_delete_eq, lookup_delete_ne, (not_elem_of_dom_1 _ _ HcΣ1) by done.
          by rewrite (not_elem_of_dom_1 _ _ Hc1a).
        - rewrite lookup_union, lookup_delete_eq, lookup_delete_ne by done.
          assert (ΣC !! d = None) as -> by (apply not_elem_of_dom; by rewrite HC0).
          by rewrite (not_elem_of_dom_1 _ _ Hd1a).
        - rewrite !lookup_insert_ne in Hr by done.
          by rewrite <-Hr, !lookup_union, lookup_delete_ne, lookup_delete_ne by done. }
      apply Prel_junk; [done|done|intros ?; contradiction|by apply not_eq_sym|exact HP1']. }
    assert (Σ1 ∪ Σ2 = delete d Σ1 ∪ <[d := (sd, kd)]> Σ2) as ->.
    { apply map_eq. intros r. destruct (decide (r = d)) as [->|Hrd].
      - by rewrite !lookup_union, lookup_delete_eq, lookup_insert_eq, H1d, union_Some_l, (left_id_L None (∪)).
      - by rewrite !lookup_union, lookup_delete_ne, lookup_insert_ne by done. }
    assert (C ∖ {[c]} = C1 ∪ C2 ∪ (C0 ∖ {[c]})) as -> by (clear -Hc1 Hc2; set_solver).
    assert (echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]}) = echsubst c d (F1 ⊎ {[+ e' +]}) ⊎ echsubst c d E2)
      as -> by (rewrite !echsubst_disj_union; multiset_solver).
    apply (IHi W (delete d Σ1) (<[d := (sd, kd)]> Σ2) (delete c ΣC) (delete c ΣC') _ C1 C2 _ _ TA TB);
      [|done| |exact HP1''|exact HP2'].
    - rewrite <-Hm, HE, !msize_disj_union, !msize_echsubst, !msize_disj_union, !msize_singleton.
      pose proof (tstep_giving_size _ _ _ Hst I). lia.
    - split; try done.
      + by apply map_disjoint_delete_l, map_disjoint_delete_r.
      + apply map_disjoint_insert_l. split; [|by apply map_disjoint_delete_r].
        rewrite lookup_delete_ne; [|done]. apply not_elem_of_dom. by rewrite HC0'.
      + apply map_disjoint_dom. rewrite dom_delete_L, dom_insert_L. clear -Hd12'. set_solver.
      + rewrite dom_delete_L. by rewrite HC0.
      + rewrite dom_delete_L. by rewrite HC0'.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + rewrite dom_insert_L. clear -HC1Σ2 Hd1'. set_solver.
      + rewrite dom_delete_L. clear -HC2Σ1. set_solver.
      + rewrite dom_delete_L. clear -HC1Σ1. set_solver.
      + rewrite dom_insert_L. clear -HC2Σ2 Hd2'. set_solver.
      + clear -HC10. set_solver.
      + clear -HC20. set_solver.
  Qed.
  (** The giving clause for a link of component 1 between its ends of
      two cut channels c and d: component 2 gets both ends of d and
      fuses them by Internalizing a link. *)
  Lemma link_cut F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C0 → d ∈ C0 →
    Prel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst HcC0 HdC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ d ∉ C1 ∧ c ∉ C2 ∧ d ∉ C2 ∧ c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧ d ∉ dom Σ2)
      as (Hc1 & Hd1' & Hc2 & Hd2' & HcΣ1 & HdΣ1 & HcΣ2 & HdΣ2)
      by (clear -HcC0 HdC0 HC10 HC20 HΣ1C0 HΣ2C0; set_solver).
    destruct (ext_link_norm F1 e c d e' HE Hst Hc1 Hd1')
      as (Hcd & Σ1a & sc & sd & kc & kd & HΣa & Hc1a & Hd1a & Hdu & Hal & HP1').
    assert (ΣC !! c = Some (sc, kc)) as HCc.
    { pose proof (f_equal (lookup c) HΣa) as H. rewrite lookup_insert_eq, lookup_union in H.
      by rewrite (not_elem_of_dom_1 _ _ HcΣ1), (left_id_L None (∪)) in H. }
    assert (ΣC !! d = Some (sd, kd)) as HCd.
    { pose proof (f_equal (lookup d) HΣa) as H.
      rewrite lookup_insert_ne, lookup_insert_eq, lookup_union in H by done.
      by rewrite (not_elem_of_dom_1 _ _ HdΣ1), (left_id_L None (∪)) in H. }
    assert (is_Some (ΣC' !! c)) as [[sc2 kc2] HC'c] by (apply elem_of_dom; by rewrite HC0').
    assert (is_Some (ΣC' !! d)) as [[sd2 kd2] HC'd] by (apply elem_of_dom; by rewrite HC0').
    destruct (Hcut c _ _ HCc HC'c) as [Hkc Hdc]. destruct (Hcut d _ _ HCd HC'd) as [Hkd Hdd].
    simpl in Hkc, Hdc, Hkd, Hdd.
    set (Σb0 := Σ2 ∪ delete c (delete d ΣC')).
    assert (Σ2 ∪ ΣC' = fusedP c d Σb0 sc2 sd2 kc2 kd2) as HΣb.
    { apply map_eq. intros r. unfold fusedP. subst Σb0.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      - by rewrite lookup_insert_eq, lookup_union, (not_elem_of_dom_1 _ _ HcΣ2), HC'c.
      - rewrite lookup_insert_ne, lookup_insert_eq by done.
        by rewrite lookup_union, (not_elem_of_dom_1 _ _ HdΣ2), HC'd.
      - rewrite !lookup_insert_ne by done.
        by rewrite !lookup_union, lookup_delete_ne, lookup_delete_ne by done. }
    assert (prim TB) as HTB by (by destruct (ctys_prim _ _ _ HT Hty)).
    assert (int_ok c d W Σb0 sc2 sd2 kc2 kd2 C2) as Hio.
    { split_and!; try done.
      - subst Σb0. rewrite dom_union_L, !dom_delete_L. clear -HcΣ2. set_solver.
      - subst Σb0. rewrite dom_union_L, !dom_delete_L. clear -HdΣ2. set_solver.
      - eapply sdual_seq_l; [|exact Hdd]. eapply sdual_unique; [exact Hdu|exact Hdc].
      - pose proof (proj1 HW') as Hwf.
        apply (wf_eq_trans _ Hwf _ kc); [by apply (wf_eq_sym _ Hwf)|].
        by apply (wf_eq_trans _ Hwf _ kd). }
    rewrite HΣb in HP2.
    pose proof (Prel_internalize c d Hcd (S n') W Σb0 TB C2 E2 sc2 sd2 kc2 kd2 HTB Hio HP2) as HP2'.
    assert (Prel (S n') W (Σ1 ∪ delete c (delete d ΣC)) TA (C1, echsubst c d (F1 ⊎ {[+ e' +]})))
      as HP1''.
    { assert (Σ1a = Σ1 ∪ delete c (delete d ΣC)) as <-.
      { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
        destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
        - rewrite lookup_union, lookup_delete_eq, (not_elem_of_dom_1 _ _ HcΣ1).
          by rewrite (not_elem_of_dom_1 _ _ Hc1a).
        - rewrite lookup_union, lookup_delete_ne, lookup_delete_eq, (not_elem_of_dom_1 _ _ HdΣ1) by done.
          by rewrite (not_elem_of_dom_1 _ _ Hd1a).
        - rewrite !lookup_insert_ne in Hr by done.
          by rewrite <-Hr, !lookup_union, lookup_delete_ne, lookup_delete_ne by done. }
      apply Prel_junk; [done|done|intros ?; contradiction|by apply not_eq_sym|exact HP1']. }
    assert (C ∖ {[c]} = C1 ∪ (C2 ∪ {[d]}) ∪ (C0 ∖ {[c; d]})) as ->.
    { apply set_eq. intros x. destruct (decide (x = d)) as [->|Hxd]; [clear -Hcd HdC0; set_solver|].
      clear -Hc1 Hc2 Hxd. set_solver. }
    assert (echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]}) = echsubst c d (F1 ⊎ {[+ e' +]}) ⊎ echsubst c d E2)
      as -> by (rewrite !echsubst_disj_union; multiset_solver).
    apply (IHi W Σ1 Σ2 (delete c (delete d ΣC)) (delete c (delete d ΣC')) _ C1 _ _ _ TA TB);
      [|done| |exact HP1''|exact HP2'].
    - rewrite <-Hm, HE, !msize_disj_union, !msize_echsubst, !msize_disj_union, !msize_singleton.
      pose proof (tstep_giving_size _ _ _ Hst I). lia.
    - split; try done.
      + by apply map_disjoint_delete_r, map_disjoint_delete_r.
      + by apply map_disjoint_delete_r, map_disjoint_delete_r.
      + rewrite !dom_delete_L, HC0. clear. set_solver.
      + rewrite !dom_delete_L, HC0'. clear. set_solver.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hx as [_ Hx]. apply lookup_delete_Some in Hy as [_ Hy].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + clear -HC2Σ1 HdΣ1. set_solver.
      + clear -HC2Σ2 HdΣ2. set_solver.
      + clear -HC10. set_solver.
      + clear -HC20. set_solver.
      + clear -HC12 Hd1'. set_solver.
  Qed.
  (** The giving clause for a link τ of the composite whose thread is in
      component 1. *)
  Lemma link_give F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C →
    Prel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst HcC.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    destruct (decide (c ∈ C1)) as [Hc1|Hc1].
    { exact (link_own n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok0 HP1 HP2
               F1 e c d e' HE Hst Hc1). }
    destruct (decide (d ∈ C1)) as [Hd1'|Hd1'].
    { assert (d ≠ c) as Hdc by (intros ->; done).
      rewrite upair_comm in Hst.
      pose proof (link_own n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok0 HP1 HP2
                    F1 e d c e' HE Hst Hd1') as H.
      apply (Prel_swap_restricted c d) in H.
      - unfold pswap in H. simpl in H.
        rewrite gswap_minus_other, msswap_echsubst_flip in H; [done|done|clear -Hd1'; set_solver].
      - apply map_disjoint_dom in Hd12. rewrite dom_union_L.
        clear -HcC HC1Σ1 HC1Σ2 HC2Σ1 HC2Σ2 HΣ1C0 HΣ2C0. set_solver.
      - rewrite dom_union_L. clear -Hd1' HC1Σ1 HC1Σ2. set_solver. }
    rewrite HE in HP1.
    pose proof (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP1 Hst ltac:(simpl; clear -Hc1 Hd1'; set_solver))
      as Hsub. simpl in Hsub. rewrite dom_union_L, HC0 in Hsub. rewrite <-HE in HP1.
    assert (c ∈ C0) as HcC0.
    { assert (c ∈ dom Σ1 ∪ C0) as H by (apply Hsub; clear; set_solver).
      clear -H HcC HC2Σ1 Hc1. set_solver. }
    assert (d ∈ dom Σ1 ∪ C0) as Hd by (apply Hsub; clear; set_solver).
    apply elem_of_union in Hd as [Hd|Hd].
    - exact (link_iface F1 e c d e' HE Hst HcC0 Hd).
    - exact (link_cut F1 e c d e' HE Hst HcC0 Hd).
  Qed.
  Local Notation own := (own_tau n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2).

  Lemma C12_0 : C1 ## C2 ∪ C0.
  Proof. pose proof (co_C12 _ _ _ _ _ _ _ _ Hok). pose proof (co_C10 _ _ _ _ _ _ _ _ Hok). set_solver. Qed.

  (** Internal steps of component 1, by kind. *)
  Lemma tau_beta F1 e e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e LBeta e' →
    Ptau_case (Prel n') W Σ T (C, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst. pose proof (own (C1, F1 ⊎ {[+ e' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} = F1 ⊎ {[+ e' +]} ⊎ E2) as -> by multiset_solver.
    apply H; [rewrite HE; by apply PStepBeta|apply C12_0].
  Qed.

  Lemma tau_spawn F1 e v e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSpawn v) e' →
    Ptau_case (Prel n') W Σ T (C, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}).
  Proof.
    intros HE Hst. pose proof (own (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]} ⊎ E2)
      as -> by multiset_solver.
    apply H; [rewrite HE; by apply PStepSpawn|apply C12_0].
  Qed.

  Lemma tau_new F1 e c e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LNew c) e' → c ∉ C → c ∉ echans (F1 ⊎ E2) → c ∉ fchans e →
    Ptau_case (Prel n') W Σ T (C ∪ {[c]}, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc Hce Hcf. pose proof (own (C1 ∪ {[c]}, F1 ⊎ {[+ e' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} = F1 ⊎ {[+ e' +]} ⊎ E2) as -> by multiset_solver.
    assert (C ∪ {[c]} = C1 ∪ {[c]} ∪ C2 ∪ C0) as -> by (clear; set_solver).
    rewrite echans_disj_union in Hce.
    apply H.
    - rewrite HE. apply PStepNew; [done|clear -Hc; set_solver|clear -Hce; set_solver|done].
    - pose proof C12_0. clear -H0 Hc. set_solver.
  Qed.

  Lemma tau_msg F1 c v e e' f f' :
    E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SSend c v)) e' →
    tstep f (LSess (SRecv c v)) f' →
    Ptau_case (Prel n') W Σ T (C, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE Hst1 Hst2. pose proof (own (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]} ⊎ E2)
      as -> by multiset_solver.
    apply H; [rewrite HE; by eapply PStepMsg|apply C12_0].
  Qed.

  Lemma tau_close F1 c e e' f f' :
    E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SClos c)) e' →
    tstep f (LSess (SClos c)) f' →
    Ptau_case (Prel n') W Σ T (C ∖ {[c]}, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE Hst1 Hst2.
    destruct (decide (c ∈ C1)) as [Hc|Hc].
    2: { exfalso. exact (own_close_contra n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB
                           Hm Hty Hok HP1 HP2 F1 e e' f f' c HE Hst1 Hst2 Hc). }
    pose proof (own (C1 ∖ {[c]}, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]} ⊎ E2)
      as -> by multiset_solver.
    pose proof C12_0 as H0.
    assert (C ∖ {[c]} = C1 ∖ {[c]} ∪ C2 ∪ C0) as -> by (clear -Hc H0; set_solver).
    apply H; [rewrite HE; by eapply PStepClose|clear -H0; set_solver].
  Qed.
End steps3.

(** ** Assembly *)

Lemma Ptau_case_conv X W Σ Σ' T p q :
  Σ = Σ' → p = q → Ptau_case X W Σ T p → Ptau_case X W Σ' T q.
Proof. by intros -> ->. Qed.

Lemma Pcase_conv X n' W Σ Σ' T p q π p' q' :
  Σ = Σ' → p = q → p' = q' → Pcase_gen X n' W Σ T p π p' → Pcase_gen X n' W Σ' T q π q'.
Proof. by intros -> -> ->. Qed.

Section assembly.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → conn_at j T).
  Context (m : nat) (IHi : conn_lt (S n') T m).

  Lemma conn_level W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB :
    msize (E1 ⊎ E2) = m → ctys TA TB T → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    Prel (S n') W (Σ1 ∪ ΣC) TA (C1, E1) → Prel (S n') W (Σ2 ∪ ΣC') TB (C2, E2) →
    Prel (S n') W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
  Proof.
    intros Hm Hty Hok HP1 HP2.
    assert (msize (E2 ⊎ E1) = m) as Hm' by (by rewrite (comm_L (⊎))).
    pose proof (ctys_sym _ _ _ Hty) as Hty'. pose proof (cut_ok_sym _ _ _ _ _ _ _ _ Hok) as Hok'.
    assert (Σ2 ∪ Σ1 = Σ1 ∪ Σ2) as HΣs by (symmetry; apply (co_union_comm _ _ _ _ _ _ _ _ Hok)).
    assert (C2 ∪ C1 ∪ C0 = C1 ∪ C2 ∪ C0) as HCs by apply union3_comm.
    assert (E2 ⊎ E1 = E1 ⊎ E2) as HEs by apply (comm_L (⊎)).
    assert (Hgive : ∀ p', ptau_link (C1 ∪ C2 ∪ C0, E1 ⊎ E2) p' → Prel (S n') W (Σ1 ∪ Σ2) T p').
    { intros p' (C' & E & e & c & d & e' & Heq & Hst & HcC & ->). injection Heq as <- HE.
      destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
      - exact (link_give n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                 F1 e c d e' HE1 Hst HcC).
      - pose proof (link_give n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c d e' HE2 Hst ltac:(by rewrite HCs)) as H.
        rewrite HΣs, HCs in H.
        assert (F2 ⊎ E1 ⊎ {[+ e' +]} = E1 ⊎ F2 ⊎ {[+ e' +]}) as <- by multiset_solver. exact H. }
    apply Prel_S_intro.
    - destruct Hty as [[-> ->]|[-> ->]].
      + exact (conn_stop n' T HT W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + intros Hirr. pose proof (conn_stop n' T HT W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        rewrite HΣs, HCs, HEs in H. by apply H.
    - intros _. destruct Hty as [[-> ->]|[-> ->]].
      + exact (conn_ready n' T HT W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + pose proof (conn_ready n' T HT W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        by rewrite HΣs, HCs, HEs in H.
    - intros π p' Hst. destruct π as [|σ].
      + simpl. split; [|intros Hl _; by apply Hgive].
        pose proof Hst as Hst0.
        apply ptau_inv in Hst as [(F & e & e' & HE & Hs & ->)
          |[(F & e & c & e' & HE & Hs & HcC & HcF & Hce & ->)
          |[(F & e & v & e' & HE & Hs & ->)
          |[(F & c & v & e & e' & f & f' & HE & Hs1 & Hs2 & ->)
          |[(F & c & e & e' & f & f' & HE & Hs1 & Hs2 & HcC & ->)
          |(F & e & c & d & e' & HE & Hs & HcC & ->)]]]]].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_beta n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e e' HE1 Hs).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_beta n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e e' HE2 Hs)].
             f_equal; [done|multiset_solver].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_new n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c e' HE1 Hs HcC HcF Hce).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_new n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e c e' HE2 Hs ltac:(by rewrite HCs)
                      ltac:(by rewrite (comm_L (⊎) F2)) Hce)].
             f_equal; [by rewrite HCs|multiset_solver].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_spawn n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e v e' HE1 Hs).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_spawn n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e v e' HE2 Hs)].
             f_equal; [done|multiset_solver].
        * destruct (gmultiset_split_in2 _ _ _ _ _ HE)
            as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
          -- exact (tau_msg n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 c v e e' f f' HE1 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_msg n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 c v e e' f f' HE2 Hs1 Hs2)].
             f_equal; [done|multiset_solver].
          -- exact (cross_msg n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 F2 e e' f f' c v HE1 HE2 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (cross_msg n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 F1 e e' f f' c v HE2 HE1 Hs1 Hs2)].
             f_equal; [done|multiset_solver].
        * destruct (gmultiset_split_in2 _ _ _ _ _ HE)
            as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
          -- exact (tau_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 c e e' f f' HE1 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 c e e' f f' HE2 Hs1 Hs2)].
             f_equal; [by rewrite HCs|multiset_solver].
          -- exact (cross_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 F2 e e' f f' c HE1 HE2 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (cross_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 F1 e e' f f' c HE2 HE1 Hs1 Hs2)].
             f_equal; [by rewrite HCs|multiset_solver].
        * intros Hg. exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl, Hok|].
          eapply Prel_down; [|apply Hgive]; [lia|].
          exists (C1 ∪ C2 ∪ C0), F, e, c, d, e'. by rewrite HE.
      + apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & Hsub & ->).
        destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        * destruct σ as [c w|c w|c|cd]; simpl in Hsub.
          -- exact (ext_recv n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_send n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_link n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e cd e' HE1 Hs Hsub).
        * rewrite <-HCs in Hsub.
          destruct σ as [c w|c w|c|cd]; simpl in Hsub.
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_recv n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_send n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_link n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e cd e' HE2 Hs Hsub)];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|multiset_solver]].
  Qed.
End assembly.
