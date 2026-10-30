(** * P-Connect, continued: links, internal steps and synchronizations *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Connect.

Lemma senv_roots_union Σ1 Σ2 : senv_roots (Σ1 ∪ Σ2) ⊆ senv_roots Σ1 ∪ senv_roots Σ2.
Proof.
  intros x. unfold senv_roots. rewrite elem_of_union, !elem_of_tenv_roots.
  intros (c0 & o & Ho & Hx). unfold tenv_of in *. rewrite lookup_fmap, lookup_union in Ho.
  destruct (Σ1 !! c0) as [e|] eqn:E1.
  - left. exists c0, o. rewrite lookup_fmap, E1. by rewrite union_Some_l in Ho.
  - right. exists c0, o. rewrite lookup_fmap. by rewrite (left_id_L None (∪)) in Ho.
Qed.

Section steps2.
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

  Lemma HW2 : strict W.
  Proof. apply Hok. Qed.

  (** Q-Link for an external link of component 1. *)
  Lemma ext_link F1 e cd e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink cd)) e' → subjs (SLink cd) ## C →
    Plink_case (Prel (S n')) W Σ T cd (C ∖ sentc (SLink cd), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SLink cd)) (C1 ∖ sentc (SLink cd), F1 ⊎ {[+ e' +]}))
      as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SLink cd) e' Hst). simpl in *. clear -Hc. set_solver. }
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst1) as Hc1. simpl in Hc1.
    cbn [sentc]. rewrite difference_empty_L in Hc1 |- *.
    destruct Hc1 as (c & d & Σ1a & sc & sd & kc & kd & -> & Hcd & HΣa & Hc1a & Hd1a & Hdu & Hal & HP1').
    simpl in Hc.
    assert (c ∉ C0 ∧ d ∉ C0) as [HcC0 HdC0] by (clear -Hc; set_solver).
    assert (ΣC !! c = None) as HCc by (apply not_elem_of_dom; by rewrite HC0).
    assert (ΣC !! d = None) as HCd by (apply not_elem_of_dom; by rewrite HC0).
    assert (ΣC ⊆ Σ1a) as HCsub.
    { apply map_subseteq_spec. intros r x Hx. pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc]; [congruence|].
      destruct (decide (r = d)) as [->|Hrd]; [congruence|].
      rewrite !lookup_insert_ne in Hr by done.
      rewrite lookup_union, Hx in Hr. destruct (Σ1 !! r) eqn:H1r.
      - exfalso. exact (proj1 (map_disjoint_spec _ _) Hd1 r _ _ H1r Hx).
      - by rewrite (left_id_L None (∪)) in Hr. }
    exists c, d, (Σ1a ∖ ΣC ∪ Σ2), sc, sd, kc, kd. split_and!; try done.
    - apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]]; mpoint.
      all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
    - assert (c ∈ dom Σ1 ∧ d ∈ dom Σ1) as [Hc1 Hd1''].
      { assert (c ∈ dom (Σ1 ∪ ΣC) ∧ d ∈ dom (Σ1 ∪ ΣC)) as [H H'] by
          (rewrite HΣa, !dom_insert_L; clear; set_solver).
        rewrite dom_union_L, HC0 in H, H'. clear -H H' HcC0 HdC0. set_solver. }
      rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc1a Hc1 Hd12. set_solver.
    - assert (c ∈ dom Σ1 ∧ d ∈ dom Σ1) as [Hc1 Hd1''].
      { assert (c ∈ dom (Σ1 ∪ ΣC) ∧ d ∈ dom (Σ1 ∪ ΣC)) as [H H'] by
          (rewrite HΣa, !dom_insert_L; clear; set_solver).
        rewrite dom_union_L, HC0 in H, H'. clear -H H' HcC0 HdC0. set_solver. }
      rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hd1a Hd1'' Hd12. set_solver.
    - eapply (iface_shrink n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok0 HP1 HP2);
        [done|by apply (tstep_giving_size _ _ _ Hst)| | |].
      + by apply map_disjoint_difference_l1.
      + rewrite dom_difference_L. intros r Hr.
        assert (r ∈ dom (Σ1 ∪ ΣC)) as H.
        { rewrite HΣa, !dom_insert_L. clear -Hr. set_solver. }
        rewrite dom_union_L in H. clear -H Hr. set_solver.
      + assert (Σ1a ∖ ΣC ∪ ΣC = Σ1a) as -> ; [|done].
        apply map_eq. intros r. pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
        mpoint. all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
  Qed.
  Lemma wext_fresh_wext W0 N W1 : wext_fresh W0 N W1 → wext W0 W1.
  Proof. by intros [? _]. Qed.

  (** The composite in a larger world, components at level j ≤ n'. *)
  Lemma conn_at_world j W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' E1' E2' :
    j ≤ n' → wext W W' → cut_ok W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' →
    Prel j W' (Σ1' ∪ ΣC1) TA (C1', E1') → Prel j W' (Σ2' ∪ ΣC2) TB (C2', E2') →
    Prel j W' (Σ1' ∪ Σ2') T (C1' ∪ C2' ∪ C0', E1' ⊎ E2').
  Proof.
    intros Hj _ Hok' H1 H2.
    exact (IHo j Hj W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' E1' E2' TA TB Hty Hok' H1 H2).
  Qed.

  (** Q-Tau for an internal step of component 1. *)
  Lemma own_tau q1 :
    proc_step (C1, E1) PTau q1 → q1.1 ## C2 ∪ C0 →
    Ptau_case (Prel n') W Σ T (q1.1 ∪ C2 ∪ C0, q1.2 ⊎ E2).
  Proof.
    intros Hst Hq Hg. simpl in Hg. pose proof Hok as Hok0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst) as [Hc1 _].
    destruct (Hc1 ltac:(rewrite dom_union_L, HC0; clear -Hg Hq; set_solver))
      as (N & W1 & HN & Hfr & HP1').
    destruct (Prel_tau_rename n' (senv_roots (Σ2 ∪ ΣC') ∪ ty_roots TB ∪ ty_roots T) _ W N W1
                _ _ _ eq_refl (proj1 HW') Hfr HN HP1') as (N' & W1' & HN'X & HN' & Hfr' & HP1'').
    exists N', W1'. split_and!; [|done|].
    - pose proof (senv_roots_mono Σ1 (Σ1 ∪ ΣC) ltac:(by apply map_union_subseteq_l)).
      pose proof (senv_roots_mono Σ2 (Σ2 ∪ ΣC') ltac:(by apply map_union_subseteq_l)).
      pose proof (senv_roots_union Σ1 Σ2) as Hsr.
      destruct Hty as [[-> ->]|[-> ->]]; clear -HN'X HN' Hsr H H0; set_solver.
    - pose proof (wext_fresh_wext _ _ _ Hfr') as Hx.
      destruct q1 as [C1' E1']. simpl in *.
      apply (conn_at_world n' W1' Σ1 Σ2 ΣC ΣC' C0 C1' C2 E1' E2 (le_n _) Hx).
      + split; try done; [apply Hx| |clear -Hg Hq; set_solver..].
        intros r x y Hx1 Hy1. destruct (Hcut r x y Hx1 Hy1). split; [|done]. by eapply wext_eq.
      + done.
      + eapply Prel_mono; [apply HW'|done|]. eapply Prel_down; [|exact HP2]. lia.
  Qed.
  (** A cut channel is the only channel both components act on. *)
  Lemma cross_subj F1 F2 e σ1 e' f σ2 f' c :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess σ1) e' → tstep f (LSess σ2) f' → subjs σ1 = {[c]} → subjs σ2 = {[c]} →
    c ∈ C0.
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hs1 Hs2.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply map_disjoint_dom in Hd12.
    destruct (decide (c ∈ C1)) as [Hc1|Hc1].
    - assert (c ∉ C2) as Hc2n by (clear -Hc1 HC12; set_solver).
      rewrite HE2 in HP2. pose proof (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP2 Hst2) as H.
      rewrite Hs2, dom_union_L, HC0' in H.
      specialize (H ltac:(clear -Hc2n; set_solver)). clear -H Hc1 HC1Σ2 HC10. set_solver.
    - rewrite HE1 in HP1. pose proof (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP1 Hst1) as H.
      rewrite Hs1, dom_union_L, HC0 in H. specialize (H ltac:(clear -Hc1; set_solver)).
      destruct (decide (c ∈ C2)) as [Hc2|Hc2]; [clear -H Hc2 HC2Σ1 HC20; set_solver|].
      rewrite HE2 in HP2. pose proof (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP2 Hst2) as H'.
      rewrite Hs2, dom_union_L, HC0' in H'. specialize (H' ltac:(clear -Hc2; set_solver)).
      clear -H H' Hd12. set_solver.
  Qed.

  (** A synchronization of two closes across the cut. *)
  Lemma cross_close F1 F2 e e' f f' c :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess (SClos c)) e' → tstep f (LSess (SClos c)) f' →
    Ptau_case (Prel n') W Σ T (C ∖ {[c]}, F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hg.
    pose proof (cross_subj F1 F2 e _ e' f _ f' c HE1 HE2 Hst1 Hst2 eq_refl eq_refl) as HcC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ c ∉ C2) as [Hc1 Hc2] by (clear -HcC0 HC10 HC20; set_solver).
    assert (proc_step (C1, E1) (PSess (SClos c)) (C1 ∖ sentc (SClos c), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE1; apply PStepSession; [done|simpl; clear -Hc1; set_solver]).
    assert (proc_step (C2, E2) (PSess (SClos c)) (C2 ∖ sentc (SClos c), F2 ⊎ {[+ f' +]}))
      as Hs2 by (rewrite HE2; apply PStepSession; [done|simpl; clear -Hc2; set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hs1) as Hc1'. simpl in Hc1'.
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP2 Hs2) as Hc2'. simpl in Hc2'.
    rewrite difference_empty_L in Hc1', Hc2'.
    destruct Hc1' as (Σ1a & k1 & (s1 & HΣa & _) & Hc1a & HP1').
    destruct Hc2' as (Σ2a & k2 & (s2 & HΣb & _) & Hc2a & HP2').
    assert (Σ1 !! c = None) as H1c by (apply not_elem_of_dom; clear -HΣ1C0 HcC0; set_solver).
    assert (Σ2 !! c = None) as H2c by (apply not_elem_of_dom; clear -HΣ2C0 HcC0; set_solver).
    assert (Σ1a = Σ1 ∪ delete c ΣC) as HE1a.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
      apply not_elem_of_dom in Hc1a.
      destruct (decide (r = c)) as [->|Hrc].
      - rewrite lookup_union, lookup_delete_eq, H1c, Hc1a. done.
      - rewrite lookup_insert_ne in Hr by done. rewrite <-Hr, !lookup_union, lookup_delete_ne by done.
        done. }
    assert (Σ2a = Σ2 ∪ delete c ΣC') as HE2a.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣb) as Hr.
      apply not_elem_of_dom in Hc2a.
      destruct (decide (r = c)) as [->|Hrc].
      - rewrite lookup_union, lookup_delete_eq, H2c, Hc2a. done.
      - rewrite lookup_insert_ne in Hr by done. rewrite <-Hr, !lookup_union, lookup_delete_ne by done.
        done. }
    exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
    assert (C ∖ {[c]} = C1 ∪ C2 ∪ (C0 ∖ {[c]})) as -> by (clear -Hc1 Hc2; set_solver).
    assert (F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = (F1 ⊎ {[+ e' +]}) ⊎ (F2 ⊎ {[+ f' +]})) as ->
      by multiset_solver.
    apply (conn_at_world n' W Σ1 Σ2 (delete c ΣC) (delete c ΣC') (C0 ∖ {[c]}) C1 C2
             _ _ (le_n _) (wext_refl W HW')).
    - split; try done.
      + by apply map_disjoint_delete_r.
      + by apply map_disjoint_delete_r.
      + rewrite dom_delete_L. by rewrite HC0.
      + rewrite dom_delete_L. by rewrite HC0'.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + clear -HC10. set_solver.
      + clear -HC20. set_solver.
    - rewrite <-HE1a. eapply Prel_down; [|exact HP1']. lia.
    - rewrite <-HE2a. eapply Prel_down; [|exact HP2']. lia.
  Qed.
  (** Two closes of one channel inside component 1 need it restricted there. *)
  Lemma own_close_contra F e e' f f' c :
    E1 = F ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SClos c)) e' →
    tstep f (LSess (SClos c)) f' → c ∉ C1 → False.
  Proof.
    intros HE Hst1 Hst2 Hc.
    assert (proc_step (C1, E1) (PSess (SClos c)) (C1 ∖ sentc (SClos c), (F ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
      as Hs by (rewrite HE, <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎));
                apply PStepSession; [done|simpl; clear -Hc; set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hs) as Hc1. simpl in Hc1.
    rewrite difference_empty_L in Hc1.
    destruct Hc1 as (Σ1a & k & _ & Hc1a & HP1').
    assert ((F ⊎ {[+ f +]}) ⊎ {[+ e' +]} = (F ⊎ {[+ e' +]}) ⊎ {[+ f +]}) as Heq by multiset_solver.
    rewrite Heq in HP1'.
    pose proof (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP1' Hst2 ltac:(simpl; clear -Hc; set_solver)) as H.
    simpl in H. clear -H Hc1a. set_solver.
  Qed.

  Lemma dom_ones_send Σv Σe Θe :
    send_split W Σe Θe → dom Σv ## dom Θe →
    dom (tenv_ones (tenv_of Σv ∪ Θe)) = dom Σv ∪ dom Σe.
  Proof.
    intros [Hsub Hsp] Hd. apply set_eq. intros r.
    rewrite elem_of_union, !elem_of_dom. unfold tenv_ones, tenv_of.
    rewrite lookup_omap, lookup_union, lookup_fmap.
    destruct (Σv !! r) as [x|] eqn:Hv; destruct (Θe !! r) as [o|] eqn:Ho; simpl.
    - exfalso. apply (Hd r); by eapply elem_of_dom_2.
    - split; [intros _; left; by eexists|intros; by eexists].
    - pose proof (Hsp r o Ho) as H. destruct o as [e1|e1 e2]; simpl in *.
      + destruct H as (e & He & _). rewrite He. split; [intros _; right; by eexists|by intros; eexists].
      + destruct H as (He & _). rewrite He. split; [by intros [? ?]|]. intros [[? ?]|[? ?]]; done.
    - split; [by intros [? ?]|]. intros [[? ?]|[y Hy]]; [done|].
      exfalso. assert (r ∈ dom Θe) as Hr by (apply Hsub; by eapply elem_of_dom_2).
      apply elem_of_dom in Hr as [? ?]. congruence.
  Qed.
  (** A message from component 1 to component 2 across the cut. *)
  Lemma cross_msg F1 F2 e e' f f' c v :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess (SSend c v)) e' → tstep f (LSess (SRecv c v)) f' →
    Ptau_case (Prel n') W Σ T (C, F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hg.
    pose proof (cross_subj F1 F2 e _ e' f _ f' c HE1 HE2 Hst1 Hst2 eq_refl eq_refl) as HcC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ c ∉ C2) as [Hc1 Hc2] by (clear -HcC0 HC10 HC20; set_solver).
    assert (proc_step (C1, E1) (PSess (SSend c v)) (C1 ∖ sentc (SSend c v), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE1; apply PStepSession; [done|simpl; clear -Hc1; set_solver]).
    assert (proc_step (C2, E2) (PSess (SRecv c v)) (C2 ∖ sentc (SRecv c v), F2 ⊎ {[+ f' +]}))
      as Hs2 by (rewrite HE2; apply PStepSession; [done|simpl; clear -Hc2; set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hs1) as Hc1'. simpl in Hc1'.
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP2 Hs2) as Hc2'. simpl in Hc2'.
    destruct Hc1' as (Σ0 & Σv & mm & U & s & k & Σe & Θe & (s0 & HΣa & Hu) & Hd0v & Hc0 & Hcv
                     & HdΘ & Hsplit & HΘΣ & HV & HP1').
    destruct Hc2' as (Σ2a & mm' & U' & s' & k' & (r0 & HΣb & Hu') & Hc2a & Hcont).
    pose proof (Vrel_fchans _ _ _ _ _ HV) as Hfw.
    unfold tenv_of in Hfw. rewrite dom_union_L, dom_fmap_L in Hfw.
    assert (dom Σe ⊆ dom Θe) as HΣeΘ by apply Hsplit.
    assert (dom Θe ⊆ C1) as HΘC1 by (rewrite HdΘ; clear; set_solver).
    assert (dom Σ1 ∪ C0 = {[c]} ∪ dom Σ0 ∪ dom Σv) as HdΣa.
    { rewrite <-HC0, <-dom_union_L, HΣa, dom_insert_L, dom_union_L. clear. set_solver. }
    assert (dom Σ2 ∪ C0 = {[c]} ∪ dom Σ2a) as HdΣb.
    { rewrite <-HC0', <-dom_union_L, HΣb, dom_insert_L. done. }
    apply map_disjoint_dom in Hd12.
    assert (Σ1 !! c = None) as H1c by (apply not_elem_of_dom; clear -HΣ1C0 HcC0; set_solver).
    assert (Σ2 !! c = None) as H2c by (apply not_elem_of_dom; clear -HΣ2C0 HcC0; set_solver).
    (* the cut at c *)
    assert (ΣC !! c = Some (s0, k)) as HCc.
    { pose proof (f_equal (lookup c) HΣa) as H. rewrite lookup_insert_eq, lookup_union, H1c in H.
      by rewrite (left_id_L None (∪)) in H. }
    assert (ΣC' !! c = Some (r0, k')) as HC'c.
    { pose proof (f_equal (lookup c) HΣb) as H. rewrite lookup_insert_eq, lookup_union, H2c in H.
      by rewrite (left_id_L None (∪)) in H. }
    destruct (Hcut c _ _ HCc HC'c) as [Hkk Hdu]. simpl in Hkk, Hdu.
    destruct (sdual_snd_inv s0 r0 mm U s Hdu Hu) as (U2 & r' & Hr0 & HUU & Hss).
    rewrite Hu' in Hr0. injection Hr0 as <- <- <-.
    set (Θ2 := tenv_of Σv ∪ Θe).
    set (Σr2 := <[c := (s', pt_shift 1 k')]> Σ2a).
    assert (dom Σv ## dom Θe) as HvΘ by (clear -HdΣa HΘC1 HC1Σ1 HC10; set_solver).
    pose proof (dom_ones_send Σv Σe Θe Hsplit HvΘ) as HDo. fold Θ2 in HDo.
    assert (dom Θ2 = dom Σv ∪ dom Θe) as HDΘ2.
    { subst Θ2. unfold tenv_of. by rewrite dom_union_L, dom_fmap_L. }
    assert (dom Σr2 = dom Σ2 ∪ C0) as HDr2.
    { subst Σr2. rewrite dom_insert_L, HdΣb. done. }
    assert (recv_ok W Σr2 Θ2) as Hrok.
    { destruct Hsplit as [Hsub Hsp]. split_and!.
      - intros r e1 e2 H1 H2.
        assert (r ∈ dom Σv ∪ dom Σe) as Hr by (rewrite <-HDo; by eapply elem_of_dom_2).
        assert (r ∈ dom Σ2 ∪ C0) as Hr2 by (rewrite <-HDr2; by eapply elem_of_dom_2).
        assert (r ∈ dom Σv ∧ r ∈ C0) as [Hrv HrC0]
          by (clear -Hr Hr2 HΣeΘ HΘC1 HC1Σ2 HC10 HdΣa Hd12; set_solver).
        assert (r ≠ c) as Hrc by (intros ->; done).
        apply elem_of_dom in Hrv as [x Hx].
        subst Θ2. unfold tenv_ones, tenv_of in H2. rewrite lookup_omap, lookup_union, lookup_fmap, Hx in H2.
        assert (Θe !! r = None) as HΘr by (apply not_elem_of_dom; clear -Hx HvΘ; apply elem_of_dom_2 in Hx; set_solver).
        rewrite HΘr in H2. simpl in H2. injection H2 as <-.
        assert (ΣC !! r = Some x) as HCr.
        { pose proof (f_equal (lookup r) HΣa) as H. rewrite lookup_insert_ne in H by done.
          rewrite !lookup_union, Hx in H.
          assert (Σ1 !! r = None) as H1r by (apply not_elem_of_dom; clear -HΣ1C0 HrC0; set_solver).
          rewrite H1r, (left_id_L None (∪)) in H. rewrite H.
          destruct (Σ0 !! r) eqn:H0r; [|done]. exfalso. exact (proj1 (map_disjoint_spec _ _) Hd0v r _ _ H0r Hx). }
        assert (ΣC' !! r = Some e1) as HC'r.
        { subst Σr2. rewrite lookup_insert_ne in H1 by done.
          pose proof (f_equal (lookup r) HΣb) as H. rewrite lookup_insert_ne, H1 in H by done.
          assert (Σ2 !! r = None) as H2r by (apply not_elem_of_dom; clear -HΣ2C0 HrC0; set_solver).
          by rewrite lookup_union, H2r, (left_id_L None (∪)) in H. }
        destruct (Hcut r x e1 HCr HC'r) as [Hq Hd]. split; [|by apply sdual_sym].
        by apply (wf_eq_sym _ (proj1 HW')).
      - intros r e1 e2 H. subst Θ2. unfold tenv_of in H. rewrite lookup_union, lookup_fmap in H.
        destruct (Σv !! r) eqn:?, (Θe !! r) as [o|] eqn:HΘr; simpl in H; simplify_eq; try done.
        pose proof (Hsp r _ HΘr) as Hb.
        rewrite (left_id_L None (∪)) in H. injection H as ->. simpl in Hb.
        destruct Hb as (_ & ? & ?). done.
      - rewrite HDr2, HDo, HDΘ2. clear -HΣeΘ HΘC1 HC1Σ2 HC10. set_solver. }
    assert (Vrel n' W Θ2 (payload_at mm' U' k') v) as HV'.
    { eapply Vrel_payload; [apply HW'|exact Hkk|]. eapply Vrel_teq; [by apply teq_ty_inst|].
      eapply Vrel_down; [|exact HV]. lia. }
    pose proof (Hcont W n' Θ2 (wext_refl W HW') (le_n _)
                  ltac:(rewrite HDΘ2; clear -HdΣa HΘC1 HC12 HC2Σ1 HC20; set_solver) Hrok HV') as HP2'.
    fold Σr2 in HP2'. cbn [fst snd sentc] in HP2'. rewrite difference_empty_L in HP2'.
    set (O := tenv_ones Θe).
    assert (∀ r, tenv_ones Θ2 !! r = match Σv !! r with Some x => Some x | None => O !! r end)
      as Hones.
    { intros r. subst Θ2 O. unfold tenv_ones, tenv_of.
      rewrite !lookup_omap, lookup_union, lookup_fmap. by destruct (Σv !! r), (Θe !! r). }
    assert (dom O = dom Σe) as HDO.
    { apply set_eq. intros r. split; intros Hr.
      - assert (r ∈ dom (tenv_ones Θ2)) as H.
        { apply elem_of_dom. rewrite Hones. apply elem_of_dom in Hr as [x Hx]. rewrite Hx.
          destruct (Σv !! r); by eexists. }
        rewrite HDo in H. apply elem_of_union in H as [H|H]; [|done]. exfalso.
        assert (r ∈ dom Θe) as Hr'.
        { subst O. apply elem_of_dom in Hr as [x Hx]. unfold tenv_ones in Hx.
          rewrite lookup_omap in Hx. apply elem_of_dom. destruct (Θe !! r); [by eexists|done]. }
        clear -H Hr' HvΘ. set_solver.
      - assert (r ∈ dom (tenv_ones Θ2)) as H by (rewrite HDo; clear -Hr; set_solver).
        apply elem_of_dom in H as [x Hx]. rewrite Hones in Hx.
        assert (Σv !! r = None) as Hv.
        { apply not_elem_of_dom. clear -Hr HΣeΘ HvΘ. set_solver. }
        rewrite Hv in Hx. by eapply elem_of_dom_2. }
    set (B2 := recv_back Σr2 Θ2).
    assert (B2 = (dom Σv ∩ C0) ∪ (dom Θe ∖ dom Σe)) as HB2.
    { subst B2. unfold recv_back. rewrite HDΘ2, HDr2, HDo.
      clear -HvΘ HΣeΘ HΘC1 HC1Σ2 HC10 Hd12 HdΣa. set_solver. }
    set (Σ1n := Σ0 ∖ ΣC). set (ΣC1n := <[c := (s, pt_shift 1 k)]> ((Σ0 ∩ ΣC) ∪ Σe)).
    set (Σ2n := Σ2 ∪ (Σv ∖ ΣC)). set (ΣC2n := recv_env Σr2 Θ2 ∖ Σ2n).
    assert (dom Σ0 ⊆ dom Σ1 ∪ C0) as H0a by (clear -HdΣa; set_solver).
    assert (dom Σv ⊆ dom Σ1 ∪ C0) as Hva by (clear -HdΣa; set_solver).
    assert (dom Σe ⊆ C1) as He1 by (clear -HΣeΘ HΘC1; set_solver).
    assert (O ##ₘ Σ0) as HO0.
    { apply map_disjoint_dom. rewrite HDO. clear -He1 H0a HC1Σ1 HC10. set_solver. }
    assert (O ##ₘ Σv) as HOv.
    { apply map_disjoint_dom. rewrite HDO. clear -HΣeΘ HvΘ. set_solver. }
    assert (O ##ₘ Σ2) as HO2.
    { apply map_disjoint_dom. rewrite HDO. clear -He1 HC1Σ2. set_solver. }
    assert (O ##ₘ Σ2a) as HO2a.
    { apply map_disjoint_dom. rewrite HDO. assert (dom Σ2a ⊆ dom Σ2 ∪ C0) by (clear -HdΣb; set_solver).
      clear -He1 HC1Σ2 HC10 H. set_solver. }
    assert (Σv ##ₘ Σ2) as Hv2.
    { apply map_disjoint_dom. clear -Hva Hd12 HΣ2C0. set_solver. }
    exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
    assert (Σ1 ∪ Σ2 = Σ1n ∪ Σ2n) as ->.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
      subst Σ1n Σ2n. destruct (decide (r = c)) as [->|Hrc]; mpoint. }
    assert (C = (C1 ∖ fchans v) ∪ (C2 ∪ B2) ∪ ((C0 ∖ dom Σv) ∪ dom Σe)) as ->.
    { assert (C1 = (C1 ∖ fchans v) ∪ dom Σe ∪ (dom Θe ∖ dom Σe)) as HC1e.
      { clear -HΣeΘ HdΘ. apply set_eq. intros x.
        destruct (decide (x ∈ fchans v)), (decide (x ∈ dom Σe)); set_solver. }
      assert (dom Σv ∩ C1 = ∅) as Hv1 by (clear -Hva HC1Σ1 HC10; set_solver).
      assert (fchans v ∩ C0 = dom Σv ∩ C0) as Hf0 by (rewrite Hfw; clear -HΘC1 HC10; set_solver).
      assert (fchans v ∩ C2 = ∅) as Hf2.
      { rewrite Hfw. clear -Hva HΘC1 HC12 HC2Σ1 HC20. set_solver. }
      rewrite HB2. apply set_eq. intros x. split.
      - intros Hx. rewrite HC1e in Hx. clear -Hx.
        destruct (decide (x ∈ dom Σv)); set_solver.
      - intros Hx. clear -Hx HΣeΘ HΘC1. set_solver. }
    assert (F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = (F1 ⊎ {[+ e' +]}) ⊎ (F2 ⊎ {[+ f' +]})) as ->
      by multiset_solver.
    assert (Σ2n ⊆ recv_env Σr2 Θ2) as Hsub2.
    { apply map_subseteq_spec. intros r x Hx. subst Σ2n.
      pose proof (f_equal (lookup r) HΣb) as Hr. pose proof (Hones r) as Ho.
      assert (ΣC' !! r = None ∨ is_Some (ΣC !! r)) as HCC.
      { destruct (ΣC' !! r) eqn:Hq; [right|by left]. apply elem_of_dom. rewrite HC0, <-HC0'.
        by eapply elem_of_dom_2. }
      unfold recv_env. subst Σr2. destruct (decide (r = c)) as [->|Hrc]; mpoint.
      all: destruct HCC as [?|[? ?]]; congruence. }
    apply (conn_at_world n' W Σ1n Σ2n ΣC1n ΣC2n _ _ _ _ _ (le_n _) (wext_refl W HW')).
    - assert (dom Σ1n = dom Σ0 ∖ C0) as HD1 by (subst Σ1n; by rewrite dom_difference_L, HC0).
      assert (dom Σ2n = dom Σ2 ∪ (dom Σv ∖ C0)) as HD2.
      { subst Σ2n. by rewrite dom_union_L, dom_difference_L, HC0. }
      assert (dom ΣC1n = {[c]} ∪ (dom Σ0 ∩ C0) ∪ dom Σe) as HD3.
      { subst ΣC1n. rewrite dom_insert_L, dom_union_L, dom_intersection_L, HC0. clear. set_solver. }
      assert (dom ΣC2n = (((dom Σ2 ∪ C0) ∖ (dom Σv ∪ dom Σe)) ∪ ((dom Σv ∪ dom Σe) ∖ (dom Σ2 ∪ C0)))
                         ∖ (dom Σ2 ∪ (dom Σv ∖ C0))) as HD4.
      { subst ΣC2n. rewrite dom_difference_L, HD2. unfold recv_env.
        rewrite dom_union_L, !dom_difference_L, HDr2, HDo. done. }
      apply map_disjoint_dom in Hd0v.
      assert (dom Σe ## dom Σv) as Hev by (clear -HΣeΘ HvΘ; set_solver).
      split; [done| | | | | | | | | | | | |].
      + apply map_disjoint_dom. rewrite HD1, HD3. clear -HcC0 He1 H0a HC1Σ1 HC10. set_solver.
      + subst ΣC2n. by apply map_disjoint_difference_r1.
      + apply map_disjoint_dom. rewrite HD1, HD2. clear -Hd0v H0a Hd12. set_solver.
      + rewrite HD3. apply set_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
        { clear -HcC0 Hcv. set_solver. }
        destruct (decide (x ∈ dom Σ0)), (decide (x ∈ dom Σv)), (decide (x ∈ C0));
          clear -HdΣa Hd0v Hxc HcC0; set_solver.
      + rewrite HD4. apply set_eq. intros x.
        destruct (decide (x ∈ dom Σ2)), (decide (x ∈ dom Σv)), (decide (x ∈ dom Σe)), (decide (x ∈ C0));
          clear -Hev He1 HC10 HC1Σ2 Hd12 Hva HΣ2C0; set_solver.
      + intros r x y Hx Hy.
        assert (Σ2n !! r = None → ΣC2n !! r = recv_env Σr2 Θ2 !! r) as HC2r.
        { intros H. subst ΣC2n. by rewrite lookup_difference, H. }
        assert (∀ r, r ∉ dom Σv ∪ dom Σe → tenv_ones Θ2 !! r = None) as Hon.
        { intros r' Hr'. apply not_elem_of_dom. by rewrite HDo. }
        assert (∀ r, r ∉ dom Σ2 ∪ C0 → Σr2 !! r = None) as Hr2n.
        { intros r' Hr'. apply not_elem_of_dom. by rewrite HDr2. }
        assert (∀ r, r ∈ C0 → Σ2n !! r = None) as H2nC0.
        { intros r' Hr'. apply not_elem_of_dom. rewrite HD2. clear -Hr' HΣ2C0. set_solver. }
        destruct (decide (r = c)) as [->|Hrc].
        * subst ΣC1n. rewrite lookup_insert_eq in Hx. injection Hx as <-.
          rewrite HC2r in Hy by (by apply H2nC0). unfold recv_env in Hy.
          rewrite lookup_union, !lookup_difference, Hon in Hy by (clear -Hcv He1 HC10 HcC0; set_solver).
          subst Σr2. rewrite lookup_insert_eq in Hy. simpl in Hy.
          rewrite (right_id_L None (∪)) in Hy. injection Hy as <-. simpl.
          split; [by apply (wf_eq_shift _ (proj1 HW'))|done].
        * subst ΣC1n. rewrite lookup_insert_ne in Hx by done.
          apply lookup_union_Some_raw in Hx as [Hx|[Hx0 Hx]].
          -- apply lookup_intersection_Some in Hx as [Hx [x' HCr]].
             assert (r ∈ C0) as HrC0 by (rewrite <-HC0; by eapply elem_of_dom_2).
             assert (r ∉ dom Σv) as Hrv.
             { intros Hin. apply (Hd0v r); [by eapply elem_of_dom_2|done]. }
             assert (x' = x) as ->.
             { pose proof (f_equal (lookup r) HΣa) as H. rewrite lookup_insert_ne in H by done.
               assert (Σ1 !! r = None) as H1r by (apply not_elem_of_dom; clear -HΣ1C0 HrC0; set_solver).
               rewrite !lookup_union, H1r, HCr, Hx in H. simpl in H.
               rewrite (left_id_L None (∪)), union_Some_l in H. by injection H. }
             rewrite HC2r in Hy by (by apply H2nC0). unfold recv_env in Hy.
             rewrite lookup_union, !lookup_difference, Hon in Hy by (clear -Hrv He1 HC10 HrC0; set_solver).
             subst Σr2. rewrite lookup_insert_ne in Hy by done.
             assert (ΣC' !! r = Σ2a !! r) as HC'r.
             { pose proof (f_equal (lookup r) HΣb) as H. rewrite lookup_insert_ne in H by done.
               assert (Σ2 !! r = None) as H2r by (apply not_elem_of_dom; clear -HΣ2C0 HrC0; set_solver).
               by rewrite lookup_union, H2r, (left_id_L None (∪)) in H. }
             rewrite <-HC'r in Hy. destruct (ΣC' !! r) as [y'|] eqn:Hy'; [|by destruct (ΣC' !! r)]. rewrite union_Some_l in Hy. injection Hy as <-. by apply (Hcut r).
          -- assert (r ∈ dom Σe) as Hre by (by eapply elem_of_dom_2).
             assert (r ∉ dom Σv ∧ r ∉ dom Σ2 ∪ C0) as [Hrv Hr2]
               by (clear -Hre Hev He1 HC1Σ2 HC10; set_solver).
             rewrite HC2r in Hy.
             2: { apply not_elem_of_dom. rewrite HD2. clear -Hrv Hr2. set_solver. }
             assert (recv_env Σr2 Θ2 !! r = tenv_ones Θ2 !! r) as Hre'.
             { unfold recv_env. rewrite lookup_union, !lookup_difference, Hr2n by done.
               by destruct (tenv_ones Θ2 !! r). }
             rewrite Hre', Hones in Hy.
             apply not_elem_of_dom in Hrv. rewrite Hrv in Hy. subst O.
             unfold tenv_ones in Hy. rewrite lookup_omap in Hy.
             destruct (Θe !! r) as [o|] eqn:HΘr; [|done].
             destruct Hsplit as [_ Hsp]. pose proof (Hsp r o HΘr) as Hb.
             destruct o as [e1|e1 e2]; simpl in Hy; [|done]. injection Hy as <-.
             destruct Hb as (e0 & He0 & Hq & Hd). rewrite He0 in Hx. injection Hx as <-. done.
      + rewrite HD2. clear -HC1Σ2 Hva HC1Σ1 HC10. set_solver.
      + rewrite HD1, HB2. clear -HC2Σ1 H0a HC20 Hd0v HΘC1 HC1Σ1 HC10. set_solver.
      + rewrite HD1. clear -HC1Σ1 H0a HC10. set_solver.
      + rewrite HD2, HB2. clear -HC2Σ2 HC2Σ1 Hva HC20 HΣ2C0 HΘC1 HC1Σ2 HC1Σ1 HC10. set_solver.
      + clear -HΣeΘ HdΘ HC10. set_solver.
      + rewrite HB2. clear -HC20 He1 HC12 HΘC1 HC10 HvΘ. set_solver.
      + rewrite HB2, Hfw. clear -HC12 Hva HC1Σ1 HC10. set_solver.
    - assert (Σ1n ∪ ΣC1n = <[c:=(s, pt_shift 1 k)]> (Σ0 ∪ Σe)) as ->.
      { assert (Σe ##ₘ Σ0) as He0.
        { apply map_disjoint_dom. clear -He1 H0a HC1Σ1 HC10. set_solver. }
        apply map_eq. intros r. subst Σ1n ΣC1n.
        destruct (decide (r = c)) as [->|Hrc]; mpoint. }
      eapply Prel_down; [|exact HP1']. lia.
    - assert (Σ2n ∪ ΣC2n = recv_env Σr2 Θ2) as -> by (subst ΣC2n; by apply map_difference_union).
      exact HP2'.
  Qed.
End steps2.
