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
End steps2.
