(** * P-Connect for the live relation (composition/ConnectCut.v, ConnectSteps.v, PConnect.v)

    Two components P-related at their own worlds compose over a cut C₀,
    and components at n give the composite at n. A synchronization on a
    cut channel is a send of one component and a receive of the other,
    each at cost one, in parallel, so the composite's cost two leaves
    room for one downward closure. β, new and spawn of a component stay
    at the index: the proof inducts on the τ layers of both components,
    and the composite world lies above both base worlds (liveness.md
    §4). The configuration lemmas are reused from ConnectCut.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveInternalize composition.PConnect.

Local Set Warnings "-register-all".
Implicit Types W : world.

Lemma LPrel_S_stop_prim n W Σ T p :
  LPrel (S n) W Σ T p → prim T → pirred p →
  Σ = ∅ ∧ ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ LVrel (S n) W ∅ T v ∧
                 (∀ e, e ∈ E → e = EUnit).
Proof.
  intros HP HT Hirr. destruct (LPrel_S_irred _ _ _ _ _ HP Hirr) as (v & E & -> & Hv & HV & HE).
  pose proof (LVrel_prim_empty _ _ _ _ _ HT HV) as H0. rewrite H0 in HV.
  split; [by apply tenv_of_empty_inv|]. by exists v, E.
Qed.

Lemma LPrel_S_ready_prim n W Σ T p : LPrel (S n) W Σ T p → prim T → ready_p W Σ p.
Proof.
  intros HP HT. destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - destruct (LPrel_S_stop_prim _ _ _ _ _ HP HT Hirr) as (-> & v & E & -> & Hv & _ & HE).
    intros _. right. split.
    + intros _. exists v, E. done.
    + intros k e He. exfalso. unfold tenv_entry, tenv_of in He.
      rewrite lookup_fmap, lookup_empty in He. by destruct k.2.
  - eapply LPrel_S_ready; [exact HP|]. intros Hirr. by apply (Hirr π p').
Qed.

(** The goal at level n. *)
Definition lconn_at (n : nat) (T : ty) : Prop :=
  ∀ W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB,
    ctys TA TB T → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    LPrel n W (Σ1 ∪ ΣC) TA (C1, E1) → LPrel n W (Σ2 ∪ ΣC') TB (C2, E2) →
    LPrel n W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).

Section lstop_ready.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan) (E1 E2 : gmultiset expr).
  Context (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : LPrel (S n') W (Σ1 ∪ ΣC) T (C1, E1)).
  Context (HP2 : LPrel (S n') W (Σ2 ∪ ΣC') TUnit (C2, E2)).

  Lemma lc_conn_ready : ready_p W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
  Proof.
    destruct Hok as [lc_HW Hd1 Hd2 Hd12 HC0 HC0' Hcut H1 H2 _ _ _ _ _].
    apply (ready_connect W W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 lc_HW Hd1 Hd2 Hd12 HC0 HC0'
             Hcut H2 H1 (λ _ _ _ _ _ _ H, H) (λ _ _ _ _ _ _ H, H)
             (LPrel_S_ready_prim _ _ _ _ _ HP1 HT) (LPrel_S_ready_prim _ _ _ _ _ HP2 prim_unit)).
    intros Ht e He. destruct (LPrel_S_stop_prim _ _ _ _ _ HP2 prim_unit (terminated_pirred _ Ht))
        as (_ & v & U & [= _ ->] & _ & HV & HU).
      apply LVrel_unit_iff in HV as [_ ->].
      apply gmultiset_elem_of_disj_union in He as [He|He]; [|by apply HU].
      by apply gmultiset_elem_of_singleton in He.
  Qed.

  Lemma lc_conn_stop : pirred (C1 ∪ C2 ∪ C0, E1 ⊎ E2) →
    ∃ v E, (C1 ∪ C2 ∪ C0, E1 ⊎ E2) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
           LVrel (S n') W (tenv_of (Σ1 ∪ Σ2)) T v ∧ (∀ e, e ∈ E → e = EUnit).
  Proof.
    intros Hirr.
    destruct (lc_conn_ready (λ p' Hp', Hirr _ _ Hp')) as [(cd & q & Hq)|[Ht _]];
      [by destruct (Hirr _ _ Hq)|].
    assert (∀ k, ¬ offered_p (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) k) as Hno.
    { intros k (σ & q & Hq & _). exact (Hirr _ _ Hq). }
    destruct (Ht Hno) as (v & U & Heq & Hv & HU).
    injection Heq as HC HE.
    assert (C1 = ∅ ∧ C2 = ∅ ∧ C0 = ∅) as (-> & -> & ->) by (clear -HC; set_solver).
    assert (∀ e, e ∈ E1 ⊎ E2 → is_val e) as Hvals.
    { intros e. rewrite HE. intros [He|He]%gmultiset_elem_of_disj_union.
      - apply gmultiset_elem_of_singleton in He. by subst.
      - rewrite (HU e He). constructor. }
    destruct (LPrel_S_stop_prim _ _ _ _ _ HP1 HT) as (H1 & v1 & U1 & [= HE1] & Hv1 & HV1 & HU1).
    { apply vals_pirred. intros e He. apply Hvals. multiset_solver. }
    destruct (LPrel_S_stop_prim _ _ _ _ _ HP2 prim_unit) as (H2 & v2 & U2 & [= HE2] & _ & HV2 & HU2).
    { apply vals_pirred. intros e He. apply Hvals. multiset_solver. }
    apply LVrel_unit_iff in HV2 as [_ ->].
    assert (Σ1 = ∅ ∧ Σ2 = ∅) as [-> ->].
    { split; [exact (map_positive_l _ _ H1)|exact (map_positive_l _ _ H2)]. }
    exists v1, (U1 ⊎ ({[+ EUnit +]} ⊎ U2)). split_and!.
    - rewrite HE1, HE2. apply pair_equal_spec. split; [set_solver|multiset_solver].
    - done.
    - rewrite (left_id_L ∅ (∪)). unfold tenv_of. rewrite fmap_empty. done.
    - intros e [He|[He|He]%gmultiset_elem_of_disj_union]%gmultiset_elem_of_disj_union;
        [by apply HU1|by apply gmultiset_elem_of_singleton in He|by apply HU2].
  Qed.
End lstop_ready.

Section lsteps1.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → lconn_at j T).
Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA TB : ty).
  Context (Hty : ctys TA TB T)
    (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : LPrel (S n') W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2 : LPrel (S n') W (Σ2 ∪ ΣC') TB (C2, E2)).
  Context (HP1n : LPrel n' W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2n : LPrel n' W (Σ2 ∪ ΣC') TB (C2, E2)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).

  Lemma lc_HW : strict W.
  Proof. apply Hok. Qed.
  Lemma lc_HWf : world_wf W.
  Proof. apply lc_HW. Qed.

  Lemma lc_Σ2C : Σ2 ##ₘ ΣC.
  Proof.
    apply map_disjoint_dom. rewrite (co_dom _ _ _ _ _ _ _ _ Hok).
    apply (co_Σ2C0 _ _ _ _ _ _ _ _ Hok).
  Qed.
  Lemma lc_Σ1C' : Σ1 ##ₘ ΣC'.
  Proof.
    apply map_disjoint_dom. rewrite (co_dom' _ _ _ _ _ _ _ _ Hok).
    apply (co_Σ1C0 _ _ _ _ _ _ _ _ Hok).
  Qed.

  (** Q-Send for a send of component 1 on an interface channel. *)
  Lemma lc_ext_send F1 e c w e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SSend c w)) e' → c ∉ C →
    Psend_case (LVrel n') (LPrel n') W Σ T (C, E1 ⊎ E2) c w
      (C ∖ fchans w, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof lc_Σ2C as H2C. pose proof lc_Σ1C' as H1C'.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SSend c w)) (C1 ∖ fchans w, F1 ⊎ {[+ e' +]})) as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SSend c w) e' Hst). simpl. clear -Hc. set_solver. }
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst1) as Hc1. simpl in Hc1.
    destruct Hc1 as (Σ0 & Σv & mm & U & s & k & Σe & Θe & (s0 & HΣa & Hu) & Hd0v & Hc0 & Hcv
                     & HdΘ & Hsplit & HΘΣ & HV & HP1').
    pose proof (LVrel_fchans _ _ _ _ _ HV) as Hfw.
    unfold tenv_of in Hfw. rewrite dom_union_L, dom_fmap_L in Hfw.
    assert (dom Σe ⊆ dom Θe) as HΣeΘ by apply Hsplit.
    assert (c ∈ dom Σ1) as HcΣ1.
    { assert (c ∈ dom (Σ1 ∪ ΣC)) as H by (rewrite HΣa, dom_insert_L; clear; set_solver).
      rewrite dom_union_L, HC0 in H. clear -H Hc. set_solver. }
    assert (dom (Σ1 ∪ ΣC) = {[c]} ∪ dom Σ0 ∪ dom Σv) as HdΣa
      by (rewrite HΣa, dom_insert_L, dom_union_L; clear; set_solver).
    rewrite dom_union_L, HC0 in HdΣa, HΘΣ.
    assert (dom Θe ⊆ C1) as HΘC1 by (rewrite HdΘ; clear; set_solver).
    set (Σv' := Σv ∖ ΣC). set (Σvc := Σv ∩ ΣC).
    exists ((Σ0 ∖ ΣC) ∪ Σ2), Σv', mm, U, s, k, (Σe ∪ (ΣC' ∩ Σv)), (Θe ∪ tenv_of Σvc).
    split_and!.
    - exists s0. split; [|done]. apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc].
      + rewrite lookup_insert_eq in Hr |- *. mpoint.
      + rewrite lookup_insert_ne in Hr |- * by done. subst Σv'. mpoint.
    - apply map_disjoint_spec. intros r x y Hx Hy. subst Σv'.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc];
        [rewrite lookup_insert_eq in Hr|rewrite lookup_insert_ne in Hr by done]; mpoint.
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc0 HcΣ1 Hd12. set_solver.
    - subst Σv'. rewrite dom_difference_L. clear -Hcv. set_solver.
    - simpl. subst Σvc. unfold tenv_of. rewrite dom_union_L, dom_fmap_L, dom_intersection_L, HC0, Hfw.
      clear -HdΣa HΘC1 HC1Σ1 HC10 HC12 HC2Σ1 HC20 HdΘ. set_solver.
    - split.
      + subst Σvc. unfold tenv_of. rewrite !dom_union_L, dom_fmap_L, !dom_intersection_L, HC0, HC0'.
        clear -HΣeΘ. set_solver.
      + intros r o Hro. subst Σvc. unfold tenv_of in Hro. rewrite lookup_union, lookup_fmap in Hro.
        destruct (Θe !! r) as [o'|] eqn:HΘr.
        * rewrite union_Some_l in Hro. injection Hro as <-. destruct Hsplit as [_ Hsp].
          pose proof (Hsp r o' HΘr) as H. assert (r ∈ C1) as HrC1 by (apply HΘC1; by eapply elem_of_dom_2).
          assert (ΣC' !! r = None) as HrC'.
          { apply not_elem_of_dom. rewrite HC0'. clear -HrC1 HC10. set_solver. }
          rewrite lookup_union, lookup_intersection, HrC'. simpl.
          destruct o' as [e1|e1 e2]; [destruct H as (e0 & -> & ?); by exists e0|].
          destruct H as (-> & ?). done.
        * pose proof (f_equal (lookup r) HΣa) as Hr.
          destruct (decide (r = c)) as [->|Hrc].
          { assert (ΣC !! c = None) as HCc.
            { apply not_elem_of_dom. rewrite HC0. clear -Hc. set_solver. }
            exfalso. rewrite lookup_intersection, HCc in Hro. mpoint. }
          rewrite lookup_insert_ne in Hr by done. rewrite lookup_intersection in Hro.
          destruct (Σv !! r) as [x|] eqn:Hvr; [|done]. destruct (ΣC !! r) as [x'|] eqn:HCr; [|done].
          simpl in Hro. injection Hro as <-.
          assert (r ∈ C0) as HrC0 by (rewrite <-HC0; by eapply elem_of_dom_2).
          assert (Σ1 !! r = None) as HΣ1r.
          { apply not_elem_of_dom. clear -HΣ1C0 HrC0. set_solver. }
          assert (x' = x) as ->.
          { rewrite lookup_union, HΣ1r, HCr, lookup_union, Hvr in Hr. simpl in Hr.
            destruct (Σ0 !! r) eqn:H0r; simpl in Hr; [|by injection Hr].
            exfalso. by apply (proj1 (map_disjoint_spec _ _) Hd0v r _ _ H0r Hvr). }
          assert (is_Some (ΣC' !! r)) as [y Hy] by (apply elem_of_dom; by rewrite HC0').
          assert (Σe !! r = None) as HΣer.
          { apply not_elem_of_dom. intros Hin. apply HΣeΘ, HΘC1 in Hin.
            clear -Hin HrC0 HC10. set_solver. }
          exists y. rewrite lookup_union, HΣer, lookup_intersection, Hy, Hvr. simpl.
          destruct (Hcut r x y HCr Hy) as [Hq Hd]. split_and!; [done| |by apply sdual_sym].
          by apply (wf_eq_dual_sym _ _ _ (proj1 HW')).
    - subst Σvc. unfold tenv_of. rewrite dom_union_L, dom_fmap_L, dom_intersection_L, dom_union_L, HC0.
      apply map_disjoint_dom in Hd12. clear -HΘC1 HC1Σ1 HC1Σ2 Hd12 HC10 HdΣa HΣ1C0 HΣ2C0. set_solver.
    - assert (tenv_of Σv' ∪ (Θe ∪ tenv_of Σvc) = tenv_of Σv ∪ Θe) as ->; [|done].
      assert (dom Θe ## dom Σv) as HΘv by (clear -HΘΣ HdΣa; set_solver).
      apply map_eq. intros r. subst Σv' Σvc. unfold tenv_of. mpoint.
    - set (Σ1' := <[c := (s, pt_shift 1 k)]> ((Σ0 ∖ ΣC) ∪ Σe)).
      set (Σ2' := Σ2 ∪ (ΣC' ∩ Σv)).
      assert (<[c:=(s, pt_shift 1 k)]> (Σ0 ∖ ΣC ∪ Σ2 ∪ (Σe ∪ ΣC' ∩ Σv)) = Σ1' ∪ Σ2') as ->.
      { apply map_eq. intros r. subst Σ1' Σ2'.
        destruct (decide (r = c)) as [->|Hrc]; [by rewrite lookup_union, !lookup_insert_eq, union_Some_l|].
        rewrite lookup_union, !lookup_insert_ne by done.
        assert (dom Σe ## dom Σ2) as HeΣ2 by (clear -HΣeΘ HΘC1 HC1Σ2; set_solver).
        assert (dom Σe ## dom ΣC') as HeC' by (rewrite HC0'; clear -HΣeΘ HΘC1 HC10; set_solver).
        mpoint. }
      assert (C ∖ fchans w = (C1 ∖ fchans w) ∪ C2 ∪ (C0 ∖ dom Σv)) as ->.
      { rewrite Hfw. clear -HdΣa HΘC1 HC12 HC20 HC2Σ1 HC10. set_solver. }
      assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
      apply (IHo n' (le_n _) W Σ1' Σ2' (Σ0 ∩ ΣC) (ΣC' ∖ Σv) _ _ _ _ _ TA TB); [done| | |].
      + assert (c ∉ C0) as HcC0 by (clear -Hc; set_solver).
        apply map_disjoint_dom in Hd12, Hd0v.
        assert (dom Σ1' = {[c]} ∪ ((dom Σ0 ∖ C0) ∪ dom Σe)) as HD1.
        { subst Σ1'. by rewrite dom_insert_L, dom_union_L, dom_difference_L, HC0. }
        assert (dom Σ2' = dom Σ2 ∪ (C0 ∩ dom Σv)) as HD2.
        { subst Σ2'. by rewrite dom_union_L, dom_intersection_L, HC0'. }
        assert (dom (Σ0 ∩ ΣC) = C0 ∖ dom Σv) as HD3.
        { rewrite dom_intersection_L, HC0. clear -HdΣa Hd0v HcC0. set_solver. }
        assert (dom (ΣC' ∖ Σv) = C0 ∖ dom Σv) as HD4.
        { by rewrite dom_difference_L, HC0'. }
        assert (dom Σ0 ⊆ dom Σ1 ∪ C0) as H0a by (clear -HdΣa; set_solver).
        assert (dom Σe ⊆ C1) as He1 by (clear -HΣeΘ HΘC1; set_solver).
        assert (dom Σe ⊆ fchans w) as Hew by (clear -HΣeΘ HdΘ; set_solver).
        split; [done| | | | | | | | | | | | |];
          try (apply map_disjoint_dom); rewrite ?HD1, ?HD2, ?HD3, ?HD4.
        * clear -HcC0 He1 HC10. set_solver.
        * clear -HΣ2C0. set_solver.
        * clear -HcΣ1 Hd12 HcC0 H0a He1 HC1Σ2 HC10 HΣ2C0. set_solver.
        * done.
        * done.
        * intros r x y Hx Hy. apply lookup_intersection_Some in Hx as [Hx _].
          apply lookup_difference_Some in Hy as [Hy Hvr].
          assert (r ∈ C0) as HrC0 by (rewrite <-HC0'; by eapply elem_of_dom_2).
          assert (r ≠ c) as Hrc by (intros ->; done).
          pose proof (f_equal (lookup r) HΣa) as Hr. rewrite lookup_insert_ne in Hr by done.
          assert (Σ1 !! r = None) as HΣ1r.
          { apply not_elem_of_dom. clear -HΣ1C0 HrC0. set_solver. }
          rewrite !lookup_union, HΣ1r, Hx, Hvr in Hr. simpl in Hr.
          destruct (ΣC !! r) eqn:HCr; [|by rewrite union_Some_l in Hr]. simpl in Hr.
          injection Hr as ->. by apply (Hcut r).
        * clear -HC1Σ2 HC10. set_solver.
        * clear -HcΣ1 HC2Σ1 H0a He1 HC12 HC20. set_solver.
        * clear -HcΣ1 HC1Σ1 H0a Hew HC10. set_solver.
        * clear -HC2Σ2 HC20. set_solver.
        * clear -HC10. set_solver.
        * clear -HC20. set_solver.
        * clear -HC12. set_solver.
      + assert (dom Σ0 ## dom Σe) as H0e by (clear -HdΣa HΣeΘ HΘC1 HC1Σ1 HC10; set_solver).
        assert (Σ1' ∪ Σ0 ∩ ΣC = <[c:=(s, pt_shift 1 k)]> (Σ0 ∪ Σe)) as -> ; [|done].
        apply map_eq. intros r. subst Σ1'.
        destruct (decide (r = c)) as [->|Hrc]; [by rewrite lookup_union, !lookup_insert_eq, union_Some_l|].
        rewrite lookup_union, !lookup_insert_ne by done. mpoint.
      + assert (Σ2' ∪ ΣC' ∖ Σv = Σ2 ∪ ΣC') as -> ; [|done].
        apply map_eq. intros r. subst Σ2'. mpoint.
  Qed.
  (** Q-Recv for a receive of component 1 on an interface channel. *)
  Lemma lc_ext_recv F1 e c w e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SRecv c w)) e' → c ∉ C →
    LPobl LVrel LPrel (S n') W Σ T (C, E1 ⊎ E2) (SRecv c w)
      (C ∖ sentc (SRecv c w), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof lc_Σ2C as H2C. pose proof lc_Σ1C' as H1C'.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SRecv c w)) (C1 ∖ sentc (SRecv c w), F1 ⊎ {[+ e' +]}))
      as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SRecv c w) e' Hst). simpl. clear -Hc. set_solver. }
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst1) as Hc1. simpl in Hc1.
    destruct Hc1 as (Σ1a & mm & U & s & k & (s0 & HΣa & Hu) & Hc1a & Hcont).
    assert (c ∈ dom Σ1) as HcΣ1.
    { assert (c ∈ dom (Σ1 ∪ ΣC)) as H by (rewrite HΣa, dom_insert_L; clear; set_solver).
      rewrite dom_union_L, HC0 in H. clear -H Hc. set_solver. }
    assert (c ∉ C0) as HcC0 by (clear -Hc; set_solver).
    assert (ΣC !! c = None) as HCc by (apply not_elem_of_dom; by rewrite HC0).
    assert (Σ2 !! c = None) as H2c.
    { apply not_elem_of_dom. apply map_disjoint_dom in Hd12. clear -Hd12 HcΣ1. set_solver. }
    assert (Σ1a !! c = None) as H1ac by (by apply not_elem_of_dom).
    assert (dom Σ1 ∪ C0 = {[c]} ∪ dom Σ1a) as HdΣa.
    { rewrite <-HC0, <-dom_union_L, HΣa, dom_insert_L. done. }
    exists (Σ1a ∖ ΣC ∪ Σ2), mm, U, s, k. split_and!.
    - exists s0. split; [|done]. apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc].
      + rewrite lookup_insert_eq in Hr |- *. mpoint.
      + rewrite lookup_insert_ne in Hr |- * by done. mpoint.
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc1a HcΣ1 Hd12. set_solver.
    - intros W' j Θ2 HW'' Hj HΘC Hok' HV. simpl in HΘC. cbn [nlower pcost scost pred] in Hj. cbn [fst snd sentc].
      set (Σr1 := <[c := (s, pt_shift 1 k)]> Σ1a).
      set (Σr := <[c := (s, pt_shift 1 k)]> (Σ1a ∖ ΣC ∪ Σ2)) in *.
      set (ones := tenv_ones Θ2).
      assert (strict W') as HW3 by apply HW''.
      assert (dom Σr1 = {[c]} ∪ dom Σ1a) as HDr1 by (subst Σr1; by rewrite dom_insert_L).
      assert (dom Σr = {[c]} ∪ (dom Σ1a ∖ C0) ∪ dom Σ2) as HDr.
      { subst Σr. rewrite dom_insert_L, dom_union_L, dom_difference_L, HC0. set_solver. }
      pose proof (dom_tenv_ones_sub Θ2) as HDo. fold ones in HDo.
      destruct Hok' as (Hdo & Htd & Hb). fold ones in Hdo, Hb.
      assert (recv_ok W' Σr1 Θ2) as Hok1.
      { split_and!; [|done|].
        - intros r e1 e2 H1 H2. apply (Hdo r e1 e2); [|done].
          assert (r ∈ dom Θ2) as HrΘ by (apply HDo; by eapply elem_of_dom_2).
          assert (r ∉ C0) as HrC0 by (clear -HrΘ HΘC; set_solver).
          subst Σr Σr1. destruct (decide (r = c)) as [->|Hrc].
          + rewrite lookup_insert_eq in H1 |- *. done.
          + rewrite lookup_insert_ne in H1 |- * by done.
            assert (ΣC !! r = None) as HCr by (apply not_elem_of_dom; by rewrite HC0).
            by rewrite lookup_union, lookup_difference, HCr, H1, union_Some_l.
        - fold ones. rewrite HDr1. rewrite HDr in Hb. clear -Hb HΘC HDo. set_solver. }
      pose proof (Hcont W' j Θ2 HW'' Hj ltac:(clear -HΘC; set_solver) Hok1 HV) as HP1'.
      fold Σr1 in HP1'. simpl in HP1'. rewrite difference_empty_L in HP1'.
      assert (LPrel j W' (Σ2 ∪ ΣC') TB (C2, E2)) as HP2'.
      { eapply LPrel_mono; [by right|]. eapply LPrel_down; [|exact HP2]. lia. }
      set (ΣCn := ΣC ∪ (ones ∩ Σ2)). set (ΣCn' := ΣC' ∪ (Σ2 ∩ ones)).
      set (Σ1n := recv_env Σr1 Θ2 ∖ ΣCn). set (Σ2n := Σ2 ∖ ones).
      set (D := dom ones ∩ dom Σ2).
      set (B1 := recv_back Σr1 Θ2).
      assert (dom Θ2 ∩ dom Σ2 = D) as HD.
      { subst D. apply dom_ones_inter. rewrite HDr in Hb. clear -Hb. set_solver. }
      assert (dom Σr1 ## dom Σ2) as Hr12.
      { rewrite HDr1. apply map_disjoint_dom in Hd12. clear -HdΣa Hd12 HΣ2C0. set_solver. }
      assert (dom ones ## C0) as HoC0 by (clear -HDo HΘC; set_solver).
      assert (B1 ## dom Σ2) as HB12.
      { subst B1. unfold recv_back. fold ones. rewrite HDr in Hb. clear -Hr12 Hb. set_solver. }
      pose proof (λ r, recv_back_not_env _ _ _ r Hok1) as HB1env. fold B1 in HB1env.
      pose proof (dom_recv_env Σr1 Θ2) as HDre.
      assert (C ∖ ∅ ∪ recv_back Σr Θ2 = (C1 ∪ B1) ∪ C2 ∪ (C0 ∪ D)) as ->.
      { subst B1. unfold recv_back. fold ones. rewrite <-HD, HDr, HDr1.
        clear -HdΣa HΘC. set_solver. }
      assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
      assert (ones ##ₘ ΣC) as HoC by (apply map_disjoint_dom; by rewrite HC0).
      assert (Σr1 ##ₘ Σ2) as Hr12' by (by apply map_disjoint_dom).
      assert (recv_env Σr Θ2 = Σ1n ∪ Σ2n) as ->.
      { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
        subst Σ1n Σ2n ΣCn. unfold recv_env. fold ones.
        destruct (decide (r = c)) as [->|Hrc].
        - subst Σr Σr1. rewrite lookup_insert_eq in Hr.
          rewrite !lookup_union, !lookup_difference, !lookup_insert_eq. mpoint.
        - subst Σr Σr1. rewrite lookup_insert_ne in Hr by done.
          rewrite !lookup_union, !lookup_difference, !lookup_insert_ne by done. mpoint. }
      apply (IHo j Hj W' Σ1n Σ2n ΣCn ΣCn' (C0 ∪ D) (C1 ∪ B1) C2 _ _ TA TB Hty).
      + assert (dom Σ1n ⊆ dom (recv_env Σr1 Θ2)) as HD1n.
        { subst Σ1n. rewrite dom_difference_L. clear. set_solver. }
        assert (dom Σ2n ⊆ dom Σ2) as HD2n.
        { subst Σ2n. rewrite dom_difference_L. clear. set_solver. }
        assert (B1 ⊆ dom Θ2) as HB1Θ by apply recv_back_dom.
        assert (dom Σr1 ⊆ dom Σ1 ∪ C0) as Hr1a by (rewrite HDr1; clear -HdΣa HcΣ1; set_solver).
        assert (dom ΣCn = C0 ∪ D) as HDC.
        { subst ΣCn D. by rewrite dom_union_L, dom_intersection_L, HC0. }
        assert (dom ΣCn' = C0 ∪ D) as HDC'.
        { subst ΣCn' D. rewrite dom_union_L, dom_intersection_L, HC0'. clear. set_solver. }
        split; [done| | | | done | done | | | | | | | |].
        * apply map_disjoint_spec. intros r x y H1 H2. subst Σ1n.
          apply lookup_difference_Some in H1 as [_ H]. congruence.
        * apply map_disjoint_spec. intros r x y H1 H2. subst Σ2n ΣCn'. mpoint.
        * apply map_disjoint_spec. intros r x y H1 H2. subst Σ1n Σ2n ΣCn.
          unfold recv_env in H1. fold ones in H1. mpoint.
        * intros r x y Hx Hy. subst ΣCn ΣCn'.
          apply lookup_union_Some_raw in Hx as [Hx|[HCr Hx]].
          { assert (is_Some (ΣC' !! r)) as [y' Hy'].
            { apply elem_of_dom. rewrite HC0', <-HC0. by eapply elem_of_dom_2. }
            rewrite lookup_union, Hy', union_Some_l in Hy. injection Hy as <-.
            destruct (Hcut r x y' Hx Hy') as [Hq Hdu]. split; [|done].
            by eapply wext_eq. }
          assert (ΣC' !! r = None) as HC'r.
          { apply not_elem_of_dom. rewrite HC0', <-HC0. by apply not_elem_of_dom. }
          rewrite lookup_union, HC'r in Hy. simpl in Hy. rewrite (left_id_L None (∪)) in Hy.
          apply lookup_intersection_Some in Hx as [Hx _].
          apply lookup_intersection_Some in Hy as [Hy _].
          assert (Σr !! r = Some y) as Hry.
          { assert (r ≠ c) as Hrc by (intros ->; congruence).
            subst Σr. rewrite lookup_insert_ne by done.
            assert (Σ1a !! r = None) as H1ar.
            { destruct (Σ1a !! r) as [z|] eqn:Hq; [|done]. exfalso.
              apply (proj1 (map_disjoint_spec _ _) Hr12' r z y); [|done].
              subst Σr1. by rewrite lookup_insert_ne. }
            by rewrite lookup_union, lookup_difference, H1ar, HCr, Hy. }
          destruct (Hdo r y x Hry Hx) as [Hq Hdu]. split; [|by apply sdual_sym].
          by apply (wf_eq_dual_sym _ _ _ (proj1 HW3)).
        * clear -HD2n HC1Σ2 HB12. set_solver.
        * clear -HD1n HDre Hr1a HC2Σ1 HC20 HΘC. set_solver.
        * intros r Hr1 Hr2. apply HD1n in Hr2. apply elem_of_union in Hr1 as [Hr1|Hr1].
          -- apply HDre in Hr2. clear -Hr1 Hr2 Hr1a HC1Σ1 HC10 HΘC. set_solver.
          -- by apply (HB1env r).
        * clear -HD2n HC2Σ2. set_solver.
        * subst D. clear -HC10 HC1Σ2 HB1Θ HΘC HB12. set_solver.
        * subst D. clear -HC20 HC2Σ2. set_solver.
        * clear -HC12 HB1Θ HΘC. set_solver.
      + assert (Σ1n ∪ ΣCn = recv_env Σr1 Θ2) as ->; [|exact HP1'].
        apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
        subst Σ1n ΣCn. unfold recv_env. fold ones.
        destruct (decide (r = c)) as [->|Hrc].
        * subst Σr1. rewrite lookup_insert_eq in Hr.
          rewrite !lookup_union, !lookup_difference, !lookup_insert_eq. mpoint.
        * subst Σr1. rewrite lookup_insert_ne in Hr by done.
          rewrite !lookup_union, !lookup_difference, !lookup_insert_ne by done. mpoint.
      + assert (Σ2n ∪ ΣCn' = Σ2 ∪ ΣC') as ->; [|exact HP2'].
        apply map_eq. intros r. subst Σ2n ΣCn'. mpoint.
  Qed.
  (** Component 1 loses interface entries only (close, link): the
      composite's successor is again a configuration over the same cut. *)
  Lemma lc_iface_shrink Σ1a F1 e e' :
    E1 = F1 ⊎ {[+ e +]} →
    Σ1a ##ₘ ΣC → dom Σ1a ⊆ dom Σ1 →
    LPrel n' W (Σ1a ∪ ΣC) TA (C1, F1 ⊎ {[+ e' +]}) →
    LPrel n' W (Σ1a ∪ Σ2) T (C, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hd Hsub HP1'.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply (IHo n' (le_n _) W Σ1a Σ2 ΣC ΣC' C0 C1 C2 _ _ TA TB); try done.
    - apply map_disjoint_dom in Hd12.
      split; try done; try (apply map_disjoint_dom); clear -Hsub Hd12 HC2Σ1 HC1Σ1; set_solver.
  Qed.

  (** Q-Close for a close of component 1 on an interface channel. *)
  Lemma lc_ext_close F1 e c e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SClos c)) e' → c ∉ C →
    Pclos_case (LPrel n') W Σ T c (C ∖ sentc (SClos c), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SClos c)) (C1 ∖ sentc (SClos c), F1 ⊎ {[+ e' +]}))
      as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SClos c) e' Hst). simpl. clear -Hc. set_solver. }
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst1) as Hc1. simpl in Hc1.
    rewrite difference_empty_L in Hc1. cbn [sentc]. rewrite difference_empty_L.
    destruct Hc1 as (Σ1a & k & (s0 & HΣa & Hu) & Hc1a & HP1').
    assert (c ∉ C0) as HcC0 by (clear -Hc; set_solver).
    assert (ΣC !! c = None) as HCc by (apply not_elem_of_dom; by rewrite HC0).
    assert (ΣC ⊆ Σ1a) as HCsub.
    { apply map_subseteq_spec. intros r x Hx. pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc]; [congruence|].
      rewrite lookup_insert_ne in Hr by done.
      rewrite lookup_union, Hx in Hr. destruct (Σ1 !! r) eqn:H1r.
      - exfalso. exact (proj1 (map_disjoint_spec _ _) Hd1 r _ _ H1r Hx).
      - by rewrite (left_id_L None (∪)) in Hr. }
    exists (Σ1a ∖ ΣC ∪ Σ2), k. split_and!.
    - exists s0. split; [|done]. apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      destruct (decide (r = c)) as [->|Hrc]; mpoint.
      all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
    - assert (c ∈ dom Σ1).
      { assert (c ∈ dom (Σ1 ∪ ΣC)) as H by (rewrite HΣa, dom_insert_L; clear; set_solver).
        rewrite dom_union_L, HC0 in H. clear -H HcC0. set_solver. }
      rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc1a H Hd12. set_solver.
    - eapply lc_iface_shrink; [done| | |].
      + by apply map_disjoint_difference_l1.
      + rewrite dom_difference_L. intros r Hr.
        assert (r ∈ dom (Σ1 ∪ ΣC)) as H.
        { rewrite HΣa, dom_insert_L. clear -Hr. set_solver. }
        rewrite dom_union_L in H. clear -H Hr. set_solver.
      + assert (Σ1a ∖ ΣC ∪ ΣC = Σ1a) as -> ; [|done].
        apply map_eq. intros r. pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
        mpoint. all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
  Qed.

  (** Component 1 keeps its interface at a lower index (branch). *)
  Lemma lc_iface_lower Σ1a F1 e' :
    Σ1a ##ₘ ΣC → dom Σ1a ⊆ dom Σ1 →
    LPrel n' W (Σ1a ∪ ΣC) TA (C1, F1 ⊎ {[+ e' +]}) →
    LPrel n' W (Σ1a ∪ Σ2) T (C, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros Hd Hsub HP1'.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply (IHo n' (le_n _) W Σ1a Σ2 ΣC ΣC' C0 C1 C2 _ _ TA TB); try done.
    - apply map_disjoint_dom in Hd12.
      split; try done; try (apply map_disjoint_dom); clear -Hsub Hd12 HC2Σ1 HC1Σ1; set_solver.
  Qed.

  (** Q-Select and Q-Branch for a choice of component 1 on an interface channel. *)
  Lemma lc_ext_choice F1 e c i e' (bra : bool) :
    E1 = F1 ⊎ {[+ e +]} →
    tstep e (LSess (if bra then SBra c i else SSel c i)) e' → c ∉ C →
    Pchoice_case (LPrel n') W Σ T c i
      (if bra then SWith else SPlus) (if bra then bra_pt else sel_pt) (C, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (if bra then SBra c i else SSel c i))
              (C1, F1 ⊎ {[+ e' +]})) as Hst1.
    { rewrite HE. rewrite <-(difference_empty_L C1) at 2.
      replace (∅ : gset chan) with (sentc (if bra then SBra c i else SSel c i)) by (by destruct bra).
      apply PStepSession; [done|]. destruct bra; simpl; clear -Hc; set_solver. }
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst1) as Hc1.
    assert (Pchoice_case (LPrel n') W (Σ1 ∪ ΣC) TA c i
              (if bra then SWith else SPlus) (if bra then bra_pt else sel_pt) (C1, F1 ⊎ {[+ e' +]})) as Hc1'
      by (destruct bra; exact Hc1).
    clear Hc1. destruct Hc1' as (Σ1a & s1 & s2 & k & (s0 & HΣa & Hu) & Hc1a & HP1').
    assert (c ∉ C0) as HcC0 by (clear -Hc; set_solver).
    assert (ΣC !! c = None) as HCc by (apply not_elem_of_dom; by rewrite HC0).
    assert (ΣC ⊆ Σ1a) as HCsub.
    { apply map_subseteq_spec. intros r x Hx. pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc]; [congruence|].
      rewrite lookup_insert_ne in Hr by done.
      rewrite lookup_union, Hx in Hr. destruct (Σ1 !! r) eqn:H1r.
      - exfalso. exact (proj1 (map_disjoint_spec _ _) Hd1 r _ _ H1r Hx).
      - by rewrite (left_id_L None (∪)) in Hr. }
    assert (c ∈ dom Σ1) as HcΣ1.
    { assert (c ∈ dom (Σ1 ∪ ΣC)) as H by (rewrite HΣa, dom_insert_L; clear; set_solver).
      rewrite dom_union_L, HC0 in H. clear -H HcC0. set_solver. }
    assert (Σ1a ∖ ΣC ∪ ΣC = Σ1a) as HΣre.
    { apply map_eq. intros r. pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      mpoint. all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence). }
    exists (Σ1a ∖ ΣC ∪ Σ2), s1, s2, k. split_and!.
    - exists s0. split; [|done]. apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      destruct (decide (r = c)) as [->|Hrc]; mpoint.
      all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc1a HcΣ1 Hd12. set_solver.
    - rewrite insert_union_l.
      assert (<[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> (Σ1a ∖ ΣC) ##ₘ ΣC) as Hdj.
      { apply map_disjoint_insert_l. split; [done|]. by apply map_disjoint_difference_l1. }
      assert (dom (<[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> (Σ1a ∖ ΣC)) ⊆ dom Σ1) as Hdm.
      { rewrite dom_insert_L, dom_difference_L. intros r Hr.
        apply elem_of_union in Hr as [->%elem_of_singleton|Hr]; [done|].
        assert (r ∈ dom (Σ1 ∪ ΣC)) as H.
        { rewrite HΣa, dom_insert_L. clear -Hr. set_solver. }
        rewrite dom_union_L in H. clear -H Hr. set_solver. }
      assert (<[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> (Σ1a ∖ ΣC) ∪ ΣC =
              <[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> Σ1a) as Hre
        by (by rewrite <-insert_union_l, HΣre).
      destruct bra.
      + apply lc_iface_lower; [done|done|]. by rewrite Hre.
      + eapply lc_iface_shrink; [done|done|done|].
        by rewrite Hre.
  Qed.

  Lemma lc_ext_sel F1 e c i e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SSel c i)) e' → c ∉ C →
    LPobl LVrel LPrel (S n') W Σ T (C, E1 ⊎ E2) (SSel c i)
      (C ∖ sentc (SSel c i), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. cbn [LPobl pred sentc].
    rewrite difference_empty_L. exact (lc_ext_choice F1 e c i e' false HE Hst Hc).
  Qed.

  Lemma lc_ext_bra F1 e c i e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SBra c i)) e' → c ∉ C →
    LPobl LVrel LPrel (S n') W Σ T (C, E1 ⊎ E2) (SBra c i)
      (C ∖ sentc (SBra c i), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. cbn [LPobl pred sentc].
    rewrite difference_empty_L. exact (lc_ext_choice F1 e c i e' true HE Hst Hc).
  Qed.
End lsteps1.

Lemma LPrel_S_comm n W Σ T p p' :
  LPrel (S n) W Σ T p → pcomm p p' → LPtau_case (LPrel (pred n)) W Σ T p'.
Proof.
  intros HP Hst. apply LPrel_S_iff in HP. destruct (HP W (wext_r_refl W)) as (_ & _ & _ & H & _).
  by apply H.
Qed.

Set Default Proof Using "All".
Section lsteps2.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → lconn_at j T).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA TB : ty).
  Context (Hty : ctys TA TB T)
    (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : LPrel (S n') W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2 : LPrel (S n') W (Σ2 ∪ ΣC') TB (C2, E2)).
  Context (HP1n : LPrel n' W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2n : LPrel n' W (Σ2 ∪ ΣC') TB (C2, E2)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).

  Lemma lc2_HW2 : strict W.
  Proof. apply Hok. Qed.


  (** The composite in a larger world, components at level j ≤ n'. *)
  Lemma lc2_conn_at_world j W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' E1' E2' :
    j ≤ n' → wext W W' → cut_ok W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' →
    LPrel j W' (Σ1' ∪ ΣC1) TA (C1', E1') → LPrel j W' (Σ2' ∪ ΣC2) TB (C2', E2') →
    LPrel j W' (Σ1' ∪ Σ2') T (C1' ∪ C2' ∪ C0', E1' ⊎ E2').
  Proof.
    intros Hj _ Hok' H1 H2.
    exact (IHo j Hj W' Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2' E1' E2' TA TB Hty Hok' H1 H2).
  Qed.

  (** Q-Tau for an internal step of component 1. *)
  Lemma lc2_own_comm q1 :
    pcomm (C1, E1) q1 → q1.1 ## C2 ∪ C0 →
    LPtau_case (LPrel (pred n')) W Σ T (q1.1 ∪ C2 ∪ C0, q1.2 ⊎ E2).
  Proof.
    intros Hst Hq Hg. simpl in Hg. pose proof Hok as Hok0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    pose proof (LPrel_S_comm _ _ _ _ _ _ HP1 Hst
                  ltac:(rewrite dom_union_L, HC0; clear -Hg Hq; set_solver)) as HP1'.
    destruct q1 as [C1' E1']. simpl in *.
    apply (lc2_conn_at_world (pred n') W Σ1 Σ2 ΣC ΣC' C0 C1' C2 E1' E2 ltac:(lia) (wext_refl W HW')).
    + split; try done; clear -Hg Hq; set_solver.
    + done.
    + eapply LPrel_down; [|exact HP2]. lia.
  Qed.
  (** A cut channel is the only channel both components act on. *)
  Lemma lc2_cross_subj F1 F2 e σ1 e' f σ2 f' c :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess σ1) e' → tstep f (LSess σ2) f' → subjs σ1 = {[c]} → subjs σ2 = {[c]} →
    c ∈ C0.
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hs1 Hs2.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply map_disjoint_dom in Hd12.
    destruct (decide (c ∈ C1)) as [Hc1|Hc1].
    - assert (c ∉ C2) as Hc2n by (clear -Hc1 HC12; set_solver).
      rewrite HE2 in HP2. pose proof (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP2 Hst2) as H.
      rewrite Hs2, dom_union_L, HC0' in H.
      specialize (H ltac:(clear -Hc2n; set_solver)). clear -H Hc1 HC1Σ2 HC10. set_solver.
    - rewrite HE1 in HP1. pose proof (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP1 Hst1) as H.
      rewrite Hs1, dom_union_L, HC0 in H. specialize (H ltac:(clear -Hc1; set_solver)).
      destruct (decide (c ∈ C2)) as [Hc2|Hc2]; [clear -H Hc2 HC2Σ1 HC20; set_solver|].
      rewrite HE2 in HP2. pose proof (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP2 Hst2) as H'.
      rewrite Hs2, dom_union_L, HC0' in H'. specialize (H' ltac:(clear -Hc2; set_solver)).
      clear -H H' Hd12. set_solver.
  Qed.

  (** A synchronization of two closes across the cut. *)
  Lemma lc2_cross_close F1 F2 e e' f f' c :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess (SClos c)) e' → tstep f (LSess (SClos c)) f' →
    LPtau_case (LPrel (pred n')) W Σ T (C ∖ {[c]}, F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hg.
    pose proof (lc2_cross_subj F1 F2 e _ e' f _ f' c HE1 HE2 Hst1 Hst2 eq_refl eq_refl) as HcC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ c ∉ C2) as [Hc1 Hc2] by (clear -HcC0 HC10 HC20; set_solver).
    assert (proc_step (C1, E1) (PSess (SClos c)) (C1 ∖ sentc (SClos c), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE1; apply PStepSession; [done|simpl; clear -Hc1; set_solver]).
    assert (proc_step (C2, E2) (PSess (SClos c)) (C2 ∖ sentc (SClos c), F2 ⊎ {[+ f' +]}))
      as Hs2 by (rewrite HE2; apply PStepSession; [done|simpl; clear -Hc2; set_solver]).
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hs1) as Hc1'. simpl in Hc1'.
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP2 Hs2) as Hc2'. simpl in Hc2'.
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
    assert (C ∖ {[c]} = C1 ∪ C2 ∪ (C0 ∖ {[c]})) as -> by (clear -Hc1 Hc2; set_solver).
    assert (F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = (F1 ⊎ {[+ e' +]}) ⊎ (F2 ⊎ {[+ f' +]})) as ->
      by multiset_solver.
    apply (lc2_conn_at_world (pred n') W Σ1 Σ2 (delete c ΣC) (delete c ΣC') (C0 ∖ {[c]}) C1 C2
             _ _ ltac:(lia) (wext_refl W HW')).
    - split; try done.
      + by apply map_disjoint_delete_r.
      + by apply map_disjoint_delete_r.
      + rewrite dom_delete_L. by rewrite HC0.
      + rewrite dom_delete_L. by rewrite HC0'.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + clear -HC10. set_solver.
      + clear -HC20. set_solver.
    - rewrite <-HE1a. eapply LPrel_down; [|exact HP1']. lia.
    - rewrite <-HE2a. eapply LPrel_down; [|exact HP2']. lia.
  Qed.
  (** A selection meets a branch across the cut. *)
  Lemma lc2_cross_choice F1 F2 e e' f f' c i :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess (SSel c i)) e' → tstep f (LSess (SBra c i)) f' →
    LPtau_case (LPrel (pred n')) W Σ T (C, F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hg.
    pose proof (lc2_cross_subj F1 F2 e _ e' f _ f' c HE1 HE2 Hst1 Hst2 eq_refl eq_refl) as HcC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ c ∉ C2) as [Hc1 Hc2] by (clear -HcC0 HC10 HC20; set_solver).
    assert (proc_step (C1, E1) (PSess (SSel c i)) (C1 ∖ sentc (SSel c i), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE1; apply PStepSession; [done|simpl; clear -Hc1; set_solver]).
    assert (proc_step (C2, E2) (PSess (SBra c i)) (C2 ∖ sentc (SBra c i), F2 ⊎ {[+ f' +]}))
      as Hs2 by (rewrite HE2; apply PStepSession; [done|simpl; clear -Hc2; set_solver]).
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hs1) as Hc1'. simpl in Hc1'.
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP2 Hs2) as Hc2'. simpl in Hc2'.
    rewrite difference_empty_L in Hc1', Hc2'.
    destruct Hc1' as (Σ1a & s1 & s2 & k1 & (s0 & HΣa & Hu1) & Hc1a & HP1').
    destruct Hc2' as (Σ2a & r1 & r2 & k2 & (s0' & HΣb & Hu2) & Hc2a & HP2').
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
    assert (ΣC !! c = Some (s0, k1)) as HCc.
    { pose proof (f_equal (lookup c) HΣa) as Hr. rewrite lookup_insert_eq, lookup_union, H1c in Hr.
      by rewrite (left_id_L None (∪)) in Hr. }
    assert (ΣC' !! c = Some (s0', k2)) as HC'c.
    { pose proof (f_equal (lookup c) HΣb) as Hr. rewrite lookup_insert_eq, lookup_union, H2c in Hr.
      by rewrite (left_id_L None (∪)) in Hr. }
    destruct (Hcut c _ _ HCc HC'c) as [Hk Hdu]. simpl in Hk, Hdu.
    destruct (sdual_plus_with _ _ _ _ _ _ Hdu Hu1 Hu2) as [Hdu1 Hdu2].
    assert (F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = (F1 ⊎ {[+ e' +]}) ⊎ (F2 ⊎ {[+ f' +]})) as ->
      by multiset_solver.
    apply (lc2_conn_at_world (pred n') W Σ1 Σ2 (<[c := (sbranch i s1 s2, sel_pt k1 i)]> ΣC)
             (<[c := (sbranch i r1 r2, bra_pt k2 i)]> ΣC') C0 C1 C2
             _ _ ltac:(lia) (wext_refl W HW')).
    - split; try done.
      + by apply map_disjoint_insert_r.
      + by apply map_disjoint_insert_r.
      + rewrite dom_insert_L, HC0. clear -HcC0. set_solver.
      + rewrite dom_insert_L, HC0'. clear -HcC0. set_solver.
      + intros r x y Hx Hy. destruct (decide (r = c)) as [->|Hrc].
        * rewrite lookup_insert_eq in Hx, Hy. injection Hx as <-. injection Hy as <-. simpl.
          split; [|by apply sdual_sbranch].
          unfold sel_pt, bra_pt. apply (wf_eq_dual _ (proj1 HW')).
          rewrite <-(pt_payload_dual k2). by apply (wf_eq_payload _ (proj1 HW')).
        * rewrite lookup_insert_ne in Hx, Hy by done. by apply (Hcut r).
    - assert (Σ1 ∪ <[c := (sbranch i s1 s2, sel_pt k1 i)]> ΣC =
              <[c := (sbranch i s1 s2, sel_pt k1 i)]> Σ1a) as ->.
      { rewrite HE1a. apply map_eq. intros r. destruct (decide (r = c)) as [->|Hrc].
        - rewrite lookup_union, !lookup_insert_eq, H1c. by rewrite (left_id_L None (∪)).
        - rewrite lookup_union, !lookup_insert_ne, lookup_union, lookup_delete_ne by done. done. }
      eapply LPrel_down; [|exact HP1']. lia.
    - assert (Σ2 ∪ <[c := (sbranch i r1 r2, bra_pt k2 i)]> ΣC' =
              <[c := (sbranch i r1 r2, bra_pt k2 i)]> Σ2a) as ->; [|eapply LPrel_down; [|exact HP2']; lia].
      rewrite HE2a. apply map_eq. intros r. destruct (decide (r = c)) as [->|Hrc].
      + rewrite lookup_union, !lookup_insert_eq, H2c. by rewrite (left_id_L None (∪)).
      + rewrite lookup_union, !lookup_insert_ne, lookup_union, lookup_delete_ne by done. done.
  Qed.

  (** Two closes of one channel inside component 1 need it restricted there. *)
  Lemma lc2_own_close_contra n'' (Hn : n' = S n'') F e e' f f' c :
    E1 = F ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SClos c)) e' →
    tstep f (LSess (SClos c)) f' → c ∉ C1 → False.
  Proof.
    intros HE Hst1 Hst2 Hc.
    assert (proc_step (C1, E1) (PSess (SClos c)) (C1 ∖ sentc (SClos c), (F ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
      as Hs by (rewrite HE, <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎));
                apply PStepSession; [done|simpl; clear -Hc; set_solver]).
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hs) as Hc1. simpl in Hc1.
    rewrite difference_empty_L in Hc1.
    destruct Hc1 as (Σ1a & k & _ & Hc1a & HP1').
    assert ((F ⊎ {[+ f +]}) ⊎ {[+ e' +]} = (F ⊎ {[+ e' +]}) ⊎ {[+ f +]}) as Heq by multiset_solver.
    rewrite Heq, Hn in HP1'.
    pose proof (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP1' Hst2 ltac:(simpl; clear -Hc; set_solver)) as H.
    simpl in H. clear -H Hc1a. set_solver.
  Qed.

  Lemma lc2_dom_ones_send Σv Σe Θe :
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
  Lemma lc2_cross_msg F1 F2 e e' f f' c v :
    E1 = F1 ⊎ {[+ e +]} → E2 = F2 ⊎ {[+ f +]} →
    tstep e (LSess (SSend c v)) e' → tstep f (LSess (SRecv c v)) f' →
    LPtau_case (LPrel (pred n')) W Σ T (C, F1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE1 HE2 Hst1 Hst2 Hg.
    pose proof (lc2_cross_subj F1 F2 e _ e' f _ f' c HE1 HE2 Hst1 Hst2 eq_refl eq_refl) as HcC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (c ∉ C1 ∧ c ∉ C2) as [Hc1 Hc2] by (clear -HcC0 HC10 HC20; set_solver).
    assert (proc_step (C1, E1) (PSess (SSend c v)) (C1 ∖ sentc (SSend c v), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE1; apply PStepSession; [done|simpl; clear -Hc1; set_solver]).
    assert (proc_step (C2, E2) (PSess (SRecv c v)) (C2 ∖ sentc (SRecv c v), F2 ⊎ {[+ f' +]}))
      as Hs2 by (rewrite HE2; apply PStepSession; [done|simpl; clear -Hc2; set_solver]).
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hs1) as Hc1'. simpl in Hc1'.
    pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP2 Hs2) as Hc2'. simpl in Hc2'.
    destruct Hc1' as (Σ0 & Σv & mm & U & s & k & Σe & Θe & (s0 & HΣa & Hu) & Hd0v & Hc0 & Hcv
                     & HdΘ & Hsplit & HΘΣ & HV & HP1').
    destruct Hc2' as (Σ2a & mm' & U' & s' & k' & (r0 & HΣb & Hu') & Hc2a & Hcont).
    pose proof (LVrel_fchans _ _ _ _ _ HV) as Hfw.
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
    pose proof (lc2_dom_ones_send Σv Σe Θe Hsplit HvΘ) as HDo. fold Θ2 in HDo.
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
        by apply (wf_eq_dual_sym _ _ _ (proj1 HW')).
      - intros r e1 e2 H. subst Θ2. unfold tenv_of in H. rewrite lookup_union, lookup_fmap in H.
        destruct (Σv !! r) eqn:?, (Θe !! r) as [o|] eqn:HΘr; simpl in H; simplify_eq; try done.
        pose proof (Hsp r _ HΘr) as Hb.
        rewrite (left_id_L None (∪)) in H. injection H as ->. simpl in Hb.
        destruct Hb as (_ & ? & ?). done.
      - rewrite HDr2, HDo, HDΘ2. clear -HΣeΘ HΘC1 HC1Σ2 HC10. set_solver. }
    assert (LVrel (pred n') W Θ2 (payload_at mm' U' k') v) as HV'.
    { rewrite <-(payload_at_dual mm' U' k').
      eapply LVrel_payload; [apply HW'|exact Hkk|]. eapply LVrel_teq; [apply HW'|by apply teq_ty_inst|].
      eapply LVrel_down; [|exact HV]. lia. }
    pose proof (Hcont W (pred n') Θ2 (wext_refl W HW') ltac:(lia)
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
    assert (Σ1 ∪ Σ2 = Σ1n ∪ Σ2n) as ->.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
      subst Σ1n Σ2n. destruct (decide (r = c)) as [->|Hrc]; mtrim; mpoint. }
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
      unfold recv_env. subst Σr2. destruct (decide (r = c)) as [->|Hrc]; mtrim; mpoint.
      all: destruct HCC as [?|[? ?]]; congruence. }
    apply (lc2_conn_at_world (pred n') W Σ1n Σ2n ΣC1n ΣC2n _ _ _ _ _ ltac:(lia) (wext_refl W HW')).
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
          split; [rewrite pt_dual_shift; by apply (wf_eq_shift _ (proj1 HW'))|done].
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
        destruct (decide (r = c)) as [->|Hrc]; mtrim; mpoint. }
      eapply LPrel_down; [|exact HP1']. lia.
    - assert (Σ2n ∪ ΣC2n = recv_env Σr2 Θ2) as -> by (subst ΣC2n; by apply map_difference_union).
      exact HP2'.
  Qed.
End lsteps2.

Section lsteps3.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → lconn_at j T).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA TB : ty).
  Context (Hty : ctys TA TB T)
    (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : LPrel (S n') W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2 : LPrel (S n') W (Σ2 ∪ ΣC') TB (C2, E2)).
  Context (HP1n : LPrel n' W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2n : LPrel n' W (Σ2 ∪ ΣC') TB (C2, E2)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).


  Lemma lc2_C12_0 : C1 ## C2 ∪ C0.
  Proof. pose proof (co_C12 _ _ _ _ _ _ _ _ Hok). pose proof (co_C10 _ _ _ _ _ _ _ _ Hok). set_solver. Qed.

  Local Notation own := (lc2_own_comm n' T HT IHo W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n).

  (** Internal synchronizations of component 1. *)
  Lemma lc2_tau_msg F1 c v e e' f f' :
    E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SSend c v)) e' →
    tstep f (LSess (SRecv c v)) f' →
    LPtau_case (LPrel (pred n')) W Σ T (C, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE Hst1 Hst2. pose proof (own (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]} ⊎ E2)
      as -> by multiset_solver.
    apply H; [rewrite HE; by eapply PCMsg|apply lc2_C12_0].
  Qed.

  Lemma lc2_tau_close F1 c e e' f f' :
    E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SClos c)) e' →
    tstep f (LSess (SClos c)) f' → c ∈ C1 →
    LPtau_case (LPrel (pred n')) W Σ T (C ∖ {[c]}, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE Hst1 Hst2 Hc.
    pose proof (own (C1 ∖ {[c]}, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]} ⊎ E2)
      as -> by multiset_solver.
    pose proof lc2_C12_0 as H0.
    assert (C ∖ {[c]} = C1 ∖ {[c]} ∪ C2 ∪ C0) as -> by (clear -Hc H0; set_solver).
    apply H; [rewrite HE; by eapply PCClose|clear -H0; set_solver].
  Qed.

  Lemma lc2_tau_choice F1 c i e e' f f' :
    E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} → tstep e (LSess (SSel c i)) e' →
    tstep f (LSess (SBra c i)) f' →
    LPtau_case (LPrel (pred n')) W Σ T (C, F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
  Proof.
    intros HE Hst1 Hst2. pose proof (own (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as H. simpl in H.
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ f' +]} = F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]} ⊎ E2)
      as -> by multiset_solver.
    apply H; [rewrite HE; by eapply PCChoice|apply lc2_C12_0].
  Qed.
End lsteps3.

(** ** Links of a component, at the index

    A link costs nothing (lock-freedom plan §6.1), so the composite
    after a link of component 1 is read at the index. Component 2 stays
    as it is: the composite with component 1's successor is given by the
    induction on the τ layer of component 1 ([lc_succ]), and the link's
    effect on component 2's ends (junk, renaming, fusion) is applied to
    the composite as a whole. The same lemmas serve a link of
    component 2, with the roles swapped. *)

Lemma lc_cut_ok_wext W W' Σ1 Σ2 ΣC ΣC' C0 C1 C1' C2 :
  wext W W' → C1' ⊆ C1 → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 → cut_ok W' Σ1 Σ2 ΣC ΣC' C0 C1' C2.
Proof.
  intros Hx Hsub [HW Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
  split; try done.
  all: first
    [ apply Hx
    | (intros r x y Hx1 Hy1; destruct (Hcut r x y Hx1 Hy1) as [H1 H2];
       split; [by apply (proj1 (proj2 Hx))|done])
    | (clear -Hsub HC1Σ2; set_solver)
    | (clear -Hsub HC1Σ1; set_solver)
    | (clear -Hsub HC10; set_solver)
    | (clear -Hsub HC12; set_solver) ].
Qed.

(** The composite with component 1 replaced by q, over any cut, with
    component 2 unchanged. *)
Definition lc_succ (n' : nat) (T : ty) (Σ2 ΣC' : senv) (C2 : gset chan) (E2 : gmultiset expr)
    (W0 : world) (Σa : senv) (q : proc) : Prop :=
  ∀ Σ1' Σ2' ΣC1 ΣC2 C0' C1' E1', Σa = Σ1' ∪ ΣC1 → q = (C1', E1') → Σ2 ∪ ΣC' = Σ2' ∪ ΣC2 →
    cut_ok W0 Σ1' Σ2' ΣC1 ΣC2 C0' C1' C2 →
    LPrel (S n') W0 (Σ1' ∪ Σ2') T (C1' ∪ C2 ∪ C0', E1' ⊎ E2).

Section lsteps_link.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA : ty).
  Context (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : LPrel (S n') W (Σ1 ∪ ΣC) TA (C1, E1)).
  Context (HQ : ∀ cd p1', proc_step (C1, E1) (PSess (SLink cd)) p1' →
    Plink_case (λ W0 Σa _ q, lc_succ n' T Σ2 ΣC' C2 E2 W0 Σa q) W (Σ1 ∪ ΣC) TA cd p1').
  Context (HA : ∀ p1', padmin (C1, E1) p1' → p1'.1 ## dom (Σ1 ∪ ΣC) →
    lc_succ n' T Σ2 ΣC' C2 E2 W (Σ1 ∪ ΣC) p1').

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).

  (** Q-Link for an external link of component 1. *)
  Lemma lc2_ext_link F1 e cd e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink cd)) e' → subjs (SLink cd) ## C →
    Plink_case (LPrel (S n')) W Σ T cd (C ∖ sentc (SLink cd), F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SLink cd)) (C1 ∖ sentc (SLink cd), F1 ⊎ {[+ e' +]}))
      as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SLink cd) e' Hst). simpl in *. clear -Hc. set_solver. }
    pose proof (HQ _ _ Hst1) as Hc1.
    cbn [sentc] in Hc1 |- *. rewrite difference_empty_L in Hc1 |- *.
    destruct Hc1 as (c & d & Σ1a & sc & sd & kc & kd & -> & Hcd & HΣa & Hc1a & Hd1a & Hdu & Hal & HX).
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
    assert (c ∈ dom Σ1 ∧ d ∈ dom Σ1) as [Hc1 Hd1''].
    { assert (c ∈ dom (Σ1 ∪ ΣC) ∧ d ∈ dom (Σ1 ∪ ΣC)) as [H H'] by
        (rewrite HΣa, !dom_insert_L; clear; set_solver).
      rewrite dom_union_L, HC0 in H, H'. clear -H H' HcC0 HdC0. set_solver. }
    assert (Σ1a ∖ ΣC ∪ ΣC = Σ1a) as HΣ1a.
    { apply map_eq. intros r. pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      mpoint. all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence). }
    assert (dom (Σ1a ∖ ΣC) ⊆ dom Σ1) as Hsub.
    { rewrite dom_difference_L. intros r Hr.
      assert (r ∈ dom (Σ1 ∪ ΣC)) as H.
      { rewrite HΣa, !dom_insert_L. clear -Hr. set_solver. }
      rewrite dom_union_L in H. clear -H Hr. set_solver. }
    exists c, d, (Σ1a ∖ ΣC ∪ Σ2), sc, sd, kc, kd. split_and!; try done.
    - apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      pose proof (proj1 (map_subseteq_spec _ _) HCsub r) as Hs.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]]; mpoint.
      all: try (first [specialize (Hs _ eq_refl) | match goal with L : ΣC !! _ = Some _ |- _ => specialize (Hs _ L) end]; simplify_eq; rewrite ?(left_id_L None (∪)); congruence).
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc1a Hc1 Hd12. set_solver.
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hd1a Hd1'' Hd12. set_solver.
    - assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
      apply (HX (Σ1a ∖ ΣC) Σ2 ΣC ΣC' C0 C1 (F1 ⊎ {[+ e' +]})); [done|done|done|].
      apply map_disjoint_dom in Hd12.
      split; try done; try (apply map_disjoint_dom);
        [rewrite dom_difference_L; clear; set_solver|clear -Hsub Hd12|clear -Hsub HC2Σ1|clear -Hsub HC1Σ1];
        set_solver.
  Qed.

  (** A link of component 1 that removes a channel restricted in
      component 1: component 2 holds neither end, so the composite
      renames junk only. *)
  Lemma lc2_link_own F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C1 →
    LPrel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst Hc.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (ptau_link (C1, E1) (C1 ∖ {[c]}, echsubst c d (F1 ⊎ {[+ e' +]}))) as Hl.
    { exists C1, F1, e, c, d, e'. by rewrite HE. }
    pose proof (HA _ (padmin_link _ _ Hl)
                  ltac:(simpl; rewrite dom_union_L, HC0; clear -HC1Σ1 HC10; set_solver)) as HX.
    pose proof (HX Σ1 Σ2 ΣC ΣC' C0 (C1 ∖ {[c]}) (echsubst c d (F1 ⊎ {[+ e' +]}))
                  eq_refl eq_refl eq_refl
                  (lc_cut_ok_wext W W Σ1 Σ2 ΣC ΣC' C0 C1 (C1 ∖ {[c]}) C2 (wext_refl W HW')
                     ltac:(clear; set_solver) Hok0)) as HXc.
    assert (C ∖ {[c]} = (C1 ∖ {[c]}) ∪ C2 ∪ C0) as -> by (clear -Hc HC12 HC10; set_solver).
    destruct (decide (d = c)) as [->|Hdc].
    { rewrite !echsubst_refl in HXc |- *.
      assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver. exact HXc. }
    assert (echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]}) =
            echsubst c d (echsubst c d (F1 ⊎ {[+ e' +]}) ⊎ E2)) as ->.
    { rewrite (echsubst_disj_union c d (echsubst c d (F1 ⊎ {[+ e' +]})) E2).
      rewrite (echsubst_id c d (echsubst c d (F1 ⊎ {[+ e' +]})));
        [|by apply echans_echsubst_notin; intros ->].
      rewrite !echsubst_disj_union. multiset_solver. }
    apply LPrel_junk; [| | |done|exact HXc].
    - rewrite dom_union_L. clear -Hc HC1Σ1 HC1Σ2. set_solver.
    - clear -Hc HC12 HC10. set_solver.
    - intros Hd'. rewrite dom_union_L. clear -Hd' HC1Σ1 HC1Σ2 HC2Σ1 HC2Σ2 HΣ1C0 HΣ2C0. set_solver.
  Qed.

  (** An external link of component 1, with the two ends named as in
      the label. *)
  Lemma lc_ext_link_norm F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∉ C1 → d ∉ C1 →
    c ≠ d ∧ ∃ Σ1a sc sd kc kd,
      Σ1 ∪ ΣC = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ1a) ∧ c ∉ dom Σ1a ∧ d ∉ dom Σ1a ∧
      sdual sc sd ∧ w_eq W kc (pt_dual kd) ∧
      lc_succ n' T Σ2 ΣC' C2 E2 W Σ1a (C1, F1 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc Hd.
    assert (proc_step (C1, E1) (PSess (SLink {[c; d]})) (C1 ∖ sentc (SLink {[c; d]}), F1 ⊎ {[+ e' +]}))
      as Hs1 by (rewrite HE; apply PStepSession; [done|simpl; clear -Hc Hd; set_solver]).
    pose proof (HQ _ _ Hs1) as Hc1. cbn [sentc] in Hc1.
    rewrite difference_empty_L in Hc1.
    destruct Hc1 as (c' & d' & Σ1a & sc & sd & kc & kd & Hcd' & Hne & HΣa & Hc1a & Hd1a & Hdu & Hal & HX).
    assert (c ≠ d) as Hcd.
    { intros <-. assert (c' ∈ ({[c; c]} : gset chan)) as H1 by (rewrite Hcd'; set_solver).
      assert (d' ∈ ({[c; c]} : gset chan)) as H2 by (rewrite Hcd'; set_solver).
      apply Hne. set_solver. }
    split; [done|].
    destruct (upair_eq_inv c d c' d' Hcd' Hcd) as [[-> ->]|[-> ->]].
    - exists Σ1a, sc, sd, kc, kd. split_and!; try done. by apply sdual_sym.
    - exists Σ1a, sd, sc, kd, kc. split_and!; try done.
      + rewrite HΣa. by apply insert_insert_ne.
      + by apply (wf_eq_dual_sym _ _ _ (proj1 (co_strict _ _ _ _ _ _ _ _ Hok))).
  Qed.

  (** A link of component 1 between its end of a cut channel c and an
      interface channel d: in the composite, component 2's end of c is
      renamed to d. *)
  Lemma lc2_link_iface F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C0 → d ∈ dom Σ1 →
    LPrel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
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
    destruct (lc_ext_link_norm F1 e c d e' HE Hst Hc1 Hd1')
      as (Hcd & Σ1a & sc & sd & kc & kd & HΣa & Hc1a & Hd1a & Hdu & Hal & HX).
    assert (ΣC !! c = Some (sc, kc)) as HCc.
    { pose proof (f_equal (lookup c) HΣa) as H. rewrite lookup_insert_eq, lookup_union in H.
      rewrite (not_elem_of_dom_1 _ _ HcΣ1), (left_id_L None (∪)) in H. done. }
    assert (ΣC !! d = None) as HCd by (apply not_elem_of_dom; by rewrite HC0).
    assert (Σ1 !! d = Some (sd, kd)) as H1d.
    { pose proof (f_equal (lookup d) HΣa) as H. rewrite lookup_insert_ne, lookup_insert_eq, lookup_union in H by done.
      rewrite HCd in H. destruct (Σ1 !! d); [by rewrite (right_id_L None (∪)) in H|done]. }
    assert (is_Some (ΣC' !! c)) as [[sc2 kc2] HC'c] by (apply elem_of_dom; by rewrite HC0').
    assert (ΣC' !! d = None) as HC'd by (apply not_elem_of_dom; by rewrite HC0').
    destruct (Hcut c _ _ HCc HC'c) as [Hkk Hdd]. simpl in Hkk, Hdd.
    assert (Σ1a = delete d Σ1 ∪ delete c ΣC) as HΣ1a.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      - rewrite lookup_union, lookup_delete_eq, lookup_delete_ne, (not_elem_of_dom_1 _ _ HcΣ1) by done.
        by rewrite (not_elem_of_dom_1 _ _ Hc1a).
      - rewrite lookup_union, lookup_delete_eq, lookup_delete_ne, HCd by done.
        by rewrite (not_elem_of_dom_1 _ _ Hd1a).
      - rewrite !lookup_insert_ne in Hr by done.
        by rewrite <-Hr, !lookup_union, lookup_delete_ne, lookup_delete_ne by done. }
    (* the composite with component 2's end of c on the interface *)
    assert (Σ2 ∪ ΣC' = <[c := (sc2, kc2)]> Σ2 ∪ delete c ΣC') as HΣb.
    { apply map_eq. intros r. destruct (decide (r = c)) as [->|Hrc].
      - rewrite !lookup_union, lookup_insert_eq, lookup_delete_eq, (not_elem_of_dom_1 _ _ HcΣ2), HC'c.
        done.
      - by rewrite !lookup_union, lookup_insert_ne, lookup_delete_ne by done. }
    assert (cut_ok W (delete d Σ1) (<[c := (sc2, kc2)]> Σ2) (delete c ΣC) (delete c ΣC')
              (C0 ∖ {[c]}) C1 C2) as Hok2.
    { split; try done.
      + by apply map_disjoint_delete_l, map_disjoint_delete_r.
      + apply map_disjoint_insert_l. split; [|by apply map_disjoint_delete_r].
        by rewrite lookup_delete_eq.
      + apply map_disjoint_dom. rewrite dom_delete_L, dom_insert_L. clear -Hd12' HcΣ1. set_solver.
      + rewrite dom_delete_L. by rewrite HC0.
      + rewrite dom_delete_L. by rewrite HC0'.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + rewrite dom_insert_L. clear -HC1Σ2 Hc1. set_solver.
      + rewrite dom_delete_L. clear -HC2Σ1. set_solver.
      + rewrite dom_delete_L. clear -HC1Σ1. set_solver.
      + rewrite dom_insert_L. clear -HC2Σ2 Hc2. set_solver.
      + clear -HC10. set_solver.
      + clear -HC20. set_solver. }
    pose proof (HX (delete d Σ1) (<[c := (sc2, kc2)]> Σ2) (delete c ΣC) (delete c ΣC') (C0 ∖ {[c]})
                  C1 (F1 ⊎ {[+ e' +]}) HΣ1a eq_refl HΣb Hok2) as HXc.
    (* rename c to d in the composite *)
    apply (LPrel_swap c d) in HXc. unfold pswap in HXc. cbn [fst snd] in HXc.
    rewrite gswap_fresh in HXc by (clear -Hc1 Hd1' Hc2 Hd2' HdC0; set_solver).
    apply (LPrel_junk _ _ _ _ _ _ c d) in HXc.
    - rewrite echsubst_msswap_same in HXc.
      assert (C ∖ {[c]} = C1 ∪ C2 ∪ C0 ∖ {[c]}) as -> by (clear -Hc1 Hc2; set_solver).
      assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
      eapply LPrel_sconv; [apply HW'| |exact HXc].
      intros r. rewrite lookup_senvswap'.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      + rewrite cswap_l, !lookup_union, lookup_delete_eq, lookup_insert_ne by done.
        rewrite (not_elem_of_dom_1 _ _ HdΣ2), (not_elem_of_dom_1 _ _ HcΣ1), (not_elem_of_dom_1 _ _ HcΣ2).
        done.
      + rewrite cswap_r, !lookup_union, lookup_insert_eq, lookup_delete_ne by done.
        rewrite (not_elem_of_dom_1 _ _ HcΣ1), H1d, (not_elem_of_dom_1 _ _ HdΣ2), (left_id_L None (∪)).
        rewrite (right_id_L None (∪)).
        split; simpl; [eapply sdual_unique; [exact Hdd|exact Hdu]|].
        apply (wf_eq_trans _ (proj1 HW') _ (pt_dual kc));
          first [by apply (wf_eq_dual_sym _ _ _ (proj1 HW'))
                |by apply (wf_eq_sym _ (proj1 HW')), (wf_eq_dual_sym _ _ _ (proj1 HW'))
                |by apply (wf_eq_dual_l _ _ _ (proj1 HW'))
                |by apply (wf_eq_sym _ (proj1 HW')), (wf_eq_dual_l _ _ _ (proj1 HW'))].
      + rewrite cswap_ne by done. rewrite !lookup_union, lookup_delete_ne, lookup_insert_ne by done.
        destruct (Σ1 !! r), (Σ2 !! r); simpl; try done; split; try apply seq_refl;
          apply (wf_eq_refl _ (proj1 HW')).
    - rewrite dom_senvswap, elem_of_gswap', cswap_l, dom_union_L, dom_delete_L, dom_insert_L.
      clear -HdΣ2 Hcd. set_solver.
    - clear -Hc1 Hc2. set_solver.
    - intros Hd'. exfalso. clear -Hd' Hd1' Hd2' HdC0. set_solver.
    - done.
  Qed.

  (** A link of component 1 between its ends of two cut channels c and
      d: the composite internalizes the link of component 2's ends. *)
  Lemma lc2_link_cut F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C0 → d ∈ C0 →
    LPrel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst HcC0 HdC0.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    apply map_disjoint_dom in Hd12 as Hd12'.
    assert (c ∉ C1 ∧ d ∉ C1 ∧ c ∉ C2 ∧ d ∉ C2 ∧ c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧ d ∉ dom Σ2)
      as (Hc1 & Hd1' & Hc2 & Hd2' & HcΣ1 & HdΣ1 & HcΣ2 & HdΣ2)
      by (clear -HcC0 HdC0 HC10 HC20 HΣ1C0 HΣ2C0; set_solver).
    destruct (lc_ext_link_norm F1 e c d e' HE Hst Hc1 Hd1')
      as (Hcd & Σ1a & sc & sd & kc & kd & HΣa & Hc1a & Hd1a & Hdu & Hal & HX).
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
    assert (Σ1a = Σ1 ∪ delete c (delete d ΣC)) as HΣ1a.
    { apply map_eq. intros r. pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      - rewrite lookup_union, lookup_delete_eq, (not_elem_of_dom_1 _ _ HcΣ1).
        by rewrite (not_elem_of_dom_1 _ _ Hc1a).
      - rewrite lookup_union, lookup_delete_ne, lookup_delete_eq, (not_elem_of_dom_1 _ _ HdΣ1) by done.
        by rewrite (not_elem_of_dom_1 _ _ Hd1a).
      - rewrite !lookup_insert_ne in Hr by done.
        by rewrite <-Hr, !lookup_union, lookup_delete_ne, lookup_delete_ne by done. }
    set (Σ2f := <[c := (sc2, kc2)]> (<[d := (sd2, kd2)]> Σ2)).
    assert (Σ2 ∪ ΣC' = Σ2f ∪ delete c (delete d ΣC')) as HΣb.
    { apply map_eq. intros r. subst Σ2f.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      - rewrite !lookup_union, lookup_insert_eq, lookup_delete_eq, (not_elem_of_dom_1 _ _ HcΣ2), HC'c.
        done.
      - rewrite !lookup_union, lookup_insert_ne, lookup_insert_eq by congruence.
        rewrite lookup_delete_ne, lookup_delete_eq by congruence.
        rewrite (not_elem_of_dom_1 _ _ HdΣ2), HC'd. done.
      - rewrite !lookup_union, !lookup_insert_ne by done.
        by rewrite lookup_delete_ne, lookup_delete_ne by done. }
    assert (cut_ok W Σ1 Σ2f (delete c (delete d ΣC)) (delete c (delete d ΣC'))
              (C0 ∖ {[c; d]}) C1 C2) as Hokc.
    { subst Σ2f. split; try done.
      + by apply map_disjoint_delete_r, map_disjoint_delete_r.
      + apply map_disjoint_dom. rewrite !dom_insert_L, !dom_delete_L.
        apply map_disjoint_dom in Hd2. clear -Hd2. set_solver.
      + apply map_disjoint_dom. rewrite !dom_insert_L. clear -Hd12' HcΣ1 HdΣ1. set_solver.
      + rewrite !dom_delete_L, HC0. clear. set_solver.
      + rewrite !dom_delete_L, HC0'. clear. set_solver.
      + intros r x y Hx Hy. apply lookup_delete_Some in Hx as [_ Hx].
        apply lookup_delete_Some in Hx as [_ Hx]. apply lookup_delete_Some in Hy as [_ Hy].
        apply lookup_delete_Some in Hy as [_ Hy]. by apply (Hcut r).
      + rewrite !dom_insert_L. clear -HC1Σ2 Hc1 Hd1'. set_solver.
      + rewrite !dom_insert_L. clear -HC2Σ2 Hc2 Hd2'. set_solver.
      + clear -HC10. set_solver.
      + clear -HC20. set_solver. }
    pose proof (HX Σ1 Σ2f (delete c (delete d ΣC)) (delete c (delete d ΣC')) (C0 ∖ {[c; d]})
                  C1 (F1 ⊎ {[+ e' +]}) HΣ1a eq_refl HΣb Hokc) as HXc.
    assert (Σ1 ∪ Σ2f = fusedP c d (Σ1 ∪ Σ2) sc2 sd2 kc2 kd2) as HΣf.
    { apply map_eq. intros r. unfold fusedP. subst Σ2f.
      destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
      - rewrite lookup_union, !lookup_insert_eq, (not_elem_of_dom_1 _ _ HcΣ1). done.
      - rewrite lookup_union, (lookup_insert_ne _ c d) by congruence.
        rewrite (lookup_insert_ne _ c d) by congruence. rewrite !lookup_insert_eq.
        rewrite (not_elem_of_dom_1 _ _ HdΣ1). done.
      - rewrite lookup_union, (lookup_insert_ne _ c r), (lookup_insert_ne _ d r) by congruence.
        rewrite (lookup_insert_ne _ c r), (lookup_insert_ne _ d r) by congruence.
        by rewrite lookup_union. }
    rewrite HΣf in HXc.
    assert (int_ok c d W (Σ1 ∪ Σ2) sc2 sd2 kc2 kd2 (C1 ∪ C2 ∪ C0 ∖ {[c; d]})) as Hio.
    { split_and!; try done.
      - rewrite dom_union_L. clear -HcΣ1 HcΣ2. set_solver.
      - rewrite dom_union_L. clear -HdΣ1 HdΣ2. set_solver.
      - clear -Hc1 Hc2. set_solver.
      - clear -Hd1' Hd2'. set_solver.
      - eapply sdual_seq_l; [|exact Hdd]. eapply sdual_unique; [exact Hdu|exact Hdc].
      - pose proof (proj1 HW') as Hwf.
        apply (wf_eq_trans _ Hwf _ (pt_dual kc)); [by apply (wf_eq_dual_sym _ _ _ Hwf)|].
        apply (wf_eq_trans _ Hwf _ kd); [by apply (wf_eq_dual_l _ _ _ Hwf)|done]. }
    pose proof (LPrel_internalize c d Hcd (S n') W (Σ1 ∪ Σ2) T _ _ sc2 sd2 kc2 kd2 HT Hio HXc)
      as HY.
    assert (C ∖ {[c]} = C1 ∪ C2 ∪ C0 ∖ {[c; d]} ∪ {[d]}) as ->.
    { apply set_eq. intros x. destruct (decide (x = d)) as [->|Hxd]; [clear -Hcd HdC0; set_solver|].
      clear -Hc1 Hc2 Hxd. set_solver. }
    assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
    exact HY.
  Qed.

  (** The giving clause for a link τ of the composite whose thread is in
      component 1. *)
  Lemma lc2_link_give F1 e c d e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C →
    LPrel (S n') W Σ T (C ∖ {[c]}, echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})).
  Proof.
    intros HE Hst HcC.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    pose proof Hok as Hok0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    destruct (decide (c ∈ C1)) as [Hc1|Hc1].
    { exact (lc2_link_own F1 e c d e' HE Hst Hc1). }
    destruct (decide (d ∈ C1)) as [Hd1'|Hd1'].
    { assert (d ≠ c) as Hdc by (intros ->; done).
      rewrite upair_comm in Hst.
      pose proof (lc2_link_own F1 e d c e' HE Hst Hd1') as H.
      apply (LPrel_swap_restricted c d) in H.
      - unfold pswap in H. simpl in H.
        rewrite gswap_minus_other, msswap_echsubst_flip in H; [done|done|clear -Hd1'; set_solver].
      - apply map_disjoint_dom in Hd12. rewrite dom_union_L.
        clear -HcC HC1Σ1 HC1Σ2 HC2Σ1 HC2Σ2 HΣ1C0 HΣ2C0. set_solver.
      - rewrite dom_union_L. clear -Hd1' HC1Σ1 HC1Σ2. set_solver. }
    rewrite HE in HP1.
    pose proof (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP1 Hst ltac:(simpl; clear -Hc1 Hd1'; set_solver))
      as Hsub. simpl in Hsub. rewrite dom_union_L, HC0 in Hsub. rewrite <-HE in HP1.
    assert (c ∈ C0) as HcC0.
    { assert (c ∈ dom Σ1 ∪ C0) as H by (apply Hsub; clear; set_solver).
      clear -H HcC HC2Σ1 Hc1. set_solver. }
    assert (d ∈ dom Σ1 ∪ C0) as Hd by (apply Hsub; clear; set_solver).
    apply elem_of_union in Hd as [Hd|Hd].
    - exact (lc2_link_iface F1 e c d e' HE Hst HcC0 Hd).
    - exact (lc2_link_cut F1 e c d e' HE Hst HcC0 Hd).
  Qed.
End lsteps_link.
