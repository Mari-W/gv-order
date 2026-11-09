(** * The guarded live fundamental theorem for processes (liveness.md §10)

    A process whose threads are typed and guarded is in the live P
    relation, by induction on the process typing as in
    [fundamental_proc] (static/Fundamental.v). With [live_adequacy] such
    a closed process is deadlock free and does not τ-diverge. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveGuardFund liveness.LivePTerm liveness.LivePConnect
  liveness.LiveAdequacy.

Set Default Proof Using "All".

Theorem live_fundamental_proc W Σ p T :
  gptyped W Σ p T → strict W → ∀ n, LPrel n W Σ T p.
Proof.
  intros [Hp Hg]. revert Hg.
  induction Hp as [W Σ ΘB C0 t T HT Hd Hdj Hb Hdu Ht
                 |W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ?
                 |W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ? HW1 HW2 HJ]; intros Hg HW.
  - apply (LPrel_term W Σ ΘB C0); try done.
    apply live_fundamental_guarded; [|done]. split; [done|]. apply Hg. simpl. set_solver.
  - assert (∀ e, e ∈ E1 → guarded e) as Hg1 by (intros e He; apply Hg; simpl; multiset_solver).
    assert (∀ e, e ∈ E2 → guarded e) as Hg2 by (intros e He; apply Hg; simpl; multiset_solver).
    assert (strict (wjoin W W)) as HWW by (by apply wjoin_sub_strict, wext_refl).
    intros n. eapply LPrel_mono; [right; by apply wext_join_self|].
    revert n. apply (LPrel_connect W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
    + exact (ptyped_prim _ _ _ _ H1).
    + by apply IH1.
    + by apply IH2.
    + apply HW.
    + apply HW.
  - assert (∀ e, e ∈ E1 → guarded e) as Hg1 by (intros e He; apply Hg; simpl; multiset_solver).
    assert (∀ e, e ∈ E2 → guarded e) as Hg2 by (intros e He; apply Hg; simpl; multiset_solver).
    assert (strict W1) as HS1.
    { split; [done|]. intros x Hx. apply (proj2 HJ x), (proj2 (wjoin_l W1 W2)), Hx. }
    assert (strict W2) as HS2.
    { split; [done|]. intros x Hx. apply (proj2 HJ x), (proj2 (wjoin_r W1 W2)), Hx. }
    apply (LPrel_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
    + exact (ptyped_prim _ _ _ _ H1).
    + by apply IH1.
    + by apply IH2.
Qed.

(** Guarded typed closed programs are deadlock free and do not τ-diverge. *)
Theorem live_soundness W p T :
  strict W → gptyped W ∅ p T → deadlock_free p ∧ no_tau_divergence p.
Proof. intros HW Hp. apply (live_adequacy W T p). by apply live_fundamental_proc. Qed.

(** A closed guarded thread. *)
Corollary live_soundness_term W t T :
  strict W → prim T → gtyped W ∅ [] ∅ [] (∅, None) t T →
  deadlock_free (∅, {[+ t +]}) ∧ no_tau_divergence (∅, {[+ t +]}).
Proof.
  intros HW HT Ht. apply (live_adequacy W T).
  apply (LPrel_term W ∅ ∅ ∅); [done|done|done|set_solver| | |].
  - intros c o Ho. by rewrite lookup_empty in Ho.
  - intros c e1 e2 He. by rewrite lookup_empty in He.
  - unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)).
    by apply live_fundamental_guarded.
Qed.

(** A guarded source program under a creation constraint, by the
    c0 world of [soundness_source]. *)
Theorem live_soundness_source n C0 t T :
  creation_ok n nofact nofact (λ _, False) C0 → prim T →
  gstyped ∅ [(C0, ids n)] [] (∅, None) t T →
  deadlock_free (∅, {[+ t +]}) ∧ no_tau_divergence (∅, {[+ t +]}).
Proof.
  intros HC HT [Hs Hg]. apply c0_creation_ok in HC.
  pose proof (styped_typed wnil _ _ _ _ _ _ Hs) as Ht.
  pose proof (wc0_strict n C0 HC) as HS.
  set (σ := plist (c0_consts n)).
  pose proof (typed_live _ _ _ _ _ _ _ _ Ht (gall_gallM _ Hg) (wc0 n C0) (λ _, ∅) σ (proj1 wnil_strict)
                (wc0_ext n C0 HC)) as H.
  assert (sf_inst (λ _, ∅) (sf_pinst σ (∅, None)) = ∅) as E.
  { unfold sf_inst, sf_pinst. simpl. rewrite set_map_empty. set_solver. }
  rewrite tenv_pinst_empty, E in H.
  assert (lsem_typed (wc0 n C0) ∅ (lenv_pinst σ []) ∅ t (pinst_ty σ T)) as Hl.
  { apply lsem_later_now. refine (proj1 (H _ _ (tenv_pol_empty _)) _ (okR_noL _)); [|by apply wc0_holds].
    intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty. }
  apply (live_adequacy (wc0 n C0) (pinst_ty σ T)).
  apply (LPrel_term _ ∅ ∅ ∅); [by apply prim_pinst|done|done|set_solver| | |].
  - intros c o Ho. by rewrite lookup_empty in Ho.
  - intros c e1 e2 He. by rewrite lookup_empty in He.
  - unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)). exact Hl.
Qed.

(** A guarded source program over the hypotheses of its top-level
    channels, in the world where its run starts (sharp edges 172). *)
Theorem live_soundness_created Ψ t T :
  created (Wpo []) Ψ → prim T → gstyped ∅ Ψ [] (∅, None) t T →
  deadlock_free (∅, {[+ t +]}) ∧ no_tau_divergence (∅, {[+ t +]}).
Proof.
  intros HΨ HT [Hs Hg].
  destruct (created_world (Wpo []) Ψ (Wpo_strict []) HΨ) as (W1 & σ & HW1 & Hh).
  pose proof (typed_live _ _ _ _ _ _ _ _ (styped_typed (Wpo []) _ _ _ _ _ _ Hs) (gall_gallM _ Hg)
                W1 (λ _, ∅) σ (proj1 (Wpo_strict [])) HW1) as H.
  assert (sf_inst (λ _, ∅) (sf_pinst σ (∅, None)) = ∅) as E.
  { unfold sf_inst, sf_pinst. simpl. rewrite set_map_empty. set_solver. }
  rewrite tenv_pinst_empty, E in H.
  assert (lsem_typed W1 ∅ (lenv_pinst σ []) ∅ t (pinst_ty σ T)) as Hl.
  { apply lsem_later_now. refine (proj1 (H _ _ (tenv_pol_empty _)) _ (okR_noL _)); [|done].
    intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty. }
  apply (live_adequacy W1 (pinst_ty σ T)).
  apply (LPrel_term _ ∅ ∅ ∅); [by apply prim_pinst|exact (proj2 (proj2 (proj2 HW1)))|done|set_solver| | |].
  - intros c o Ho. by rewrite lookup_empty in Ho.
  - intros c e1 e2 He. by rewrite lookup_empty in He.
  - unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)). exact Hl.
Qed.

(** ** The examples of GuardEx.v as live programs *)
Theorem fw_live_sound :
  deadlock_free (∅, {[+ Forwarder.fw_main +]}) ∧ no_tau_divergence (∅, {[+ Forwarder.fw_main +]}).
Proof. apply (live_soundness_created _ _ TUnit Forwarder.fw_created); [constructor|apply fw_gstyped]. Qed.
Theorem tc_live_sound :
  deadlock_free (∅, {[+ TailCall.tc_main +]}) ∧ no_tau_divergence (∅, {[+ TailCall.tc_main +]}).
Proof. apply (live_soundness_created _ _ TUnit TailCall.tc_created); [constructor|apply tc_gstyped]. Qed.
Theorem fa_live_sound :
  deadlock_free (∅, {[+ FirstAction.fa_go +]}) ∧ no_tau_divergence (∅, {[+ FirstAction.fa_go +]}).
Proof. apply (live_soundness_created _ _ TUnit TreeCopy.tca_created); [constructor|apply fa_gstyped]. Qed.
Theorem fac_live_sound :
  deadlock_free (∅, {[+ FirstAction.fac_go +]}) ∧ no_tau_divergence (∅, {[+ FirstAction.fac_go +]}).
Proof. apply (live_soundness_created _ _ TUnit TreeCopy.tca_created); [constructor|apply fac_gstyped]. Qed.
