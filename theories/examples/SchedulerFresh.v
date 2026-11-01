(** * scheduler with fresh points

    [sched_main] of Scheduler.v. r₀ is created at a fresh γ with no
    facts. r₁ needs the alias (r₁,0) ≡ (r₀,0) for the link, so the old
    rule E-Const creates it at γ itself, which the hypothesis of r₀
    makes known. r₂ is created at a fresh ε with γ+1 ≺ ε (L = [γ+1]).
    The world of Scheduler.v had three constants, one alias and one
    fact. Here it is empty. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Scheduler.

Set Default Proof Using "All".

Lemma sched_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) sched_main TUnit.
Proof.
  intros HW. unfold sched_main.
  apply (t_newfresh_lh W _ _ ∅ _ _ _ _ Sd [] []); [constructor|set_solver|].
  fresh_clean.
  tstep.
  { tstep; [tstep| |done|apply ubs_none].
    apply (KTNew _ _ _ Sd (pvar 0)). eapply skn_inst; [by left|by left|done]. }
  cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sd [Pt (NVar 0) 1] [] ltac:(done)).
  { constructor; [|constructor]. eapply skn_inst; [by left|by left|done]. }
  { intros l h _ Hh. by apply elem_of_nil in Hh. }
  fresh_clean.
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pt_inst (pshift 1) (pvar 0)]);
             (bcs_inst (pshift 1) (fresh_bcs [Pt (NVar 0) 1] []), [pvar 0])]).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1) in *.
  assert (slt W Ψ (pv 1 1) (pvar 0)) as Hab.
  { apply (slt_fresh_l W Ψ (pshift 1) [Pt (NVar 0) 1] [] (pvar 0) (Pt (NVar 0) 1));
      [by right; left|by left]. }
  assert (slt W Ψ (pvar 1) (pvar 0)) as Ha0b.
  { eapply sl_trans; [apply (slt_po W _ (pvar 1) HW)|exact Hab]. }
  assert (slt W Ψ (pvar 0) (pv 0 1)) as Hbb by apply (slt_po W _ (pvar 0) HW).
  assert (slt W Ψ (pvar 1) (pv 0 1)) as Hc0b1 by (eapply sl_trans; [exact Ha0b|exact Hbb]).
  assert (slt W Ψ (pv 1 1) (pv 0 1)) as Hc1b1 by (eapply sl_trans; [exact Hab|exact Hbb]).
  tstep.
  { (* ag₁ = link ⟨r₁, r₀⟩ *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      tstep; [tstep; tstep|apply (KTLink _ _ _ Sd (pvar 1) (pvar 1) (se_refl _ _ _))|done|].
      apply ubs_none.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { (* ag₂ = let () = recvclose r₁ in close (send ⟨∗, r₂⟩) *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; done]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + unfold recvclose. tstep.
        * tstep; [tstep|apply KTRecv|kscope|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
          exists (pv 0 1). split; [done|]. right. done.
        * cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
          exists (pv 0 1). split; [done|]. right. done.
      + unfold sendclose. tstep.
        * tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pvar 0)); cbn; set_solver|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 0 1). split; [done|]. right. done.
        * apply KTClos.
        * done.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  (* ag₀ *)
  cbn. unfold ag0, sendclose, recvclose. tstep.
  { tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pvar 1)); cbn; set_solver|done|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done.
    - apply KTClos.
    - done.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma sched_deadlock_free_fresh : deadlock_free (∅, {[+ sched_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply sched_typed_fresh, Wpo_nil_strict.
Qed.
