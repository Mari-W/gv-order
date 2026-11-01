(** * sync with a fresh point

    [sync_main] of Sync.v, its channel created by E-NewFresh with no
    facts. The world loses its one constant and becomes empty. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Sync.

Set Default Proof Using "All".

Lemma sync_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) sync_main TUnit.
Proof.
  intros HW. unfold sync_main.
  apply (t_newfresh_lh W _ _ ∅ _ _ _ _ Ssync [] []); [constructor|set_solver|].
  fresh_clean.
  tstep.
  { cbn. tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (Pt (NVar 0) 1)) (Some (pvar 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      tstep.
      + tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (pvar 0)); cbn; set_solver|done|].
        * tstep; tstep.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (Pt (NVar 0) 1). split; [done|]. right. apply (slt_po W _ (pvar 0) HW).
      + apply KTClos.
      + done.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (Pt (NVar 0) 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma sync_deadlock_free_fresh : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply sync_typed_fresh, Wpo_nil_strict.
Qed.
