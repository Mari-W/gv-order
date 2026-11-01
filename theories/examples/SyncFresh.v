(** * sync with a fresh point

    [sync_main] of Sync.v, its channel created by E-NewFresh with no
    facts. The world loses its one constant and becomes empty. The
    channel is bound by the encoded let of new, so the program is the
    copy [sync_main_ex] (sharp edges 99, 103). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Sync.

Set Default Proof Using "All".

(** [sync_main] with c bound by the encoded let of new. *)
Definition sync_main_ex : expr :=
  let_new_pair
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Lemma sync_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) sync_main_ex TUnit.
Proof.
  intros HW. unfold sync_main_ex, let_new_pair.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Ssync [] []); [constructor|set_solver|].
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

Lemma sync_deadlock_free_fresh : deadlock_free (∅, {[+ sync_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply sync_typed_fresh, Wpo_nil_strict.
Qed.
