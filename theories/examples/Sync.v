(** * sync: typable

    sync = let (c, d) = new ∗ in
           let () = spawn (λu. let () = u in close (send ⟨∗, c⟩)) in
           let (x, d) = recv d in let () = x in close d

    c : !∗.Close@(a,0) and d : ?∗.Close@(a,0). Each thread holds one end
    only, so no fact beyond program order is needed. The thunk blocks
    at (a,0) and (a,1), its upper point is (a,1), its lower point (a,0). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Ssync : sty := SSnd 0 TUnit SEnd.

Definition sync_thunk : expr :=
  Lam (LetU (Var 0) (App EClos (App ESend (Pair EUnit (Var 2))))).

Definition sync_main : expr :=
  LetP (App ENew EUnit)
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Lemma sync_typed W : world_wf W → pt_known W (pc 0 0) →
  typed W ∅ [] ∅ [] (∅, None) sync_main TUnit.
Proof.
  intros HW Ha. unfold sync_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Ssync (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { cbn. tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      tstep.
      + tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
        * tstep; tstep.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
      + apply KTClos.
      + done.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma sync_deadlock_free : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  apply (soundness (Wpo [0]) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply sync_typed; [apply Wpo_strict|].
  unfold pt_known, Wpo. simpl. set_solver.
Qed.
