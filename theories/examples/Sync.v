(** * sync: typable

      S    = !∗.Close
      sync = let (c : S@ι, c′ : S̄@ι) = new ι { } ∗ in
             spawn (λ^{ι+1}_{ι} ∗. close (send ⟨∗, c⟩));
             let (x : ∗, c′₁ : Close@(ι+1)) = recv c′ in
             x;
             close c′₁

    The creation constraint of ι is empty. Each thread holds one end
    only, so no fact beyond program order is needed. The thunk blocks at
    ι and ι+1, its upper point is ι+1 and its lower point ι.

      ∅; · ⊢^∅ sync : ∗        so        thread sync is deadlock free

    (sharp edges 105) *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Ssync : sty := SSnd TUnit SEnd.

Definition sync_thunk : expr :=
  Lam (LetU (Var 0) (App EClos (App ESend (Pair EUnit (Var 2))))).

Definition sync_main : expr :=
  let_new_pair
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Lemma sync_typed : styped ∅ [] [] (∅, None) sync_main TUnit.
Proof.
  apply styped_Wpo. pose proof (proj1 Wpo_nil_strict') as HW.
  set (W := Wpo []) in *. unfold sync_main, let_new_pair.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Ssync [] []); [constructor|set_solver|].
  fresh_clean.
  tstep.
  { cbn. tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (Pt (NVar 0) 1)) (Some (pvar 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      tstep.
      + tstep; [|apply (KTSend _ _ _ TUnit SEnd (pvar 0)); cbn; set_solver|].
        * tstep; tstep.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (Pt (NVar 0) 1). split; [done|]. right. apply (slt_po W _ (pvar 0) HW).
      + apply KTClos.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (Pt (NVar 0) 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma sync_deadlock_free : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply sync_typed].
Qed.
