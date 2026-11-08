(** * sync: typable

    sync = let (c, d) = new ∗ in
           let () = spawn (λu. let () = u in close (send ⟨∗, c⟩)) in
           let (x, d) = recv d in let () = x in close d

    c : !∗.Close@ι and d : ?∗.Close@ι, with ι a top-level point
    created with no facts. Each thread holds one end only, so no fact
    beyond program order is needed. The thunk blocks at ι and ι+1, its
    upper point is ι+1, its lower point ι. The program types under the
    hypothesis of ι ([sync_Ψ]), and the run starts in a world that
    places ι (sharp edges 105, 172). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Ssync : sty := SSeq (SSnd 0 TUnit) SEnd.

Definition sync_thunk : expr :=
  Lam (LetU (Var 0) (App EClos (App ESend (Pair EUnit (Var 2))))).

Definition sync_main : expr :=
  let_new_pair
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Definition sync_Ψ : hyps := hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) (fresh_bcs [] []), ids 1)].

Lemma sync_created : created (Wpo []) sync_Ψ.
Proof. apply created_lh; [constructor|constructor|set_solver]. Qed.

Lemma sync_typed : styped ∅ sync_Ψ [] (∅, None) sync_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold sync_main, let_new_pair, sync_Ψ.
  new_top HWs Ssync (pvar 0).
  fresh_clean.
  tstep.
  { cbn. tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (Pt (NVar 0) 1)) (Some (pt_dual (pvar 0))) 0); [set_solver| |].
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

Lemma sync_deadlock_free : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  apply (soundness_created_s sync_Ψ _ TUnit sync_created); [constructor|apply sync_typed].
Qed.
