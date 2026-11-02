(** * scheduler: typable

    Milner's scheduler with three agents on a ring r₀, r₁, r₂, as a
    closed program.

      ag₀ = let () = close (send ⟨∗, r₀⟩) in recvclose r₂          (main)
      ag₁ = link ⟨r₁, r₀⟩                                          (spawned)
      ag₂ = let () = recvclose r₁ in close (send ⟨∗, r₂⟩)          (spawned)
      recvclose r = let (x, r) = recv r in let () = x in close r

    r₀ lives at (a,0), r₂ at (b,0) and r₁ at (c,0). link asks
    (c,0) ≡ (a,0) (KTLink), the spec's (r₁,0) ≡ (r₀,0). ag₀ holds r₂ while
    it sends and closes r₀, so it needs (a,1) ≺ (b,0). ag₂ holds r₂ while
    it receives on and closes r₁, so it needs (c,0) ≺ (b,0) and
    (c,1) ≺ (b,0), which follow through the alias and successor
    congruence. The world has the alias and (a,1) ≺ (b,0).

    Reversed ag₀ = let () = recvclose r₂ in close (send ⟨∗, r₀⟩) is
    rejected: it receives on r₂ at (b,0) while it holds r₀ at (a,0), so
    E-Let* and E-App ask (b,0) ≺ (a,0), while ag₂ asks (c,0) ≺ (b,0), and
    (c,0) ≡ (a,0) closes the cycle (a,0) ≺ (b,0) ≺ (a,0). No strict world
    has all three, and link needs the alias whatever points [new] picks
    for r₀ and r₁.

    The program types in the empty world. r₀ is created at γ with no
    fact, r₁ by the alias at γ, which gives the alias that link needs,
    and r₂ at ε with γ+1 ≺ ε (sharp edges 105). The points (a,0), (b,0)
    and (c,0) above are γ, ε and γ. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition ag1_thunk : expr := Lam (LetU (Var 0) (App ELink (Pair (Var 4) (Var 5)))).
Definition ag2_thunk : expr := Lam (LetU (Var 0) (LetU (recvclose (Var 3)) (sendclose (Var 2)))).
Definition ag0 : expr := LetU (sendclose (Var 5)) (recvclose (Var 0)).

Definition sched_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed : styped ∅ [] [] (∅, None) sched_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold sched_main.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sd [] []); [constructor|set_solver|].
  fresh_clean.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pvar 0) HWs); [eapply skn_inst; [by left|by left|done]|].
  cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sd [Pt (NVar 0) 1] []).
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

Lemma sched_deadlock_free : deadlock_free (∅, {[+ sched_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply sched_typed].
Qed.
