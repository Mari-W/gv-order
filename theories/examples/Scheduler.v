(** * scheduler: typable

    A reduced variant of Milner's cyclic scheduler, three agents on a
    ring r₀, r₁, r₂, as a closed program. It has no collectors, and one
    of its agents is a [link]. Dardha and Gay's Example 1
    (dardha2018new p. 3) in full, k agents in a ring with one collector
    each, is examples/MilnerSched.v.

      Sd  = !∗.Close
      ag₀ = close (send ⟨∗, r₀⟩); recvclose r₂           (main)
      ag₁ = link ⟨r₁, r₀⟩                                (spawned)
      ag₂ = recvclose r₁; close (send ⟨∗, r₂⟩)           (spawned)
      recvclose r = let (v : ∗, r′ : Close@(x+1)) = recv r in v; close r′
                                                         r at x

    The three channels come from

      let (r₀, …) = new γ { } ∗          r₀ at γ
      let (r₁, …) = new κ { κ ≡ γ } ∗    r₁ at γ
      let (r₂, …) = new ε { γ+1 ≺ ε } ∗  r₂ at ε

    link asks γ ≡ γ (KTLink), the spec's r₁ ≡ r₀. ag₀ holds r₂ while it
    sends and closes r₀, so it needs γ+1 ≺ ε. ag₂ holds r₂ while it
    receives on and closes r₁, so it needs γ ≺ ε and γ+1 ≺ ε, which
    follow through the alias and successor congruence. The λ of ag₁ is
    λ^γ_γ ∗ and the λ of ag₂ is λ^{ε+1}_γ ∗.

    Reversed ag₀ = recvclose r₂; close (send ⟨∗, r₀⟩) is rejected. It
    receives on r₂ at ε while it holds r₀ at γ, so E-Let∗ and E-App ask
    ε ≺ γ, while ag₂ asks γ ≺ ε, and γ ≡ γ closes the cycle γ ≺ ε ≺ γ. No
    strict order has all three, and link needs the alias whatever points
    new picks for r₀ and r₁. [sched_rev_underivable]
    (examples/Rejected.v) proves that the three facts do not hold
    together.

      ∅; · ⊢^∅ sched_main : ∗   so   thread sched_main is deadlock free

    (sharp edges 105) *)

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
      tstep; [tstep; tstep|apply (KTLink _ _ _ Sd (pvar 1) (pvar 1) (se_refl _ _ _))|].
      apply ubs_none.
    - apply KTSpawn.
    - apply ubs_none. }
  cbn. tstep.
  { (* ag₂ = recvclose r₁; close (send ⟨∗, r₂⟩) *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; done]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + unfold recvclose. tstep.
        * tstep; [tstep|apply KTRecv|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
          exists (pv 0 1). split; [done|]. right. done.
        * cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
          exists (pv 0 1). split; [done|]. right. done.
      + unfold sendclose. tstep.
        * tstep; [tstep; tstep|apply (KTSend _ _ _ TUnit SEnd (pvar 0)); cbn; set_solver|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 0 1). split; [done|]. right. done.
        * apply KTClos.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - apply ubs_none. }
  (* ag₀ *)
  cbn. unfold ag0, sendclose, recvclose. tstep.
  { tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ TUnit SEnd (pvar 1)); cbn; set_solver|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done.
    - apply KTClos.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma sched_deadlock_free : deadlock_free (∅, {[+ sched_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply sched_typed].
Qed.
