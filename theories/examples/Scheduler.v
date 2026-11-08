(** * scheduler: typable

    A reduced variant of Milner's cyclic scheduler, three agents on a
    ring r₀, r₁, r₂, as a closed program. It has no collectors, and one
    of its agents is a [link]. Dardha and Gay's Example 1
    (dardha2018new p. 3) in full, k agents in a ring with one collector
    each, is examples/MilnerSched.v.

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
    for r₀ and r₁. [sched_rev_underivable] (examples/Rejected.v) proves
    that the three facts do not hold together.

    The program types under the hypotheses of its two top-level points
    γ and ε ([sched_Ψ]). r₀ is created at γ with no fact, r₁ by the
    alias at γ, which gives the alias that link needs, and r₂ at ε with
    γ+1 ≺ ε (sharp edges 105, 172). The points (a,0), (b,0) and (c,0)
    above are γ, ε and γ.

    With end points ag₁ holds r₁ at γ and r₀′ at γ̄, so its lower point
    lies below both partners. r₀ is created with {γ ≺ γ̄} ([ccd_C]),
    and r₂ with γ+1 ≺ ε for ag₀ and γ̄+1 ≺ ε̄ for ag₂, which holds r₂ at
    ε while it acts on r₁′ at γ̄. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Definition ag1_thunk : expr := Lam (LetU (Var 0) (App ELink (Pair (Var 4) (Var 5)))).
Definition ag2_thunk : expr := Lam (LetU (Var 0) (LetU (recvclose (Var 3)) (sendclose (Var 2)))).
Definition ag0 : expr := LetU (sendclose (Var 5)) (recvclose (Var 0)).

Definition sched_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Definition sched_Lr : list (point * bool) :=
  [(Pt (NVar 0) 1, true); (pt_dual (Pt (NVar 0) 1), false)].

Definition sched_Ψ : hyps :=
  hyps_inst (pshift 1) (hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) ccd_C, ids 1)]) ++
    [(bcs_inst (pshift 1) (freshp_bcs sched_Lr []), ids 1)].

Lemma sched_created : created (Wpo []) sched_Ψ.
Proof.
  apply created_p; [apply created_snoc; [constructor|apply ccd_ok|constructor]| |].
  { cbn. repeat (apply Forall_cons; split; [eapply skn_inst; [by left|by left|done]|]). by apply Forall_nil. }
  { intros l h b _ Hh. by apply elem_of_nil in Hh. }
Qed.

Lemma sched_typed : styped ∅ sched_Ψ [] (∅, None) sched_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold sched_main, sched_Ψ.
  new_top HWs Sd (pvar 1). new_top HWs Sd (pvar 1). new_top HWs Sd (pvar 0).
  set (Lr := sched_Lr).
  fresh_clean.
  set (Ψ := [(ccd_C, [pvar 1]); (bcs_inst (pshift 1) (freshp_bcs Lr []), [pvar 0])]).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1) in *.
  assert (slt W Ψ (pvar 1) (pt_dual (pvar 1))) as Hcc by (apply slt_ccd; by left).
  assert (slt W Ψ (pv 1 1) (pvar 0)) as Hab.
  { apply (slt_freshp_l W Ψ (pshift 1) Lr [] (pvar 0) (Pt (NVar 0) 1) true);
      [by right; left|by left]. }
  assert (slt W Ψ (pt_dual (pv 1 1)) (pt_dual (pvar 0))) as Hab'.
  { apply (slt_freshp_l W Ψ (pshift 1) Lr [] (pvar 0) (pt_dual (Pt (NVar 0) 1)) false);
      [by right; left|by right; left]. }
  assert (slt W Ψ (pt_dual (pvar 1)) (pt_dual (pvar 0))) as Ha0b'.
  { eapply sl_trans; [apply (slt_po W _ (pt_dual (pvar 1)) HW)|exact Hab']. }
  assert (slt W Ψ (pt_dual (pvar 0)) (pv 0 1)) as Hb'b1 by apply sl_dpo.
  assert (slt W Ψ (pt_dual (pv 1 1)) (pv 0 1)) as Hc1b1' by (eapply sl_trans; [exact Hab'|exact Hb'b1]).
  assert (slt W Ψ (pt_dual (pvar 1)) (pv 0 1)) as Hc0b1' by (eapply sl_trans; [exact Ha0b'|exact Hb'b1]).
  assert (slt W Ψ (pvar 1) (pt_dual (pvar 0))) as Hab0' by (eapply sl_trans; [exact Hcc|exact Ha0b']).
  assert (slt W Ψ (pvar 1) (pvar 0)) as Ha0b.
  { eapply sl_trans; [apply (slt_po W _ (pvar 1) HW)|exact Hab]. }
  assert (slt W Ψ (pvar 0) (pv 0 1)) as Hbb by apply (slt_po W _ (pvar 0) HW).
  assert (slt W Ψ (pvar 1) (pv 0 1)) as Hc0b1 by (eapply sl_trans; [exact Ha0b|exact Hbb]).
  assert (slt W Ψ (pv 1 1) (pv 0 1)) as Hc1b1 by (eapply sl_trans; [exact Hab|exact Hbb]).
  tstep.
  { (* ag₁ = link ⟨r₁, r₀⟩ *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; done]. }
      cbn. tstep; [tstep|]. cbn.
      tstep; [tstep; tstep|apply (KTLink _ _ _ Sd (pvar 1))|done|].
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
  apply (soundness_created_s sched_Ψ _ TUnit sched_created); [constructor|apply sched_typed].
Qed.
