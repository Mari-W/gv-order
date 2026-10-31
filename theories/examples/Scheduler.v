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
    for r₀ and r₁. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition ag1_thunk : expr := Lam (LetU (Var 0) (App ELink (Pair (Var 4) (Var 5)))).
Definition ag2_thunk : expr := Lam (LetU (Var 0) (LetU (recvclose (Var 3)) (sendclose (Var 2)))).
Definition ag0 : expr := LetU (sendclose (Var 5)) (recvclose (Var 0)).

Definition sched_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed W : world_wf W →
  pt_known W (pc 0 0) → pt_known W (pc 1 0) → pt_known W (pc 2 0) →
  w_eq W (pc 2 0) (pc 0 0) → w_lt W (pc 0 1) (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) sched_main TUnit.
Proof.
  intros HW Ha Hb Hc Hca Hab.
  assert (w_lt W (pc 0 0) (pc 1 0)) as Ha0b.
  { eapply (wf_lt_trans _ HW); [apply (wf_lt_po _ HW (pc 0 0))|exact Hab]. }
  assert (w_lt W (pc 2 0) (pc 1 0)) as Hc0b.
  { eapply (wf_lt_eq _ HW); [exact Hca|exact Ha0b|apply (wf_eq_refl _ HW)]. }
  assert (w_lt W (pc 2 1) (pc 1 0)) as Hc1b.
  { eapply (wf_lt_eq _ HW); [apply (wf_eq_shift _ HW _ _ Hca)|exact Hab|apply (wf_eq_refl _ HW)]. }
  assert (w_lt W (pc 1 0) (pc 1 1)) as Hbb by apply (wf_lt_po _ HW (pc 1 0)).
  unfold sched_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 2 0) (or_introl Hc))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 1 0) (or_introl Hb))|done|apply ubs_none]. }
  cbn. tstep.
  { (* ag₁ = link ⟨r₁, r₀⟩ *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 2 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|left; by apply se_sym, se_w]. }
      cbn. tstep; [tstep|]. cbn.
      tstep; [tstep; tstep|apply (KTLink _ _ _ Sd (pc 2 0) (pc 0 0) (se_w _ _ _ _ Hca))|done|].
      apply ubs_none.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { (* ag₂ = let () = recvclose r₁ in close (send ⟨∗, r₂⟩) *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 1)) (Some (pc 2 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + unfold recvclose. tstep.
        * tstep; [tstep|apply KTRecv|kscope|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
          exists (pc 1 1). split; [done|]. right. apply sl_w. by eapply (wf_lt_trans _ HW).
        * cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
          exists (pc 1 1). split; [done|]. right. apply sl_w. by eapply (wf_lt_trans _ HW).
      + unfold sendclose. tstep.
        * tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 1 0)); cbn; set_solver|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 1). split; [done|]. right. by apply sl_w.
        * apply KTClos.
        * done.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  (* ag₀ *)
  cbn. unfold ag0, sendclose, recvclose. tstep.
  { tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w.
    - apply KTClos.
    - done.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world: (c,0) ≡ (a,0) and (a,1) ≺ (b,0). The rank reads c as a. *)
Fixpoint ren20 (p : pname) : pname :=
  match p with
  | NConst a => if decide (a = 2) then NConst 0 else NConst a
  | NVar a => NVar a
  | NSlot q b i => NSlot (ren20 q) b i
  | NBr q b i => NBr (ren20 q) b i
  end.

Definition cn20 (x : point) : point := Pt (ren20 (pt_name x)) (pt_off x).

Definition Wsched : world :=
  wgen (list_to_set (NConst <$> [0; 1; 2]))
    (λ x y, x = pc 2 0 ∧ y = pc 0 0) (λ x y, x = pc 0 1 ∧ y = pc 1 0).

Lemma Wsched_strict : strict Wsched.
Proof.
  apply (wgen_strict _ _ _ cn20 (prank (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0))).
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y [-> ->]. right. unfold pt_root. simpl. set_solver.
  - intros x y [-> ->]. right. unfold pt_root. simpl. set_solver.
  - done.
  - done.
  - intros x y [-> ->]. done.
  - intros x. apply prank_shift. lia.
  - intros x y [-> ->]. vm_compute. lia.
Qed.

Lemma sched_deadlock_free : deadlock_free (∅, {[+ sched_main +]}).
Proof.
  apply (soundness Wsched _ TUnit Wsched_strict).
  apply ptyped_closed; [constructor|].
  apply sched_typed; [apply Wsched_strict|..].
  1-3: unfold pt_known; simpl; set_solver.
  - by apply geq_base.
  - by apply glt_base.
Qed.
