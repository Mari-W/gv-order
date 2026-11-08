(** * cycle: typable

    cycle = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
            let () = spawn (λu. let () = u in let () = close c′ in close d′) in
            let () = close c in close d

    c, c′ : Close@(a,0) and d, d′ : Close@(b,0). Both threads close c
    while they hold d, so both need (a,0) ≺ (b,0).
    The paper's P-Connect over {c, d} is here the closed program that
    creates both channels.

    The program types under the hypotheses of its two top-level points
    ([cycle_Ψ]). c is created with no fact and d with the creation
    constraint γ ≺ ε, where γ and ε are the points of c and d (sharp
    edges 105, 172).

    With end points the thunk holds c′ and d′ at γ̄ and ε̄. Its gate asks
    γ̄ ≺ ε, the main thread's gate asks γ ≺ ε̄, and the upper point ε̄ of
    the thunk asks γ̄ ≺ ε̄. The constraint of d is {γ, γ̄} ≺ {ε, ε̄}
    ([freshp_bcs]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Definition cycle_thunk : expr :=
  Lam (LetU (Var 0) (LetU (App EClos (Var 3)) (App EClos (Var 1)))).

Definition cycle_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Definition cycle_Lc : list (point * bool) :=
  [(pvar 0, true); (pvar 0, false); (pt_dual (pvar 0), true); (pt_dual (pvar 0), false)].

Definition cycle_Ψ : hyps :=
  hyps_inst (pshift 1) (hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) (fresh_bcs [] []), ids 1)]) ++
    [(bcs_inst (pshift 1) (freshp_bcs cycle_Lc []), ids 1)].

Lemma cycle_created : created (Wpo []) cycle_Ψ.
Proof.
  apply created_p; [apply created_lh; [constructor|constructor|set_solver]| |].
  { cbn. repeat (apply Forall_cons; split; [eapply skn_inst; [by left|by left|done]|]). by apply Forall_nil. }
  { intros l h b _ Hh. by apply elem_of_nil in Hh. }
Qed.

Lemma cycle_typed : styped ∅ cycle_Ψ [] (∅, None) cycle_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold cycle_main, cycle_Ψ.
  new_top HWs SEnd (pvar 1). new_top HWs SEnd (pvar 0).
  set (Lc := cycle_Lc).
  fresh_clean.
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 1]);
             (bcs_inst (pshift 1) (freshp_bcs Lc []), [pvar 0])]).
  assert (∀ l b, (l, b) ∈ Lc → slt W Ψ (pt_inst (pshift 1) l) (pt_polar b (pvar 0))) as HL.
  { intros l b Hl. by apply (slt_freshp_l W Ψ (pshift 1) Lc [] (pvar 0)); [right; left|]. }
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hγε by (apply (HL (pvar 0) true); set_solver).
  assert (slt W Ψ (pvar 1) (pt_dual (pvar 0))) as Hγε'.
  { apply (HL (pvar 0) false); set_solver. }
  assert (slt W Ψ (pt_dual (pvar 1)) (pvar 0)) as Hγ'ε.
  { apply (HL (pt_dual (pvar 0)) true); set_solver. }
  assert (slt W Ψ (pt_dual (pvar 1)) (pt_dual (pvar 0))) as Hγ'ε'.
  { apply (HL (pt_dual (pvar 0)) false); set_solver. }
  tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pvar 0))) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; done]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
        exists (pt_dual (pvar 0)). split; [done|]. right. done.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_dual (pvar 0)). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [|done].
    intros y Hy. mem_cases Hy. done. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma cycle_deadlock_free : deadlock_free (∅, {[+ cycle_main +]}).
Proof.
  apply (soundness_created_s cycle_Ψ _ TUnit cycle_created); [constructor|apply cycle_typed].
Qed.
