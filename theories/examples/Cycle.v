(** * cycle: typable

    cycle = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
            let () = spawn (λu. let () = u in let () = close c′ in close d′) in
            let () = close c in close d

    c, c′ : Close@(a,0) and d, d′ : Close@(b,0). Both threads close c
    while they hold d, so both need (a,0) ≺ (b,0), and the world has it.
    The paper's P-Connect over {c, d} is here the closed program that
    creates both channels.

    The program types in the empty world. c is created with no fact and
    d with the creation constraint γ ≺ ε, where γ and ε are the points of
    c and d (sharp edges 105). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition cycle_thunk : expr :=
  Lam (LetU (Var 0) (LetU (App EClos (Var 3)) (App EClos (Var 1)))).

Definition cycle_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Lemma cycle_typed W : world_wf W → typed W ∅ [] ∅ [] (∅, None) cycle_main TUnit.
Proof.
  intros HW. unfold cycle_main.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [] []); [constructor|set_solver|].
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pvar 0] []).
  { constructor; [|constructor]. eapply skn_inst; [by left|by left|done]. }
  { intros l h _ Hh. by apply elem_of_nil in Hh. }
  fresh_clean.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 1]);
             (bcs_inst (pshift 1) (fresh_bcs [pvar 0] []), [pvar 0])]).
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hγε.
  { apply (slt_fresh_l W Ψ (pshift 1) [pvar 0] [] (pvar 0) (pvar 0)); [by right; left|by left]. }
  tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 1)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; done]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
        exists (pvar 0). split; [done|]. right. done.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pvar 0). split; [done|]. apply sle_refl, HW.
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
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply cycle_typed, Wpo_strict.
Qed.
