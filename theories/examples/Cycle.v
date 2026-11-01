(** * cycle: typable

    cycle = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
            let () = spawn (λu. let () = u in let () = close c′ in close d′) in
            let () = close c in close d

    c, c′ : Close@(a,0) and d, d′ : Close@(b,0). Both threads close c
    while they hold d, so both need (a,0) ≺ (b,0), and the world has it.
    The paper's P-Connect over {c, d} is here the closed program that
    creates both channels. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition cycle_thunk : expr :=
  Lam (LetU (Var 0) (LetU (App EClos (Var 3)) (App EClos (Var 1)))).

Definition cycle_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Lemma cycle_typed W : strict W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  w_lt W (pc 0 0) (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) cycle_main TUnit.
Proof.
  intros HWs Ha Hb Hab. pose proof (proj1 HWs) as HW. unfold cycle_main.
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (pc 0 0) HWs (or_introl Ha)).
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (pc 1 0) HWs (or_introl Hb)).
  cbn. tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
        exists (pc 1 0). split; [done|]. right. by apply sl_w.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 0). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [|done].
    intros y Hy. mem_cases Hy. by apply sl_w. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wcycle : world := Wfacts [0; 1] [(pc 0 0, pc 1 0)].

Lemma Wcycle_strict : strict Wcycle.
Proof.
  apply (Wfacts_strict _ _ (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0)); [lia| |].
  - apply Forall_singleton. cbn. set_solver.
  - apply Forall_singleton. cbn. lia.
Qed.

Lemma cycle_deadlock_free : deadlock_free (∅, {[+ cycle_main +]}).
Proof.
  apply (soundness Wcycle _ TUnit Wcycle_strict).
  apply ptyped_closed; [constructor|]. apply cycle_typed; [apply Wcycle_strict| | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.
