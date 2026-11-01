(** * cycle with fresh points

    [cycle_main] of Cycle.v. c is created at a fresh γ with no facts,
    d at a fresh ε with γ ≺ ε (L = [γ]). The world of Cycle.v had two
    constants and the fact (0, 0) ≺ (1, 0). Here it is empty. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Cycle.

Set Default Proof Using "All".

(** [cycle_main] with d bound by the encoded let of new (sharp edges
    99). let p = new ∗ in let (d, d′) = p in … *)
Definition cycle_main_ex : expr :=
  LetP (App ENew EUnit) (let_new_pair
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Lemma cycle_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) cycle_main_ex TUnit.
Proof.
  intros HW. unfold cycle_main_ex.
  apply (t_newfresh_lh W _ _ ∅ _ _ _ _ SEnd [] []); [constructor|set_solver|].
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pvar 0] [] ltac:(done)).
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

Lemma cycle_deadlock_free_fresh : deadlock_free (∅, {[+ cycle_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply cycle_typed_fresh, Wpo_nil_strict.
Qed.
