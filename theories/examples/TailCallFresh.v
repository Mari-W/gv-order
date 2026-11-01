(** * tail call with a fresh point

    [tc_main] of TailCall.v. c is created at a fresh γ with the
    infinite constraint {γ+k ≺ ζ ∣ k ∈ ℕ}, where ζ = (1, 0) is the
    ceiling. Every fact of the constraint has the form q ≺ v with q on
    the fresh channel, so betweenness holds vacuously. The world keeps
    the constant 1 for the ceiling and loses the constant 0 and all its
    facts (a,k) ≺ (1,0). The channel is bound by the encoded let of
    new, so the program is the copy [tc_main_ex] (sharp edges 99,
    103). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.TailCall.

Set Default Proof Using "All".

Definition tcf_facts (g : fact) : Prop := ∃ k, g = FLt (Pt (NVar 0) k) (pvar 1).
Definition tcf_C : bcs := BCs [pc 1 0] tcf_facts.

(** [tc_main] with c bound by the encoded let of new. *)
Definition tc_main_ex : expr :=
  LetP (Pair tcs tcr) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Lemma tc_typed_fresh W : world_wf W → pt_known W (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) tc_main_ex TUnit.
Proof.
  intros HW Hz. unfold tc_main_ex, let_new_pair.
  tstep.
  { tstep; [apply tcr_typed, HW|apply tcs_typed, HW]. }
  cbn.
  apply (t_newfresh_open W _ _ ∅ _ _ _ _ Sb tcf_C).
  { intros f [k ->] Hs. right. eexists _, _. split; [done|].
    split_and!; [by exists k|done|done|done]. }
  { constructor; [by left|constructor]. }
  { intros u p q v (Hf & _ & _ & Hu) _ _. destruct Hf as [k E]. by injection E as -> ->. }
  fresh_clean.
  set (Ψ := [(bcs_inst (pshift 1) tcf_C, [pvar 0])]).
  assert (∀ k, slt W Ψ (Pt (NVar 0) k) (pc 1 0)) as Hγζ.
  { intros k. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) tcf_C) (pvar 0) (Pt (NVar 0) k) (pvar 1));
      [by left|by exists k|cbn; lia]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) tc_C [pvar 0; pc 1 0]) as HC.
  { apply bcs_hold_intro. intros g (k & ->) _. apply (Hγζ k). }
  assert (Forall (skn W Ψ) [pvar 0; pc 1 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor; [by left|constructor]]. }
  match goal with |- typed _ _ _ _ [Some ?A; _; None; None; Some ?B; Some ?D] _ _ _ =>
    change A with (TSess (dual Sb) (pvar 0));
    change B with (TBox 2 tc_C (TLolli None None TUnit tcr_body));
    change D with (TBox 2 tc_C (TLolli None None TUnit tcs_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcr_body [pvar 0; pc 1 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcs_body [pvar 0; pc 1 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world: the ceiling's constant 1 and no fact. *)
Lemma tc_deadlock_free_fresh : deadlock_free (∅, {[+ tc_main_ex +]}).
Proof.
  apply (soundness (Wpo [1]) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply tc_typed_fresh; [apply Wpo_strict|].
  unfold pt_known, Wpo. simpl. set_solver.
Qed.
