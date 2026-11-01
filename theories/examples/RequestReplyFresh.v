(** * request/reply with fresh points

    [rr_main] of RequestReply.v. a is created at a fresh γ with no
    facts, b at a fresh ε with the infinite constraint

      {γ+k ≺ ε+k,  ε+k ≺ γ+k+1  ∣  k ∈ ℕ}.

    Betweenness asks γ+k ≺ γ+k′+1 for every pair of facts γ+k ≺ ε+k and
    ε+k′ ≺ γ+k′+1 with k ≤ k′, and program order gives it. The world of
    RequestReply.v held these facts on two constants. Here it is empty,
    and the box constraint is unchanged. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.RequestReply.

Set Default Proof Using "All".

(** The constraint of b: the variable 0 is ε, the variable 1 is γ. *)
Definition rrf_facts (g : fact) : Prop :=
  ∃ k, g = FLt (pv 1 k) (pv 0 k) ∨ g = FLt (pv 0 k) (pv 1 (S k)).
Definition rrf_C : bcs := BCs [pvar 0] rrf_facts.

Lemma rr_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) rr_main TUnit.
Proof.
  intros HW. unfold rr_main.
  tstep.
  { tstep; [apply cli_typed, HW|apply srv_typed, HW]. }
  cbn.
  apply (t_newfresh_lh W _ _ ∅ _ _ _ _ Sa [] []); [constructor|set_solver|].
  fresh_clean.
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ Sb rrf_C (pvar 1) _ _ _
           (fresh_lo_var1 (bc_env rrf_C) rrf_facts ltac:(done) ltac:(by exists 0; left)) _).
  { intros f [k [-> | ->]] Hs.
    - left. eexists _, _. split; [done|]. split_and!; [exists k; by left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [exists k; by right|done|done|done]. }
  { constructor; [|constructor]. eapply skn_inst; [by left|by left|done]. }
  { intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) [_ Hpq].
    destruct Hf as [k [E|E]]; injection E as -> ->; [|done].
    destruct Hf' as [k' [E|E]]; injection E as -> ->; [done|].
    cbn in Hpq. unfold fresh_outer. cbn. apply sl_w, wf_lt_same; [done|done|cbn; lia]. }
  fresh_clean.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 1]);
             (bcs_inst (pshift 1) rrf_C, [pvar 0])]).
  assert (∀ k, slt W Ψ (pv 1 k) (pv 0 k)) as Hlo.
  { intros k. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) rrf_C) (pvar 0) (pv 1 k) (pv 0 k));
      [by right; left|exists k; by left|cbn; lia]. }
  assert (∀ k, slt W Ψ (pv 0 k) (pv 1 (S k))) as Hhi.
  { intros k. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) rrf_C) (pvar 0) (pv 0 k) (pv 1 (S k)));
      [by right; left|exists k; by right|cbn; lia]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pvar 1; pvar 0]) as HC.
  { apply bcs_hold_intro. intros g (k & [-> | ->]) _; cbn; [apply Hlo|apply Hhi]. }
  assert (Forall (skn W Ψ) [pvar 1; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; Some ?A'; Some ?B'; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess (dual Sb) (pvar 0)); change B with (TSess Sb (pvar 0));
    change A' with (TSess (dual Sa) (pvar 1)); change B' with (TSess Sa (pvar 1));
    change D with (TBox 2 rq_C (TLolli None None TUnit cli_body));
    change E with (TBox 2 rq_C (TLolli None None TUnit srv_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Hlo 0)]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 rq_C None srv_body [pvar 1; pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None cli_body [pvar 1; pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rr_deadlock_free_fresh : deadlock_free (∅, {[+ rr_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply rr_typed_fresh, Wpo_nil_strict.
Qed.
