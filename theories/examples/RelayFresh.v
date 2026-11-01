(** * relay with a fresh point for d

    [rel_main] of Relay.v. c stays at the constant point (a, 0) and is
    created by E-Const. Its facts relate (a, k) to its own carried
    points (a, k)[0], and the constraint of E-NewFresh relates a fresh
    point to outer points only, so these facts stay in the world. d is
    created at a fresh ε with

      {(a,0) ≺ ε,  (a,0)[0] ≺ ε,  ε ≺ (a,1),  ε ≺ (a,0)[0]+1}.

    Betweenness asks (a,0) ≺ (a,1), (a,0) ≺ (a,0)[0]+1, (a,0)[0] ≺ (a,1)
    and (a,0)[0] ≺ (a,0)[0]+1, which program order and the facts of c
    give. The world loses the constant b and the four facts on (b, 0). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Relay.

Set Default Proof Using "All".

Abbreviation sl0 o := (Pt (NSlot (NConst 0) 0 0) o).

(** The constraint of d: the variable 0 is ε, 1 is (a,0), 2 is (a,0)[0]. *)
Definition relf_facts (g : fact) : Prop :=
  g = FLt (pvar 1) (pvar 0) ∨ g = FLt (pvar 2) (pvar 0) ∨
  g = FLt (pvar 0) (pv 1 1) ∨ g = FLt (pvar 0) (pv 2 1).
Definition relf_C : bcs := BCs [pc 0 0; sl0 0] relf_facts.

(** The facts of c that stay in the world. *)
Definition rel_own (W : world) : Prop :=
  (∀ k, w_lt W (pc 0 k) (rel_sl k) ∧ w_lt W (rel_sl k) (pt_shift 1 (pc 0 k))) ∧
  (∀ k, w_lt W (pc 0 (S k)) (rel_ip (S k)) ∧ w_lt W (rel_sl (S k)) (rel_ip (S k)) ∧
        w_lt W (rel_ip (S k)) (pt_shift 1 (pc 0 (S k))) ∧
        w_lt W (rel_ip (S k)) (pt_shift 1 (rel_sl (S k)))).

(** [rel_main] with d bound by the encoded let of new (sharp edges
    99). *)
Definition rel_main_ex : expr :=
  LetP (Pair relay prod) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

Lemma rel_typed_fresh W : strict W → pt_known W (pc 0 0) → rel_own W →
  typed W ∅ [] ∅ [] (∅, None) rel_main_ex TUnit.
Proof.
  intros HWs Ha [Hown Hrnd]. pose proof (proj1 HWs) as HW. unfold rel_main_ex.
  destruct (Hown 0) as [Ha0s Hsa1].
  tstep.
  { tstep; [apply prod_typed, HWs|apply relay_typed, HW]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ Srl (pc 0 0) HWs (or_introl Ha)).
  cbn.
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ SEnd relf_C _ _ _ _).
  { intros f Hf Hs. destruct Hf as [-> | [-> | [-> | ->]]].
    - left. eexists _, _. split; [done|]. split_and!; [by left|done|done|done].
    - left. eexists _, _. split; [done|]. split_and!; [by right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [by right; right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [by right; right; right|done|done|done]. }
  { constructor; [by left|constructor; [by left|constructor]]. }
  { intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) _.
    destruct Hf as [E|[E|[E|E]]]; injection E as -> ->; try done;
    destruct Hf' as [E|[E|[E|E]]]; injection E as -> ->; try done; unfold fresh_outer; cbn.
    - apply sl_w, wf_lt_same; [done|done|cbn; lia].
    - apply sl_w. eapply (wf_lt_trans _ HW); [exact Ha0s|]. apply wf_lt_same; [done|done|cbn; lia].
    - apply sl_w. exact Hsa1.
    - apply sl_w, wf_lt_same; [done|done|cbn; lia]. }
  fresh_clean.
  set (Ψ := [(bcs_inst (pshift 1) relf_C, [pvar 0])]).
  assert (∀ u v, relf_facts (FLt u v) → fact_scoped 3 (FLt u v) →
            slt W Ψ (pt_inst (plist [pvar 0; pc 0 0; sl0 0]) u) (pt_inst (plist [pvar 0; pc 0 0; sl0 0]) v))
    as Hhyp.
  { intros u v Hf Hs. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) relf_C) (pvar 0) u v);
      [by left|done|done]. }
  assert (slt W Ψ (pc 0 0) (pvar 0)) as H1 by (apply (Hhyp (pvar 1) (pvar 0)); [by left|cbn; lia]).
  assert (slt W Ψ (sl0 0) (pvar 0)) as H2
    by (apply (Hhyp (pvar 2) (pvar 0)); [by right; left|cbn; lia]).
  assert (slt W Ψ (pvar 0) (pc 0 1)) as H3
    by (apply (Hhyp (pvar 0) (pv 1 1)); [by right; right; left|cbn; lia]).
  assert (slt W Ψ (pvar 0) (sl0 1)) as H4
    by (apply (Hhyp (pvar 0) (pv 2 1)); [by right; right; right|cbn; lia]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pc 0 0; pvar 0]) as HC.
  { assert (∀ g, c0 (pc 0 0) (pvar 0) g → fact_holds (seqs W Ψ) (slt W Ψ) g) as Hc0.
    { intros g Hg. unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn;
        first [exact H1|exact H2|exact H3|exact H4|apply sl_w; exact Ha0s|apply sl_w; exact Hsa1]. }
    assert (∀ k g, c0 (pc 0 (S k)) (rel_ip (S k)) g → fact_holds (seqs W Ψ) (slt W Ψ) g) as HcS.
    { intros k g Hg. destruct (Hrnd k) as (A1 & A2 & A3 & A4). destruct (Hown (S k)) as [A5 A6].
      unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn; apply sl_w;
        first [exact A1|exact A2|exact A3|exact A4|exact A5|exact A6]. }
    apply bcs_hold_intro. intros g [Hg|(k & Hg)] _.
    - apply Hc0. exact (c0_inst _ _ _ _ Hg).
    - apply (HcS k). exact (c0_inst _ _ _ _ Hg). }
  assert (Forall (skn W Ψ) [pc 0 0; pvar 0]) as HK.
  { constructor; [by left|constructor; [eapply skn_inst; [by left|by left|done]|constructor]]. }
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess (dual SEnd) (pvar 0)); change B with (TSess SEnd (pvar 0));
    change A' with (TSess (dual Srl) (pc 0 0)); change B' with (TSess Srl (pc 0 0));
    change D with (TBox 2 rel_C (TLolli None None TUnit prod_body));
    change E with (TBox 2 rel_C (TLolli None None TUnit relay_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact H1]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 rel_C None relay_body [pc 0 0; pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None prod_body [pc 0 0; pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world: the constant a and the facts of c without b. *)
Definition rel1_facts (x y : point) : Prop :=
  rel_L_facts x y ∧ x ≠ pc 1 0 ∧ y ≠ pc 1 0.

Definition Wrel1 : world := wgen (list_to_set (NConst <$> [0])) (λ _ _, False) rel1_facts.

Lemma Wrel1_strict : strict Wrel1.
Proof.
  apply (wgen_strict _ _ _ id rel_rank); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y [(k & H) [Hx Hy]]; right; rewrite !elem_of_list_to_set;
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->];
      destruct k; cbn in *; first [set_solver|congruence].
  - intros x. unfold rel_rank, pt_shift. cbn.
    assert (0 < rel_step (pt_name x)) by (unfold rel_step; repeat case_match; lia). nia.
  - intros x y [(k & H) _]; unfold id;
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->];
      destruct k; unfold rel_rank; cbn; lia.
Qed.

Lemma rel_deadlock_free_fresh : deadlock_free (∅, {[+ rel_main_ex +]}).
Proof.
  apply (soundness Wrel1 _ TUnit Wrel1_strict).
  apply ptyped_closed; [constructor|]. apply rel_typed_fresh; [apply Wrel1_strict| |split].
  - unfold pt_known, Wrel1. simpl. set_solver.
  - intros k. split; apply glt_base; (split; [exists k|split; [destruct k; discriminate|]]);
      try naive_solver; destruct k; discriminate.
  - intros k. split_and!; apply glt_base; (split; [exists (S k); naive_solver|]); split; discriminate.
Qed.
