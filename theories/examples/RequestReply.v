(** * request/reply: typable, recursive (SHARP-EDGES 65)

    C states every round at once:

      C = {ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1  ∣  k ∈ ℕ}
      srv : □(∀ι ι′. C. ∗ ⊸ (Sa@ι ⊗ Sb@ι′ ⊸^{ι′} ∗))
      srv = !(f = λp. let (a, b) = p in let (x, a) = recv a in let () = x in
                     spawn (λv. let () = v in (force f) ⟨a, send ⟨∗, b⟩⟩))
      cli : the same box over the dual sessions
      cli = !(f = λp. let (a, b) = p in let (a, u) = ⟨send ⟨∗, a⟩, ∗⟩ in let () = u in
                     let (x, b) = recv b in let () = x in
                     spawn (λv. let () = v in (force f) ⟨a, b⟩))
      main = let (s, c) = ⟨srv, cli⟩ in let (a, a′) = new ∗ in let (b, b′) = new ∗ in
             let () = spawn (λu. let () = u in (force s) ⟨a, b⟩) in (force c) ⟨a′, b′⟩

    The recursive force at (ι+1, ι′+1) asks C there, and C[ι+1, ι′+1] ⊆ C,
    so the body's own hypothesis gives it ([bcs_hold_self]). The send in
    the server's thunk blocks at ι′ while the pair holds a at ι+1, the
    fact ι′ ≺ ι+1 of C.

    main types under the hypotheses of its two top-level points γ and
    ε ([rr_Ψ]). It creates a at γ with no fact and b at ε with the
    creation constraint {γ+k ≺ ε+k, ε+k ≺ γ+k+1 ∣ k ∈ ℕ}, and forces
    both boxes at (γ, ε) (sharp edges 105, 172).

    With end points the gates compare with partner points:
    C = {ι+k ≺ (ι′+k)‾, ι′+k ≺ (ι+k+1)‾ ∣ k ∈ ℕ}, and the upper point of
    both bodies is ι̅′+1. main forces srv at (γ, ε) and cli at (γ̄, ε̄),
    a is created with {γ ≺ γ̄} and b with both instances of C. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Definition rq_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 0 k) (pt_dual (pv 1 k)) ∨ g = FLt (pv 1 k) (pt_dual (pv 0 (S k))).
Definition rq_C : bcs := BCs [] rq_P.

Definition srv_body : ty :=
  TLolli (Some (pt_dual (pv 1 1))) None (TProd (TSess Sa (pv 0 0)) (TSess Sb (pv 1 0))) TUnit.
Definition cli_body : ty :=
  TLolli (Some (pt_dual (pv 1 1))) None (TProd (TSess (dual Sa) (pv 0 0)) (TSess (dual Sb) (pv 1 0))) TUnit.

Definition srv : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (App ESpawn (Lam (LetU (Var 0)
      (App (App EForce (Var 6)) (Pair (Var 1) (App ESend (Pair EUnit (Var 3)))))))))))).

Definition cli : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 2)) (LetU (Var 1)
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 4) (Var 1)))))))))))).

Definition rr_main : expr :=
  LetP (Pair srv cli) (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

(** C[ι+1, ι′+1] ⊆ C. *)
Lemma rq_step g : rq_P g → fact_scoped 2 g → rq_P (fact_map (pt_inst (plist [pv 0 1; pv 1 1])) g).
Proof. intros (k & [-> | ->]) _; exists (S k); [by left|by right]. Qed.

Lemma rq_call W Ψ :
  (rq_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pv 0 1; pv 1 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rq_step]. Qed.

Lemma srv_typed W F : world_wf W → typed W ∅ [] ∅ [] F srv (TBox 2 0 rq_C (TLolli None None TUnit srv_body)).
Proof.
  intros HW. unfold srv.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open rq_C srv_body. cbn. unfold srv_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SSeq (SRcv 0 TUnit) Sa) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pt_dual (pv 1 0))|].
      exists (pt_dual (pv 1 1)). split; [done|]. right.
      eapply sl_trans; [hyp0 (pv 0 0) (pt_dual (pv 1 0))|apply (slt_po W _ (pt_dual (pv 1 0)) HW)]. }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 1 2))) (Some (pv 0 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [right; apply sl_dpo|right; hyp0 (pv 0 0) (pt_dual (pv 1 0))]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rq_C None srv_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep.
    + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 1 0)))).
      * tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      * apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
      * kscope.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pt_dual (pv 0 1))|].
        exists (pt_dual (pv 1 2)). split; [done|]. right. apply sl_ppo, ppo_same; [done|cbn; lia].
    + tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pv 1 2)). split; [done|]. apply sle_refl, HW.
Qed.

Lemma cli_typed W F : world_wf W → typed W ∅ [] ∅ [] F cli (TBox 2 0 rq_C (TLolli None None TUnit cli_body)).
Proof.
  intros HW. unfold cli.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open rq_C cli_body. cbn. unfold cli_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (dual Sa)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (dual Sa) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pt_dual (pv 1 0))|].
      exists (pt_dual (pv 1 1)). split; [done|]. right.
      eapply sl_trans; [hyp0 (pv 0 0) (pt_dual (pv 1 0))|apply (slt_po W _ (pt_dual (pv 1 0)) HW)]. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0)) (TSess (SSeq (SRcv 0 TUnit) (dual Sb)) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pt_dual (pv 0 1))|].
      exists (pt_dual (pv 1 1)). split; [done|]. right. apply sl_dpo. }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 1 2))) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (pv 1 0) (pt_dual (pv 0 1))|right; apply sl_dpo]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rq_C None cli_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pv 1 2)). split; [done|]. apply sle_refl, HW.
Qed.

(** The constraint of b: the variable 0 is ε, the variable 1 is γ. *)
Definition rrf_facts (g : fact) : Prop :=
  ∃ k, g = FLt (pv 1 k) (pt_dual (pv 0 k)) ∨ g = FLt (pv 0 k) (pt_dual (pv 1 (S k))) ∨
       g = FLt (pt_dual (pv 1 k)) (pv 0 k) ∨ g = FLt (pt_dual (pv 0 k)) (pv 1 (S k)).
Definition rrf_C : bcs := BCs [pconst 1] rrf_facts.

Definition rr_Ψ : hyps :=
  ([] ++ [(ccd_C, [pconst 1])]) ++ [(rrf_C, [pconst 0])].

Lemma rr_created : created (Wpo []) rr_Ψ.
Proof.
  pose proof (proj1 Wpo_nil_strict') as HW.
  refine (created_fresh (Wpo []) ([] ++ [(ccd_C, [pconst 1])]) rrf_C 0 _ _ _ _ ltac:(fresh_const)).
  { apply created_snoc; [constructor|apply ccd_ok|constructor|fresh_const]. }
  { intros f [k [-> | [-> | [-> | ->]]]] Hs.
    - left. eexists _, _. split; [done|]. split_and!; [exists k; by left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [exists k; by right; left|done|done|done].
    - left. eexists _, _. split; [done|]. split_and!; [exists k; by right; right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [exists k; by right; right; right|done|done|done]. }
  { cbn. constructor; [|constructor]. eapply skn_inst; [by left|by left|done]. }
  { intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) [_ Hpq]%ple_inv.
    destruct Hf as [k [E|[E|[E|E]]]]; injection E as -> ->; try done;
    destruct Hf' as [k' [E|[E|[E|E]]]]; injection E as -> ->; try done;
    cbn in Hpq; unfold fresh_outer; cbn; apply sl_w, wf_lt_same; [done|done|cbn; lia|done|done|cbn; lia
      |done|done|cbn; lia|done|done|cbn; lia]. }
Qed.

Lemma rr_typed : styped ∅ rr_Ψ [] (∅, None) rr_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold rr_main, let_new_pair_at, rr_Ψ.
  tstep.
  { tstep; (apply typed_hyps_nil; [exact HWs|]); [apply cli_typed, HW|apply srv_typed, HW]. }
  cbn.
  new_top HWs Sa (pconst 1). new_top HWs Sb (pconst 0).
  fresh_clean.
  set (Ψ := [(ccd_C, [pconst 1]); (rrf_C, [pconst 0])]).
  assert (slt W Ψ (pconst 1) (pt_dual (pconst 1))) as Hcc by (apply slt_ccd; by left).
  assert (∀ k, slt W Ψ (pc 1 k) (pt_dual (pc 0 k))) as Hlo.
  { intros k. apply (slt_hyp_fresh W Ψ rrf_C (pconst 0) (pv 1 k) (pt_dual (pv 0 k)));
      [by right; left|exists k; by left|cbn; lia]. }
  assert (∀ k, slt W Ψ (pc 0 k) (pt_dual (pc 1 (S k)))) as Hhi.
  { intros k. apply (slt_hyp_fresh W Ψ rrf_C (pconst 0) (pv 0 k) (pt_dual (pv 1 (S k))));
      [by right; left|exists k; by right; left|cbn; lia]. }
  assert (∀ k, slt W Ψ (pt_dual (pc 1 k)) (pc 0 k)) as Hlo'.
  { intros k. apply (slt_hyp_fresh W Ψ rrf_C (pconst 0) (pt_dual (pv 1 k)) (pv 0 k));
      [by right; left|exists k; by right; right; left|cbn; lia]. }
  assert (∀ k, slt W Ψ (pt_dual (pc 0 k)) (pc 1 (S k))) as Hhi'.
  { intros k. apply (slt_hyp_fresh W Ψ rrf_C (pconst 0) (pt_dual (pv 0 k)) (pv 1 (S k)));
      [by right; left|exists k; by right; right; right|cbn; lia]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pconst 1; pconst 0]) as HC.
  { apply bcs_hold_intro. intros g (k & [-> | ->]) _; cbn; [apply Hlo|apply Hhi]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pt_dual (pconst 1); pt_dual (pconst 0)]) as HC'.
  { apply bcs_hold_intro. intros g (k & [-> | ->]) _; cbn; [exact (Hlo' k)|exact (Hhi' k)]. }
  assert (Forall (skn W Ψ) [pconst 1; pconst 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pconst 1); pt_dual (pconst 0)]) as HK'.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess (dual Sb) (pt_dual (pconst 0))); change B with (TSess Sb (pconst 0));
    change A' with (TSess (dual Sa) (pt_dual (pconst 1))); change B' with (TSess Sa (pconst 1));
    change D with (TBox 2 0 rq_C (TLolli None None TUnit cli_body));
    change E with (TBox 2 0 rq_C (TLolli None None TUnit srv_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pc 0 1))) (Some (pconst 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [right; exact Hcc|right; apply (Hlo 0)]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 rq_C None srv_body [pconst 1; pconst 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pc 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rq_C None cli_body [pt_dual (pconst 1); pt_dual (pconst 0)]);
      [done|done|exact HC'|exact HK'|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rr_deadlock_free : deadlock_free (∅, {[+ rr_main +]}).
Proof.
  apply (soundness_created_s rr_Ψ _ TUnit rr_created); [constructor|apply rr_typed].
Qed.
