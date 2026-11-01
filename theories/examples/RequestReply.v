(** * request/reply: typable, recursive (SHARP-EDGES 65)

    C states every round at once:

      C = {ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1  ∣  k ∈ ℕ}
      srv : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ (Sa@ι ⊗ Sb@ι′ ⊸^{ι′}_⊤ ∗))
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

    In the empty world main creates a at γ with no fact and b at ε with
    the creation constraint {γ+k ≺ ε+k, ε+k ≺ γ+k+1 ∣ k ∈ ℕ}, and forces
    both boxes at (γ, ε) (sharp edges 105). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition rq_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (pv 1 k) ∨ g = FLt (pv 1 k) (pv 0 (S k)).
Definition rq_C : bcs := BCs [] rq_P.

Definition srv_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Sa (pv 0 0)) (TSess Sb (pv 1 0))) TUnit.
Definition cli_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess (dual Sa) (pv 0 0)) (TSess (dual Sb) (pv 1 0))) TUnit.

Definition srv : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (App ESpawn (Lam (LetU (Var 0)
      (App (App EForce (Var 6)) (Pair (Var 1) (App ESend (Pair EUnit (Var 3)))))))))))).

Definition cli : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 2)) (LetU (Var 1)
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 4) (Var 1)))))))))))).

Definition rr_main : expr :=
  LetP (Pair srv cli) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

(** C[ι+1, ι′+1] ⊆ C. *)
Lemma rq_step g : rq_P g → fact_scoped 2 g → rq_P (fact_map (pt_inst (plist [pv 0 1; pv 1 1])) g).
Proof. intros (k & [-> | ->]) _; exists (S k); [by left|by right]. Qed.

Lemma rq_call W Ψ :
  (rq_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pv 0 1; pv 1 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rq_step]. Qed.

Lemma srv_typed W F : world_wf W → typed W ∅ [] ∅ [] F srv (TBox 2 rq_C (TLolli None None TUnit srv_body)).
Proof.
  intros HW. unfold srv.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rq_C srv_body. cbn. unfold srv_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SRcv 0 TUnit Sa) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; hyp0 (pv 1 0) (pv 0 1)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None srv_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep.
    + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess (SSnd 0 TUnit Sb) (pv 1 0)))).
      * tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      * apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
      * kscope.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pv 0 1)|].
        exists (pv 1 1). split; [done|]. right. apply (slt_po W _ (pv 1 0) HW).
    + tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma cli_typed W F : world_wf W → typed W ∅ [] ∅ [] F cli (TBox 2 rq_C (TLolli None None TUnit cli_body)).
Proof.
  intros HW. unfold cli.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rq_C cli_body. cbn. unfold cli_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd TUnit (TSess (SSnd 0 TUnit (dual Sa)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (dual Sa) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0)) (TSess (SRcv 0 TUnit (dual Sb)) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pv 0 1)|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (pv 1 0) (pv 0 1)|right; apply (slt_po W _ (pv 1 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None cli_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

(** The constraint of b: the variable 0 is ε, the variable 1 is γ. *)
Definition rrf_facts (g : fact) : Prop :=
  ∃ k, g = FLt (pv 1 k) (pv 0 k) ∨ g = FLt (pv 0 k) (pv 1 (S k)).
Definition rrf_C : bcs := BCs [pvar 0] rrf_facts.

Lemma rr_typed W : world_wf W → typed W ∅ [] ∅ [] (∅, None) rr_main TUnit.
Proof.
  intros HW. unfold rr_main.
  tstep.
  { tstep; [apply cli_typed, HW|apply srv_typed, HW]. }
  cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sa [] []); [constructor|set_solver|].
  fresh_clean.
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ Sb rrf_C _ _ _ _).
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
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
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

Lemma rr_deadlock_free : deadlock_free (∅, {[+ rr_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply rr_typed, Wpo_strict.
Qed.
