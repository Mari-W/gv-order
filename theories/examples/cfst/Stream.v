(** * Two streams in a cycle (Mordido and Pérez 2026, Listings 1.1 and 1.2)

      Stream = µX. !∗;X  (Sb)          dual Stream = µX. ?∗;X  (Sa)
      C = {ι+k ≺ κ+k, κ+k ≺ ι+k+1, ι+k ≺ ζ, κ+k ≺ ζ ∣ k}
      client    : □(∀ι κ ζ. C. ∗ ⊸ (Sb@ι ⊗ Sa@κ ⊸^ζ ∗))
      client    = !(f = λp. let (c1, c2) = p in let c1 = send ⟨∗, c1⟩ in
                           let (x, c2) = recv c2 in (force f) ⟨c1, c2⟩)
      newclient : □(∀ι κ ζ. C. ∗ ⊸ (Sb@κ ⊗ Sa@ι ⊸^ζ ∗))
      newclient = !(g = λp. let (c1, c2) = p in let (x, c2) = recv c2 in
                           (force g) ⟨send ⟨∗, c1⟩, c2⟩)
      main = let (cl, ncl) = ⟨client, newclient⟩ in
             let (w1, r1) = new ∗ in let (w2, r2) = new ∗ in
             spawn (λu. (force cl) ⟨w1, r2⟩); (force ncl) ⟨w2, r1⟩

    The program starts under one top-level point z with no fact, the
    ceiling of both recursions, which no channel occupies. Channel 1 is
    a and channel 2 is b. a is created with a+k ≺ z for every k, and b
    with a+k ≺ b+k ≺ a+k+1 and b+k ≺ z ([lsa_C], [lsb_C] of
    CfstTools.v), at every polarity of the points. client meets C at
    ι = a and κ = b̄, newclient at ι = ā and κ = b. Mordido and Pérez fix the priority sequences
    [1, 3, 5, …] and [2, 4, 6, …] at new. Here the creation constraints
    state the same interleaving as facts, and the instants of each
    channel count its actions. The protocol is regular. The example
    shows that the cyclic two-thread network with one stream in each
    direction types. Unit () becomes ∗. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstTools.

Set Default Proof Using "All".

Definition st_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 0 k) (pt_dual (pv 1 k)) ∨ g = FLt (pv 1 k) (pt_dual (pv 0 (S k))) ∨
       g = FLt (pv 0 k) (pv 2 0) ∨ g = FLt (pv 1 k) (pv 2 0).
Definition st_C : bcs := BCs [] st_P.

Definition cl_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess Sb (pv 0 0)) (TSess (dual Sb) (pv 1 0))) TUnit.
Definition ncl_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess Sb (pv 1 0)) (TSess (dual Sb) (pv 0 0))) TUnit.

Definition client : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 2)) (LetU (Var 1)
      (App (App EForce (Var 7)) (Pair (Var 3) (Var 0))))))))).

Definition newclient : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 0)) (LetU (Var 1)
    (App (App EForce (Var 5)) (Pair (App ESend (Pair EUnit (Var 3))) (Var 0))))))).

Definition st_main : expr :=
  LetP (Pair client newclient) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 1))))))
      (App (App EForce (Var 4)) (Pair (Var 1) (Var 2)))))).

(** C[ι+1, κ+1, ζ] ⊆ C. *)
Lemma st_step g : st_P g → fact_scoped 3 g → st_P (fact_map (pt_inst (plist [pv 0 1; pv 1 1; pv 2 0])) g).
Proof. intros (k & [-> | [-> | [-> | ->]]]) _; exists (S k); cbn; auto. Qed.

Lemma st_call W Ψ : (st_C, ids 3) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pv 0 1; pv 1 1; pv 2 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact st_step]. Qed.

Lemma st_facts W Ψ k : (st_C, [pv 0 0; pv 1 0; pv 2 0]) ∈ Ψ →
  slt W Ψ (pv 0 k) (pt_dual (pv 1 k)) ∧ slt W Ψ (pv 1 k) (pt_dual (pv 0 (S k))) ∧
  slt W Ψ (pv 0 k) (pv 2 0) ∧ slt W Ψ (pv 1 k) (pv 2 0).
Proof.
  intros Hg. split_and!.
  - eapply (sl_hyp0 W Ψ st_P [pv 0 0; pv 1 0; pv 2 0] (pv 0 k) (pt_dual (pv 1 k))); [done|exists k; by left|cbn; lia|done|done].
  - eapply (sl_hyp0 W Ψ st_P [pv 0 0; pv 1 0; pv 2 0] (pv 1 k) (pt_dual (pv 0 (S k)))); [done|exists k; by right; left|cbn; lia|done|done].
  - eapply (sl_hyp0 W Ψ st_P [pv 0 0; pv 1 0; pv 2 0] (pv 0 k) (pv 2 0)); [done|exists k; by right; right; left|cbn; lia|done|done].
  - eapply (sl_hyp0 W Ψ st_P [pv 0 0; pv 1 0; pv 2 0] (pv 1 k) (pv 2 0)); [done|exists k; by right; right; right|cbn; lia|done|done].
Qed.

Lemma skn_ids3 W Ψ C : (C, [pv 0 0; pv 1 0; pv 2 0]) ∈ Ψ → Forall (skn W Ψ) [pv 0 1; pv 1 1; pv 2 0].
Proof.
  intros Hg. apply Forall_cons. split; [|apply Forall_cons; split; [|apply Forall_singleton]].
  - apply (skn_in W Ψ C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [done|by left|done].
  - apply (skn_in W Ψ C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [done|by right; left|done].
  - apply (skn_in W Ψ C [pv 0 0; pv 1 0; pv 2 0] (pv 2 0)); [done|by right; right; left|done].
Qed.

Ltac box_open3 C T :=
  try change (bcs_inst (pshift 3) C) with C;
  change (lenv_pinst (pshift 3) [Some (TBox 3 0 C (TLolli None None TUnit T))])
    with [Some (pinst_ty (pshift 3) (TBox 3 0 C (TLolli None None TUnit T)))];
  rewrite (pinst_closed _ (TBox 3 0 C (TLolli None None TUnit T))) by (split; [constructor|]; unfold T; body_scope).

Lemma client_typed W F : world_wf W →
  typed W ∅ [] ∅ [] F client (TBox 3 0 st_C (TLolli None None TUnit cl_body)).
Proof.
  intros HW. unfold client.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open3 st_C cl_body. cbn. unfold cl_body.
  pose proof (λ k, st_facts W [(st_C, [pv 0 0; pv 1 0; pv 2 0])] k ltac:(by left)) as H0.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit Sb (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 0)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0)) (TSess (SSeq (SRcv 0 TUnit) (dual Sb)) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 0)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 0). }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 st_C None cl_body [pv 0 1; pv 1 1; pv 2 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply st_call. by left.
    + apply (skn_ids3 W _ st_C). by left.
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

Lemma newclient_typed W F : world_wf W →
  typed W ∅ [] ∅ [] F newclient (TBox 3 0 st_C (TLolli None None TUnit ncl_body)).
Proof.
  intros HW. unfold newclient.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open3 st_C ncl_body. cbn. unfold ncl_body.
  pose proof (λ k, st_facts W [(st_C, [pv 0 0; pv 1 0; pv 2 0])] k ltac:(by left)) as H0.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SSeq (SRcv 0 TUnit) (dual Sb)) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 0)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 0). }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 st_C None ncl_body [pv 0 1; pv 1 1; pv 2 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply st_call. by left.
    + apply (skn_ids3 W _ st_C). by left.
  - eapply (tv_pair W HW _ _ _ _ _ _ (TSess Sb (pv 1 1))); [reflexivity|tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 1 0)))).
    + tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    + apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 0)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 0).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

(** After both [new]s b is 0, a is 1 and the ceiling z is 2. *)
Lemma st_typed : styped ∅ ls_Ψ [] (∅, None) st_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold st_main, ls_Ψ.
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply newclient_typed, HW|exact HWs|apply client_typed, HW]. }
  cbn. new_top HWs Sb (pvar 1). new_top HWs Sb (pvar 0).
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 2]); (BCs [pvar 2] lsa_P, [pvar 1]); (BCs [pvar 1; pvar 2] lsb_P, [pvar 0])]).
  assert (∀ k c c', slt W Ψ (pt_polar c (pv 1 k)) (pt_polar c' (pv 0 k)) ∧
                 slt W Ψ (pt_polar c (pv 0 k)) (pt_polar c' (pv 1 (S k))) ∧
                 slt W Ψ (pt_polar c (pv 1 k)) (pv 2 0) ∧ slt W Ψ (pt_polar c (pv 0 k)) (pv 2 0)) as Hf.
  { intros k c c'. split_and!.
    - eapply (sl_hyp W Ψ [pvar 1; pvar 2] lsb_P [pvar 0] (FLt (pt_polar c (pv 1 k)) (pt_polar c' (pv 0 k))));
        [by right; right; left|exists k, c, c'; by left|destruct c, c'; fsc|by destruct c, c'].
    - eapply (sl_hyp W Ψ [pvar 1; pvar 2] lsb_P [pvar 0] (FLt (pt_polar c (pv 0 k)) (pt_polar c' (pv 1 (S k)))));
        [by right; right; left|exists k, c, c'; by right; left|destruct c, c'; fsc|by destruct c, c'].
    - eapply (sl_hyp W Ψ [pvar 2] lsa_P [pvar 1] (FLt (pt_polar c (pv 0 k)) (pv 1 0)));
        [by right; left|by exists k, c|destruct c; fsc|by destruct c].
    - eapply (sl_hyp W Ψ [pvar 1; pvar 2] lsb_P [pvar 0] (FLt (pt_polar c (pv 0 k)) (pv 2 0)));
        [by right; right; left|exists k, c, c; by right; right|destruct c; fsc|by destruct c]. }
  (* client gets a at α and b′ at β̄, newclient gets b at β and a′ at ᾱ *)
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pv 1 0; pt_dual (pv 0 0); pv 2 0]) as HC.
  { apply bcs_hold_intro. intros g (k & [-> | [-> | [-> | ->]]]) _; cbn;
      first [apply (Hf k true true)|apply (Hf k true false)|apply (Hf k false true)|apply (Hf k false false)]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pt_dual (pv 1 0); pv 0 0; pv 2 0]) as HC'.
  { apply bcs_hold_intro. intros g (k & [-> | [-> | [-> | ->]]]) _; cbn;
      first [apply (Hf k true true)|apply (Hf k true false)|apply (Hf k false true)|apply (Hf k false false)]. }
  assert (Forall (skn W Ψ) [pv 1 0; pt_dual (pv 0 0); pv 2 0]) as HK.
  { constructor; [eapply skn_inst; [by right; left|by left|done]|].
    constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pv 1 0); pv 0 0; pv 2 0]) as HK'.
  { constructor; [eapply skn_inst; [by right; left|by left|done]|].
    constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 0)) (Some (pt_dual (pv 1 0))) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Hf 0 false true)]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 3 st_C None cl_body [pv 1 0; pt_dual (pv 0 0); pv 2 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 st_C None ncl_body [pt_dual (pv 1 0); pv 0 0; pv 2 0]);
      [done|done|exact HC'|exact HK'|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem st_deadlock_free : deadlock_free (∅, {[+ st_main +]}).
Proof. apply (soundness_created_s ls_Ψ _ TUnit ls_created); [constructor|apply st_typed]. Qed.
