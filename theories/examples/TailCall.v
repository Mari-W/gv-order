(** * tail call with a ceiling: typable, sequential (SHARP-EDGES 65)

      C = {ι+k ≺ ζ ∣ k ∈ ℕ}
      snd : □(∀ι ζ. C. ∗ ⊸^⊥_⊤ (Sb@ι ⊸^ζ_⊤ ∗))
      snd = !(f = λc. (force f) (send ⟨∗, c⟩))
      rcv : □(∀ι ζ. C. ∗ ⊸^⊥_⊤ (S̄b@ι ⊸^ζ_⊤ ∗))
      rcv = !(g = λc. let (x, c) = recv c in let () = x in (force g) c)
      tc_main = let (s, r) = ⟨snd, rcv⟩ in let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force r) c′) in (force s) c

    Both recursions are tail calls, no spawn. The body of each λ runs
    under the frame variable μ with ζ ≺ μ. The send and the receive
    block at ι and ask ι ≺ μ, which is ι ≺ ζ ≺ μ. The tail call at
    (ι+1, ζ) has upper point ζ and asks ζ ≺ μ, the frame hypothesis.
    Its force asks C[ι+1, ζ] ⊆ C ([tc_sub]).

    In the empty world main creates c with {ι+k ≺ ι[0] ∣ k ∈ ℕ} and
    forces at (ι, ι[0]). The ceiling is the carried point ι[0], which no
    channel occupies (sharp edges 105). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition tc_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (pv 1 0).
Definition tc_C : bcs := BCs [] tc_P.

Definition tcs_body : ty := TLolli (Some (pv 1 0)) None (TSess Sb (pv 0 0)) TUnit.
Definition tcr_body : ty := TLolli (Some (pv 1 0)) None (TSess (dual Sb) (pv 0 0)) TUnit.

Definition tcs : expr := EBox (Lam (App (App EForce (Var 1)) (App ESend (Pair EUnit (Var 0))))).
Definition tcr : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (Var 1) (App (App EForce (Var 3)) (Var 0))))).

Definition tc_main : expr :=
  LetP (Pair tcs tcr) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Lemma tc_sub g : tc_P g → fact_scoped 2 g → tc_P (fact_map (pt_inst (plist [pv 0 1; pv 1 0])) g).
Proof. intros (k & ->) _. by exists (S k). Qed.

Lemma tc_call W Ψ : (tc_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) tc_C [pv 0 1; pv 1 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact tc_sub]. Qed.

Lemma tcs_typed W F : world_wf W → typed W ∅ [] ∅ [] F tcs (TBox 2 tc_C (TLolli None None TUnit tcs_body)).
Proof.
  intros HW. unfold tcs.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open tc_C tcs_body. cbn. unfold tcs_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcs_body [pv 0 1; pv 1 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply tc_call. by left.
    + apply (skn_ids2 W _ tc_C); [by left|done|done].
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess (SSnd 0 TUnit Sb) (pv 0 0)))).
    + tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    + apply (KTSend _ _ _ 0 TUnit Sb (pv 0 0)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

Lemma tcr_typed W F : world_wf W → typed W ∅ [] ∅ [] F tcr (TBox 2 tc_C (TLolli None None TUnit tcr_body)).
Proof.
  intros HW. unfold tcr.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open tc_C tcr_body. cbn. unfold tcr_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SRcv 0 TUnit (dual Sb)) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcr_body [pv 0 1; pv 1 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply tc_call. by left.
    + apply (skn_ids2 W _ tc_C); [by left|done|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** main creates c with the creation constraint {ι+k ≺ ζ ∣ k ∈ ℕ}, where
    the ceiling ζ is the carried point ι[0]. Sb carries no channel, so
    ζ is no channel point. It is a point of ι, known through the
    hypothesis of new. Every fact stays inside ι, and the pair rank
    (0, k) for ι+k and (1, o) for ζ+o orders them (sharp edges 105). *)
Abbreviation tcz := (Pt (NSlot (NVar 0) 0 0) 0).

Definition tcc_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) tcz.
Definition tcc_C : bcs := BCs [] tcc_P.

Definition tcc_rank (x : point) : nat * nat :=
  (match pt_name x with NSlot (NVar 0) 0 0 => 1 | _ => 0 end, pt_off x).

Lemma tcc_ok peq plt : cc_ok peq plt tcc_C.
Proof.
  apply (cc_ok_inner peq plt tcc_P (λ x y, lexlt (tcc_rank x) (tcc_rank y))).
  - unfold lexlt. intros x y z; lia.
  - unfold lexlt. intros x; lia.
  - intros [n o] _. unfold lexlt, tcc_rank, pt_shift. simpl. right. split; [done|lia].
  - intros g [k ->] _. eexists _, _. split; [done|]. unfold lexlt, tcc_rank. simpl. left. lia.
Qed.

Lemma tc_typed W : strict W → typed W ∅ [] ∅ [] (∅, None) tc_main TUnit.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold tc_main.
  tstep.
  { tstep; [apply tcr_typed, HW|apply tcs_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ Sb tcc_C); [apply tcc_ok|constructor|].
  fresh_clean.
  set (Ψ := [(tcc_C, [pvar 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) tc_C [pvar 0; tcz]) as HC.
  { apply bcs_hold_intro. intros g (k & ->) _. cbn.
    eapply (sl_hyp0 _ _ _ _ (pv 0 k) tcz); [by left|by exists k|cbn; lia|reflexivity|reflexivity]. }
  assert (Forall (skn W Ψ) [pvar 0; tcz]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  match goal with |- typed _ _ _ _ [Some ?A; _; None; None; Some ?B; Some ?D] _ _ _ =>
    change A with (TSess (dual Sb) (pvar 0));
    change B with (TBox 2 tc_C (TLolli None None TUnit tcr_body));
    change D with (TBox 2 tc_C (TLolli None None TUnit tcs_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some tcz) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcr_body [pvar 0; tcz]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists tcz. split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 tc_C None tcs_body [pvar 0; tcz]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma tc_deadlock_free : deadlock_free (∅, {[+ tc_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply tc_typed, Wpo_strict.
Qed.
