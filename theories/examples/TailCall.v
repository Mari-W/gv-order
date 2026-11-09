(** * tail call with a ceiling: typable, sequential (SHARP-EDGES 65)

      C = {ι+k ≺ ζ ∣ k ∈ ℕ}
      snd : □(∀ι ζ. C. ∗ ⊸ (Sb@ι ⊸^ζ ∗))
      snd = !(f = λc. (force f) (send ⟨∗, c⟩))
      rcv : □(∀ι ζ. C. ∗ ⊸ (S̄b@ι ⊸^ζ ∗))
      rcv = !(g = λc. let (x, c) = recv c in let () = x in (force g) c)
      tc_main = let (s, r) = ⟨snd, rcv⟩ in let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force r) c′) in (force s) c

    Both recursions are tail calls, no spawn. The body of each λ runs
    under the future variable μ with ζ ≺ μ. The send and the receive
    block at ι and ask ι ≺ μ, which is ι ≺ ζ ≺ μ. The tail call at
    (ι+1, ζ) has upper point ζ and asks ζ ≺ μ, the future hypothesis.
    Its force asks C[ι+1, ζ] ⊆ C ([tc_sub]).

    main types under the hypothesis of its top-level point ι
    ([tc_Ψ]). It creates c at ι with {ι+k ≺ ι[0] ∣ k ∈ ℕ} and forces at
    (ι, ι[0]). The ceiling is the payload point ι[0], which no channel
    occupies (sharp edges 105, 172). With end points the receiver
    holds c′ at ῑ and main forces rcv at (ῑ, ι[0]), so the constraint
    of c also has ῑ+k ≺ ι[0]. *)

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
  LetP (Pair tcs tcr) (let_new_pair_at (EPt (pconst 0))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Lemma tc_sub g : tc_P g → fact_scoped 2 g → tc_P (fact_map (pt_inst (plist [pv 0 1; pv 1 0])) g).
Proof. intros (k & ->) _. by exists (S k). Qed.

Lemma tc_call W Ψ : (tc_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) tc_C [pv 0 1; pv 1 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact tc_sub]. Qed.

Lemma tcs_typed W F : world_wf W → typed W ∅ [] ∅ [] F tcs (TBox 2 0 tc_C (TLolli None None TUnit tcs_body)).
Proof.
  intros HW. unfold tcs.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open tc_C tcs_body. cbn. unfold tcs_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 tc_C None tcs_body [pv 0 1; pv 1 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply tc_call. by left.
    + apply (skn_ids2 W _ tc_C); [by left|done|done].
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 0 0)))).
    + tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    + apply (KTSend _ _ _ 0 TUnit Sb (pv 0 0)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

Lemma tcr_typed W F : world_wf W → typed W ∅ [] ∅ [] F tcr (TBox 2 0 tc_C (TLolli None None TUnit tcr_body)).
Proof.
  intros HW. unfold tcr.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open tc_C tcr_body. cbn. unfold tcr_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SSeq (SRcv 0 TUnit) (dual Sb)) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 tc_C None tcr_body [pv 0 1; pv 1 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply tc_call. by left.
    + apply (skn_ids2 W _ tc_C); [by left|done|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** main creates c with the creation constraint {ι+k ≺ ζ ∣ k ∈ ℕ}, where
    the ceiling ζ is the payload point ι[0]. Sb carries no channel, so
    ζ is no channel point. It is a point of ι, known through the
    hypothesis of new. Every fact stays inside ι, and the pair rank
    (0, k) for ι+k and (1, o) for ζ+o orders them (sharp edges 105). *)
Abbreviation tcz := (Pt (NPayload (NVar 0) 0 0) 0).

Definition tcc_P (g : fact) : Prop := ∃ k b, g = FLt (pt_polar b (pv 0 k)) tcz.
Definition tcc_C : bcs := BCs [] tcc_P.

Definition tcc_rank (x : point) : nat * nat :=
  (match pt_name x with NPayload (NVar 0) 0 0 => 1 | _ => 0 end, pt_off x).

Lemma tcc_ok peq plt : cc_ok peq plt tcc_C.
Proof.
  apply (cc_ok_inner peq plt tcc_P (λ x y, lexlt (tcc_rank x) (tcc_rank y))).
  - unfold lexlt. intros x y z; lia.
  - unfold lexlt. intros x; lia.
  - intros [n pb o] _. unfold lexlt, tcc_rank, pt_shift. simpl. right. split; [done|lia].
  - intros g (k & [] & ->) _; eexists _, _; (split; [done|]); unfold lexlt, tcc_rank; simpl; left; lia.
  - intros [n pb o] _. unfold lexlt, tcc_rank, pt_shift, pt_dual. simpl. right. split; [done|lia].
Qed.

Definition tc_Ψ : hyps := [] ++ [(tcc_C, [pconst 0])].

(** The ceiling at the constant of c. *)
Abbreviation tczc := (Pt (NPayload (NConst 0) 0 0) 0).

Lemma tc_created : created (Wpo []) tc_Ψ.
Proof. apply created_snoc; [constructor|apply tcc_ok|constructor|fresh_const]. Qed.

Lemma tc_typed : styped ∅ tc_Ψ [] (∅, None) tc_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold tc_main, let_new_pair_at, tc_Ψ.
  tstep.
  { tstep; (apply typed_hyps_nil; [exact HWs|]); [apply tcr_typed, HW|apply tcs_typed, HW]. }
  cbn. new_top HWs Sb (pconst 0).
  fresh_clean.
  set (Ψ := [(tcc_C, [pconst 0])]).
  assert (∀ b, bcs_hold (seqs W Ψ) (slt W Ψ) tc_C [pt_polar b (pconst 0); tczc]) as HC.
  { intros b. apply bcs_hold_intro. intros g (k & ->) _. cbn.
    eapply (sl_hyp0 _ _ _ _ (pt_polar b (pv 0 k)) tcz);
      [by left|by exists k, b|destruct b; cbn; lia|destruct b; reflexivity|reflexivity]. }
  assert (∀ b, Forall (skn W Ψ) [pt_polar b (pconst 0); tczc]) as HK.
  { intros b. constructor; [eapply skn_inst; [by left|by left|by destruct b]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  match goal with |- typed _ _ _ _ [Some ?A; _; None; None; Some ?B; Some ?D] _ _ _ =>
    change A with (TSess (dual Sb) (pt_dual (pconst 0)));
    change B with (TBox 2 0 tc_C (TLolli None None TUnit tcr_body));
    change D with (TBox 2 0 tc_C (TLolli None None TUnit tcs_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some tczc) (Some (pconst 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 tc_C None tcr_body [pt_dual (pconst 0); tczc]);
        [done|done|exact (HC false)|exact (HK false)|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists tczc. split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 tc_C None tcs_body [pconst 0; tczc]);
      [done|done|exact (HC true)|exact (HK true)|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma tc_deadlock_free : deadlock_free (∅, {[+ tc_main +]}).
Proof.
  apply (soundness_created_s tc_Ψ _ TUnit tc_created); [constructor|apply tc_typed].
Qed.
