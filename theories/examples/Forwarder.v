(** * forwarder in a box: typable, recursive, without aliases (SHARP-EDGES 67, 150)

      Si = μX. ?(Close@σ).X                σ = x[0] for the action at x
      So = μX. !(∃^{σ̄} κ. {κ ≺ σ}. Close@κ).X
      Cf = {ι+k ≺ ι′+k,  ι+k ≺ ι̅′+k,  ι′+k ≺ ι̅+k+1,  ι′+k ≺ (ι′+k)[0]‾,
            (ι+k)[0] ≺ (ι′+k)[0],  (ι′+k)[0]‾ ≺ (ι+k)[0]‾  ∣  k ∈ ℕ}
      Cp = {ι+k ≺ ι[0], ι[0]‾,  ι[0], ι[0]‾ ≺ ι̅+k+1  ∣  k ∈ ℕ}      ι[0] = (ι+k)[0]
      fwd   : □(∀ι ι′. Cf. ∗ ⊸ (Si@ι ⊗ So@ι′ ⊸^{ι′} ∗))
      fwd   = !(f = λp. let (a, b) = p in let (d, a) = recv a in
                       let (b, u) = ⟨send ⟨d, b⟩, ∗⟩ in let () = u in
                       spawn (λw. let () = w in (force f) ⟨a, b⟩))
      fprod : □(∀ι. Cp. ∗ ⊸ (S̄i@ι ⊸^{ι[0]‾} ∗))
      fprod = !(g = λc. let (e, e′) = new@(ι[0]) ∗ in let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in
                       let () = u in let () = close e′ in
                       spawn (λw. let () = w in (force g) c))
      fcons : □(∀ι. Cp. ∗ ⊸ (S̄o@ι ⊸^{ι[0]} ∗))
      fcons = !(h = λc. let (d, c) = recv c in [open d at κ]
                       let () = close d in
                       spawn (λw. let () = w in (force h) c))
      fw_main = let ((p, f), h) = ⟨⟨fprod, fwd⟩, fcons⟩ in
                let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                let () = spawn (λw. let () = w in (force p) a′) in
                let () = spawn (λw. let () = w in (force h) b′) in (force f) ⟨a, b⟩

    recv a gives d the type Close@ρ with ρ = (ι+k)[0]. The send at ι′+k
    has the payload point σ = (ι′+k)[0], and it packs d at κ = ρ. E-Pack
    asks the constraint ρ ≺ σ and the bound σ̄ ≼ ρ̄ (the head of d is its
    partner point ρ̄), and the send asks ι′+k ≺ σ̄. All three are facts
    of Cf. The consumer opens the payload at a fresh κ with κ ≺ σ and
    closes d at κ while it holds c at θ+k+1 (θ its point). Cp gives
    σ ≺ θ̄+k+1, so κ lies below the partner of c. The upper point of the
    consumer is σ, and κ ≺ σ is its witness. The recursive calls ask Cf
    and Cp one round later, which C contains ([fw_sub], [fp_sub]).

    Before (main, with E-Conv up to ≡), the box carried the alias
    (ι+k)[0] ≡ (ι′+k)[0], and So sent Close@σ. The alias splits into two
    order facts that point in opposite directions, ρ ≺ σ for the
    receiver and σ̄ ≺ ρ̄ for the sender. No fact relates σ to σ̄ or ρ to
    ρ̄, and ≺ is not closed under x ↦ x̄, so the two are consistent.

    In the empty world main creates a with the producer constraint fpa_C
    and b with the facts that relate it to a ([fwb_ok], sharp edges
    105). Both are order-only creation constraints.

    With end points every gate compares with partner points ([fw_C],
    [fp_C]). The producer's upper point is ι[0]‾, where it closes e′.
    main forces fwd at (γ, ε), the producer at γ̄ and the consumer at
    ε̄. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.
From LRGV Require Import examples.cfst.CfstTools.

Set Default Proof Using "All".

Abbreviation svv a k := (Pt (NPayload (NVar a) k 0) 0).
Abbreviation sl a k := (Pt (NPayload (NConst a) k 0) 0).

Definition Sfi : sty := SMu (SSeq (SRcv 1 (TSess SEnd (pvar 0))) (SVar 0)).
(** The outgoing payload is an existential. Under the payload binder
    the variable 0 is σ, the payload point x[0] of the send at x. Under
    the existential binder the variable 0 is κ and the variable 1 is σ.
    The bound is σ̄ and the constraint is {κ ≺ σ}. *)
Definition Cfo_P (g : fact) : Prop := g = FLt (pvar 0) (pvar 1).
Definition Pfo : ty := TEx (LPt (pt_dual (pvar 0))) 1 (BCs [pvar 0] Cfo_P) (TSess SEnd (pvar 0)).
Definition Sfo : sty := SMu (SSeq (SSnd 1 Pfo) (SVar 0)).

Lemma Pfo_scoped : pscoped 1 Pfo.
Proof.
  cbn. split; [|split].
  - intros ? Hv. injection Hv. lia.
  - unfold bcs_scoped. cbn. constructor; [|constructor]. intros ? Hv. injection Hv. lia.
  - intros ? Hv. injection Hv. lia.
Qed.

(** With end points every gate compares a blocking point with the
    partner points of the other held ends: ι ≺ ι̅′ for the recv on a,
    ι′ ≺ (ι+1)‾ for the send on b, ι′ ≺ (ι′[0])‾ for its payload. *)
Definition fw_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 0 k) (pt_dual (pv 1 k)) ∨ g = FLt (pv 0 k) (pv 1 k) ∨
       g = FLt (pv 1 k) (pt_dual (svv 1 k)) ∨ g = FLt (pt_dual (svv 1 k)) (pt_dual (svv 0 k)) ∨
       g = FLt (svv 0 k) (svv 1 k) ∨ g = FLt (pv 1 k) (pt_dual (pv 0 (S k))).
Definition fw_C : bcs := BCs [] fw_P.

(** The producer sends e at ι[0] and closes e′ at ι[0]‾, the consumer
    closes d at ι[0]. One constraint serves both. *)
Definition fp_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 0 k) (pt_dual (svv 0 k)) ∨ g = FLt (pv 0 k) (svv 0 k) ∨
       g = FLt (pt_dual (svv 0 k)) (pt_dual (pv 0 (S k))) ∨ g = FLt (svv 0 k) (pt_dual (pv 0 (S k))).
Definition fp_C : bcs := BCs [] fp_P.

Definition fwd_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Sfi (pv 0 0)) (TSess Sfo (pv 1 0))) TUnit.
Definition fprod_body : ty := TLolli (Some (pt_dual (svv 0 0))) None (TSess (dual Sfi) (pv 0 0)) TUnit.
Definition fcons_body : ty := TLolli (Some (svv 0 0)) None (TSess (dual Sfo) (pv 0 0)) TUnit.

Definition fwd : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1))
    (LetP (Pair (App ESend (Pair (Var 1) (Var 2))) EUnit) (LetU (Var 0)
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 3) (Var 2))))))))))).

Definition fprod : expr :=
  EBox (Lam (let_new_pair
    (LetP (Pair (App ESend (Pair (Var 1) (Var 2))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 2))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 2)))))))))).

Definition fcons : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (App EClos (Var 1))
    (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 1)))))))).

Definition fw_main : expr :=
  LetP (Pair (Pair fprod fwd) fcons) (LetP (Var 1)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 3)))))
        (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 7)) (Var 1)))))
          (App (App EForce (Var 4)) (Pair (Var 3) (Var 1)))))))).

(** C[ι+1, ι′+1] ⊆ C and C[ι+1] ⊆ C: round k goes to round k+1. *)
Lemma fw_sub g : fw_P g → fact_scoped 2 g → fw_P (fact_map (pt_inst (plist [pv 0 1; pv 1 1])) g).
Proof.
  intros (k & [-> | [-> | [-> | [-> | [-> | ->]]]]]) _; exists (S k);
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

Lemma fp_sub g : fp_P g → fact_scoped 1 g → fp_P (fact_map (pt_inst (plist [pv 0 1])) g).
Proof.
  intros (k & [-> | [-> | [-> | ->]]]) _; exists (S k); repeat (first [left; reflexivity|right]); reflexivity.
Qed.

Lemma fw_call W Ψ : (fw_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pv 0 1; pv 1 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fw_sub]. Qed.

Lemma fp_call W Ψ : (fp_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fp_C [pv 0 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fp_sub]. Qed.

Ltac fmem := hnf; eexists; repeat (first [left; reflexivity|right]); reflexivity.

Ltac fhyp x y :=
  eapply (sl_hyp0 _ _ _ _ x y); [by left|fmem|cbn; lia|reflexivity|reflexivity].

Lemma fwd_typed W F : world_wf W → typed W ∅ [] ∅ [] F fwd (TBox 2 0 fw_C (TLolli None None TUnit fwd_body)).
Proof.
  intros HW. unfold fwd.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open fw_C fwd_body. cbn. unfold fwd_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess SEnd (pvar 0))) Sfi) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 0 0) (pt_dual (pv 1 0))|].
      exists (pv 1 0). split; [done|]. right. fhyp (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
              (TProd (payload_at 1 Pfo (pv 1 0)) (TSess (SSeq (SSnd 1 Pfo) Sfo) (pv 1 0)))).
    - tstep; [eapply t_conv; [|tstep]; conv_sess|].
      (* pack d : Close@ι[0] at κ = ι[0]: the constraint ι[0] ≺ ι′[0] and
         the bound (ι′[0])‾ ≺ (ι[0])‾ are facts of Cf *)
      eapply (t_pack W _ _ _ _ _ _ (LPt (pt_dual (svv 1 0))) 1 (BCs [svv 1 0] Cfo_P)
                (TSess SEnd (pvar 0)) [svv 0 0]).
      + done.
      + constructor; [skn_payload|constructor].
      + apply bcs_hold_env. intros f -> _. cbn. fhyp (svv 0 0) (svv 1 0).
      + split; [|done]. intros y Hy. mem_cases Hy. right. fhyp (pt_dual (svv 1 0)) (pt_dual (svv 0 0)).
      + cbn. tstep.
    - apply (KTSend _ _ _ 1 Pfo Sfo (pv 1 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. fhyp (pv 1 0) (pt_dual (svv 1 0)).
    - exact Pfo_scoped.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 1 0) (pt_dual (pv 0 1))|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [right; fhyp (pv 1 0) (pt_dual (pv 0 1))|right; apply sl_dpo]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 fw_C None fwd_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fw_call. by left.
    + apply (skn_ids2 W _ fw_C); [by left|done|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma skn_fp W Ψ x : (fp_C, [pvar 0]) ∈ Ψ → pt_root x = NVar 0 → Forall (skn W Ψ) [x].
Proof.
  intros Hg Hx. apply Forall_singleton. apply (skn_in W Ψ fp_C [pvar 0] (pvar 0)); [done|by left|done].
Qed.

Lemma fprod_typed W F : strict W → typed W ∅ [] ∅ [] F fprod (TBox 1 0 fp_C (TLolli None None TUnit fprod_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fprod.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fp_C fprod_body. cbn. unfold fprod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (svv 0 0) HWs); [skn_payload|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (svv 0 0)) (TSess (SSeq (SSnd 1 (TSess SEnd (pvar 0))) (dual Sfi)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) (dual Sfi) (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. fhyp (pv 0 0) (pt_dual (svv 0 0)).
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 0 0) (svv 0 0)|].
      exists (pt_dual (svv 0 0)). split; [done|]. right. fhyp (pv 0 0) (pt_dual (svv 0 0)). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pt_dual (svv 0 0)) (pt_dual (pv 0 1))|].
    exists (pt_dual (svv 0 0)). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (svv 0 1))) (Some (pt_dual (pv 0 1))) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fprod_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fp_call. by left.
    + apply (skn_fp W _ (pv 0 1)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (svv 0 1)). split; [done|]. apply sle_refl, HW.
Qed.

Lemma fcons_typed W F : world_wf W → typed W ∅ [] ∅ [] F fcons (TBox 1 0 fp_C (TLolli None None TUnit fcons_body)).
Proof.
  intros HW. unfold fcons.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fp_C fcons_body. cbn. unfold fcons_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 Pfo) (dual Sfo)) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - exact Pfo_scoped.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (svv 0 0). split; [done|]. right. fhyp (pv 0 0) (svv 0 0). }
  (* open the payload: d at a fresh κ (variable 0) with κ ≺ σ, σ = θ[0];
     θ is now the variable 1 *)
  cbn. eapply (tv_open W _ _ _ _ _ 1); [reflexivity|intros []|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
  cbn. rewrite ?sf_pinst_empty.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ' := Q) end.
  assert (slt W Ψ' (pvar 0) (svv 1 0)) as Hk.
  { assert ((BCs [svv 1 0] Cfo_P, [pvar 0]) ∈ Ψ') as Hin by (by right; left).
    assert (bcs_open 1 (BCs [svv 1 0] Cfo_P)
              (fact_map (pt_inst (pup 1 (plist [svv 1 0]))) (FLt (pvar 0) (pvar 1)))) as Ho.
    { exists (FLt (pvar 0) (pvar 1)). split_and!; [done|split; cbn; lia|done]. }
    apply (hyp_in_fact W Ψ' _ _ Hin) in Ho. exact Ho. }
  assert (∀ u v, fp_P (FLt u v) → fact_scoped 1 (FLt u v) →
            slt W Ψ' (pt_inst (plist [pvar 1]) u) (pt_inst (plist [pvar 1]) v)) as Hp.
  { intros u v Hg Hs. eapply (sl_hyp0 _ _ _ _ u v); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
  assert (slt W Ψ' (svv 1 0) (pt_dual (pv 1 1))) as Hs1.
  { apply (Hp (svv 0 0) (pt_dual (pv 0 1))); [exists 0; by right; right; right|cbn; lia]. }
  tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; eapply sl_trans; [exact Hk|exact Hs1]|].
    exists (svv 1 0). split; [done|]. right. exact Hk. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (svv 1 1)) (Some (pt_dual (pv 1 1))) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fcons_body [pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g (k & [-> | [-> | [-> | ->]]]) _; cbn.
      * apply (Hp (pv 0 (S k)) (pt_dual (svv 0 (S k)))); [exists (S k); by left|cbn; lia].
      * apply (Hp (pv 0 (S k)) (svv 0 (S k))); [exists (S k); by right; left|cbn; lia].
      * apply (Hp (pt_dual (svv 0 (S k))) (pt_dual (pv 0 (S (S k))))); [exists (S k); by right; right; left|cbn; lia].
      * apply (Hp (svv 0 (S k)) (pt_dual (pv 0 (S (S k))))); [exists (S k); by right; right; right|cbn; lia].
    + constructor; [|constructor]. right. exists fp_C, [pvar 1], (pvar 1). split_and!; [by left|by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (svv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

(** ** main in the empty world (sharp edges 105)

    main forces fwd at (γ, ε), the producer at γ̄ (a′) and the consumer
    at ε̄ (b′). a is created at γ with the facts inside γ,

      Ca = {γ+k, γ̄+k ≺ (γ+k)[0], (γ+k)[0]‾ ≺ γ+k+1  ∣  k ∈ ℕ},

    which hold the producer constraint at γ̄. b is created at ε with the
    facts that relate it to a and the consumer constraint at ε̄,

      Cb = {γ+k ≺ ε+k, ε̄+k,  ε+k ≺ (ε+k)[0]‾, γ̄+k+1,
            (γ+k)[0] ≺ (ε+k)[0],  (ε+k)[0]‾ ≺ (γ+k)[0]‾,
            ε̄+k ≺ (ε+k)[0], (ε+k)[0]‾,  (ε+k)[0], (ε+k)[0]‾ ≺ ε+k+1  ∣  k ∈ ℕ}.

    Cb has only ≺ facts ([cc_ok_out]). Inside ε they follow the rank
    3k for ε+k and 3k+1 for (ε+k)[0] at either polarity. The facts that
    enter ε from γ and leave it to γ close through program order and
    Ca. The pair (γ+k)[0] ≺ (ε+k)[0] ≺ (γ+k)[0]‾ would ask
    (γ+k)[0] ≺ (γ+k)[0]‾ of Ca, but the two points of ε have the same
    rank, so that pair is never chained. *)

Definition fpa_P (g : fact) : Prop :=
  ∃ k b b', g = FLt (pt_polar b (pv 0 k)) (pt_polar b' (svv 0 k)) ∨
            g = FLt (pt_polar b' (svv 0 k)) (pv 0 (S k)).
Definition fpa_C : bcs := BCs [] fpa_P.

Definition fwb_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 1 k) (pt_dual (pv 0 k)) ∨ g = FLt (pv 1 k) (pv 0 k) ∨
       g = FLt (pv 0 k) (pt_dual (svv 0 k)) ∨
       g = FLt (pt_dual (svv 0 k)) (pt_dual (svv 1 k)) ∨ g = FLt (svv 1 k) (svv 0 k) ∨
       g = FLt (pv 0 k) (pt_dual (pv 1 (S k))) ∨
       g = FLt (pt_dual (pv 0 k)) (pt_dual (svv 0 k)) ∨ g = FLt (pt_dual (pv 0 k)) (svv 0 k) ∨
       g = FLt (pt_dual (svv 0 k)) (pv 0 (S k)) ∨ g = FLt (svv 0 k) (pv 0 (S k)).
Definition fwb_C : bcs := BCs [pvar 0] fwb_P.

Definition fwa_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 2 * pt_off x
  | NPayload (NVar 0) k 0 => 2 * k + 1 + 2 * pt_off x
  | _ => pt_off x
  end.

Lemma fpa_ok peq plt : cc_ok peq plt fpa_C.
Proof.
  apply (cc_ok_inner peq plt fpa_P (λ x y, fwa_rank x < fwa_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold fwa_rank, pt_shift. simpl. repeat case_match; lia.
  - intros g (k & b & b' & [-> | ->]) _; destruct b, b'; eexists _, _; (split; [done|]);
      unfold fwa_rank; cbn; lia.
  - intros [n pb o] _. unfold fwa_rank, pt_shift, pt_dual. simpl. repeat case_match; lia.
Qed.

(** The rank inside ε: ε+k at 3k, (ε+k)[0]+j at 3k+1+j. *)
Definition fwb_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 3 * pt_off x
  | NPayload (NVar 0) k 0 => 3 * k + 1 + pt_off x
  | _ => pt_off x
  end.

Lemma fwb_ok W Ψ : world_wf W → (fpa_C, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) fwb_C.
Proof.
  intros HW Hg.
  set (T := glt (cc_up (seqs W Ψ)) (cc_up (slt W Ψ))).
  assert (∀ x y, slt W Ψ x y → T (pt_inst (λ a, pvar (a + 1)) x) (pt_inst (λ a, pvar (a + 1)) y))
    as Hup by (intros; by apply cc_up_lt).
  assert (∀ k b, T (pv 1 k) (pt_polar b (svv 1 k))) as Ha1.
  { intros k b. destruct b; [apply (Hup (pv 0 k) (svv 0 k))|apply (Hup (pv 0 k) (pt_dual (svv 0 k)))].
    - eapply (sl_hyp0 _ _ _ _ (pv 0 k) (svv 0 k)); [exact Hg|exists k, true, true; by left|cbn; lia|done|done].
    - eapply (sl_hyp0 _ _ _ _ (pv 0 k) (pt_dual (svv 0 k)));
        [exact Hg|exists k, true, false; by left|cbn; lia|done|done]. }
  assert (∀ k b, T (pt_polar b (svv 1 k)) (pv 1 (S k))) as Ha2.
  { intros k b. destruct b; [apply (Hup (svv 0 k) (pv 0 (S k)))|apply (Hup (pt_dual (svv 0 k)) (pv 0 (S k)))].
    - eapply (sl_hyp0 _ _ _ _ (svv 0 k) (pv 0 (S k))); [exact Hg|exists k, true, true; by right|cbn; lia|done|done].
    - eapply (sl_hyp0 _ _ _ _ (pt_dual (svv 0 k)) (pv 0 (S k)));
        [exact Hg|exists k, true, false; by right|cbn; lia|done|done]. }
  assert (∀ k j, k < j → T (pv 1 k) (pv 1 j)) as Hpo.
  { intros k j Hkj. apply (th_pofs _ _ _ _ (theory_gen _ _)). unfold pofs. simpl. split; [done|lia]. }
  assert (∀ j k b, j ≤ k → T (pv 1 j) (pt_polar b (svv 1 k))) as Hs.
  { intros j k b Hjk. destruct (decide (j = k)) as [<-|Hne]; [apply Ha1|].
    eapply glt_trans; [apply (Hpo j k); lia|apply Ha1]. }
  assert (∀ j k, j ≤ k → T (pv 1 j) (pt_dual (pv 1 (S k)))) as Hd.
  { intros j k Hjk. apply (th_pofs _ _ _ _ (theory_gen _ _)). unfold pofs. simpl. split; [done|lia]. }
  assert (pup 1 (plist [pvar 0]) 0 = pvar 0) as E0 by (unfold pup; by rewrite decide_True by lia).
  assert (pup 1 (plist [pvar 0]) 1 = pvar 1) as E1 by (unfold pup; by rewrite decide_False by lia).
  apply (cc_ok_out _ _ fwb_C (λ x y, fwb_rank x < fwb_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold fwb_rank, pt_shift. simpl. repeat case_match; lia.
  - intros [n pb o] _. unfold fwb_rank, pt_shift, pt_dual. simpl. repeat case_match; lia.
  - intros a b (f & (k & Hf) & _ & E). repeat destruct Hf as [Hf|Hf]; subst; discriminate.
  - intros a b (f & (k & Hf) & _ & E). repeat destruct Hf as [Hf|Hf]; subst; cbn in E;
      rewrite ?E0, ?E1 in E; injection E as -> ->; cbn;
      first [left; split_and!; [done|done|unfold fwb_rank; cbn; lia]
            |right; left; split; [discriminate|done]
            |right; right; split; [done|discriminate]].
  - intros u p q v (f & (k & Hf) & _ & E) (f' & (j & Hf') & _ & E') Hu Hp Hq Hv Hpq.
    repeat destruct Hf as [Hf|Hf]; subst; cbn in E; rewrite ?E0, ?E1 in E; injection E as -> ->;
      repeat destruct Hf' as [Hf'|Hf']; subst; cbn in E'; rewrite ?E0, ?E1 in E'; injection E' as -> ->;
      cbn in Hu, Hp, Hq, Hv;
      try discriminate Hp; try discriminate Hq;
      try (exfalso; apply Hu; reflexivity); try (exfalso; apply Hv; reflexivity);
      (destruct Hpq as [Epq|Hlt]; [try discriminate Epq; injection Epq as Epq|
        unfold fwb_rank in Hlt; cbn in Hlt]);
      first [apply (Hs k j false); lia|apply (Hd k j); lia
            |eapply glt_trans; [apply (Ha2 k true)|];
             first [apply (Hs (S k) j false); lia|apply (Hd (S k) j); lia]].
Qed.

Lemma fw_typed : styped ∅ [] [] (∅, None) fw_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fw_main.
  tstep.
  { tstep; [apply fcons_typed, HW|]. tstep; [apply fwd_typed, HW|apply fprod_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sfi fpa_C); [apply fpa_ok|constructor|].
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sfo fwb_C); [apply fwb_ok; [done|by left]|
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]|].
  fresh_clean.
  match goal with |- typed _ _ ?Ψ0 _ _ _ _ _ => set (Ψ := Ψ0) end.
  assert (∀ u v, fwb_P (FLt u v) → fact_scoped 2 (FLt u v) →
            slt W Ψ (pt_inst (plist [pvar 0; pv 1 0]) u) (pt_inst (plist [pvar 0; pv 1 0]) v)) as Hb.
  { intros u v Hf Hs. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) fwb_C) (pvar 0) u v);
      [by right; left|done|done]. }
  assert (∀ u v, fpa_P (FLt u v) → fact_scoped 1 (FLt u v) →
            slt W Ψ (pt_inst (plist [pv 1 0]) u) (pt_inst (plist [pv 1 0]) v)) as Ha.
  { intros u v Hg Hs. eapply (sl_hyp0 _ _ _ _ u v); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pv 1 0; pvar 0]) as HCf.
  { apply bcs_hold_intro. intros g (k & Hg) _.
    destruct Hg as [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn.
    - apply (Hb (pv 1 k) (pt_dual (pv 0 k))); [fmem|cbn; lia].
    - apply (Hb (pv 1 k) (pv 0 k)); [fmem|cbn; lia].
    - apply (Hb (pv 0 k) (pt_dual (svv 0 k))); [fmem|cbn; lia].
    - apply (Hb (pt_dual (svv 0 k)) (pt_dual (svv 1 k))); [fmem|cbn; lia].
    - apply (Hb (svv 1 k) (svv 0 k)); [fmem|cbn; lia].
    - apply (Hb (pv 0 k) (pt_dual (pv 1 (S k)))); [fmem|cbn; lia]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fp_C [pt_dual (pv 1 0)]) as HCa.
  { apply bcs_hold_intro. intros g (k & [-> | [-> | [-> | ->]]]) _; cbn.
    - apply (Ha (pt_polar false (pv 0 k)) (pt_polar false (svv 0 k))); [exists k, false, false; by left|cbn; lia].
    - apply (Ha (pt_polar false (pv 0 k)) (pt_polar true (svv 0 k))); [exists k, false, true; by left|cbn; lia].
    - apply (Ha (pt_polar false (svv 0 k)) (pv 0 (S k))); [exists k, true, false; by right|cbn; lia].
    - apply (Ha (pt_polar true (svv 0 k)) (pv 0 (S k))); [exists k, true, true; by right|cbn; lia]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fp_C [pt_dual (pvar 0)]) as HCb.
  { apply bcs_hold_intro. intros g (k & [-> | [-> | [-> | ->]]]) _; cbn.
    - apply (Hb (pt_dual (pv 0 k)) (pt_dual (svv 0 k))); [fmem|cbn; lia].
    - apply (Hb (pt_dual (pv 0 k)) (svv 0 k)); [fmem|cbn; lia].
    - apply (Hb (pt_dual (svv 0 k)) (pv 0 (S k))); [fmem|cbn; lia].
    - apply (Hb (svv 0 k) (pv 0 (S k))); [fmem|cbn; lia]. }
  assert (Forall (skn W Ψ) [pv 1 0; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pv 1 0)]) as HKa
    by (constructor; [eapply skn_inst; [by left|by left|done]|constructor]).
  assert (Forall (skn W Ψ) [pt_dual (pvar 0)]) as HKb
    by (constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]).
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E; Some ?G; None] _ _ _ =>
    change A with (TSess (dual Sfo) (pt_dual (pvar 0))); change B with (TSess Sfo (pvar 0));
    change A' with (TSess (dual Sfi) (pt_dual (pv 1 0))); change B' with (TSess Sfi (pv 1 0));
    change D with (TBox 2 0 fw_C (TLolli None None TUnit fwd_body));
    change E with (TBox 1 0 fp_C (TLolli None None TUnit fprod_body));
    change G with (TBox 1 0 fp_C (TLolli None None TUnit fcons_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (Pt (NPayload (NVar 1) 0 0) 0))) (Some (pv 1 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fprod_body [pt_dual (pv 1 0)]);
        [done|done|exact HCa|exact HKa|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (Pt (NPayload (NVar 1) 0 0) 0)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (svv 0 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fcons_body [pt_dual (pvar 0)]);
        [done|done|exact HCb|exact HKb|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (svv 0 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 fw_C None fwd_body [pv 1 0; pvar 0]);
      [done|done|exact HCf|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma fw_deadlock_free : deadlock_free (∅, {[+ fw_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply fw_typed].
Qed.
