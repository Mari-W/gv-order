(** * forwarder in a box: typable, recursive (SHARP-EDGES 67)

      Si = μX. ?(∃κ. Close@κ).X       So = μX. !(∃κ. Close@κ).X
      Cf = {ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1,  ι′+k ≺ (ι′+k)[0],
            (ι+k)[0] ≡ (ι′+k)[0]  ∣  k ∈ ℕ}                  (positions from 0)
      Cp = {ι+k ≺ (ι+k)[0],  (ι+k)[0] ≺ ι+k+1  ∣  k ∈ ℕ}
      fwd   : □(∀ι ι′. Cf. ∗ ⊸ (Si@ι ⊗ So@ι′ ⊸^{ι′} ∗))
      fwd   = !(f = λp. let (a, b) = p in let (d, a) = recv a in
                       let (b, u) = ⟨send ⟨d, b⟩, ∗⟩ in let () = u in
                       spawn (λw. let () = w in (force f) ⟨a, b⟩))
      fprod : □(∀ι. Cp. ∗ ⊸ (S̄i@ι ⊸^{ι[0]} ∗))
      fprod = !(g = λc. let (e, e′) = new ∗ in let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in
                       let () = u in let () = close e′ in
                       spawn (λw. let () = w in (force g) c))
      fcons : □(∀ι. Cp. ∗ ⊸ (S̄o@ι ⊸^{ι[0]} ∗))
      fcons = !(h = λc. let (d, c) = recv c in let () = close d in
                       spawn (λw. let () = w in (force h) c))
      fw_main = let ((p, f), h) = ⟨⟨fprod, fwd⟩, fcons⟩ in
                let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                let () = spawn (λw. let () = w in (force p) a′) in
                let () = spawn (λw. let () = w in (force h) b′) in (force f) ⟨a, b⟩

    recv a gives d the type Close@ι[0], and send at ι′ asks Close@ι′[0].
    E-Conv up to Γ ⊢ ≡ ([t_conv] with [steq]) moves d along the fact
    ι[0] ≡ ι′[0] of Cf ([se_hyp0]). The producer creates e at ι[0], the
    point its payload must live at. The recursive calls ask Cf and Cp one
    round later, which C contains ([fw_sub], [fp_sub]).

    In the empty world main creates a with the producer constraint fp_C
    and b with the facts that relate it to a, the alias family
    (γ+k)[0] ≡ (ε+k)[0] included ([fwb_ok], sharp edges 105). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Abbreviation svv a k := (Pt (NSlot (NVar a) k 0) 0).
Abbreviation sl a k := (Pt (NSlot (NConst a) k 0) 0).

Definition Sfi : sty := SMu (SSeq (SRcv 1 (TSess SEnd (pvar 0))) (SVar 0)).
Definition Sfo : sty := SMu (SSeq (SSnd 1 (TSess SEnd (pvar 0))) (SVar 0)).

Definition fw_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 0 k) (pv 1 k) ∨ g = FLt (pv 1 k) (pv 0 (S k)) ∨
       g = FLt (pv 1 k) (svv 1 k) ∨ g = FEq (svv 0 k) (svv 1 k).
Definition fw_C : bcs := BCs [] fw_P.

Definition fp_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (svv 0 k) ∨ g = FLt (svv 0 k) (pv 0 (S k)).
Definition fp_C : bcs := BCs [] fp_P.

Definition fwd_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Sfi (pv 0 0)) (TSess Sfo (pv 1 0))) TUnit.
Definition fprod_body : ty := TLolli (Some (svv 0 0)) None (TSess (dual Sfi) (pv 0 0)) TUnit.
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
  intros (k & [-> | [-> | [-> | ->]]]) _; exists (S k);
    [left|right; left|right; right; left|right; right; right]; reflexivity.
Qed.

Lemma fp_sub g : fp_P g → fact_scoped 1 g → fp_P (fact_map (pt_inst (plist [pv 0 1])) g).
Proof. intros (k & [-> | ->]) _; exists (S k); [left|right]; reflexivity. Qed.

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
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open fw_C fwd_body. cbn. unfold fwd_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess SEnd (pvar 0))) Sfi) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. fhyp (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
              (TProd (TSess SEnd (svv 1 0)) (TSess (SSeq (SSnd 1 (TSess SEnd (pvar 0))) Sfo) (pv 1 0)))).
    - tstep; [eapply t_conv; [|tstep]; conv_sess|].
      (* the alias: d : Close@ι[0] becomes Close@ι′[0] along ι[0] ≡ ι′[0] *)
      eapply t_conv; [|tstep]. split; [|apply seq_refl].
      eapply (se_hyp0 _ _ _ _ (svv 0 0) (svv 1 0)); [by left|fmem|cbn; lia|reflexivity|reflexivity].
    - apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) Sfo (pv 1 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. fhyp (pv 1 0) (svv 1 0).
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 1 0) (pv 0 1)|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 0 1)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; fhyp (pv 0 1) (pv 1 1)]. }
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
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fp_C fprod_body. cbn. unfold fprod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (svv 0 0) HWs); [skn_slot|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (svv 0 0)) (TSess (SSeq (SSnd 1 (TSess SEnd (pvar 0))) (dual Sfi)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) (dual Sfi) (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. fhyp (pv 0 0) (svv 0 0).
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 0 0) (svv 0 0)|].
      exists (svv 0 0). split; [done|]. right. fhyp (pv 0 0) (svv 0 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (svv 0 0) (pv 0 1)|].
    exists (svv 0 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (svv 0 1)) (Some (pv 0 1)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fprod_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fp_call. by left.
    + apply (skn_fp W _ (pv 0 1)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (svv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma fcons_typed W F : world_wf W → typed W ∅ [] ∅ [] F fcons (TBox 1 0 fp_C (TLolli None None TUnit fcons_body)).
Proof.
  intros HW. unfold fcons.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fp_C fcons_body. cbn. unfold fcons_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess SEnd (pvar 0))) (dual Sfo)) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (svv 0 0). split; [done|]. right. fhyp (pv 0 0) (svv 0 0). }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (svv 0 0) (pv 0 1)|].
    exists (svv 0 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (svv 0 1)) (Some (pv 0 1)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fcons_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fp_call. by left.
    + apply (skn_fp W _ (pv 0 1)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (svv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

(** ** main in the empty world (sharp edges 105)

    a is created at γ with the constraint of the producer, fp_C itself,
    whose facts stay inside γ. b is created at ε with the facts that
    relate it to a and the constraint of the consumer,

      Cb = {γ+k ≺ ε+k,  ε+k ≺ γ+k+1,  ε+k ≺ (ε+k)[0],
            (γ+k)[0] ≡ (ε+k)[0],  (ε+k)[0] ≺ ε+k+1  ∣  k ∈ ℕ}.

    Its model reads (ε+k)[0] as (γ+k)[0], orders the points of ε by
    their offsets, and the facts that enter and leave ε close through
    program order and fp_C at γ. *)

Definition fwb_P (g : fact) : Prop :=
  ∃ k, g = FLt (pv 1 k) (pv 0 k) ∨ g = FLt (pv 0 k) (pv 1 (S k)) ∨
       g = FLt (pv 0 k) (svv 0 k) ∨ g = FEq (svv 1 k) (svv 0 k) ∨
       g = FLt (svv 0 k) (pv 0 (S k)).
Definition fwb_C : bcs := BCs [pvar 0] fwb_P.

Definition fwa_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 2 * pt_off x
  | NSlot (NVar 0) k 0 => 2 * k + 1 + 2 * pt_off x
  | _ => pt_off x
  end.

Lemma fwa_ok peq plt : cc_ok peq plt fp_C.
Proof.
  apply (cc_ok_inner peq plt fp_P (λ x y, fwa_rank x < fwa_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n o] _. unfold fwa_rank, pt_shift. simpl. repeat case_match; lia.
  - intros g (k & [-> | ->]) _; eexists _, _; (split; [done|]); unfold fwa_rank; cbn; lia.
Qed.

(** The map of the model: (ε+k)[0] and everything carried there go to
    (γ+k)[0]. *)
Fixpoint fwb_name (p : pname) : pname :=
  match p with
  | NSlot (NVar 0) k 0 => NSlot (NVar 1) k 0
  | NSlot q k i => NSlot (fwb_name q) k i
  | _ => p
  end.

Definition fwb_phi (x : point) : point := Pt (fwb_name (pt_name x)) (pt_off x).

Lemma fwb_name_old p : pn_root p ≠ NVar 0 → fwb_name p = p.
Proof.
  induction p as [c|c|q IH k i]; simpl; [done|done|]. intros H.
  destruct q as [c|[|c]|q' k' i']; destruct i; simpl in *; try done; rewrite ?IH; done.
Qed.

Lemma fwb_name_root p : pn_root (fwb_name p) = NVar 0 → pn_root p = NVar 0.
Proof.
  induction p as [c|c|q IH k i]; simpl; [done|done|].
  destruct q as [c|[|c]|q' k' i']; destruct i; simpl in *; auto.
Qed.

Lemma fwb_name_var0 p : fwb_name p = NVar 0 → p = NVar 0.
Proof.
  destruct p as [c|c|q k i]; simpl; [done|done|].
  destruct q as [c|[|c]|q' k' i']; destruct i; simpl; done.
Qed.

Lemma fwb_ok W Ψ : world_wf W → (fp_C, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) fwb_C.
Proof.
  intros HW Hg.
  set (T := glt (cc_up (seqs W Ψ)) (cc_up (slt W Ψ))).
  assert (∀ x y, slt W Ψ x y → T (pt_inst (λ a, pvar (a + 1)) x) (pt_inst (λ a, pvar (a + 1)) y))
    as Hup by (intros; by apply cc_up_lt).
  assert (∀ k, T (pv 1 k) (svv 1 k)) as Ha1.
  { intros k. apply (Hup (pv 0 k) (svv 0 k)).
    eapply (sl_hyp0 _ _ _ _ (pv 0 k) (svv 0 k)); [exact Hg|exists k; by left|cbn; lia|done|done]. }
  assert (∀ k, T (svv 1 k) (pv 1 (S k))) as Ha2.
  { intros k. apply (Hup (svv 0 k) (pv 0 (S k))).
    eapply (sl_hyp0 _ _ _ _ (svv 0 k) (pv 0 (S k))); [exact Hg|exists k; by right|cbn; lia|done|done]. }
  assert (∀ k j, k < j → T (pv 1 k) (pv 1 j)) as Hpo.
  { intros k j Hkj. apply (th_pofs _ _ _ _ (theory_gen _ _)). unfold pofs. simpl. split; [done|lia]. }
  apply (cc_model (seqs W Ψ) (slt W Ψ) fwb_C fwb_phi (λ x y, pofs x y)
           (λ u p, ∃ k, (u = pv 1 k ∧ p = pv 0 k) ∨ (u = svv 1 k ∧ p = pv 0 (S k)))
           (λ q v, ∃ k, (q = pv 0 k ∧ v = pv 1 (S k)) ∨ (q = pv 0 k ∧ v = svv 1 k))).
  - intros [n o] Hn. unfold fwb_phi, pt_root in *. simpl in *. by rewrite fwb_name_old.
  - done.
  - intros [n o] i Hr. unfold fwb_phi, pt_slot, pt_root in *. simpl in *.
    destruct n as [c|[|c]|q k i']; destruct i; simpl in *; try done.
  - intros [n o] [n' o'] i E. unfold fwb_phi, pt_slot in *. cbn [pt_name pt_off] in *.
    injection E as E1 <-.
    destruct (decide (n = NVar 0)) as [->|Hn].
    + cbn [fwb_name] in E1. symmetry in E1. apply fwb_name_var0 in E1 as ->. done.
    + destruct (decide (n' = NVar 0)) as [->|Hn'].
      * cbn [fwb_name] in E1. apply fwb_name_var0 in E1 as ->. done.
      * assert (∀ m, m ≠ NVar 0 → fwb_name (NSlot m o i) = NSlot (fwb_name m) o i) as Hs.
        { intros m Hm. destruct m as [c|[|c]|q k j]; destruct i; simpl; done. }
        rewrite (Hs n), (Hs n') by done. by rewrite E1.
  - apply pofs_trans.
  - intros p _. apply pofs_shift.
  - apply pofs_irrefl.
  - assert (∀ m j, (pv 0 m = pv 0 j ∨ pofs (pv 0 m) (pv 0 j)) → m ≤ j) as Hle.
    { intros m j [E|[_ Ho]]; [injection E; lia|simpl in Ho; lia]. }
    assert (∀ k j, k ≤ j → T (pv 1 k) (svv 1 j)) as Hle'.
    { intros k j Hkj. destruct (decide (k = j)) as [<-|Hne]; [apply Ha1|].
      eapply glt_trans; [apply (Hpo k j); lia|apply Ha1]. }
    intros u p q v (k & [[-> ->]|[-> ->]]) (j & [[-> ->]|[-> ->]]) Hpq; apply Hle in Hpq.
    + apply Hpo. lia.
    + by apply Hle'.
    + eapply glt_trans; [apply Ha2|apply Hpo; lia].
    + eapply glt_trans; [apply Ha2|apply Hle'; lia].
  - intros a b (f & (k & Hf) & Hs & E). simpl in E.
    destruct Hf as [->|[->|[->|[->| ->]]]]; try discriminate.
    injection E as -> ->. cbn. apply geq_refl.
  - intros a b (f & (k & Hf) & Hs & E). simpl in E.
    destruct Hf as [->|[->|[->|[->| ->]]]]; try discriminate; injection E as -> ->; cbn.
    + right; left. split_and!; [done|done|]. exists (pv 1 k), (pv 0 k).
      split_and!; [exists k; by left|left; apply geq_refl|by left].
    + right; right; left. split_and!; [done|done|]. exists (pv 0 k), (pv 1 (S k)).
      split_and!; [exists k; by left|by left|left; apply geq_refl].
    + right; right; left. split_and!; [done|done|]. exists (pv 0 k), (svv 1 k).
      split_and!; [exists k; by right|by left|left; apply geq_refl].
    + right; left. split_and!; [done|done|]. exists (svv 1 k), (pv 0 (S k)).
      split_and!; [exists k; by right|left; apply geq_refl|by left].
Qed.

Lemma se_hyp_fresh W Ψ C x u v :
  (C, [x]) ∈ Ψ → bc_facts C (FEq u v) → fact_scoped (S (length (bc_env C))) (FEq u v) →
  seqs W Ψ (pt_inst (plist (x :: bc_env C)) u) (pt_inst (plist (x :: bc_env C)) v).
Proof.
  intros Hin Hf Hs. apply se_h. exists C, [x]. split; [done|].
  exists (fact_map (pt_inst (pup 1 (plist (bc_env C)))) (FEq u v)). split.
  - exists (FEq u v). split_and!; [done|done|done].
  - by rewrite open1_comp.
Qed.

Lemma fw_typed : styped ∅ [] [] (∅, None) fw_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fw_main.
  tstep.
  { tstep; [apply fcons_typed, HW|]. tstep; [apply fwd_typed, HW|apply fprod_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sfi fp_C); [apply fwa_ok|constructor|].
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sfo fwb_C); [apply fwb_ok; [done|by left]|
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]|].
  fresh_clean.
  match goal with |- typed _ _ ?Ψ0 _ _ _ _ _ => set (Ψ := Ψ0) end.
  assert (∀ u v, fwb_P (FLt u v) → fact_scoped 2 (FLt u v) →
            slt W Ψ (pt_inst (plist [pvar 0; pv 1 0]) u) (pt_inst (plist [pvar 0; pv 1 0]) v)) as Hb.
  { intros u v Hf Hs. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) fwb_C) (pvar 0) u v);
      [by right; left|done|done]. }
  assert (∀ k, seqs W Ψ (svv 1 k) (svv 0 k)) as Hbe.
  { intros k. apply (se_hyp_fresh W Ψ (bcs_inst (pshift 1) fwb_C) (pvar 0) (svv 1 k) (svv 0 k));
      [by right; left|exists k; by right; right; right; left|cbn; lia]. }
  assert (∀ g, fp_P g → fact_scoped 1 g →
            fact_holds (seqs W Ψ) (slt W Ψ) (fact_map (pt_inst (plist [pv 1 0])) g)) as Ha.
  { intros [x y|x y] Hg Hs; cbn.
    - eapply (sl_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity].
    - eapply (se_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pv 1 0; pvar 0]) as HCf.
  { apply bcs_hold_intro. intros g (k & Hg) _.
    destruct Hg as [-> | [-> | [-> | ->]]]; cbn.
    - apply (Hb (pv 1 k) (pv 0 k)); [exists k; by left|cbn; lia].
    - apply (Hb (pv 0 k) (pv 1 (S k))); [exists k; by right; left|cbn; lia].
    - apply (Hb (pv 0 k) (svv 0 k)); [exists k; by right; right; left|cbn; lia].
    - apply Hbe. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fp_C [pv 1 0]) as HCa.
  { apply bcs_hold_intro. intros g Hg Hs. by apply Ha. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fp_C [pvar 0]) as HCb.
  { apply bcs_hold_intro. intros g (k & [-> | ->]) _; cbn.
    - apply (Hb (pv 0 k) (svv 0 k)); [exists k; by right; right; left|cbn; lia].
    - apply (Hb (svv 0 k) (pv 0 (S k))); [exists k; by right; right; right; right|cbn; lia]. }
  assert (Forall (skn W Ψ) [pv 1 0; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pv 1 0]) as HKa by (constructor; [eapply skn_inst; [by left|by left|done]|constructor]).
  assert (Forall (skn W Ψ) [pvar 0]) as HKb
    by (constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]).
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E; Some ?G; None] _ _ _ =>
    change A with (TSess (dual Sfo) (pvar 0)); change B with (TSess Sfo (pvar 0));
    change A' with (TSess (dual Sfi) (pv 1 0)); change B' with (TSess Sfi (pv 1 0));
    change D with (TBox 2 0 fw_C (TLolli None None TUnit fwd_body));
    change E with (TBox 1 0 fp_C (TLolli None None TUnit fprod_body));
    change G with (TBox 1 0 fp_C (TLolli None None TUnit fcons_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (Pt (NSlot (NVar 1) 0 0) 0)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fprod_body [pv 1 0]);
        [done|done|exact HCa|exact HKa|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (Pt (NSlot (NVar 1) 0 0) 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (svv 0 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 fp_C None fcons_body [pvar 0]);
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
