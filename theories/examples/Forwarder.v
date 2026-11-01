(** * forwarder in a box: typable, recursive (SHARP-EDGES 67)

      Si = μX. ?(∃κ. Close@κ).X       So = μX. !(∃κ. Close@κ).X
      Cf = {ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1,  ι′+k ≺ (ι′+k)[0],
            (ι+k)[0] ≡ (ι′+k)[0]  ∣  k ∈ ℕ}                  (slots from 0)
      Cp = {ι+k ≺ (ι+k)[0],  (ι+k)[0] ≺ ι+k+1  ∣  k ∈ ℕ}
      fwd   : □(∀ι ι′. Cf. ∗ ⊸^⊥_⊤ (Si@ι ⊗ So@ι′ ⊸^{ι′}_⊤ ∗))
      fwd   = !(f = λp. let (a, b) = p in let (d, a) = recv a in
                       let (b, u) = ⟨send ⟨d, b⟩, ∗⟩ in let () = u in
                       spawn (λw. let () = w in (force f) ⟨a, b⟩))
      fprod : □(∀ι. Cp. ∗ ⊸^⊥_⊤ (S̄i@ι ⊸^{ι[0]}_⊤ ∗))
      fprod = !(g = λc. let (e, e′) = new ∗ in let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in
                       let () = u in let () = close e′ in
                       spawn (λw. let () = w in (force g) c))
      fcons : □(∀ι. Cp. ∗ ⊸^⊥_⊤ (S̄o@ι ⊸^{ι[0]}_⊤ ∗))
      fcons = !(h = λc. let (d, c) = recv c in let () = close d in
                       spawn (λw. let () = w in (force h) c))
      fw_main = let ((p, f), h) = ⟨⟨fprod, fwd⟩, fcons⟩ in
                let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                let () = spawn (λw. let () = w in (force p) a′) in
                let () = spawn (λw. let () = w in (force h) b′) in (force f) ⟨a, b⟩

    recv a gives d the type Close@ι[0], and send at ι′ asks Close@ι′[0].
    E-Conv up to Γ ⊢ ≡ ([t_conv] with [steq]) moves d along the fact
    ι[0] ≡ ι′[0] of Cf ([se_hyp0]). The producer creates e at ι[0], the
    slot its payload must live at. The recursive calls ask Cf and Cp one
    round later, which C contains ([fw_sub], [fp_sub]). [Wfw] has
    (a,k)[0] ≡ (b,k)[0] for every k, and its strictness reads (b,k)[0]
    as (a,k)[0] through a map on names that respects slots
    ([wgen_strict_cong]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Abbreviation svv a k := (Pt (NSlot (NVar a) k 0) 0).
Abbreviation sl a k := (Pt (NSlot (NConst a) k 0) 0).

Definition Sfi : sty := SMu (SRcv 1 (TSess SEnd (pvar 0)) (SVar 0)).
Definition Sfo : sty := SMu (SSnd 1 (TSess SEnd (pvar 0)) (SVar 0)).

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

Lemma fwd_typed W F : world_wf W → typed W ∅ [] ∅ [] F fwd (TBox 2 fw_C (TLolli None None TUnit fwd_body)).
Proof.
  intros HW. unfold fwd.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open fw_C fwd_body. cbn. unfold fwd_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SRcv 1 (TSess SEnd (pvar 0)) Sfi) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; fhyp (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. fhyp (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
              (TProd (TSess SEnd (svv 1 0)) (TSess (SSnd 1 (TSess SEnd (pvar 0)) Sfo) (pv 1 0)))).
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
  - apply (typed_force W _ _ _ _ _ _ 2 fw_C None fwd_body [pv 0 1; pv 1 1]);
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

Lemma fprod_typed W F : strict W → typed W ∅ [] ∅ [] F fprod (TBox 1 fp_C (TLolli None None TUnit fprod_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fprod.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 fp_C fprod_body. cbn. unfold fprod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (svv 0 0) HWs); [skn_slot|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (svv 0 0)) (TSess (SSnd 1 (TSess SEnd (pvar 0)) (dual Sfi)) (pv 0 0)))).
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
  - apply (typed_force W _ _ _ _ _ _ 1 fp_C None fprod_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fp_call. by left.
    + apply (skn_fp W _ (pv 0 1)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (svv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma fcons_typed W F : world_wf W → typed W ∅ [] ∅ [] F fcons (TBox 1 fp_C (TLolli None None TUnit fcons_body)).
Proof.
  intros HW. unfold fcons.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 fp_C fcons_body. cbn. unfold fcons_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SRcv 1 (TSess SEnd (pvar 0)) (dual Sfo)) (pv 0 0))).
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
  - apply (typed_force W _ _ _ _ _ _ 1 fp_C None fcons_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply fp_call. by left.
    + apply (skn_fp W _ (pv 0 1)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (svv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

(** The facts of the three constraints at ((a,0), (b,0)), (a,0) and (b,0). *)
Definition fw_facts (W : world) : Prop :=
  ∀ k, w_lt W (pc 0 k) (pc 1 k) ∧ w_lt W (pc 1 k) (pc 0 (S k)) ∧
       w_lt W (pc 1 k) (sl 1 k) ∧ w_eq W (sl 0 k) (sl 1 k) ∧
       w_lt W (pc 0 k) (sl 0 k) ∧ w_lt W (sl 0 k) (pc 0 (S k)) ∧
       w_lt W (sl 1 k) (pc 1 (S k)).

Lemma fw_typed W : strict W → pt_known W (pc 0 0) → pt_known W (pc 1 0) → fw_facts W →
  typed W ∅ [] ∅ [] (∅, None) fw_main TUnit.
Proof.
  intros HWs Ha Hb H. pose proof (proj1 HWs) as HW. unfold fw_main.
  assert (bcs_hold (seqs W []) (slt W []) fw_C [pc 0 0; pc 1 0]) as HCf.
  { apply bcs_hold_intro. intros g (k & Hg) _. destruct (H k) as (A1 & A2 & A3 & A4 & _).
    destruct Hg as [-> | [-> | [-> | ->]]]; cbn;
      first [by apply sl_w|by apply se_w]. }
  assert (∀ a, (∀ k, w_lt W (pc a k) (sl a k) ∧ w_lt W (sl a k) (pc a (S k))) →
            bcs_hold (seqs W []) (slt W []) fp_C [pc a 0]) as HCp.
  { intros a Ha'. apply bcs_hold_intro. intros g (k & Hg) _. destruct (Ha' k) as (A1 & A2).
    destruct Hg as [-> | ->]; cbn; by apply sl_w. }
  assert (bcs_hold (seqs W []) (slt W []) fp_C [pc 0 0]) as HCa.
  { apply HCp. intros k. destruct (H k) as (_ & _ & _ & _ & A5 & A6 & _). done. }
  assert (bcs_hold (seqs W []) (slt W []) fp_C [pc 1 0]) as HCb.
  { apply HCp. intros k. destruct (H k) as (_ & _ & A3 & _ & _ & _ & A7). done. }
  assert (Forall (skn W []) [pc 0 0; pc 1 0]) as HK.
  { constructor; [by left|constructor; [by left|constructor]]. }
  assert (Forall (skn W []) [pc 0 0]) as HKa by (constructor; [by left|constructor]).
  assert (Forall (skn W []) [pc 1 0]) as HKb by (constructor; [by left|constructor]).
  tstep.
  { tstep; [apply fcons_typed, HW|]. tstep; [apply fwd_typed, HW|apply fprod_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Sfi (pc 0 0) HWs (or_introl Ha)).
  cbn. apply (t_new_at W _ _ _ _ _ _ _ Sfo (pc 1 0) HWs (or_introl Hb)).
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sl 0 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 1 fp_C None fprod_body [pc 0 0]);
        [done|done|exact HCa|exact HKa|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (sl 0 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sl 1 0)) (Some (pc 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 1 fp_C None fcons_body [pc 1 0]);
        [done|done|exact HCb|exact HKb|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (sl 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 fw_C None fwd_body [pc 0 0; pc 1 0]);
      [done|done|exact HCf|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world: (b,k)[0] ≡ (a,k)[0] and the order facts of the three
    constraints. The rank reads (b,k)[0] as (a,k)[0] and orders
    (a,k), (b,k), (a,k)[0] by 3k, 3k+1, 3k+2. *)
Definition fw_slot (q : pname) (b i : nat) : pname :=
  match q, i with NConst 1, 0 => NSlot (NConst 0) b 0 | _, _ => NSlot q b i end.

Fixpoint fw_ren (p : pname) : pname :=
  match p with NSlot q b i => fw_slot (fw_ren q) b i | _ => p end.

Definition fw_cn (x : point) : point := Pt (fw_ren (pt_name x)) (pt_off x).

Definition fw_E (x y : point) : Prop := ∃ k, x = sl 1 k ∧ y = sl 0 k.

Definition fw_L (x y : point) : Prop :=
  ∃ k, (x = pc 0 k ∧ y = pc 1 k) ∨ (x = pc 1 k ∧ y = pc 0 (S k)) ∨
       (x = pc 1 k ∧ y = sl 1 k) ∨ (x = pc 0 k ∧ y = sl 0 k) ∨
       (x = sl 0 k ∧ y = pc 0 (S k)) ∨ (x = sl 1 k ∧ y = pc 1 (S k)).

Definition Wfw : world := wgen (list_to_set (NConst <$> [0; 1])) fw_E fw_L.

Definition fw_base (p : pname) : nat :=
  match p with NConst 1 => 1 | NSlot (NConst 0) k 0 => 3 * k + 2 | _ => 0 end.
Definition fw_step (p : pname) : nat :=
  match p with NConst 0 => 3 | NConst 1 => 3 | _ => 1 end.
Definition fw_rank (x : point) : nat := fw_base (pt_name x) + fw_step (pt_name x) * pt_off x.

Lemma Wfw_strict : strict Wfw.
Proof.
  apply (wgen_strict_cong _ _ _ fw_cn fw_rank).
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (k & -> & ->). right. rewrite !elem_of_list_to_set. cbn. set_solver.
  - intros x y (k & H); right; rewrite !elem_of_list_to_set;
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->]; cbn; set_solver.
  - done.
  - intros [p o] [q o'] i E. unfold fw_cn in *. cbn in *. injection E as E1 E2. by rewrite E1, E2.
  - intros x y (k & -> & ->). done.
  - intros x. unfold fw_rank, pt_shift. cbn.
    assert (0 < fw_step (pt_name x)) by (unfold fw_step; repeat case_match; lia). nia.
  - intros x y (k & H);
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->]; unfold fw_rank; cbn; lia.
Qed.

Lemma fw_deadlock_free : deadlock_free (∅, {[+ fw_main +]}).
Proof.
  apply (soundness Wfw _ TUnit Wfw_strict).
  apply ptyped_closed; [constructor|]. apply fw_typed; [apply Wfw_strict| | |].
  - unfold pt_known, Wfw. simpl. set_solver.
  - unfold pt_known, Wfw. simpl. set_solver.
  - intros k. split_and!; try (apply glt_base; exists k; naive_solver).
    apply geq_sym, geq_base. by exists k.
Qed.
