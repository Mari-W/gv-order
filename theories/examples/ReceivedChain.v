(** * received chain: typable, recursion on a received channel (SHARP-EDGES 65)

      Sch = μX. ?(∃κ. X@κ).Close
      C = {ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹ ∣ n ∈ ℕ}      ι[0]ⁿ = ι[0]…[0] (n times, positions from 0)
      rch : □(∀ι. C. ∗ ⊸ (Sch@ι ⊸^{ι+1} ∗))
      rch = !(f = λc. let (d, c) = recv c in let () = close c in
                     spawn (λw. let () = w in (force f) d))
      sch : □(∀ι. C. ∗ ⊸ (S̄ch@ι ⊸^{ι+1} ∗))
      sch = !(g = λc. let (e, e′) = new ∗ in let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in let () = u in
                     let () = close c in spawn (λw. let () = w in (force g) e′))
      ch_main = let (r, s) = ⟨rch, sch⟩ in let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force s) c′) in (force r) c

    The receiver closes c at ι+1 while the thunk holds d at ι[0], the
    fact ι+1 ≺ ι[0] of C at n = 0. The call forces f at ι[0], and
    C[ι[0]/ι] is C without its first fact ([ch_sub]). The sender creates
    e at ι[0] with new, sends it at ι while it holds e′ at ι[0], which
    asks ι ≺ ι[0], derived from ι ≺ ι+1 ≺ ι[0]. The upper point ι+1 of the
    λ covers both blocking points. A tail call would need a ceiling, as
    in the tail-call example.

    In the empty world main creates c with the box constraint itself as
    its creation constraint and forces both boxes at its point. Every
    fact stays inside ι, ordered by the rank 2·depth + offset (sharp
    edges 105).

    With end points the receiver asks ι[0]ⁿ+1 ≺ (ι[0]ⁿ⁺¹)‾ ([ch_C]). The
    sender keeps e′ at ι[0]‾ and recurs there, so its box has its own
    constraint [chs_C]: ι[0]ⁿ ≺ (ι[0]ⁿ⁺¹)‾ and ι[0]ⁿ+1 ≺ ι[0]ⁿ⁺¹, at ι for
    n = 0 and at the negative points after. main forces the receiver at
    γ and the sender at γ̄, and c is created with both ([chc_C]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Fixpoint chv (n : nat) : pname := match n with 0 => NVar 0 | S m => NPayload (chv m) 0 0 end.

Definition Sch : sty := SMu (SSeq (SRcv 1 (TSess (SVar 0) (pvar 0))) SEnd).

(** The receiver closes c at ι[0]ⁿ+1 while it holds d at ι[0]ⁿ⁺¹, whose
    partner point is (ι[0]ⁿ⁺¹)‾. *)
Definition ch_P (g : fact) : Prop := ∃ n, g = FLt (Pt (chv n) 1) (MkPt (chv (S n)) false 0).
Definition ch_C : bcs := BCs [] ch_P.

(** The sender holds c at ι and e′ at ι[0]‾, sends e at ι[0] and recurs
    at ι[0]‾. Its round n sits at ι[0]ⁿ, positive for n = 0 and negative
    after: ι[0]ⁿ ≺ (ι[0]ⁿ⁺¹)‾ for the payload and ι[0]ⁿ+1 ≺ ι[0]ⁿ⁺¹ for the
    close. *)
Definition sp (n : nat) : bool := match n with 0 => true | S _ => false end.
Definition chs_P (g : fact) : Prop :=
  ∃ n, g = FLt (MkPt (chv n) (sp n) 0) (MkPt (chv (S n)) false 0) ∨
       g = FLt (MkPt (chv n) (sp n) 1) (MkPt (chv (S n)) true 0).
Definition chs_C : bcs := BCs [] chs_P.

Definition rch_body : ty := TLolli (Some (pv 0 1)) None (TSess Sch (pv 0 0)) TUnit.
Definition sch_body : ty := TLolli (Some (pv 0 1)) None (TSess (dual Sch) (pv 0 0)) TUnit.

Definition rch : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (App EClos (Var 0))
    (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 2)))))))).

Definition sch : expr :=
  EBox (Lam (let_new_pair
    (LetP (Pair (App ESend (Pair (Var 1) (Var 2))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 1))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 3)))))))))).

Definition ch_main : expr :=
  LetP (Pair rch sch) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Abbreviation chs := (Pt (NPayload (NVar 0) 0 0) 0).

Lemma chv_inst n : pn_inst (plist [chs]) (chv n) = Pt (chv (S n)) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv pn_inst]. by rewrite IH. Qed.

Lemma ch_sub g : ch_P g → fact_scoped 1 g → ch_P (fact_map (pt_inst (plist [chs])) g).
Proof.
  intros (n & ->) _. exists (S n). cbn [fact_map]. unfold pt_inst. cbn [pt_name pt_off pt_pol].
  rewrite !chv_inst. done.
Qed.

Lemma ch_call W Ψ : (ch_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) ch_C [chs].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact ch_sub]. Qed.

Lemma chv_inst_dchs n : pn_inst (plist [pt_dual chs]) (chv (S n)) = Pt (chv (S (S n))) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv pn_inst] in *. by rewrite IH. Qed.

Lemma chv_inst_dual n : pn_inst (plist [pt_dual (pvar 0)]) (chv (S n)) = Pt (chv (S n)) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv pn_inst] in *. by rewrite IH. Qed.

(** C_s[ι[0]‾/ι] is C_s without its round 0. *)
Lemma chs_sub g : chs_P g → fact_scoped 1 g → chs_P (fact_map (pt_inst (plist [pt_dual chs])) g).
Proof.
  intros (n & [-> | ->]) _; exists (S n); cbn [fact_map]; unfold pt_inst; cbn [pt_name pt_off pt_pol];
    destruct n; cbn [sp pn_inst]; rewrite ?chv_inst_dchs; first [left; reflexivity|right; reflexivity].
Qed.

Lemma chs_call W Ψ : (chs_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) chs_C [pt_dual chs].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact chs_sub]. Qed.

Lemma skn_ch W Ψ C x : (C, [pvar 0]) ∈ Ψ → pt_root x = NVar 0 → Forall (skn W Ψ) [x].
Proof.
  intros Hg Hx. apply Forall_singleton. apply (skn_in W Ψ C [pvar 0] (pvar 0)); [done|by left|done].
Qed.

Lemma rch_typed W F : world_wf W → typed W ∅ [] ∅ [] F rch (TBox 1 0 ch_C (TLolli None None TUnit rch_body)).
Proof.
  intros HW. unfold rch.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 ch_C rch_body. cbn. unfold rch_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SSeq (SRcv 1 (TSess Sch (pvar 0))) SEnd) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 1) (pt_dual (Pt (NPayload (NVar 0) 0 0) 0))|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 chs)) (Some (pt_dual chs)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 ch_C None rch_body [chs]);
      [done|done| | |apply ubs_none|tstep].
    + apply ch_call. by left.
    + apply (skn_ch W _ ch_C chs); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 chs). split; [done|]. apply sle_refl, HW.
Qed.

Lemma sch_typed W F : strict W → typed W ∅ [] ∅ [] F sch (TBox 1 0 chs_C (TLolli None None TUnit sch_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold sch.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 chs_C sch_body. cbn. unfold sch_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  assert (∀ Ψ, (chs_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 1) chs) as Hlt1.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pv 0 1) chs); [exact Hg|exists 0; by right|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (chs_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 0) chs) as Hlt.
  { intros Ψ Hg. apply (sl_trans _ _ _ (pv 0 1)); [apply (slt_po W _ (pv 0 0) HW)|by apply Hlt1]. }
  assert (∀ Ψ, (chs_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 0) (pt_dual chs)) as Hlt'.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pv 0 0) (pt_dual chs)); [exact Hg|exists 0; by left|cbn; lia|reflexivity|reflexivity]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ Sch chs HWs).
  { right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess Sch chs) (TSess (SSeq (SSnd 1 (TSess Sch (pvar 0))) SEnd) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess Sch (pvar 0)) SEnd (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. apply Hlt'. by left.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply Hlt; by left|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; apply Hlt1; by left|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 (pt_dual chs))) (Some chs) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 chs_C None sch_body [pt_dual chs]);
      [done|done| | |apply ubs_none|tstep].
    + apply chs_call. by left.
    + apply (skn_ch W _ chs_C (pt_dual chs)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 (pt_dual chs)). split; [done|]. apply sle_refl, HW.
Qed.

(** main creates c with both box constraints as its creation
    constraint, the receiver's at γ and the sender's at γ̄. Every fact
    stays inside γ, ordered by the rank 2·depth + offset, which ignores
    polarity (sharp edges 105). *)
Definition chc_P (g : fact) : Prop :=
  ch_P g ∨
  ∃ n, g = FLt (MkPt (chv n) false 0) (MkPt (chv (S n)) false 0) ∨
       g = FLt (MkPt (chv n) false 1) (MkPt (chv (S n)) true 0).
Definition chc_C : bcs := BCs [] chc_P.

Lemma chv_vb n : pn_vb 1 (chv n).
Proof. induction n as [|n IH]; simpl; [lia|done]. Qed.

Fixpoint chv_depth (p : pname) : option nat :=
  match p with
  | NVar 0 => Some 0
  | NPayload q 0 0 => match chv_depth q with Some n => Some (S n) | None => None end
  | _ => None
  end.

Definition ch_rank (x : point) : nat :=
  match chv_depth (pt_name x) with Some n => 2 * n + pt_off x | None => pt_off x end.

Lemma chv_depth_chv n : chv_depth (chv n) = Some n.
Proof. induction n as [|n IH]; [done|]. simpl. by rewrite IH. Qed.

Lemma chc_ok peq plt : cc_ok peq plt chc_C.
Proof.
  apply (cc_ok_inner peq plt chc_P (λ x y, ch_rank x < ch_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold ch_rank, pt_shift. simpl. case_match; lia.
  - intros g [[n ->]|(n & [-> | ->])] _; eexists _, _; (split; [done|]); unfold ch_rank; cbn [pt_name pt_off];
      change (chv (S n)) with (NPayload (chv n) 0 0); cbn [chv_depth]; rewrite chv_depth_chv; lia.
  - intros [n pb o] _. unfold ch_rank, pt_shift, pt_dual. simpl. case_match; lia.
Qed.

Lemma ch_typed : styped ∅ [] [] (∅, None) ch_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold ch_main.
  tstep.
  { tstep; [apply sch_typed, HWs|apply rch_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ Sch chc_C); [apply chc_ok|constructor|].
  fresh_clean.
  set (Ψ := [(chc_C, [pvar 0])]).
  assert (∀ x y, chc_P (FLt x y) → fact_scoped 1 (FLt x y) → slt W Ψ x y) as Hc.
  { intros x y Hg Hs.
    assert (slt W Ψ (pt_inst (plist [pvar 0]) x) (pt_inst (plist [pvar 0]) y)) as H.
    { eapply (sl_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
    change (plist [pvar 0]) with (plist (ids 1)) in H. destruct Hs as [Hx Hy].
    by rewrite !pt_inst_ids in H by done. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) ch_C [pvar 0]) as HC.
  { apply bcs_hold_intro. intros g [n ->] Hs.
    change (plist [pvar 0]) with (plist (ids 1)). destruct Hs as [Hx Hy]. cbn [fact_map fact_holds].
    rewrite !pt_inst_ids by done. apply Hc; [left; by exists n|split; done]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) chs_C [pt_dual (pvar 0)]) as HCs.
  { apply bcs_hold_intro. intros g (n & [-> | ->]) _; cbn [fact_map fact_holds];
      (destruct n as [|m]; unfold pt_inst; cbn [pt_name pt_pol pt_off sp]; rewrite ?chv_inst_dual; cbn;
        [apply (Hc (MkPt (chv 0) false _) (MkPt (chv 1) _ 0))
        |apply (Hc (MkPt (chv (S m)) false _) (MkPt (chv (S (S m))) _ 0))]);
      first [right; exists 0; by left|right; exists 0; by right
            |right; exists (S m); by left|right; exists (S m); by right
            |split; apply chv_vb]. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pvar 0)]) as HKs.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  match goal with |- typed _ _ _ _ [Some ?A; _; None; None; Some ?B; Some ?D] _ _ _ =>
    change A with (TSess (dual Sch) (pt_dual (pvar 0))) end.
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 1))) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 chs_C None sch_body [pt_dual (pvar 0)]);
        [done|done|exact HCs|exact HKs|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pv 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 ch_C None rch_body [pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma ch_deadlock_free : deadlock_free (∅, {[+ ch_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply ch_typed].
Qed.
