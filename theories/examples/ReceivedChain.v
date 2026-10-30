(** * received chain: typable, recursion on a received channel (SHARP-EDGES 65)

      Sch = μX. ?(∃κ. X@κ).Close
      C = {ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹ ∣ n ∈ ℕ}      ι[0]ⁿ = ι[0]…[0] (n times, slots from 0)
      rch : □(∀ι. C. ∗ ⊸^⊥_⊤ (Sch@ι ⊸^{ι+1}_⊤ ∗))
      rch = !(f = λc. let (d, c) = recv c in let () = close c in
                     spawn (λw. let () = w in (force f) d))
      sch : □(∀ι. C. ∗ ⊸^⊥_⊤ (S̄ch@ι ⊸^{ι+1}_⊤ ∗))
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
    in the tail-call example. [Wch] has (a,0)[0]ⁿ + 1 ≺ (a,0)[0]ⁿ⁺¹,
    strict by the rank 2·depth + offset. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Fixpoint chv (n : nat) : pname := match n with 0 => NVar 0 | S m => NSlot (chv m) 0 0 end.
Fixpoint chc (n : nat) : pname := match n with 0 => NConst 0 | S m => NSlot (chc m) 0 0 end.

Definition Sch : sty := SMu (SRcv 1 (TSess (SVar 0) (pvar 0)) SEnd).

Definition ch_P (g : fact) : Prop := ∃ n, g = FLt (Pt (chv n) 1) (Pt (chv (S n)) 0).
Definition ch_C : bcs := BCs [] ch_P.

Definition rch_body : ty := TLolli (Some (pv 0 1)) None (TSess Sch (pv 0 0)) TUnit.
Definition sch_body : ty := TLolli (Some (pv 0 1)) None (TSess (dual Sch) (pv 0 0)) TUnit.

Definition rch : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (App EClos (Var 0))
    (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 2)))))))).

Definition sch : expr :=
  EBox (Lam (LetP (App ENew EUnit)
    (LetP (Pair (App ESend (Pair (Var 1) (Var 2))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 1))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 3)))))))))).

Definition ch_main : expr :=
  LetP (Pair rch sch) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Abbreviation chs := (Pt (NSlot (NVar 0) 0 0) 0).

Lemma chv_inst n : pn_inst (plist [chs]) (chv n) = Pt (chv (S n)) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv pn_inst]. by rewrite IH. Qed.

Lemma chc_inst n : pn_inst (plist [pc 0 0]) (chv n) = Pt (chc n) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv chc pn_inst]. by rewrite IH. Qed.

Lemma ch_sub g : ch_P g → fact_scoped 1 g → ch_P (fact_map (pt_inst (plist [chs])) g).
Proof.
  intros (n & ->) _. exists (S n). cbn [fact_map]. unfold pt_inst. cbn [pt_name pt_off].
  rewrite !chv_inst. done.
Qed.

Lemma ch_call W Ψ : (ch_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) ch_C [chs].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact ch_sub]. Qed.

Lemma skn_ch W Ψ x : (ch_C, [pvar 0]) ∈ Ψ → pt_root x = NVar 0 → Forall (skn W Ψ) [x].
Proof.
  intros Hg Hx. apply Forall_singleton. apply (skn_in W Ψ ch_C [pvar 0] (pvar 0)); [done|by left|done].
Qed.

Lemma rch_typed W F : world_wf W → typed W ∅ [] ∅ [] F rch (TBox 1 ch_C (TLolli None None TUnit rch_body)).
Proof.
  intros HW. unfold rch.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 ch_C rch_body. cbn. unfold rch_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SRcv 1 (TSess Sch (pvar 0)) SEnd) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 1) (Pt (NSlot (NVar 0) 0 0) 0)|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 chs)) (Some chs) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 1 ch_C None rch_body [chs]);
      [done|done| | |apply ubs_none|tstep].
    + apply ch_call. by left.
    + apply (skn_ch W _ chs); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 chs). split; [done|]. apply sle_refl, HW.
Qed.

Lemma sch_typed W F : world_wf W → typed W ∅ [] ∅ [] F sch (TBox 1 ch_C (TLolli None None TUnit sch_body)).
Proof.
  intros HW. unfold sch.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 ch_C sch_body. cbn. unfold sch_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  assert (∀ Ψ, (ch_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 0) chs) as Hlt.
  { intros Ψ Hg. apply (sl_trans _ _ _ (pv 0 1)); [apply (slt_po W _ (pv 0 0) HW)|].
    eapply (sl_hyp0 _ _ _ _ (pv 0 1) chs); [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  cbn. tstep.
  { tstep; [tstep| |done|apply ubs_none]. apply (KTNew _ _ _ Sch chs).
    right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess Sch chs) (TSess (SSnd 1 (TSess Sch (pvar 0)) SEnd) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess Sch (pvar 0)) SEnd (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. apply Hlt. by left.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply Hlt; by left|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 1) (Pt (NSlot (NVar 0) 0 0) 0)|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 chs)) (Some chs) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 1 ch_C None sch_body [chs]);
      [done|done| | |apply ubs_none|tstep].
    + apply ch_call. by left.
    + apply (skn_ch W _ chs); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 chs). split; [done|]. apply sle_refl, HW.
Qed.

Lemma ch_typed W : world_wf W → pt_known W (pc 0 0) →
  (∀ n, w_lt W (Pt (chc n) 1) (Pt (chc (S n)) 0)) →
  typed W ∅ [] ∅ [] (∅, None) ch_main TUnit.
Proof.
  intros HW Ha H. unfold ch_main.
  assert (bcs_hold (seqs W []) (slt W []) ch_C [pc 0 0]) as HC.
  { apply bcs_hold_intro. intros g (n & ->) _. apply sl_w. cbn [fact_map fact_holds].
    unfold pt_inst. cbn [pt_name pt_off]. rewrite !chc_inst. apply H. }
  assert (Forall (skn W []) [pc 0 0]) as HK by (constructor; [by left|constructor]).
  tstep.
  { tstep; [apply sch_typed, HW|apply rch_typed, HW]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sch (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 1 ch_C None sch_body [pc 0 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 1 ch_C None rch_body [pc 0 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition ch_L (x y : point) : Prop := ∃ n, x = Pt (chc n) 1 ∧ y = Pt (chc (S n)) 0.

Definition Wch : world := wgen (list_to_set (NConst <$> [0])) (λ _ _, False) ch_L.

Lemma chc_root n : pn_root (chc n) = NConst 0.
Proof. induction n; simpl; auto. Qed.

Lemma Wch_strict : strict Wch.
Proof.
  apply (wgen_strict _ _ _ id (prank (λ _, 1) (λ _, 0) (λ r _ _, r + 2))); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (n & -> & ->); right; unfold pt_root; cbn [pt_name]; rewrite !chc_root;
      rewrite !elem_of_list_to_set; cbn; set_solver.
  - intros x. apply prank_shift. lia.
  - assert (∀ n, pn_rank (λ _, 0) (λ r _ _, r + 2) (chc n) = 2 * n) as Hr
      by (induction n as [|n IH]; cbn; lia).
    intros x y (n & -> & ->). unfold id, prank. cbn [pt_name pt_off]. rewrite !Hr. lia.
Qed.

Lemma ch_deadlock_free : deadlock_free (∅, {[+ ch_main +]}).
Proof.
  apply (soundness Wch _ TUnit Wch_strict).
  apply ptyped_closed; [constructor|]. apply ch_typed; [apply Wch_strict| |].
  - unfold pt_known, Wch. simpl. set_solver.
  - intros n. apply glt_base. by exists n.
Qed.
