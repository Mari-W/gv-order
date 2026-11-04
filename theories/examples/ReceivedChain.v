(** * received chain: typable, recursion on a received channel (SHARP-EDGES 65)

      Sch = μX. ?(∃κ. X@κ).Close
      C = {ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹ ∣ n ∈ ℕ}      ι[0]ⁿ = ι[0]…[0] (n times, positions from 0)
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
    in the tail-call example.

    In the empty world main creates c with the box constraint itself as
    its creation constraint and forces both boxes at its point. Every
    fact stays inside ι, ordered by the rank 2·depth + offset (sharp
    edges 105). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Fixpoint chv (n : nat) : pname := match n with 0 => NVar 0 | S m => NSlot (chv m) 0 0 end.

Definition Sch : sty := SMu (SRcv 1 (TSess (SVar 0) (pvar 0)) SEnd).

Definition ch_P (g : fact) : Prop := ∃ n, g = FLt (Pt (chv n) 1) (Pt (chv (S n)) 0).
Definition ch_C : bcs := BCs [] ch_P.

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

Abbreviation chs := (Pt (NSlot (NVar 0) 0 0) 0).

Lemma chv_inst n : pn_inst (plist [chs]) (chv n) = Pt (chv (S n)) 0.
Proof. induction n as [|n IH]; [done|]. cbn [chv pn_inst]. by rewrite IH. Qed.

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

Lemma sch_typed W F : strict W → typed W ∅ [] ∅ [] F sch (TBox 1 ch_C (TLolli None None TUnit sch_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold sch.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 ch_C sch_body. cbn. unfold sch_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  assert (∀ Ψ, (ch_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 0) chs) as Hlt.
  { intros Ψ Hg. apply (sl_trans _ _ _ (pv 0 1)); [apply (slt_po W _ (pv 0 0) HW)|].
    eapply (sl_hyp0 _ _ _ _ (pv 0 1) chs); [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ Sch chs HWs).
  { right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
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

(** main creates c with the box constraint itself as its creation
    constraint. Every fact stays inside ι, ordered by the rank
    2·depth + offset (sharp edges 105). *)
Fixpoint chv_depth (p : pname) : option nat :=
  match p with
  | NVar 0 => Some 0
  | NSlot q 0 0 => match chv_depth q with Some n => Some (S n) | None => None end
  | _ => None
  end.

Definition ch_rank (x : point) : nat :=
  match chv_depth (pt_name x) with Some n => 2 * n + pt_off x | None => pt_off x end.

Lemma chv_depth_chv n : chv_depth (chv n) = Some n.
Proof. induction n as [|n IH]; [done|]. simpl. by rewrite IH. Qed.

Lemma ch_ok peq plt : cc_ok peq plt ch_C.
Proof.
  apply (cc_ok_inner peq plt ch_P (λ x y, ch_rank x < ch_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n o] _. unfold ch_rank, pt_shift. simpl. case_match; lia.
  - intros g [n ->] _. eexists _, _. split; [done|]. unfold ch_rank. cbn [pt_name pt_off].
    change (chv (S n)) with (NSlot (chv n) 0 0). cbn [chv_depth]. rewrite chv_depth_chv. lia.
Qed.

Lemma ch_typed : styped ∅ [] [] (∅, None) ch_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold ch_main.
  tstep.
  { tstep; [apply sch_typed, HWs|apply rch_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ Sch ch_C); [apply ch_ok|constructor|].
  fresh_clean.
  set (Ψ := [(ch_C, [pvar 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) ch_C [pvar 0]) as HC.
  { apply bcs_hold_self; [by left|vb_list|]. intros g Hg Hs.
    change (plist [pvar 0]) with (plist (ids 1)).
    destruct g as [x y|x y]; destruct Hs as [Hx Hy]; simpl; by rewrite !pt_inst_ids. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 1 ch_C None sch_body [pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 1 ch_C None rch_body [pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma ch_deadlock_free : deadlock_free (∅, {[+ ch_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply ch_typed].
Qed.
