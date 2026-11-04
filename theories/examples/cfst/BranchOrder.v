(** * Branch-dependent order (Mordido and Pérez 2026, mordido-perez.md §9.5, K11)

      c : ⊕{A: !∗;Close, B: !∗;Close}      d : Close
      T1 = select A c; send ∗ c; close c
      T2 = branch c { A ⇒ close d; recv c; close c
                    | B ⇒ recv c; close d; close c }
      T3 = close d

    The two branches of T2 order c and d in opposite ways. Branch A
    closes d while it holds c, and branch B receives on c while it
    holds d. Under K11 a choice at ι continues at ι[A] or ι[B], so the
    two orders live on different points. A = select₁ is the index 0
    and B = select₂ the index 1. The program types in the empty world
    with two creation constraints. c is created first with

      ι ≺ ι[A]      ι ≺ ι[B]      ι[B] ≺ ι[A]

    and d is created at δ with

      ι[B] ≺ δ ≺ ι[B]+1      δ ≺ ι[A].

    The first two facts of c are the ones select and branch owe. The
    third is there for conservativity. The constraint of d derives
    ι[B] ≺ ι[A] between outer points, so the context must state it
    before d exists ([bod_ok]). With it T2 types, and K11 keeps the
    example typable.

    Under K5 the program is not typable. K5 put both continuations of
    a choice at ι+1. Branch A blocks on δ while it holds c at ι+1, so
    it needs δ ≺ ι+1. Branch B blocks on c at ι+1 while it holds d, so
    it needs ι+1 ≺ δ. E-Case types both branches under one context,
    and the cycle ι+1 ≺ δ ≺ ι+1 has no model.

    T1 runs as a spawned thread on c, T3 as a spawned thread on the
    second end of d, and T2 is the main thread. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstTools.

Set Default Proof Using "All".

(** ⊕{A: !∗;Close, B: !∗;Close} *)
Definition bo_S : sty := SPlus Sd Sd.

(** T1 on c = Var 4 inside its thunk. *)
Definition bo_t1 : expr := LetU (Var 0) (sendclose (App ESel1 (Var 4))).

(** T3 on the second end of d, Var 1 inside its thunk. *)
Definition bo_t3 : expr := LetU (Var 0) (App EClos (Var 1)).

(** T2 on the second end of c (Var 2) and on d (Var 1). *)
Definition bo_t2 : expr :=
  Case (App EBra (Var 2))
    (LetU (App EClos (Var 2)) (recvclose (Var 0)))
    (LetP (App ERecv (Var 0)) (LetU (Var 1) (LetU (App EClos (Var 4)) (App EClos (Var 0))))).

Definition bo_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam bo_t1)) (LetU (App ESpawn (Lam bo_t3)) bo_t2))).

(** The creation constraint of c, over ι = 0, is ι ≺ ι[A], ι ≺ ι[B] and
    ι[B] ≺ ι[A]. The rank of a point is ten times its size plus 5 on the
    name of ι[A], so ι = 0, ι[B] = 10 and ι[A] = 15. *)
Abbreviation sA k := (Pt (NPayload (NVar 0) 0 0) k).
Abbreviation sB k := (Pt (NPayload (NVar 0) 0 1) k).

Definition boc_P (g : fact) : Prop :=
  g = FLt (pv 0 0) (sA 0) ∨ g = FLt (pv 0 0) (sB 0) ∨ g = FLt (sB 0) (sA 0).
Definition boc_C : bcs := BCs [] boc_P.

Definition boc_rank (x : point) : nat :=
  10 * pt_size x + if decide (pt_name x = NPayload (NVar 0) 0 0) then 5 else 0.

Lemma boc_ok peq plt : cc_ok peq plt boc_C.
Proof.
  apply (cc_ok_inner peq plt boc_P (λ x y, boc_rank x < boc_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n o] _. unfold boc_rank, pt_size, pt_shift. simpl. case_decide; lia.
  - intros g [-> | [-> | ->]] _; eexists _, _; (split; [done|]); vm_compute; lia.
Qed.

(** The creation constraint of d, over δ = 0 with c = 1 outside, is
    c[B] ≺ δ ≺ c[B]+1 and δ ≺ c[A]. It derives c[B] ≺ c[A] between the
    outer points, which the constraint of c states. *)
Definition bod_P (g : fact) : Prop :=
  g = FLt (Pt (NPayload (NVar 1) 0 1) 0) (pv 0 0) ∨ g = FLt (pv 0 0) (Pt (NPayload (NVar 1) 0 1) 1) ∨
  g = FLt (pv 0 0) (Pt (NPayload (NVar 1) 0 0) 0).
Definition bod_C : bcs := BCs [pvar 0] bod_P.

Lemma bod_ok W : cc_ok (seqs W [(boc_C, [pvar 0])]) (slt W [(boc_C, [pvar 0])]) bod_C.
Proof.
  apply (cc_ok_out _ _ bod_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po| | |].
  - intros a b (f & Hf & _ & E). destruct Hf as [-> | [-> | ->]]; discriminate E.
  - intros a b (f & Hf & _ & E). destruct Hf as [-> | [-> | ->]]; injection E as -> ->; cbn; auto.
  - intros u p q v (f & Hf & _ & E) (f' & Hf' & _ & E') Hu Hp Hq Hv _.
    destruct Hf as [-> | [-> | ->]]; injection E as -> ->; cbn in Hu; try done.
    destruct Hf' as [-> | [-> | ->]]; injection E' as -> ->; cbn in Hv; try done.
    + apply (glt_ofs _ _ _ 0 1). lia.
    + apply (glt_up _ _ (Pt (NPayload (NVar 0) 0 1) 0) (Pt (NPayload (NVar 0) 0 0) 0)).
      eapply (sl_hyp0 _ _ _ _ (sB 0) (sA 0)); [by left|by right; right|cbn; lia|reflexivity|reflexivity].
Qed.

(** After both [new]s d is 0 and c is 1. The points of c after the
    choice are c[A]+k and c[B]+k. *)
Abbreviation bA k := (Pt (NPayload (NVar 1) 0 0) k).
Abbreviation bB k := (Pt (NPayload (NVar 1) 0 1) k).

Lemma bo_typed : styped ∅ [] [] (∅, None) bo_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold bo_main.
  apply (t_new_open W _ _ ∅ _ _ _ _ bo_S boc_C); [apply boc_ok|constructor|].
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ SEnd bod_C); [apply bod_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(bcs_inst (pshift 1) boc_C, [pvar 1]); (bcs_inst (pshift 1) bod_C, [pvar 0])]).
  assert (slt W Ψ (pv 1 0) (bA 0) ∧ slt W Ψ (pv 1 0) (bB 0)) as [HcA HcB].
  { split; eapply (sl_hyp0 _ _ _ _ (pv 0 0) _); [by left|by left|cbn; lia|reflexivity|reflexivity
                                                |by left|by right; left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (bB 0) (pv 0 0) ∧ slt W Ψ (pv 0 0) (bB 1) ∧ slt W Ψ (pv 0 0) (bA 0))
    as (HBd & HdB & HdA).
  { split_and!; eapply (sl_hyp W _ [pvar 1] bod_P [pvar 0]);
      [by right; left|by left|fsc|reflexivity|by right; left|by right; left|fsc|reflexivity
      |by right; left|by right; right|fsc|reflexivity]. }
  cbn. tstep.
  { (* T1 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (bA 1)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold bo_t1, sendclose. cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bA 1)) (TSess SEnd (bA 1))); [|apply KTClos|done|].
    2:{ apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (bA 1). split; [done|]. apply sle_refl, HW. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (bA 0)) (TProd TUnit (TSess Sd (bA 0)))).
    - tstep; [|tstep].
      eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pv 1 0)) (TSess bo_S (pv 1 0)));
        [tstep|apply KTSel1, HcA|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (bA 1). split; [done|]. right.
      eapply sl_trans; [exact HcA|apply (slt_po W _ (bA 0) HW)].
    - apply (KTSend _ _ _ 0 TUnit SEnd (bA 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (bA 1). split; [done|]. right. apply (slt_po W _ (bA 0) HW). }
  cbn. tstep.
  { (* T3 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold bo_t3. cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 0 0). split; [done|]. apply sle_refl, HW. }
  (* T2 *)
  unfold bo_t2. cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 1 0)) (TSess (dual bo_S) (pv 1 0)));
      [tstep|apply KTBra; [exact HcA|exact HcB]|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
    eapply sl_trans; [exact HcB|exact HBd].
  - (* A: close d at δ holding c at c[A], then recv and close c *)
    cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done]. exact HdA. }
    unfold recvclose. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (bA 0)) (TSess (SSeq (SRcv 0 TUnit) SEnd) (bA 0)));
        [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bA 1)) (TSess SEnd (bA 1))); [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - (* B: recv on c at c[B] holding d, then close d holding c at c[B]+1 *)
    cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (bB 0)) (TSess (SSeq (SRcv 0 TUnit) SEnd) (bB 0)));
        [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done]. exact HBd. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done]. exact HdB. }
    cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bB 1)) (TSess SEnd (bB 1))); [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem bo_deadlock_free : deadlock_free (∅, {[+ bo_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply bo_typed].
Qed.
