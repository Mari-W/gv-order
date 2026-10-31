(** * Branch-dependent order (Mordido and Pérez 2026, mordido-perez.md §9.5, K10)

      c : ⊕{A: !∗;Close, B: !∗;Close}      d : Close
      T1 = select A c; send ∗ c; close c
      T2 = branch c { A ⇒ close d; recv c; close c
                    | B ⇒ recv c; close d; close c }
      T3 = close d

    The two branches of T2 order c and d in opposite ways. Branch A
    closes d while it holds c, and branch B receives on c while it
    holds d. With branch roots (K10) branch A runs at ι◁A and branch B
    at ι◁B, so the two orders live on different points. The program
    types and is deadlock free in the world

      ι ≺ ι◁B ≺ (d,0) ≺ ι◁A        (d,0) ≺ ι◁B+1

    with ι = (a,0), A = select₁ = [false] and B = select₂ = [true].

    Under K5 the program is not typable. K5 put both continuations of
    a choice at ι+1. Branch A blocks on (d,0) while it holds c at ι+1,
    so it needs (d,0) ≺ ι+1. Branch B blocks on c at ι+1 while it holds
    d, so it needs ι+1 ≺ (d,0). E-Case types both branches in one world,
    and the cycle ι+1 ≺ (d,0) ≺ ι+1 makes that world non-strict.

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
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam bo_t1)) (LetU (App ESpawn (Lam bo_t3)) bo_t2))).

(** The points: ι◁A, ι◁A+1, ι◁B, ι◁B+1 and (d,0). *)
Abbreviation bA k := (Pt (NBr (NConst 0) 0 false) k).
Abbreviation bB k := (Pt (NBr (NConst 0) 0 true) k).

Section bo.
  Context (W : world) (HW : world_wf W).
  Context (Ha : pt_known W (pc 0 0)) (Hd : pt_known W (pc 1 0)).
  Context (HBd : w_lt W (bB 0) (pc 1 0)) (HdB : w_lt W (pc 1 0) (bB 1)) (HdA : w_lt W (pc 1 0) (bA 0)).

  Lemma bo_typed : typed W ∅ [] ∅ [] (∅, None) bo_main TUnit.
  Proof.
    unfold bo_main.
    tstep.
    { tstep; [tstep|apply (KTNew _ _ _ bo_S (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ SEnd (pc 1 0) (or_introl Hd))|done|apply ubs_none]. }
    cbn. tstep.
    { (* T1 *)
      tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (bA 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      unfold bo_t1, sendclose. cbn. tstep; [tstep|]. cbn.
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bA 1)) (TSess SEnd (bA 1))); [|apply KTClos|done|].
      2:{ apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (bA 1). split; [done|]. apply sle_refl, HW. }
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (bA 0)) (TProd TUnit (TSess Sd (bA 0)))).
      - tstep; [|tstep].
        eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 0)) (TSess bo_S (pc 0 0)));
          [tstep|apply KTSel1|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (bA 1). split; [done|]. right.
        eapply sl_trans; [apply (slt_br W _ (pc 0 0) false HW)|apply (slt_po W _ (bA 0) HW)].
      - apply (KTSend _ _ _ 0 TUnit SEnd (bA 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (bA 1). split; [done|]. right. apply (slt_po W _ (bA 0) HW). }
    cbn. tstep.
    { (* T3 *)
      tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 1 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      unfold bo_t3. cbn. tstep; [tstep|]. cbn.
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 1 0)) (TSess SEnd (pc 1 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
    (* T2 *)
    unfold bo_t2. cbn. cstep.
    - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pc 0 0)) (TSess (dual bo_S) (pc 0 0)));
        [tstep|apply KTBra|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
      eapply sl_trans; [apply (slt_br W _ (pc 0 0) true HW)|apply sl_w, HBd].
    - (* A: close d at (d,0) holding c at ι◁A, then recv and close c *)
      cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 1 0)) (TSess SEnd (pc 1 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|done]. apply sl_w, HdA. }
      unfold recvclose. cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (bA 0)) (TSess (SSeq (SRcv 0 TUnit) SEnd) (bA 0)));
          [tstep|apply KTRecv|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
      cbn. tstep; [tstep|]. cbn.
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bA 1)) (TSess SEnd (bA 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
    - (* B: recv on c at ι◁B holding d, then close d holding c at ι◁B+1 *)
      cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (bB 0)) (TSess (SSeq (SRcv 0 TUnit) SEnd) (bB 0)));
          [tstep|apply KTRecv|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|done]. apply sl_w, HBd. }
      cbn. tstep; [tstep|]. cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 1 0)) (TSess SEnd (pc 1 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|done]. apply sl_w, HdB. }
      cbn.
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (bB 1)) (TSess SEnd (bB 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  Qed.
End bo.

(** The world: ι◁B ≺ (d,0) ≺ ι◁A and (d,0) ≺ ι◁B+1 on a = 0 and d = 1.
    The rank of a point is ten times its size plus 12 on d and 5 on
    the name of ι◁A, so ι = 0, ι◁B = 10, (d,0) = 12, ι◁A = 15 and
    ι◁B+1 = 20. *)
Definition bo_L (x y : point) : Prop :=
  (x = bB 0 ∧ y = pc 1 0) ∨ (x = pc 1 0 ∧ y = bB 1) ∨ (x = pc 1 0 ∧ y = bA 0).

Definition Wbo : world := wgen (list_to_set (NConst <$> [0; 1])) (λ _ _, False) bo_L.

Definition bo_bonus (x : point) : nat :=
  if decide (pt_root x = NConst 1) then 12
  else if decide (pt_name x = NBr (NConst 0) 0 false) then 5 else 0.

Definition bo_rank (x : point) : nat := 10 * pt_size x + bo_bonus x.

Lemma Wbo_strict : strict Wbo.
Proof.
  apply (wgen_strict_br lt _ _ _ id bo_rank); try done.
  - intros a. lia.
  - intros a b c. lia.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y [[-> ->]|[[-> ->]|[-> ->]]]; right; rewrite !elem_of_list_to_set; cbn; set_solver.
  - intros x y i. unfold id. by intros ->.
  - intros x y i. unfold id. by intros ->.
  - intros x. unfold bo_rank, bo_bonus, pt_size, pt_shift, pt_root. simpl. lia.
  - intros x i. unfold id, bo_rank, bo_bonus. rewrite pt_root_br.
    unfold pt_size, pt_br. simpl.
    destruct (decide (pt_root x = NConst 1)); [lia|].
    repeat case_decide; lia.
  - intros x y [[-> ->]|[[-> ->]|[-> ->]]]; vm_compute; lia.
Qed.

Lemma bo_deadlock_free : deadlock_free (∅, {[+ bo_main +]}).
Proof.
  apply (soundness Wbo _ TUnit Wbo_strict).
  apply ptyped_closed; [constructor|]. apply bo_typed; [apply Wbo_strict| | | | |].
  - unfold pt_known, Wbo. simpl. set_solver.
  - unfold pt_known, Wbo. simpl. set_solver.
  - apply glt_base. by left.
  - apply glt_base. by right; left.
  - apply glt_base. by right; right.
Qed.
