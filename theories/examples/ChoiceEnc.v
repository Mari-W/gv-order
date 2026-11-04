(** * Choice as a derived form: sums plus delegation

    PGV encodes S₁ ⊕ S₂ as !(S₁ + S₂).end (Kokke and Dardha,
    Prioritise the Best Variation, p. 6). Here the payload of the
    carrier binds two points, and each arm of the sum lies at its own
    point:

      Sch S₁ S₂ = !(∃ι₀ ι₁. (dual S₁)@ι₀ ⊕ (dual S₂)@ι₁).Close
      Sbr T₁ T₂ = ?(∃ι₀ ι₁. T₁@ι₀ ⊕ T₂@ι₁).Close = dual (Sch (dual T₁) (dual T₂))

    At a carrier point x the arm i lies at x[i]. The derived
    forms use only new, send, recv, close, the sum and its case:

      sel₁ = λc. let (k, k′) = new ∗ at x[0] in let () = close (send ⟨inj₁ k′, c⟩) in k
      sel₂ = λc. let (k, k′) = new ∗ at x[1] in let () = close (send ⟨inj₂ k′, c⟩) in k
      branch c e₁ e₂ = let (p, c) = recv c in let () = close c in case p e₁ e₂

    [sel1_typed], [sel2_typed] and [branch_typed] are their typing
    rules, derived from the rules of [typed]. No rule, constant or
    definition of the core changes.

    The test program is T2 of the cfst branch, which needs a different
    order per branch:

      c : ⊕{A: !∗.Close, B: !∗.Close}      d : Close
      T1 = let k = sel₁ c in close (send ⟨∗, k⟩)
      T2 = branch c′ { k ⇒ close d; recv k; close k | k ⇒ recv k; close d; close k }
      T3 = close d′

    Branch A closes d while it holds k at a[0] and asks δ ≺ a[0].
    Branch B receives on k at a[1] while it holds d and asks a[1] ≺ δ.
    The two facts name two points, so they do not meet. [choice_typed]
    types the program under the top-level constraint
    {a+1 ≺ a[1], a[1] ≺ δ, δ ≺ a[0], δ ≺ a[1]+1}, and [choice_deadlock_free]
    follows from [soundness_source]. With both arms at a[0] the two facts
    are δ ≺ a[0] and a[0] ≺ δ, a cycle ([same_slot_cycle]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** The encoding *)

Definition Sch (S1 S2 : sty) : sty :=
  SSeq (SSnd 2 (TSum (TSess (dual S1) (pvar 0)) (TSess (dual S2) (pvar 1)))) SEnd.
Definition Sbr (T1 T2 : sty) : sty :=
  SSeq (SRcv 2 (TSum (TSess T1 (pvar 0)) (TSess T2 (pvar 1)))) SEnd.

Lemma dual_Sch S1 S2 : dual (Sch S1 S2) = Sbr (dual S1) (dual S2).
Proof. done. Qed.

Definition sel1 : expr :=
  Lam (let_new (LetU (App EClos (App ESend (Pair (Inj1 (Var 0)) (Var 4)))) (Var 1))).
Definition sel2 : expr :=
  Lam (let_new (LetU (App EClos (App ESend (Pair (Inj2 (Var 0)) (Var 4)))) (Var 1))).

(** The branches see the received continuation at 0 and the outer
    variables from 3. The spent pair and carrier sit at 1 and 2. *)
Definition branch (e e1 e2 : expr) : expr :=
  LetP (App ERecv e) (LetU (App EClos (Var 0)) (Case (Var 1) e1 e2)).

Abbreviation sl0 x := (pt_slot x 0).
Abbreviation sl1 x := (pt_slot x 1).

(** ** Environments of unlimited bindings *)

Lemma allunl_heads Δ : allunl Δ = true → lenv_heads Δ = ∅.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |done].
  intros H. apply andb_true_iff in H as [H1 H2]. destruct T; try done. simpl. rewrite IH; [set_solver|done].
Qed.

Lemma allunl_bot Δ : allunl Δ = true → lenv_bot Δ = false.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |done].
  intros H. apply andb_true_iff in H as [H1 H2]. destruct T; try done. simpl. by apply IH.
Qed.

Lemma allunl_lp e x Δ : allunl Δ = true → lp e x Δ = Δ.
Proof.
  revert x. induction Δ as [|[T|] Δ IH]; intros x; simpl; [done| |].
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite H1. simpl. by rewrite IH.
  - intros H. by rewrite IH.
Qed.

Lemma allunl_sok e1 x1 e2 x2 Δ : allunl Δ = true → sok e1 x1 e2 x2 Δ = true.
Proof.
  revert x1 x2. induction Δ as [|[T|] Δ IH]; intros x1 x2; simpl; [done| |].
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite H1. simpl. by apply IH.
  - intros H. by apply IH.
Qed.

Lemma allunl_nones Δ : allunl (lenv_nones Δ) = true.
Proof. induction Δ; simpl; done. Qed.

Lemma lenv_heads_nones Δ : lenv_heads (lenv_nones Δ) = ∅.
Proof. induction Δ; simpl; done. Qed.

Lemma lenv_bot_nones Δ : lenv_bot (lenv_nones Δ) = false.
Proof. induction Δ; simpl; done. Qed.

(** Knownness of x[i] is that of x: they share a root. *)
Lemma skn_slot W Ψ x i : skn W Ψ x → skn W Ψ (pt_slot x i).
Proof. intros [H|(C & xs & y & Hg & Hy & E)]; [by left|right; by exists C, xs, y]. Qed.

(** ** Selection is a derived form

    sel_i takes the carrier at x and returns the continuation at x[i].
    It blocks at x (send) and at x+1 (close), so its upper point is
    x+1. send asks {x} ≺ {x[0], x[1]}, and close c asks x+1 ≺ x[i],
    because sel_i holds k at x[i]. *)

Section sel.
  Context (W : world) (HWs : strict W).

  Local Ltac unl Hu :=
    cbn; repeat first [rewrite (allunl_lp _ _ _ Hu)|rewrite (allunl_sok _ _ _ _ _ Hu)
      |rewrite (allunl_heads _ Hu)|rewrite (allunl_bot _ Hu)|rewrite Hu]; cbn.

  Local Ltac ubp Hu :=
    apply ubs_intro;
    [intros y Hy; cbn in Hy; rewrite ?(allunl_lp _ _ _ Hu), ?(allunl_heads _ Hu) in Hy; mem_cases Hy; done|];
    cbn; eexists; rewrite lookup_insert_eq; split; [done|];
    first [apply sle_refl; assumption|right; apply slt_po; assumption].

  Lemma sel_typed (i : nat) (inj : expr → expr) Φ Ψ Δ F S1 S2 S x :
    (i = 0 ∧ inj = Inj1 ∧ S = S1) ∨ (i = 1 ∧ inj = Inj2 ∧ S = S2) →
    skn W Ψ x → allunl Δ = true →
    slt W Ψ x (sl0 x) → slt W Ψ x (sl1 x) → slt W Ψ (pt_shift 1 x) (pt_slot x i) →
    typed W Φ Ψ ∅ Δ F
      (Lam (let_new (LetU (App EClos (App ESend (Pair (inj (Var 0)) (Var 4)))) (Var 1))))
      (TLolli (Some (pt_shift 1 x)) None (TSess (Sch S1 S2) x) (TSess S (pt_slot x i))).
  Proof.
    intros Hi Hx Hu H0 H1 Hc. pose proof (proj1 HWs) as HW.
    set (φ := fresh (dom Φ)).
    apply (tv_lam W HW _ _ _ _ _ _ _ _ _ φ); [apply is_fresh|unl Hu; done|].
    apply (t_new_at W _ _ _ _ _ _ _ S (pt_slot x i) HWs); [by apply skn_slot|].
    assert (slt W Ψ x (pt_slot x i)) as Hxi by (destruct Hi as [(-> & _)|(-> & _)]; done).
    destruct Hi as [(-> & -> & ->)|(-> & -> & ->)].
    all: apply tv_letu; [exact HW|unl Hu; reflexivity| |];
      [|apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]].
    all: unl Hu; tstep; [unl Hu|apply (KTClos _ _ _ (pt_shift 1 x))|done|ubp Hu].
    all: tstep; [unl Hu|apply (KTSend _ _ _ 2 (TSum (TSess (dual S1) (pvar 0)) (TSess (dual S2) (pvar 1))) SEnd x)
                 |kscope|ubp Hu].
    all: try (intros h Hh; mem_cases Hh; done).
    all: eapply tv_pair; [exact HW|unl Hu; reflexivity| |];
      [apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]|].
    all: unl Hu; first [apply t_inj1|apply t_inj2];
      apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity].
  Qed.

  Lemma sel1_typed Φ Ψ Δ F S1 S2 x :
    skn W Ψ x → allunl Δ = true →
    slt W Ψ x (sl0 x) → slt W Ψ x (sl1 x) → slt W Ψ (pt_shift 1 x) (sl0 x) →
    typed W Φ Ψ ∅ Δ F sel1
      (TLolli (Some (pt_shift 1 x)) None (TSess (Sch S1 S2) x) (TSess S1 (sl0 x))).
  Proof. intros. unfold sel1. apply (sel_typed 0 Inj1); auto. Qed.

  Lemma sel2_typed Φ Ψ Δ F S1 S2 x :
    skn W Ψ x → allunl Δ = true →
    slt W Ψ x (sl0 x) → slt W Ψ x (sl1 x) → slt W Ψ (pt_shift 1 x) (sl1 x) →
    typed W Φ Ψ ∅ Δ F sel2
      (TLolli (Some (pt_shift 1 x)) None (TSess (Sch S1 S2) x) (TSess S2 (sl1 x))).
  Proof. intros. unfold sel2. apply (sel_typed 1 Inj2); auto. Qed.
End sel.

(** ** Branching is a derived form

    branch receives the sum at x while the context holds Δ₂, closes the
    carrier at x+1 while it holds the sum and Δ₂, and continues in the
    arm i with the continuation at x[i]. The sum has the heads x[0] and
    x[1], so the close asks x+1 ≺ x[0] and x+1 ≺ x[1] whatever the arm. *)

Lemma branch_typed W Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T x :
  world_wf W → lenv_split Δ Δ1 Δ2 →
  typed W Φ Ψ ∅ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSess (Sbr T1 T2) x) →
  ub_below_s W Ψ Φ (Some x) (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) →
  ub_below_s W Ψ Φ (Some (pt_shift 1 x))
    (sf_unionb F ({[sl0 x]} ∪ {[sl1 x]} ∪ lenv_heads Δ2) (lenv_bot Δ2)) →
  typed W Φ Ψ ∅ (Some (TSess T1 (sl0 x)) :: None :: None :: Δ2) F e1 T →
  typed W Φ Ψ ∅ (Some (TSess T2 (sl1 x)) :: None :: None :: Δ2) F e2 T →
  typed W Φ Ψ ∅ Δ F (branch e e1 e2) T.
Proof.
  intros HW Hs He Hr Hc H1 H2. unfold branch.
  set (P := TSum (TSess T1 (sl0 x)) (TSess T2 (sl1 x))).
  apply (t_letp W Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ P (TSess SEnd (pt_shift 1 x))); [apply (comp0 W HW)|exact Hs| |].
  { rewrite (tenv_heads0 W HW), (left_id_L ∅ (∪)).
    apply (tv_appk W HW _ _ _ _ _ _ (Some x) (TSess (Sbr T1 T2) x)); [exact He| |kscope|exact Hr].
    apply (KTRecv _ _ _ 2 (TSum (TSess T1 (pvar 0)) (TSess T2 (pvar 1))) SEnd x). }
  apply (t_letu W Φ Ψ ∅ ∅ ∅ _ (Some (TSess SEnd (pt_shift 1 x)) :: None :: lenv_nones Δ2)
           (None :: Some P :: Δ2)); [apply (comp0 W HW)| | |].
  { apply lsplit_l, lsplit_r, lenv_split_nones_l. }
  { rewrite (tenv_heads0 W HW), (left_id_L ∅ (∪)).
    apply (tv_appk W HW _ _ _ _ _ _ (Some (pt_shift 1 x)) (TSess SEnd (pt_shift 1 x))); [|apply KTClos|done|].
    - apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [by simplify_eq|done|].
      apply list_elem_of_lookup_2, lenv_empty_nones in Hy. discriminate.
    - exact Hc. }
  apply (t_case W Φ Ψ ∅ ∅ ∅ _ (None :: Some P :: lenv_nones Δ2) (None :: None :: Δ2) F _ _ _
           (TSess T1 (sl0 x)) (TSess T2 (sl1 x))); [apply (comp0 W HW)| | |exact H1|exact H2].
  { apply lsplit_none, lsplit_l, lenv_split_nones_l. }
  apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [done|by simplify_eq|].
  apply list_elem_of_lookup_2, lenv_empty_nones in Hy. discriminate.
Qed.

(** ** T1 ∥ T2 ∥ T3

      choice = let (c, c′) = new ∗ at a in let (d, d′) = new ∗ at δ in
               let () = spawn (λu. let () = u in close (send ⟨∗, sel₁ c⟩)) in
               let () = spawn (λu. let () = u in close d′) in
               branch c′ { k ⇒ let () = close d in recvclose k
                         | k ⇒ let (x, k) = recv k in let () = x in
                               let () = close d in close k }

    c : (Sch Sd Sd)@a and d : Close@δ, with a and δ the top-level
    variables 0 and 1. The facts each step asks:

      T1   send on c at a         a ≺ a[0], a ≺ a[1] (KTSend), a ≺ a[0] (holds k)
           close c at a+1         a+1 ≺ a[0] (holds k)
      T2   recv c′ at a           a ≺ δ (holds d)
           close c′ at a+1        a+1 ≺ δ, a+1 ≺ a[0], a+1 ≺ a[1] (holds d and the sum)
           branch A, close d      δ ≺ a[0] (holds k)
           branch B, recv k       a[1] ≺ δ (holds d)
           branch B, close d      δ ≺ a[1]+1 (holds k)

    The top-level constraint states four of them, and program order and
    transitivity give the rest. *)

Abbreviation pa k := (pv 0 k).
Abbreviation pd k := (pv 1 k).
Abbreviation pa0 k := (Pt (NSlot (NVar 0) 0 0) k).
Abbreviation pa1 k := (Pt (NSlot (NVar 0) 0 1) k).

Definition ch_fact (g : fact) : Prop :=
  g = FLt (pa 1) (pa1 0) ∨ g = FLt (pa1 0) (pd 0) ∨ g = FLt (pd 0) (pa0 0) ∨ g = FLt (pd 0) (pa1 1).
Definition Cch : bcs := BCs [] ch_fact.

Definition t1_thunk : expr := Lam (LetU (Var 0) (sendclose (App sel1 (Var 4)))).
Definition t3_thunk : expr := Lam (LetU (Var 0) (App EClos (Var 1))).
Definition t2_arm1 : expr := LetU (App EClos (Var 4)) (recvclose (Var 0)).
Definition t2_arm2 : expr :=
  LetP (App ERecv (Var 0)) (LetU (Var 1) (LetU (App EClos (Var 6)) (App EClos (Var 0)))).

Definition choice_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn t1_thunk)
      (LetU (App ESpawn t3_thunk)
        (branch (Var 2) t2_arm1 t2_arm2)))).

Lemma ch_rank_ok : c0_acyclic 2 Cch.
Proof.
  set (r := λ x : point, match pt_name x with
    | NVar 0 => 10 * pt_off x
    | NSlot (NVar 0) 0 1 => 15 + 10 * pt_off x
    | NVar 1 => 17 + 10 * pt_off x
    | NSlot (NVar 0) 0 0 => 20 + 10 * pt_off x
    | _ => 10 * pt_off x
    end).
  apply (c0_acyclic_rank 2 _ r).
  - intros [p o]. unfold r, pt_shift. simpl. repeat case_match; lia.
  - by intros ? ? [?|[?|[?|?]]].
  - intros x y [[= -> ->]|[[= -> ->]|[[= -> ->]|[= -> ->]]]]; unfold r; cbn; lia.
Qed.

Lemma choice_typed : styped ∅ [(Cch, ids 2)] [] (∅, None) choice_main TUnit.
Proof.
  apply styped_wnil. set (W := wnil). set (Ψ := [(Cch, ids 2)]).
  pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold choice_main.
  assert (∀ x y, ch_fact (FLt x y) → slt W Ψ x y) as Hf.
  { intros x y Hxy. apply (sl_hyp0 W Ψ ch_fact (ids 2) x y); [by left|done| | |].
    - destruct Hxy as [[= -> ->]|[[= -> ->]|[[= -> ->]|[= -> ->]]]]; cbn; lia.
    - apply pt_inst_ids. destruct Hxy as [[= -> ->]|[[= -> ->]|[[= -> ->]|[= -> ->]]]]; cbn; lia.
    - apply pt_inst_ids. destruct Hxy as [[= -> ->]|[[= -> ->]|[[= -> ->]|[= -> ->]]]]; cbn; lia. }
  assert (slt W Ψ (pa 1) (pa1 0)) as F1 by (apply Hf; by left).
  assert (slt W Ψ (pa1 0) (pd 0)) as F2 by (apply Hf; by right; left).
  assert (slt W Ψ (pd 0) (pa0 0)) as F3 by (apply Hf; by right; right; left).
  assert (slt W Ψ (pd 0) (pa1 1)) as F4 by (apply Hf; by right; right; right).
  assert (slt W Ψ (pa 0) (pa 1)) as P0 by apply (slt_po W _ (pa 0) HW).
  assert (slt W Ψ (pa0 0) (pa0 1)) as P1 by apply (slt_po W _ (pa0 0) HW).
  assert (slt W Ψ (pa 1) (pd 0)) as D1 by (eapply sl_trans; [exact F1|exact F2]).
  assert (slt W Ψ (pa 0) (pd 0)) as D2 by (eapply sl_trans; [exact P0|exact D1]).
  assert (slt W Ψ (pa 1) (pa0 0)) as D3 by (eapply sl_trans; [exact D1|exact F3]).
  assert (slt W Ψ (pa 0) (pa0 0)) as D4 by (eapply sl_trans; [exact P0|exact D3]).
  assert (slt W Ψ (pa 0) (pa1 0)) as D5 by (eapply sl_trans; [exact P0|exact F1]).
  assert (slt W Ψ (pa 1) (pa0 1)) as D6 by (eapply sl_trans; [exact D3|exact P1]).
  assert (skn W Ψ (pa 0)) as Ka by (right; exists Cch, (ids 2), (pvar 0); split_and!; [by left|by left|done]).
  assert (skn W Ψ (pd 0)) as Kd by (right; exists Cch, (ids 2), (pvar 1); split_and!; [by left|by right; left|done]).
  apply (t_new_at W _ _ _ _ _ _ _ (Sch Sd Sd) (pa 0) HWs Ka). cbn.
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (pd 0) HWs Kd). cbn.
  (* T1 *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pa0 1)) (Some (pa 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    - tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (pa0 0)); cbn; set_solver|done|].
      + eapply tv_pair; [exact HW|reflexivity| |tstep].
        eapply tv_app; [exact HW|reflexivity| |tstep|].
        * apply (sel1_typed W HWs _ _ _ _ Sd Sd (pa 0)); [exact Ka|reflexivity|exact D4|exact D5|exact D3].
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pa0 1). split; [done|]. right. exact D6.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pa0 1). split; [done|]. right. exact P1.
    - apply (KTClos _ _ _ (pa0 1)).
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pa0 1). split; [done|]. apply sle_refl, HW. }
  (* T3 *)
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pd 0)) (Some (pd 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    tstep; [tstep|apply (KTClos _ _ _ (pd 0))|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pd 0). split; [done|]. apply sle_refl, HW. }
  (* T2 *)
  cbn.
  eapply (branch_typed W _ _ _ [None; None; None; None; Some _; None; None; None]
                               [None; Some _; None; None; None; None; None; None]
                               _ _ _ _ (dual Sd) (dual Sd) _ (pa 0) HW).
  { repeat constructor. }
  { tstep. }
  { apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  { apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  - (* branch A: close d, then receive on k at a[0] *)
    cbn. unfold t2_arm1, recvclose. tstep.
    + tstep; [tstep|apply (KTClos _ _ _ (pd 0))|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + cbn. tstep.
      * tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
      * cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - (* branch B: receive on k at a[1], then close d *)
    cbn. unfold t2_arm2. tstep.
    + tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + cbn. tstep; [tstep|]. cbn. tstep.
      * tstep; [tstep|apply (KTClos _ _ _ (pd 0))|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
      * tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem choice_deadlock_free : deadlock_free (∅, {[+ choice_main +]}).
Proof. apply (soundness_source 2 Cch _ TUnit (c0_acyclic_creation _ _ ch_rank_ok)); [constructor|apply choice_typed]. Qed.

(** ** Negative control: both arms at one point

      Sch₀ = !(∃ι₀. (?∗.Close)@ι₀ ⊕ (?∗.Close)@ι₀).Close

    The program [choice_main] with c : Sch₀@a and the payload of one
    point. Both arms receive k at a[0]. Branch A closes d while it holds
    k and asks δ ≺ a[0] (E-Let* puts a[0] into the frame of close d,
    E-App asks the upper point δ below it). Branch B receives on k at
    a[0] while it holds d and asks a[0] ≺ δ. E-Case types both arms in
    the same context, and the type of k comes from the payload, so the
    two facts speak of the same two points. E-Conv keeps points (eqT
    compares them by equality) and E-Weak drops only unlimited
    bindings, so every derivation asks both facts. Every Γ that the
    derivation of a closed program meets has an acyclic ≺, by the
    argument of examples/Rejected.v, and δ ≺ a[0] ≺ δ is a cycle. The
    choice of the point plays no role: the lemma holds for every point
    the two arms share. *)

Definition Sch0 : sty :=
  SSeq (SSnd 1 (TSum (TSess (dual Sd) (pvar 0)) (TSess (dual Sd) (pvar 0)))) SEnd.

Lemma same_slot_cycle W Ψ (k δ : point) :
  (∀ p, ¬ slt W Ψ p p) → ¬ (slt W Ψ δ k ∧ slt W Ψ k δ).
Proof. intros Hacy [H1 H2]. apply (Hacy δ). by eapply sl_trans. Qed.

(** No top-level constraint that [soundness_source] accepts states the
    two facts of the shared point: a top-level C with δ ≺ a[0] and
    a[0] ≺ δ fails [c0_acyclic]. *)
Lemma same_slot_not_acyclic P :
  P (FLt (pd 0) (pa0 0)) → P (FLt (pa0 0) (pd 0)) → ¬ c0_acyclic 2 (BCs [] P).
Proof.
  intros H1 H2 [_ Hacy]. apply (Hacy (pd 0)).
  apply (glt_trans _ _ _ (pa0 0)); apply glt_base; unfold c0_lt;
    apply bcs_open_nil; split; [done| |done|]; cbn; lia.
Qed.

(** With separate points a[0] and a[1] the same two facts are δ ≺ a[0] and a[1] ≺ δ,
    and the top-level constraint [Cch] holds both without a cycle
    ([ch_rank_ok]). *)

(** ** Stage 2: a recursive choice

      R = μX. &{Next: !∗.X, Stop: Close} = μX. Sbr (!∗.X) Close
      srv : □(∀ι. C. ∗ ⊸ (R@ι ⊸^{ι[1]} ∗))
      srv = !(f = λc. branch c { k ⇒ spawn (λw. let () = w in (force f) (send ⟨∗, k⟩))
                               | k ⇒ close k })
      loop_main = let (f, u) = ⟨srv, ∗⟩ in let () = u in
                  let (c, c′) = new ∗ at a in
                  let () = spawn (λw. let () = w in (force f) c) in
                  let (x, c₂) = recv (sel₁ c′) in let () = x in
                  let (x, c₃) = recv (sel₁ c₂) in let () = x in
                  close (sel₂ c₃)

    Round n runs at the point p_n with p_0 = a and p_{n+1} = p_n[0] + 1:
    Next hands over k at p_n[0], the server sends ∗ on it, and the
    continuation lies at p_n[0] + 1. The client does two Next and one
    Stop.

    The body of srv receives at ι and closes the carrier at ι+1 while it
    holds the sum, which asks ι+1 ≺ ι[0] and ι+1 ≺ ι[1]. Stop closes k at
    ι[1], so the upper point of the body is ι[1]. Next sends at ι[0] in a
    thread that then forces f at ι[0]+1, whose upper point is
    (ι[0]+1)[1]. So the thread asks ι[0] ≺ (ι[0]+1)[1] and the call asks
    the constraint at ι[0]+1. The constraint C is the two facts at every
    round, an infinite constraint as in examples/ReceivedChain.v:

      C = {p_n + 1 ≺ p_n[0], p_n + 1 ≺ p_n[1] ∣ n ∈ ℕ}

    C[p_1/ι] is C without its first round ([lp_sub]). The program
    starts under C as its top-level constraint. *)

Definition Rs : sty := SMu (Sbr (SSeq (SSnd 0 TUnit) (SVar 0)) SEnd).

Fixpoint cvp (n : nat) : point :=
  match n with 0 => pvar 0 | S m => pt_shift 1 (pt_slot (cvp m) 0) end.

Definition lp_P (g : fact) : Prop :=
  ∃ n, g = FLt (pt_shift 1 (cvp n)) (sl0 (cvp n)) ∨ g = FLt (pt_shift 1 (cvp n)) (sl1 (cvp n)).
Definition lp_C : bcs := BCs [] lp_P.

Lemma pt_inst_slot σ x i : pt_inst σ (pt_slot x i) = pt_slot (pt_inst σ x) i.
Proof. destruct x as [p o]. done. Qed.

Lemma cvp_inst n : pt_inst (plist [cvp 1]) (cvp n) = cvp (S n).
Proof.
  induction n as [|n IH]; [done|].
  change (cvp (S n)) with (pt_shift 1 (pt_slot (cvp n) 0)).
  by rewrite pt_inst_shift, pt_inst_slot, IH.
Qed.

Lemma cvp_vb n : pn_vb 1 (pt_name (cvp n)).
Proof. induction n as [|n IH]; cbn; [lia|exact IH]. Qed.

Lemma lp_sub g : lp_P g → fact_scoped 1 g → lp_P (fact_map (pt_inst (plist [cvp 1])) g).
Proof.
  intros (n & [-> | ->]) _; exists (S n); cbn [fact_map];
    rewrite pt_inst_shift, pt_inst_slot, cvp_inst; [left|right]; done.
Qed.

Lemma lp_fact W Ψ n i : (lp_C, ids 1) ∈ Ψ → i < 2 → slt W Ψ (pt_shift 1 (cvp n)) (pt_slot (cvp n) i).
Proof.
  intros Hg Hi. pose proof (cvp_vb n) as Hv.
  apply (sl_hyp0 W Ψ lp_P (ids 1) (pt_shift 1 (cvp n)) (pt_slot (cvp n) i)); [done| | | |].
  - exists n. destruct i as [|[|]]; [by left|by right|lia].
  - split; cbn; done.
  - by apply pt_inst_ids.
  - by apply pt_inst_ids.
Qed.

Lemma lp_call W Ψ : (lp_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) lp_C [cvp 1].
Proof. intros Hg. apply bcs_hold_self; [done|constructor; [apply (cvp_vb 1)|constructor]|exact lp_sub]. Qed.

Lemma lp_self W Ψ : (lp_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) lp_C [pvar 0].
Proof.
  intros Hg. apply bcs_hold_self; [done|vb_list|]. intros g Hg' Hs.
  change (plist [pvar 0]) with (plist (ids 1)).
  destruct g as [x y|x y]; destruct Hs as [Hx Hy]; simpl; by rewrite !pt_inst_ids.
Qed.

Lemma skn_v0 W Ψ C x : (C, ids 1) ∈ Ψ → pt_root x = NVar 0 → skn W Ψ x.
Proof. intros Hg Hx. right. exists C, (ids 1), (pvar 0). split_and!; [done|by left|done]. Qed.

Lemma cvp_root n : pt_root (cvp n) = NVar 0.
Proof. induction n as [|n IH]; [done|]. exact IH. Qed.

(** Selection at round n asks p_n ≺ p_n[0], p_n ≺ p_n[1] and
    p_n + 1 ≺ p_n[i], all from C and program order. *)
Lemma lp_sel W Ψ n i : world_wf W → (lp_C, ids 1) ∈ Ψ → i < 2 → slt W Ψ (cvp n) (pt_slot (cvp n) i).
Proof. intros HW Hg Hi. eapply sl_trans; [apply (slt_po W _ _ HW)|by apply lp_fact]. Qed.

Definition srv_body : ty := TLolli (Some (sl1 (pv 0 0))) None (TSess Rs (pv 0 0)) TUnit.
Definition Tsrv : ty := TBox 1 0 lp_C (TLolli None None TUnit srv_body).

Definition next_arm : expr :=
  App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 5)) (App ESend (Pair EUnit (Var 1)))))).
Definition stop_arm : expr := App EClos (Var 0).

Definition srv : expr := EBox (Lam (branch (Var 0) next_arm stop_arm)).

Lemma srv_typed W Ψ F : world_wf W → typed W ∅ Ψ ∅ [] F srv Tsrv.
Proof.
  intros HW. unfold srv, Tsrv.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 lp_C srv_body. cbn.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ' := Q) end.
  assert ((lp_C, ids 1) ∈ Ψ') as Hg by (apply elem_of_app; right; by left).
  unfold srv_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn.
  eapply (branch_typed W _ _ _ [Some (TSess Rs (pv 0 0)); Some Tsrv] [None; Some Tsrv]
            _ _ _ _ (SSeq (SSnd 0 TUnit) Rs) SEnd _ (pv 0 0) HW).
  { apply lsplit_l, lsplit_unl; [done|constructor]. }
  { eapply t_conv; [|tstep]. conv_sess. }
  { apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sl1 (pv 0 0)). split; [done|]. right.
    eapply sl_trans; [apply (slt_po W _ (pv 0 0) HW)|apply (lp_fact W Ψ' 0 1 Hg); lia]. }
  { apply ubs_intro; [intros y Hy; mem_cases Hy; apply (lp_fact W Ψ' 0 _ Hg); lia|].
    exists (sl1 (pv 0 0)). split; [done|]. right. apply (lp_fact W Ψ' 0 1 Hg); lia. }
  - (* Next *)
    unfold next_arm. tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sl1 (cvp 1))) (Some (sl0 (pv 0 0))) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    + apply (typed_force0 W _ _ _ _ _ _ 1 lp_C None srv_body [cvp 1]);
        [done|done|by apply lp_call|constructor; [apply (skn_v0 W _ lp_C); [done|apply cvp_root]|constructor]
        |apply ubs_none|tstep].
    + tstep; [|apply (KTSend _ _ _ 0 TUnit Rs (sl0 (pv 0 0))); cbn; set_solver|done|].
      * tstep; tstep.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (sl1 (cvp 1)). split; [done|]. right.
        eapply sl_trans; [apply (slt_po W _ _ HW)|].
        eapply sl_trans; [apply (slt_po W _ (cvp 1) HW)|apply (lp_fact W Ψ' 1 1 Hg); lia].
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (sl1 (cvp 1)). split; [done|]. apply sle_refl, HW.
  - (* Stop *)
    unfold stop_arm. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sl1 (pv 0 0)). split; [done|]. apply sle_refl, HW.
Qed.

Definition client : expr :=
  LetP (App ERecv (App sel1 (Var 0)))
    (LetU (Var 1)
      (LetP (App ERecv (App sel1 (Var 0)))
        (LetU (Var 1) (App EClos (App sel2 (Var 0)))))).

Definition loop_main : expr :=
  LetP (Pair srv EUnit) (LetU (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 2)))))
      client))).

Definition lp_rank_n : pname → nat :=
  fix h p := match p with NSlot q b _ => h q + b + 2 | _ => 0 end.

Lemma lp_acyclic : c0_acyclic 1 lp_C.
Proof.
  apply (c0_acyclic_rank 1 _ (λ x, lp_rank_n (pt_name x) + pt_off x)).
  - intros [p o]. cbn. lia.
  - by intros ? ? [n [?|?]].
  - intros x y [n [[= -> ->]|[= -> ->]]]; cbn; lia.
Qed.

Lemma loop_typed : styped ∅ [(lp_C, ids 1)] [] (∅, None) loop_main TUnit.
Proof.
  apply styped_wnil. set (W := wnil). set (Ψ := [(lp_C, ids 1)]).
  pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold loop_main.
  assert ((lp_C, ids 1) ∈ Ψ) as Hg by by left.
  tstep.
  { tstep; [tstep|apply srv_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Rs (pv 0 0) HWs); [by apply (skn_v0 W _ lp_C)|]. cbn.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sl1 (pv 0 0))) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 lp_C None srv_body [pvar 0]);
        [done|done|by apply lp_self|constructor; [by apply (skn_v0 W _ lp_C)|constructor]|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (sl1 (pv 0 0)). split; [done|]. apply sle_refl, HW. }
  cbn. unfold client.
  assert (∀ n, skn W Ψ (cvp n)) as Hk by (intros n; apply (skn_v0 W _ lp_C); [done|apply cvp_root]).
  (* round 0: Next *)
  tstep.
  { tstep; [|apply KTRecv| |].
    - eapply tv_app; [exact HW|reflexivity| | |apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
      + apply (sel1_typed W HWs _ _ _ _ (SSeq (SRcv 0 TUnit) (dual Rs)) SEnd (cvp 0)); [apply Hk|reflexivity|
          apply (lp_sel W Ψ 0 0); [done|done|lia]|apply (lp_sel W Ψ 0 1); [done|done|lia]|apply (lp_fact W Ψ 0 0); [done|lia]].
      + eapply t_conv; [|tstep]. conv_sess.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn.
  (* round 1: Next *)
  tstep.
  { tstep; [|apply KTRecv| |].
    - eapply tv_app; [exact HW|reflexivity| | |apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
      + apply (sel1_typed W HWs _ _ _ _ (SSeq (SRcv 0 TUnit) (dual Rs)) SEnd (cvp 1)); [apply Hk|reflexivity|
          apply (lp_sel W Ψ 1 0); [done|done|lia]|apply (lp_sel W Ψ 1 1); [done|done|lia]|apply (lp_fact W Ψ 1 0); [done|lia]].
      + eapply t_conv; [|tstep]. conv_sess.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn.
  (* round 2: Stop *)
  tstep; [|apply KTClos|done|]; cycle 1.
  { apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  eapply tv_app; [exact HW|reflexivity| | |apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  - apply (sel2_typed W HWs _ _ _ _ (SSeq (SRcv 0 TUnit) (dual Rs)) SEnd (cvp 2)); [apply Hk|reflexivity|
      apply (lp_sel W Ψ 2 0); [done|done|lia]|apply (lp_sel W Ψ 2 1); [done|done|lia]|apply (lp_fact W Ψ 2 1); [done|lia]].
  - eapply t_conv; [|tstep]. conv_sess.
Qed.

Theorem loop_deadlock_free : deadlock_free (∅, {[+ loop_main +]}).
Proof. apply (soundness_source 1 lp_C _ TUnit (c0_acyclic_creation _ _ lp_acyclic)); [constructor|apply loop_typed]. Qed.
