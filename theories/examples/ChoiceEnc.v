(** * Choice as a derived form: sums plus delegation

    PGV encodes S₁ ⊕ S₂ as !(S₁ + S₂).end (Kokke and Dardha,
    Prioritise the Best Variation, p. 6). Here the payload of the
    carrier binds two points, and each arm of the sum lies at its own
    slot:

      Sch S₁ S₂ = !(∃ι₀ ι₁. (dual S₁)@ι₀ ⊕ (dual S₂)@ι₁).Close
      Sbr T₁ T₂ = ?(∃ι₀ ι₁. T₁@ι₀ ⊕ T₂@ι₁).Close = dual (Sch (dual T₁) (dual T₂))

    At a carrier point x the arm i lies at the slot x.i. The derived
    forms use only new, send, recv, close, the sum and its case:

      sel₁ = λc. let (k, k′) = new ∗ at x.0 in let () = close (send ⟨inj₁ k′, c⟩) in k
      sel₂ = λc. let (k, k′) = new ∗ at x.1 in let () = close (send ⟨inj₂ k′, c⟩) in k
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

    Branch A closes d while it holds k at a.0 and asks δ ≺ a.0.
    Branch B receives on k at a.1 while it holds d and asks a.1 ≺ δ.
    The two facts name two points, so they do not meet. [choice_typed]
    types the program under the top-level constraint
    {a+1 ≺ a.1, a.1 ≺ δ, δ ≺ a.0, δ ≺ a.1+1}, and [choice_deadlock_free]
    follows from [soundness_source]. With both arms at a.0 the two facts
    are δ ≺ a.0 and a.0 ≺ δ, a cycle ([same_slot_cycle]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** The encoding *)

Definition Sch (S1 S2 : sty) : sty :=
  SSnd 2 (TSum (TSess (dual S1) (pvar 0)) (TSess (dual S2) (pvar 1))) SEnd.
Definition Sbr (T1 T2 : sty) : sty :=
  SRcv 2 (TSum (TSess T1 (pvar 0)) (TSess T2 (pvar 1))) SEnd.

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

(** Knownness of a slot is that of its base: they share a root. *)
Lemma skn_slot W Ψ x i : skn W Ψ x → skn W Ψ (pt_slot x i).
Proof. intros [H|(C & xs & y & Hg & Hy & E)]; [by left|right; by exists C, xs, y]. Qed.

(** ** Selection is a derived form

    sel_i takes the carrier at x and returns the continuation at x.i.
    It blocks at x (send) and at x+1 (close), so its upper point is
    x+1. send asks {x} ≺ {x.0, x.1}, and close c asks x+1 ≺ x.i,
    because sel_i holds k at x.i. *)

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
    arm i with the continuation at x.i. The sum has the heads x.0 and
    x.1, so the close asks x+1 ≺ x.0 and x+1 ≺ x.1 whatever the arm. *)

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
