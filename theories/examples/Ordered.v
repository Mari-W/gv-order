(** * Example: a box that needs ι ≺ ι′ between its arguments (58)

    ordered : □(∀ι ι′. {ι ≺ ι′}. ∗ ⊸ Close@ι ⊗ Close@ι′ ⊸^{ι′} ∗)
    ordered = !(f = λp. let (c, d) = p in let () = close c in close d)

    close c blocks at ι while the body still holds d at ι′, so E-App
    asks ι ≺ ι′. With end points the gate compares ι with the partner
    point ι̅′ of d and the upper point ι′ of the λ, so the constraint is
    {ι ≺ ι′, ι ≺ ι̅′}. Program order relates nothing between two point
    variables, so without the constraint the box does not type, which
    [ord_no_constraint] (examples/Rejected.v) proves. With it
    the fact is the hypothesis itself. A caller forces the box at
    ((a, 0), (a, 1)), where program order meets the constraint. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition ord_body : ty :=
  TLolli (Some (pvar 1)) None (TProd (TSess SEnd (pvar 0)) (TSess SEnd (pvar 1))) TUnit.

Definition ord_C : bcs := BCs [] (λ g, g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pt_dual (pvar 1))).

Definition ord_ty : ty := TBox 2 0 ord_C (TLolli None None TUnit ord_body).

Definition ord_box : expr :=
  EBox (Lam (LetP (Var 0)
    (LetU (App (Konst KClos) (Var 1)) (App (Konst KClos) (Var 0))))).

Lemma ordered_typed W F : world_wf W → typed W ∅ [] ∅ [] F ord_box ord_ty.
Proof.
  intros HW. unfold ord_box, ord_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. set (Bx := TBox 2 _ _ _).
  set (Ψ := [(_, _)]). set (Tc := TSess SEnd (pvar 0)). set (Td := TSess SEnd (pvar 1)).
  unfold ord_body. fold Tc Td.
  apply (t_abs W _ _ _ _ _ _ _ _ _ _ 1); [set_solver|done|].
  apply (t_letpair W _ _ ∅ ∅ ∅ _ [Some (TProd Tc Td); None] [None; Some Bx] _ _ _ Tc Td).
  { apply tenv_comp_empty_l, se_dsym. }
  { repeat constructor. }
  { apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; done. }
  apply (t_letstar W _ _ ∅ ∅ ∅ _ [None; Some Tc; None; None] [Some Td; None; None; Some Bx]).
  { apply tenv_comp_empty_l, se_dsym. }
  { repeat constructor. }
  { eapply (t_app W _ _ ∅ ∅ ∅ _ (lenv_nones _) _ _ _ _ (Some (pvar 0)) None Tc TUnit).
    - apply tenv_comp_empty_l, se_dsym.
    - apply lenv_split_nones_l.
    - apply ub_below_s_intro.
      + intros y Hy. unfold sf_union, tenv_heads in Hy. rewrite map_fold_empty in Hy.
        subst Td Bx. simpl in Hy. assert (y = pt_dual (pvar 1)) as -> by set_solver.
        eapply (sl_hyp0 W _ _ _ (pvar 0) (pt_dual (pvar 1))); [by left|by right|cbn; lia|done|done].
      + exists (pvar 1). split; [done|]. right.
        eapply (sl_hyp0 W _ _ _ (pvar 0) (pvar 1)); [by left|by left|cbn; lia|done|done].
    - apply t_const; [apply lenv_empty_nones|apply KTClos|done].
    - apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; try done.
      destruct y as [|[|y]]; simplify_eq/=. }
  eapply t_weak; [apply (lwk_cons _ [None; None; None]), lwk_cons, lwk_cons, lwk_drop;
                [done|constructor]|].
  eapply (t_app W _ _ ∅ ∅ ∅ _ (lenv_nones _) _ _ _ _ (Some (pvar 1)) None Td TUnit).
  - apply tenv_comp_empty_l, se_dsym.
  - apply lenv_split_nones_l.
  - apply ub_below_s_intro.
    + intros y Hy. simpl in Hy. set_solver.
    + exists (pvar 1). split; [done|]. left. apply se_refl.
  - apply t_const; [apply lenv_empty_nones|apply KTClos|done].
  - apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; try done.
    destruct y as [|[|y]]; simplify_eq/=.
Qed.

(** Forcing at ((a, 0), (a, 1)): (a, 0) ≺ (a, 1) by program order, and
    both points are known when a is (59). *)
Lemma ordered_force W F a : world_wf W → pt_known W (Pt (NConst a) 0) →
  typed W ∅ [] ∅ [] (F, None) (App EForce ord_box)
    (ty_inst [Pt (NConst a) 0; Pt (NConst a) 1] ord_body).
Proof.
  intros HW Ha. apply typed_force0 with (m := 2) (C := ord_C) (ub := None); [done|done| | |done|].
  - apply bcs_hold_intro. intros g [-> | ->] _; cbn; apply sl_w.
    + apply (wf_lt_po_n W (Pt (NConst a) 0) 0 HW).
    + apply (wf_lt_dpo _ HW (Pt (NConst a) 0)).
  - constructor; [left; exact Ha|constructor; [left; unfold pt_known in *; exact Ha|constructor]].
  - by apply ordered_typed.
Qed.
