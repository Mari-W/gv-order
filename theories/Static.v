(** * The static system (spec §9, with sharp edges 52 and 53)

    Θ; Δ ⊢^F_G t : T and Σ ⊢_G p : T. The facts G enter through the
    world W_G they generate: the judgments are indexed by a world W,
    and every side condition on points is read in W (≡_G as [w_eq W],
    ≺_G as [w_lt W]). Fundamental and soundness ask W strict.

    Sharp edges 54 (option D) and 56: the fresh μ of E-Abs and E-Exp is
    a frame variable φ with the single hypothesis u ≺ φ, so both rules
    have one premise about the body at the same world W. E-Exp types
    the body once, with the box's ιs as the point variables 0, …, m-1
    and the outer environment and hypotheses shifted past them. E-Const
    asks the payload of send and recv to be scoped by its binders
    ([kscoped]). [typed_pinst] substitutes points for point variables.
    [typed_ityped] does that and instantiates φ by any frame above u at
    any later world in one induction, and yields the infinitary
    judgment [ityped] of sharp edges 53, whose fundamental theorem
    [ifundamental] is the old one. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export TermRules2.

Set Default Proof Using "All".

(** ** The infinitary judgment

    The reading of sharp edges 53: the bodies of λ and box are typed in
    every later world and under every frame above the upper point. It
    is now the target of frame instantiation (below), not the static
    system itself. *)

Inductive ityped (W : world) : tenv → lenv → gset point → expr → ty → Prop :=
  | it_unit Δ F :                                        (* E-Unit *)
      lenv_empty Δ →
      ityped W ∅ Δ F EUnit TUnit
  | it_konst Δ F k T :                                   (* E-Const *)
      lenv_empty Δ → konst_ty (w_eq W) (w_lt W) (pt_known W) k T →
      ityped W ∅ Δ F (Konst k) T
  | it_var Δ F x T :                                     (* E-LVar *)
      lenv_only Δ x T →
      ityped W ∅ Δ F (Var x) T
  | it_chan Δ F c s k s' y :                             (* E-Ch, ι′ ≡_G ι *)
      lenv_empty Δ → seq s s' → w_eq W k y →
      ityped W {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | it_lam Θ Δ F e T U ub lb :                           (* E-Abs *)
      lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
      (∀ W1 F', wext W W1 → ub_below W1 ub F' → ityped W1 Θ (Some T :: Δ) F' e U) →
      ityped W Θ Δ F (Lam e) (TLolli ub lb T U)
  | it_app Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :           (* E-App *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
      ityped W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      ityped W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
      ityped W Θ Δ F (App e1 e2) U
  | it_pair Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :                (* E-Pair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      ityped W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      ityped W Θ2 Δ2 (F ∪ heads T) e2 U →
      ityped W Θ Δ F (Pair e1 e2) (TProd T U)
  | it_letu Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :                  (* E-Let* *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      ityped W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      ityped W Θ2 Δ2 F e2 T →
      ityped W Θ Δ F (LetU e1 e2) T
  | it_letp Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :            (* E-LetPair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      ityped W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      ityped W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      ityped W Θ Δ F (LetP e1 e2) T
  | it_inj1 Θ Δ F e T U :                                (* E-Inj *)
      ityped W Θ Δ F e T → ityped W Θ Δ F (Inj1 e) (TSum T U)
  | it_inj2 Θ Δ F e T U :
      ityped W Θ Δ F e U → ityped W Θ Δ F (Inj2 e) (TSum T U)
  | it_case Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :          (* E-Case *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      ityped W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      ityped W Θ2 (Some T1 :: Δ2) F e1 T →
      ityped W Θ2 (Some T2 :: Δ2) F e2 T →
      ityped W Θ Δ F (Case e e1 e2) T
  | it_box Δ F e m C ub T :                              (* E-Exp *)
      lenv_unl Δ → term_wf ∅ (Some (TBox m C ub T) :: Δ) e →
      (∀ W1 xs F', wext W W1 → length xs = m → pcs_hold (w_lt W1) (pcs_inst (plist xs) C) →
         ub_below W1 (pt_inst (plist xs) <$> ub) F' →
         ityped W1 ∅ (Some (TBox m C ub T) :: Δ) F' e (ty_inst xs T)) →
      ityped W ∅ Δ F (EBox e) (TBox m C ub T)
  | it_wk Θ Δ' Δ F e T :                                 (* E-Weak *)
      lenv_wk Δ' Δ → ityped W Θ Δ' F e T → ityped W Θ Δ F e T
  | it_contract Θ Δ U F e T :                            (* E-Contract *)
      unlimited U →
      ityped W Θ (Some U :: Some U :: Δ) F e T →
      ityped W Θ (Some U :: Δ) F (rename pred e) T
  | it_conv Θ Δ F e T T' :                               (* E-Conv *)
      teq T T' → ityped W Θ Δ F e T → ityped W Θ Δ F e T'.

(** E-Force is E-App at the constant force. *)
Lemma ityped_force W Θ Δ F e m C ub T xs :
  world_wf W → length xs = m → pcs_hold (w_lt W) (pcs_inst (plist xs) C) →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  ityped W Θ Δ F e (TBox m C ub T) →
  ityped W Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs HC Hub He.
  eapply (it_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply it_konst; [apply lenv_empty_nones|]. by constructor.
  - simpl. by rewrite union_empty_r_L.
Qed.

(** ** Typed terms are well formed (the premises of E-Abs and E-Exp) *)

Lemma lenv_wk_avail Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail Δ' x → lenv_avail Δ x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by exists T|].
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
Qed.

Lemma lenv_wk_avail_lin Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail_lin Δ x → lenv_avail_lin Δ' x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx & Hnb); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    + exists T. auto.
    + destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by destruct (Hnb Hu)|].
    destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
Qed.

Lemma lenv_empty_no_avail Δ x : lenv_empty Δ → ¬ lenv_avail Δ x.
Proof.
  intros HΔ (T & Hx). apply list_elem_of_lookup_2 in Hx.
  apply HΔ in Hx. done.
Qed.

Lemma ub_below_empty W ub : ub_below W ub ∅.
Proof. destruct ub; simpl; [set_solver|done]. Qed.

Lemma ityped_term_wf W Θ Δ F e T : ityped W Θ Δ F e T → strict W → term_wf Θ Δ e.
Proof.
  unfold term_wf. induction 1 as
    [W Δ F HΔ
    |W Δ F k T HΔ Hk
    |W Δ F x T Ho
    |W Δ F c s k s' y HΔ _ _
    |W Θ Δ F e T U ub lb _ _ IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ _ _ IH1 _ IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ _ IH1 _ IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ _ IH1 _ IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ _ IH1 _ IH2
    |W Θ Δ F e T U _ IH
    |W Θ Δ F e T U _ IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ _ IH0 _ IH1 _ IH2
    |W Δ F e m C ub T HΔ Hwf _ IH
    |W Θ Δ' Δ F e T Hwk _ IH
    |W Θ Δ U F e T Hu _ IH
    |W Θ Δ F e T T' _ _ IH]; intros HW.
  (* E-Unit *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Const *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-LVar *)
  - split_and!; simpl.
    + by rewrite dom_empty_L.
    + destruct Ho as [Hlk _]. by exists T.
    + intros x' (T' & Hx' & _). destruct Ho as [_ Huniq].
      by destruct (Huniq x' T' Hx') as [-> _].
  (* E-Ch *)
  - split_and!; simpl; [by rewrite dom_singleton_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Abs *)
  - destruct (IH W ∅ (wext_refl _ HW) (ub_below_empty _ _) HW) as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-App *)
  - destruct (IH1 HW) as (Hfc1 & Hfv1 & Hrv1). destruct (IH2 HW) as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Pair *)
  - destruct (IH1 HW) as (Hfc1 & Hfv1 & Hrv1). destruct (IH2 HW) as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Let* *)
  - destruct (IH1 HW) as (Hfc1 & Hfv1 & Hrv1). destruct (IH2 HW) as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-LetPair *)
  - destruct (IH1 HW) as (Hfc1 & Hfv1 & Hrv1). destruct (IH2 HW) as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl.
        -- intros _. done.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply (Hrv2 (S (S x))). exists T'. auto.
  (* E-Inj *)
  - exact (IH HW).
  - exact (IH HW).
  (* E-Case *)
  - destruct (IH0 HW) as (Hfc0 & Hfv0 & Hrv0). destruct (IH1 HW) as (Hfc1 & Hfv1 & Hrv1).
    destruct (IH2 HW) as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split_and!.
      * eapply allfv_mono; [|exact Hfv0]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv1]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
      * eapply allfv_mono; [|exact Hfv2]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv0. exists T'. auto.
      * right. left. apply (Hrv1 (S x)). exists T'. auto.
  (* E-Exp *)
  - destruct Hwf as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-Weak *)
  - destruct (IH HW) as (Hfc & Hfv & Hrv). split_and!; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros x Hx. eauto using lenv_wk_avail.
    + intros x Hx. apply Hrv. eauto using lenv_wk_avail_lin.
  (* E-Contract *)
  - destruct (IH HW) as (Hfc & Hfv & Hrv). split_and!.
    + by rewrite fchans_rename.
    + apply allfv_rename. eapply allfv_mono; [|exact Hfv].
      intros [|[|x]] (T' & HT'); simpl in *; by exists T'.
    + intros [|x] (T' & Hx & Hnb); simpl in Hx.
      * simplify_eq. by destruct (Hnb Hu).
      * apply (freevar_rename e (S (S x)) pred). apply Hrv. by exists T'.
  (* E-Conv *)
  - exact (IH HW).
Qed.

(** ** The fundamental theorem for the infinitary judgment *)

Theorem ifundamental W Θ Δ F e T : ityped W Θ Δ F e T → strict W → sem_typed W Θ Δ F e T.
Proof.
  intros Ht. pose proof Ht as Ht0. revert Ht0.
  induction Ht as
    [W Δ F HΔ
    |W Δ F k T HΔ Hk
    |W Δ F x T Ho
    |W Δ F c s k s' y HΔ Hs Hk
    |W Θ Δ F e T U ub lb Hlb Hb IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |W Θ Δ F e T U H IH
    |W Θ Δ F e T U H IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |W Δ F e m C ub T HΔ Hwf Hb IH
    |W Θ Δ' Δ F e T Hwk H IH
    |W Θ Δ U F e T Hu H IH
    |W Θ Δ F e T T' Hteq H IH]; intros Ht0 HW.
  - by apply sem_typed_unit.
  - by apply sem_typed_konst.
  - by apply sem_typed_var.
  - by apply sem_typed_chan.
  - apply sem_typed_lam; [| |].
    + eapply (ityped_term_wf W); [|exact HW].
      apply (Hb W ∅ (wext_refl _ HW) (ub_below_empty _ _)).
    + done.
    + intros W1 F' HW1 Hub'. apply IH; [done|done| |apply HW1]. by apply Hb.
  - eapply sem_typed_app; [done|done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_pair; [done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_letu; [done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_letp; [done|done|by apply IH1|by apply IH2].
  - apply sem_typed_inj1. by apply IH.
  - apply sem_typed_inj2. by apply IH.
  - eapply sem_typed_case; [done|done|by apply IH0|by apply IH1|by apply IH2].
  - apply sem_typed_box; [done|done|].
    intros W1 xs F' HW1 Hxs HC Hub'. apply IH; [done..| |apply HW1]. by apply Hb.
  - eapply sem_typed_wk; [done|by apply IH].
  - apply sem_typed_contract; [done|by apply IH].
  - eapply sem_typed_teq; [done|by apply IH].
Qed.

(** ** The finitary static system (sharp edges 54, option D)

    E-Abs and E-Exp type the body under the frame {φ} for a fresh
    frame variable φ, with the single hypothesis u ≺ φ. A frame is a
    set of points and at most one frame variable: the body of λ or box
    starts at {φ} and the other rules only add points. φ occurs only in
    frames and in the hypotheses Φ, never in a type, an environment or
    the world, so it is never a point that [new] or force could alias.
    x ≺ φ holds when x ≼ u in W for the hypothesis u ≺ φ. E-Exp types
    the body with the ιs as point variables (sharp edges 57). *)

Notation sframe := (gset point * option nat)%type.
Notation fhyps := (gmap nat (option point)).

(** F[ρ]: replace the frame variable by a concrete frame. *)
Definition sf_inst (ρ : nat → gset point) (F : sframe) : gset point :=
  F.1 ∪ match F.2 with Some φ => ρ φ | None => ∅ end.

Definition sf_union (F : sframe) (X : gset point) : sframe := (F.1 ∪ X, F.2).

(** Facts about points (sharp edges 58). Inside a box body the
    constraint C of every enclosing box is a list Ψ of hypotheses
    x ≺ y on point variables. The static order is generated by ≺ of W,
    the hypotheses, ≡ of W and transitivity. C has ≺ facts only: an ≡
    hypothesis would also have to enter ≡ (successor and slot
    congruence, the duality of entries), and none of the examples
    needs one. *)
Inductive slt (W : world) (Ψ : list (point * point)) : point → point → Prop :=
  | sl_w x y : w_lt W x y → slt W Ψ x y
  | sl_h x y : (x, y) ∈ Ψ → slt W Ψ x y
  | sl_eql x x' y : w_eq W x x' → slt W Ψ x' y → slt W Ψ x y
  | sl_eqr x y y' : slt W Ψ x y' → w_eq W y' y → slt W Ψ x y
  | sl_trans x y z : slt W Ψ x y → slt W Ψ y z → slt W Ψ x z.

Definition sle (W : world) (Ψ : list (point * point)) (x y : point) : Prop :=
  w_eq W x y ∨ slt W Ψ x y.

Definition ub_below_h (W : world) (Ψ : list (point * point)) (ub : option point)
    (F : gset point) : Prop :=
  match ub with None => True | Some x => ∀ y, y ∈ F → slt W Ψ x y end.

Definition lb_below_h (W : world) (Ψ : list (point * point)) (lb : option point)
    (H : gset point) : Prop :=
  match lb with None => H = ∅ | Some x => ∀ y, y ∈ H → sle W Ψ x y end.

(** A map of the generators maps every derived fact. *)
Lemma slt_map W Ψ (R : point → point → Prop) (f : point → point) :
  (∀ x y, w_lt W x y → R (f x) (f y)) →
  (∀ x y, (x, y) ∈ Ψ → R (f x) (f y)) →
  (∀ x x' y, w_eq W x x' → R (f x') (f y) → R (f x) (f y)) →
  (∀ x y y', R (f x) (f y') → w_eq W y' y → R (f x) (f y)) →
  (∀ x y z, R x y → R y z → R x z) →
  ∀ x y, slt W Ψ x y → R (f x) (f y).
Proof. intros Hw Hh Hl Hr Ht x y H. induction H; eauto. Qed.

(** Without hypotheses the static order is the order of W. *)
Lemma slt_nil W x y : world_wf W → slt W [] x y → w_lt W x y.
Proof.
  intros HW H. induction H as [x y H|x y H|x x' y Hx _ IH|x y y' _ IH Hy|x y z _ IH1 _ IH2].
  - done.
  - by apply elem_of_nil in H.
  - eapply (wf_lt_eq _ HW); [exact Hx|exact IH|apply (wf_eq_refl _ HW)].
  - eapply (wf_lt_eq _ HW); [apply (wf_eq_refl _ HW)|exact IH|exact Hy].
  - by eapply (wf_lt_trans _ HW).
Qed.

Lemma pcs_hold_mono_w W W' C : wext W W' → pcs_hold (w_lt W) C → pcs_hold (w_lt W') C.
Proof. intros (_ & _ & Hl & _) H p Hp. apply Hl, H, Hp. Qed.

Lemma pcs_inst_app σ C C' : pcs_inst σ (C ++ C') = pcs_inst σ C ++ pcs_inst σ C'.
Proof. apply fmap_app. Qed.

(** {u} ≺ F, with x ≺ φ derived from x ≼ u and the hypothesis u ≺ φ. *)
Definition ub_below_s (W : world) (Ψ : list (point * point)) (Φ : fhyps)
    (ub : option point) (F : sframe) : Prop :=
  ub_below_h W Ψ ub F.1 ∧
  match ub, F.2 with
  | Some x, Some φ => ∃ u, Φ !! φ = Some (Some u) ∧ sle W Ψ x u
  | _, _ => True
  end.

(** ρ meets the hypotheses: {u} ≺_W ρ(φ) for every u ≺ φ in Φ. *)
Definition inst_ok (W : world) (Φ : fhyps) (ρ : nat → gset point) : Prop :=
  ∀ φ u, Φ !! φ = Some u → ub_below W u (ρ φ).

(** ** Point substitution (sharp edges 56, 57)

    The body of a box is typed once, with the box's ιs as the point
    variables 0, …, m-1 and every outer point variable shifted past
    them. [typed_ityped] substitutes points for the variables. A
    payload ∃ιs.T is scoped: its points are constants or among its m
    binders, so substitution commutes with [payload_at]. *)

Definition pshift (m : nat) : nat → point := λ a, pvar (a + m).

Lemma pt_shift_0 x : pt_shift 0 x = x.
Proof. destruct x as [p o]. unfold pt_shift. simpl. f_equal. lia. Qed.

Lemma pt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
Proof. unfold pt_inst, pvar. simpl. apply pt_shift_0. Qed.

Lemma pt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
Proof.
  destruct x as [p o]. unfold pt_inst, pt_shift. simpl.
  destruct (pn_inst σ p). simpl. f_equal. lia.
Qed.

Lemma pt_inst_slot σ x i : pt_inst σ (pt_slot x i) = pt_slot (pt_inst σ x) i.
Proof. destruct x as [p o]. unfold pt_inst, pt_slot, pt_shift. simpl. done. Qed.

Lemma pn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
Proof.
  induction p as [a|a|p IH b i]; simpl; [done|done|].
  by rewrite pt_inst_slot, pt_inst_shift, IH.
Qed.

Lemma pt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
Proof. unfold pt_inst at 2 3. by rewrite pt_inst_shift, pn_inst_comp. Qed.

Lemma pn_inst_ext_root σ τ p :
  (∀ a, pn_root p = NVar a → σ a = τ a) → pn_inst σ p = pn_inst τ p.
Proof. induction p as [a|a|p IH b i]; simpl; intros H; [done|by apply H|by rewrite IH]. Qed.

Lemma pt_inst_ext_root σ τ x :
  (∀ a, pt_root x = NVar a → σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. unfold pt_inst. f_equal. by apply pn_inst_ext_root. Qed.

Lemma pt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. apply pt_inst_ext_root. auto. Qed.

Lemma pn_inst_pvar p : pn_inst pvar p = Pt p 0.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|]. by rewrite IH. Qed.

Lemma pt_inst_pvar x : pt_inst pvar x = x.
Proof. destruct x as [p o]. unfold pt_inst. simpl. by rewrite pn_inst_pvar. Qed.

Lemma pn_inst_const σ p a : pn_root p = NConst a → pn_inst σ p = Pt p 0.
Proof.
  induction p as [a'|a'|p IH b i]; simpl; intros H; [done|done|].
  by rewrite (IH H).
Qed.

Lemma pt_inst_const σ x a : pt_root x = NConst a → pt_inst σ x = x.
Proof. destruct x as [p o]. intros H. unfold pt_inst. simpl. by rewrite (pn_inst_const σ p a H). Qed.

(** Lifting composes, and the identity lifts to itself. *)
Lemma pup_ext n σ τ a : (∀ b, σ b = τ b) → pup n σ a = pup n τ a.
Proof. intros H. unfold pup. by rewrite H. Qed.

Lemma pup_pvar n a : pup n pvar a = pvar a.
Proof.
  unfold pup. destruct (decide (a < n)); [done|].
  rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma pup_comp τ σ n a : pt_inst (pup n τ) (pup n σ a) = pup n (pt_inst τ ∘ σ) a.
Proof.
  unfold pup at 2 3. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True.
  - change ((pt_inst τ ∘ σ) (a - n)) with (pt_inst τ (σ (a - n))).
    rewrite !pt_inst_comp. apply pt_inst_ext. intros b. simpl.
    rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
    by replace (b + n - n) with b by lia.
Qed.

Lemma pcs_comp τ σ C : pcs_inst τ (pcs_inst σ C) = pcs_inst (pt_inst τ ∘ σ) C.
Proof.
  unfold pcs_inst. rewrite <-list_fmap_compose. apply list_fmap_ext.
  intros _ p _. simpl. by rewrite !pt_inst_comp.
Qed.

Lemma pcs_pvar C : pcs_inst pvar C = C.
Proof.
  unfold pcs_inst. rewrite <-(list_fmap_id C) at 2. apply list_fmap_ext.
  intros _ [x y] _. simpl. by rewrite !pt_inst_pvar.
Qed.

Lemma pcs_hold_inst (lt lt' : point → point → Prop) σ C :
  (∀ x y, lt x y → lt' (pt_inst σ x) (pt_inst σ y)) →
  pcs_hold lt C → pcs_hold lt' (pcs_inst σ C).
Proof.
  intros Hl H p Hp. unfold pcs_inst in Hp. apply list_elem_of_fmap in Hp as (q & -> & Hq).
  apply Hl, H, Hq.
Qed.

Lemma pinst_ty_ext T : ∀ σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    intros σ τ H; simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_ext|destruct lb; simpl; f_equal; auto using pt_inst_ext|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + apply pcs_inst_ext. intros a. by apply pup_ext.
    + destruct ub; simpl; [|done]. f_equal. apply pt_inst_ext. intros a. by apply pup_ext.
    + apply IH. intros a. by apply pup_ext.
  - f_equal. by apply pt_inst_ext.
Qed.

Lemma pinst_ty_comp T : ∀ τ σ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    intros τ σ; simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_comp|destruct lb; simpl; f_equal; auto using pt_inst_comp|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + rewrite pcs_comp. apply pcs_inst_ext. intros a. apply pup_comp.
    + destruct ub; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. intros a. apply pup_comp.
    + rewrite IH. apply pinst_ty_ext. intros a. apply pup_comp.
  - f_equal. apply pt_inst_comp.
Qed.

Lemma pinst_ty_pvar T : pinst_ty pvar T = T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_pvar|destruct lb; simpl; f_equal; auto using pt_inst_pvar|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + rewrite (pcs_inst_ext _ pvar); [apply pcs_pvar|apply pup_pvar].
    + destruct ub as [u|]; simpl; [|done]. f_equal.
      rewrite (pt_inst_ext _ pvar); [apply pt_inst_pvar|apply pup_pvar].
    + rewrite (pinst_ty_ext _ _ pvar); [done|apply pup_pvar].
  - f_equal. apply pt_inst_pvar.
Qed.

(** Instantiating a list after lifting past it. *)
Lemma plist_shift xs m b : length xs = m → plist xs (b + m) = pvar b.
Proof.
  intros Hxs. unfold plist. rewrite lookup_ge_None_2 by lia.
  unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma plist_pup_shift xs m σ a :
  length xs = m → pt_inst (pt_inst (plist xs) ∘ pup m σ) (pshift m a) = σ a.
Proof.
  intros Hxs. unfold pshift. rewrite pt_inst_pvar_at. simpl.
  unfold pup. rewrite decide_False by lia. replace (a + m - m) with a by lia.
  rewrite pt_inst_comp. transitivity (pt_inst pvar (σ a)); [|apply pt_inst_pvar].
  apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma plist_pup_comm xs n σ a :
  length xs = n →
  pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a).
Proof.
  intros Hxs. unfold pup. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold plist.
    destruct (lookup_lt_is_Some_2 xs a) as [x Hx]; [lia|].
    by rewrite list_lookup_fmap, Hx.
  - assert (plist xs a = pvar (a - n)) as ->.
    { unfold plist. rewrite lookup_ge_None_2 by lia. by rewrite Hxs. }
    rewrite pt_inst_pvar_at, pt_inst_comp.
    transitivity (pt_inst pvar (σ (a - n))); [|apply pt_inst_pvar].
    apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at.
    apply plist_shift. by rewrite length_fmap.
Qed.

(** ** Point scoping: every point variable lies below k *)

Definition pt_scoped (k : nat) (x : point) : Prop := ∀ a, pt_root x = NVar a → a < k.

Definition opt_scoped (k : nat) (o : option point) : Prop :=
  match o with Some x => pt_scoped k x | None => True end.

Definition pcs_scoped (k : nat) (C : list (point * point)) : Prop :=
  ∀ p, p ∈ C → pt_scoped k p.1 ∧ pt_scoped k p.2.

Fixpoint pscoped (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli ub lb T1 U => opt_scoped k ub ∧ opt_scoped k lb ∧ pscoped k T1 ∧ pscoped k U
  | TProd T1 U | TSum T1 U => pscoped k T1 ∧ pscoped k U
  | TBox n C ub T1 => pcs_scoped (n + k) C ∧ opt_scoped (n + k) ub ∧ pscoped (n + k) T1
  | TSess _ x => pt_scoped k x
  end.

Lemma pinst_ty_ext_scoped T : ∀ k σ τ,
  pscoped k T → (∀ a, a < k → σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  assert (∀ k σ τ x, pt_scoped k x → (∀ a, a < k → σ a = τ a) →
            pt_inst σ x = pt_inst τ x) as Hpt.
  { intros k σ τ x Hx H. apply pt_inst_ext_root. intros a Ha. by apply H, Hx. }
  assert (∀ k n σ τ, (∀ a, a < k → σ a = τ a) → ∀ a, a < n + k → pup n σ a = pup n τ a) as Hup.
  { intros k n σ τ H a Ha. unfold pup. destruct (decide (a < n)); [done|].
    rewrite H; [done|lia]. }
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    intros k σ τ HT H; simpl in *.
  - done.
  - destruct HT as (Hub & Hlb & H1 & H2).
    f_equal; [destruct ub; simpl in *; [f_equal; eauto|done]
             |destruct lb; simpl in *; [f_equal; eauto|done]|eauto|eauto].
  - destruct HT. f_equal; eauto.
  - destruct HT. f_equal; eauto.
  - destruct HT as (HC & Hub & H1). f_equal.
    + unfold pcs_inst. apply list_fmap_ext. intros i p Hp.
      destruct (HC p (list_elem_of_lookup_2 _ _ _ Hp)) as [Hp1 Hp2].
      f_equal; (eapply Hpt; [done|]); by apply Hup.
    + destruct ub; simpl in *; [|done]. f_equal. eapply Hpt; [done|]. by apply Hup.
    + eapply IH; [done|]. by apply Hup.
  - f_equal. eauto.
Qed.

Lemma payload_pinst σ m T x :
  pscoped m T → pinst_ty σ (payload_at m T x) = payload_at m T (pt_inst σ x).
Proof.
  intros HT. unfold payload_at, ty_inst. rewrite pinst_ty_comp.
  apply (pinst_ty_ext_scoped T m); [done|]. intros a Ha. simpl. unfold plist, slots.
  rewrite !list_lookup_fmap, !lookup_seq_lt by done. simpl. apply pt_inst_slot.
Qed.

(** E-Const asks the payload of send and recv to be scoped by its m
    binders (§4: "P ::= ∃ιs. T, all points of T bound"). *)
Definition kscoped (k : konst) (T : ty) : Prop :=
  match k, T with
  | KSend, TLolli _ _ (TProd _ (TSess (SSnd m P _) _)) _ => pscoped m P
  | KRecv, TLolli _ _ (TSess (SRcv m P _) _) _ => pscoped m P
  | _, _ => True
  end.

Lemma opt_heads_pinst σ o : opt_heads (pt_inst σ <$> o) = set_map (pt_inst σ) (opt_heads o).
Proof. destruct o; simpl; [by rewrite set_map_singleton_L|by rewrite set_map_empty]. Qed.

Lemma heads_pinst σ T : heads (pinst_ty σ T) = set_map (pt_inst σ) (heads T).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    simpl.
  - by rewrite set_map_empty.
  - apply opt_heads_pinst.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite set_map_empty.
  - by rewrite set_map_singleton_L.
Qed.

(** ** Facts survive substitution

    A world knows constants only (wf_names_const). A fact about a point
    with a variable root is reflexivity or program order, and both hold
    of any instance. *)

Section transfer.
  Context (W W1 : world) (σ : nat → point).
  Context (HW : world_wf W) (HW1 : wext W W1).

  Lemma pinst_eq x y : w_eq W x y → w_eq W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_eq_supp _ HW x y Hxy) as [->|[Hx Hy]]; [apply (wf_eq_refl _ Hwf)|].
    destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
    rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma pinst_lt x y : w_lt W x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_lt_supp _ HW x y Hxy) as [[Hn Ho]|[Hx Hy]].
    - destruct x as [p o], y as [p' o']. simpl in *. subst p'.
      replace (pt_inst σ (Pt p o')) with (pt_shift (S (o' - o - 1)) (pt_inst σ (Pt p o))).
      + by apply wf_lt_po_n.
      + unfold pt_inst, pt_shift. simpl. f_equal. lia.
    - destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
      rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma pinst_le x y : w_le W x y → w_le W1 (pt_inst σ x) (pt_inst σ y).
  Proof. intros [H|H]; [left; by apply pinst_eq|right; by apply pinst_lt]. Qed.

  Lemma pinst_known x : pt_known W x → pt_known W1 (pt_inst σ x).
  Proof.
    intros Hx. destruct (wf_names_const _ HW _ Hx) as [a Ha].
    rewrite (pt_inst_const σ x a Ha). destruct HW1 as [HN _]. unfold pt_known in *. set_solver.
  Qed.

  Lemma ub_below_pinst ub F :
    ub_below W ub F → ub_below W1 (pt_inst σ <$> ub) (set_map (pt_inst σ) F).
  Proof.
    destruct ub as [x|]; simpl; [|done]. intros H y Hy.
    apply elem_of_map in Hy as (y0 & -> & Hy0). by apply pinst_lt, H.
  Qed.

  Lemma lb_below_pinst lb H :
    lb_below W lb H → lb_below W1 (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply pinst_le, Hl.
    - intros ->. apply set_map_empty.
  Qed.

  Lemma konst_ty_pinst (plt plt' : point → point → Prop) k T :
    (∀ x y, plt x y → plt' (pt_inst σ x) (pt_inst σ y)) →
    kscoped k T → konst_ty (w_eq W) plt (pt_known W) k T →
    konst_ty (w_eq W1) plt' (pt_known W1) k (pinst_ty σ T).
  Proof.
    intros Hlt Hk. destruct 1 as [S x Hx|ub lb|m P S x Hh|m P S x|x|S x x' Hxx'|n C ub P xs Hxs HC];
      simpl in *.
    - constructor. by apply pinst_known.
    - constructor.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
      intros h Hh'. rewrite <-payload_pinst, heads_pinst in Hh' by done.
      apply elem_of_map in Hh' as (h0 & -> & Hh0). by apply Hlt, Hh.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
    - constructor.
    - constructor. by apply pinst_eq.
    - assert (∀ a, pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a))
        as Hc by (intros a; by apply plist_pup_comm).
      assert (pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup n σ) <$> ub) =
              pt_inst σ <$> (pt_inst (plist xs) <$> ub)) as E1.
      { destruct ub; simpl; [|done]. f_equal. rewrite !pt_inst_comp.
        apply pt_inst_ext. intros a. apply Hc. }
      assert (ty_inst (pt_inst σ <$> xs) (pinst_ty (pup n σ) P) = pinst_ty σ (ty_inst xs P)) as E2.
      { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. apply Hc. }
      rewrite <-E1, <-E2. constructor; [by rewrite length_fmap|].
      assert (pcs_inst (plist (pt_inst σ <$> xs)) (pcs_inst (pup n σ) C)
              = pcs_inst σ (pcs_inst (plist xs) C)) as E3.
      { rewrite !pcs_comp. apply pcs_inst_ext. intros a. apply Hc. }
      rewrite E3. by apply (pcs_hold_inst plt).
  Qed.

  (** Facts derived from W and the hypotheses Ψ survive into W₁ when
      the hypotheses hold there (sharp edges 58). *)
  Lemma pcs_inst_elem Ψ x y : (x, y) ∈ Ψ → (pt_inst σ x, pt_inst σ y) ∈ pcs_inst σ Ψ.
  Proof. intros H. unfold pcs_inst. apply list_elem_of_fmap. by exists (x, y). Qed.

  Lemma slt_pinst Ψ x y :
    pcs_hold (w_lt W1) (pcs_inst σ Ψ) → slt W Ψ x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ. pose proof (wext_wf _ _ HW1) as Hwf. revert x y.
    apply (slt_map W Ψ (w_lt W1) (pt_inst σ)).
    - intros x y. apply pinst_lt.
    - intros x y Hxy. exact (HΨ _ (pcs_inst_elem Ψ x y Hxy)).
    - intros x x' y Hx H. eapply (wf_lt_eq _ Hwf); [by apply pinst_eq|exact H|apply (wf_eq_refl _ Hwf)].
    - intros x y y' H Hy. eapply (wf_lt_eq _ Hwf); [apply (wf_eq_refl _ Hwf)|exact H|by apply pinst_eq].
    - intros x y z. apply (wf_lt_trans _ Hwf).
  Qed.

  Lemma slt_pinst_s Ψ Ψ' x y :
    pcs_hold (slt W1 Ψ') (pcs_inst σ Ψ) → slt W Ψ x y → slt W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ. revert x y. apply (slt_map W Ψ (slt W1 Ψ') (pt_inst σ)).
    - intros x y H. apply sl_w. by apply pinst_lt.
    - intros x y Hxy. exact (HΨ _ (pcs_inst_elem Ψ x y Hxy)).
    - intros x x' y Hx H. eapply sl_eql; [by apply pinst_eq|exact H].
    - intros x y y' H Hy. eapply sl_eqr; [exact H|by apply pinst_eq].
    - intros x y z. apply sl_trans.
  Qed.

  Lemma sle_pinst Ψ x y :
    pcs_hold (w_lt W1) (pcs_inst σ Ψ) → sle W Ψ x y → w_le W1 (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply pinst_eq|right; by apply (slt_pinst Ψ)]. Qed.

  Lemma sle_pinst_s Ψ Ψ' x y :
    pcs_hold (slt W1 Ψ') (pcs_inst σ Ψ) → sle W Ψ x y → sle W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply pinst_eq|right; by apply (slt_pinst_s Ψ)]. Qed.

  Lemma ub_below_h_pinst Ψ ub F :
    pcs_hold (w_lt W1) (pcs_inst σ Ψ) →
    ub_below_h W Ψ ub F → ub_below W1 (pt_inst σ <$> ub) (set_map (pt_inst σ) F).
  Proof.
    intros HΨ. destruct ub as [x|]; simpl; [|done]. intros H y Hy.
    apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (slt_pinst Ψ), H.
  Qed.

  Lemma ub_below_h_pinst_s Ψ Ψ' ub F :
    pcs_hold (slt W1 Ψ') (pcs_inst σ Ψ) →
    ub_below_h W Ψ ub F → ub_below_h W1 Ψ' (pt_inst σ <$> ub) (set_map (pt_inst σ) F).
  Proof.
    intros HΨ. destruct ub as [x|]; simpl; [|done]. intros H y Hy.
    apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (slt_pinst_s Ψ), H.
  Qed.

  Lemma lb_below_h_pinst Ψ lb H :
    pcs_hold (w_lt W1) (pcs_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below W1 (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.

  Lemma lb_below_h_pinst_s Ψ Ψ' lb H :
    pcs_hold (slt W1 Ψ') (pcs_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below_h W1 Ψ' (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst_s Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.
End transfer.

(** ** Substitution in environments, hypotheses and frames *)

Definition lenv_pinst (σ : nat → point) (Δ : lenv) : lenv := fmap (M:=option) (pinst_ty σ) <$> Δ.

Definition ends_pinst (σ : nat → point) (o : ends) : ends :=
  match o with
  | One e => One (e.1, pt_inst σ e.2)
  | Both e1 e2 => Both (e1.1, pt_inst σ e1.2) (e2.1, pt_inst σ e2.2)
  end.

Definition tenv_pinst (σ : nat → point) (Θ : tenv) : tenv := ends_pinst σ <$> Θ.

Definition fhyps_pinst (σ : nat → point) (Φ : fhyps) : fhyps := fmap (M:=option) (pt_inst σ) <$> Φ.

Definition sf_pinst (σ : nat → point) (F : sframe) : sframe := (set_map (pt_inst σ) F.1, F.2).

Lemma unlimited_pinst σ U : unlimited U → unlimited (pinst_ty σ U).
Proof. by destruct U. Qed.

Lemma lenv_heads_pinst σ Δ : lenv_heads (lenv_pinst σ Δ) = set_map (pt_inst σ) (lenv_heads Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl.
  - by rewrite set_map_empty.
  - by rewrite IH, heads_pinst, set_map_union_L.
  - done.
Qed.

Lemma lenv_empty_pinst σ Δ : lenv_empty Δ → lenv_empty (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho'). by rewrite (HΔ o' Ho').
Qed.

Lemma lenv_unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (HΔ o' Ho') as [->|(U & -> & HU)]; [by left|right].
  exists (pinst_ty σ U). split; [done|by apply unlimited_pinst].
Qed.

Lemma lenv_pinst_lookup σ Δ x : lenv_pinst σ Δ !! x = fmap (pinst_ty σ) <$> Δ !! x.
Proof. unfold lenv_pinst. apply list_lookup_fmap. Qed.

Lemma lenv_only_pinst σ Δ x T : lenv_only Δ x T → lenv_only (lenv_pinst σ Δ) x (pinst_ty σ T).
Proof.
  intros [Hx Hu]. split.
  - by rewrite lenv_pinst_lookup, Hx.
  - intros y T' Hy. rewrite lenv_pinst_lookup in Hy.
    destruct (Δ !! y) as [[T0|]|] eqn:E; simplify_eq/=.
    destruct (Hu y T0 E) as [-> ->]. done.
Qed.

Lemma lenv_split_pinst σ Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_wk_pinst σ Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_pinst σ Δ') (lenv_pinst σ Δ).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_pinst_ext σ τ Δ : (∀ a, σ a = τ a) → lenv_pinst σ Δ = lenv_pinst τ Δ.
Proof.
  intros H. unfold lenv_pinst. apply list_fmap_ext. intros i [T|] _; simpl; [|done].
  f_equal. by apply pinst_ty_ext.
Qed.

Lemma lenv_pinst_comp τ σ Δ : lenv_pinst τ (lenv_pinst σ Δ) = lenv_pinst (pt_inst τ ∘ σ) Δ.
Proof.
  unfold lenv_pinst. rewrite <-list_fmap_compose. apply list_fmap_ext.
  intros i [T|] _; simpl; [|done]. f_equal. apply pinst_ty_comp.
Qed.

Lemma lenv_pinst_pvar Δ : lenv_pinst pvar Δ = Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |]; rewrite IH; [|done].
  by rewrite pinst_ty_pvar.
Qed.

Lemma ends_heads_pinst σ c o :
  ends_heads c (ends_pinst σ o) = set_map (pt_inst σ) (ends_heads c o).
Proof. destruct o; simpl; set_solver. Qed.

Lemma tenv_heads_pinst σ Θ : tenv_heads (tenv_pinst σ Θ) = set_map (pt_inst σ) (tenv_heads Θ).
Proof.
  apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_heads. split.
  - intros (c & o & Hc & Hx). unfold tenv_pinst in Hc. rewrite lookup_fmap in Hc.
    destruct (Θ !! c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
    rewrite ends_heads_pinst in Hx.
    apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
    apply elem_of_tenv_heads. eauto.
  - intros (x0 & -> & Hx0). apply elem_of_tenv_heads in Hx0 as (c & o & Hc & Hx).
    exists c, (ends_pinst σ o). split.
    + unfold tenv_pinst. by rewrite lookup_fmap, Hc.
    + rewrite ends_heads_pinst. by apply elem_of_map_2.
Qed.

Lemma tenv_pinst_pvar Θ : tenv_pinst pvar Θ = Θ.
Proof.
  apply map_eq. intros c. unfold tenv_pinst. rewrite lookup_fmap.
  destruct (Θ !! c) as [[[s x]|[s1 x1] [s2 x2]]|]; simpl; rewrite ?pt_inst_pvar; done.
Qed.

Lemma tenv_comp_pinst W W1 σ Θ Θ1 Θ2 :
  world_wf W → wext W W1 → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
Proof.
  intros HW HW1 [Hj Hd]. split.
  - intros c. unfold tenv_pinst. rewrite !lookup_fmap. pose proof (Hj c) as Hc.
    destruct (Θ1 !! c), (Θ2 !! c), (Θ !! c); inversion Hc; subst; simpl; constructor.
  - intros c e1 e2 H1 H2. unfold tenv_pinst in H1, H2. rewrite lookup_fmap in H1, H2.
    destruct (Θ1 !! c) as [[e1'|]|] eqn:E1; simplify_eq/=.
    destruct (Θ2 !! c) as [[e2'|]|] eqn:E2; simplify_eq/=.
    destruct (Hd c e1' e2' E1 E2) as [He Hs]. split; [|done].
    by apply (pinst_eq W W1).
Qed.

Lemma sf_pinst_union σ F X : sf_pinst σ (sf_union F X) = sf_union (sf_pinst σ F) (set_map (pt_inst σ) X).
Proof. unfold sf_pinst, sf_union. simpl. by rewrite set_map_union_L. Qed.

Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite elem_of_map. split.
  - intros (y & -> & Hy). by rewrite pt_inst_pvar.
  - intros Hx. exists x. by rewrite pt_inst_pvar.
Qed.

Lemma ub_below_s_pinst W W1 σ Ψ Ψ' Φ ub F :
  world_wf W → wext W W1 → pcs_hold (slt W1 Ψ') (pcs_inst σ Ψ) → ub_below_s W Ψ Φ ub F →
  ub_below_s W1 Ψ' (fhyps_pinst σ Φ) (pt_inst σ <$> ub) (sf_pinst σ F).
Proof.
  intros HW HW1 HΨ [HP Hφ]. split; [by apply (ub_below_h_pinst_s W W1 σ HW HW1 Ψ)|].
  destruct ub as [x|], F as [P [φ|]]; simpl in *; try done.
  destruct Hφ as (u & Hu & Hle). exists (pt_inst σ u). split.
  - unfold fhyps_pinst. by rewrite lookup_fmap, Hu.
  - by apply (sle_pinst_s W W1 σ HW HW1 Ψ).
Qed.

Lemma eqT_pinst ρ T : ∀ U σ, eqT ρ T U → eqT ρ (pinst_ty σ T) (pinst_ty σ U).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C ub T1 IH | s x];
    intros [| ub' lb' U1 U2 | U1 U2 | U1 U2 | n' C' ub' U1 | r y] σ; simpl; try done.
  - intros (-> & -> & H1 & H2). split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros (-> & -> & -> & H1). split_and!; auto.
  - intros (-> & H). split_and!; auto.
Qed.

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma sf_pinst_fresh σ φ : sf_pinst σ (∅, Some φ) = (∅, Some φ).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

Inductive typed (W : world) : fhyps → list (point * point) → tenv → lenv → sframe → expr → ty → Prop :=
  | t_unit Φ Ψ Δ F :                                    (* E-Unit *)
      lenv_empty Δ →
      typed W Φ Ψ ∅ Δ F EUnit TUnit
  | t_konst Φ Ψ Δ F k T :                               (* E-Const *)
      lenv_empty Δ → konst_ty (w_eq W) (slt W Ψ) (pt_known W) k T → kscoped k T →
      typed W Φ Ψ ∅ Δ F (Konst k) T
  | t_var Φ Ψ Δ F x T :                                 (* E-LVar *)
      lenv_only Δ x T →
      typed W Φ Ψ ∅ Δ F (Var x) T
  | t_chan Φ Ψ Δ F c s k s' y :                         (* E-Ch, ι′ ≡_G ι *)
      lenv_empty Δ → seq s s' → w_eq W k y →
      typed W Φ Ψ {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | t_lam Φ Ψ Θ Δ F e T U ub lb φ :                     (* E-Abs *)
      φ ∉ dom Φ →
      lb_below_h W Ψ lb (tenv_heads Θ ∪ lenv_heads Δ) →
      typed W (<[φ := ub]> Φ) Ψ Θ (Some T :: Δ) (∅, Some φ) e U →
      typed W Φ Ψ Θ Δ F (Lam e) (TLolli ub lb T U)
  | t_app Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :       (* E-App *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_s W Ψ Φ ub F →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (opt_heads lb)) e2 T →
      typed W Φ Ψ Θ Δ F (App e1 e2) U
  | t_pair Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :            (* E-Pair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (heads T)) e2 U →
      typed W Φ Ψ Θ Δ F (Pair e1 e2) (TProd T U)
  | t_letu Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :              (* E-Let* *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      typed W Φ Ψ Θ2 Δ2 F e2 T →
      typed W Φ Ψ Θ Δ F (LetU e1 e2) T
  | t_letp Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :        (* E-LetPair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      typed W Φ Ψ Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (LetP e1 e2) T
  | t_inj1 Φ Ψ Θ Δ F e T U :                            (* E-Inj *)
      typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F (Inj1 e) (TSum T U)
  | t_inj2 Φ Ψ Θ Δ F e T U :
      typed W Φ Ψ Θ Δ F e U → typed W Φ Ψ Θ Δ F (Inj2 e) (TSum T U)
  | t_case Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :      (* E-Case *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      typed W Φ Ψ Θ2 (Some T1 :: Δ2) F e1 T →
      typed W Φ Ψ Θ2 (Some T2 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (Case e e1 e2) T
  | t_box Φ Ψ Δ F e m C ub T φ :                        (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ)) (pcs_inst (pshift m) Ψ ++ C) ∅
        (lenv_pinst (pshift m) (Some (TBox m C ub T) :: Δ)) (∅, Some φ) e T →
      typed W Φ Ψ ∅ Δ F (EBox e) (TBox m C ub T)
  | t_wk Φ Ψ Θ Δ' Δ F e T :                             (* E-Weak *)
      lenv_wk Δ' Δ → typed W Φ Ψ Θ Δ' F e T → typed W Φ Ψ Θ Δ F e T
  | t_contract Φ Ψ Θ Δ U F e T :                        (* E-Contract *)
      unlimited U →
      typed W Φ Ψ Θ (Some U :: Some U :: Δ) F e T →
      typed W Φ Ψ Θ (Some U :: Δ) F (rename pred e) T
  | t_conv Φ Ψ Θ Δ F e T T' :                           (* E-Conv *)
      teq T T' → typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F e T'.

(** E-Force is E-App at the constant force. The instance must meet the
    box's constraint, read from W and the hypotheses Ψ (sharp edges 58). *)
Lemma typed_force W Φ Ψ Θ Δ F e m C ub T xs :
  world_wf W → length xs = m → pcs_hold (slt W Ψ) (pcs_inst (plist xs) C) →
  ub_below_s W Ψ Φ (pt_inst (plist xs) <$> ub) F →
  typed W Φ Ψ Θ Δ F e (TBox m C ub T) →
  typed W Φ Ψ Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs HC Hub He.
  eapply (t_app W Φ Ψ Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply t_konst; [apply lenv_empty_nones| |done]. by constructor.
  - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
Qed.

(** ** Frame instantiation

    Replacing the frame variables by concrete frames that meet the
    hypotheses, at any later world, turns a derivation into one of the
    infinitary judgment. Monotonicity in W is folded in: typing reads W
    only through facts, and facts survive W ⊑ W₁. *)

Lemma sf_inst_union ρ F X : sf_inst ρ (sf_union F X) = sf_inst ρ F ∪ X.
Proof. destruct F as [P [φ|]]; unfold sf_inst, sf_union; simpl; set_solver. Qed.

Lemma ub_below_s_inst W W1 Φ ρ ub F :
  world_wf W → wext W W1 → inst_ok W1 Φ ρ → ub_below_s W [] Φ ub F →
  ub_below W1 ub (sf_inst ρ F).
Proof.
  intros HW HW1 Hρ [HP Hφ]. destruct ub as [x|]; [|done]. simpl.
  intros y Hy. unfold sf_inst in Hy. apply elem_of_union in Hy as [Hy|Hy].
  - assert (ub_below W (Some x) F.1) as HP'.
    { intros z Hz. apply (slt_nil _ _ _ HW). by apply HP. }
    exact (ub_below_mono W W1 (Some x) F.1 HW1 HP' y Hy).
  - destruct F as [P [φ|]]; simpl in *; [|by apply elem_of_empty in Hy].
    destruct Hφ as (u & Hu & Hle). pose proof (Hρ φ (Some u) Hu y Hy) as Huy.
    pose proof (wext_wf _ _ HW1) as Hwf. destruct HW1 as (_ & He & Hl & _).
    destruct Hle as [Heq|Hlt%(slt_nil _ _ _ HW)].
    + exact (wf_lt_eq _ Hwf x u y y (He _ _ Heq) Huy (wf_eq_refl _ Hwf y)).
    + exact (wf_lt_trans _ Hwf x u y (Hl _ _ Hlt) Huy).
Qed.

Lemma inst_ok_mono W W1 Φ ρ : wext W W1 → inst_ok W Φ ρ → inst_ok W1 Φ ρ.
Proof. intros HW1 Hρ φ u Hu. exact (ub_below_mono W W1 u _ HW1 (Hρ φ u Hu)). Qed.

Lemma inst_ok_insert W Φ ρ φ ub F' :
  inst_ok W Φ ρ → ub_below W ub F' →
  inst_ok W (<[φ := ub]> Φ) (λ ψ, if decide (ψ = φ) then F' else ρ ψ).
Proof.
  intros Hρ Hub ψ u Hu. cbv beta. destruct (decide (ψ = φ)) as [->|Hne].
  - by simplify_map_eq.
  - simplify_map_eq. by apply Hρ.
Qed.

Lemma sf_inst_fresh ρ φ F' :
  sf_inst (λ ψ, if decide (ψ = φ) then F' else ρ ψ) (∅, Some φ) = F'.
Proof. unfold sf_inst. simpl. rewrite decide_True; [|done]. by rewrite union_empty_l_L. Qed.

Lemma inst_ok_pinst_insert W Φ σ φ ub ρ F' :
  inst_ok W (fhyps_pinst σ Φ) ρ → ub_below W (pt_inst σ <$> ub) F' →
  inst_ok W (fhyps_pinst σ (<[φ := ub]> Φ)) (λ ψ, if decide (ψ = φ) then F' else ρ ψ).
Proof. intros Hρ Hub. unfold fhyps_pinst. rewrite fmap_insert. by apply inst_ok_insert. Qed.

(** Typed terms are well formed, read off the finitary derivation: the
    box body is typed once, so no instance of C is needed. *)
Lemma unlimited_pinst_iff σ U : unlimited (pinst_ty σ U) ↔ unlimited U.
Proof. by destruct U. Qed.

Lemma term_wf_lenv_pinst σ Θ Δ e : term_wf Θ (lenv_pinst σ Δ) e ↔ term_wf Θ Δ e.
Proof.
  assert (∀ x, lenv_avail (lenv_pinst σ Δ) x ↔ lenv_avail Δ x) as Ha.
  { intros x. unfold lenv_avail. rewrite lenv_pinst_lookup.
    destruct (Δ !! x) as [[T|]|]; simpl; split; intros [U HU]; simplify_eq; eauto. }
  assert (∀ x, lenv_avail_lin (lenv_pinst σ Δ) x ↔ lenv_avail_lin Δ x) as Hl.
  { intros x. unfold lenv_avail_lin. rewrite lenv_pinst_lookup.
    destruct (Δ !! x) as [[T|]|]; simpl; split; intros (U & HU & Hn); simplify_eq.
    + eexists. split; [reflexivity|]. by rewrite <-(unlimited_pinst_iff σ).
    + eexists. split; [reflexivity|]. by rewrite unlimited_pinst_iff. }
  unfold term_wf. split; intros (Hfc & Hfv & Hrv); split_and!; try done.
  - eapply allfv_mono; [|exact Hfv]. intros x. apply Ha.
  - intros x Hx. apply Hrv, Hl, Hx.
  - eapply allfv_mono; [|exact Hfv]. intros x. apply Ha.
  - intros x Hx. apply Hrv, Hl, Hx.
Qed.

Lemma typed_term_wf_s W Φ Ψ Θ Δ F e T : typed W Φ Ψ Θ Δ F e T → term_wf Θ Δ e.
Proof.
  unfold term_wf. induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk _
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ _ _
    |Φ Ψ Θ Δ F e T U ub lb φ _ _ _ IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ _ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Δ F e T U _ IH
    |Φ Ψ Θ Δ F e T U _ IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ _ IH0 _ IH1 _ IH2
    |Φ Ψ Δ F e m C ub T φ HΔ _ _ IH
    |Φ Ψ Θ Δ' Δ F e T Hwk _ IH
    |Φ Ψ Θ Δ U F e T Hu _ IH
    |Φ Ψ Θ Δ F e T T' _ _ IH].
  (* E-Unit *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Const *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-LVar *)
  - split_and!; simpl.
    + by rewrite dom_empty_L.
    + destruct Ho as [Hlk _]. by exists T.
    + intros x' (T' & Hx' & _). destruct Ho as [_ Huniq].
      by destruct (Huniq x' T' Hx') as [-> _].
  (* E-Ch *)
  - split_and!; simpl; [by rewrite dom_singleton_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Abs *)
  - destruct IH as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-App *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Pair *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Let* *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-LetPair *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl.
        -- intros _. done.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply (Hrv2 (S (S x))). exists T'. auto.
  (* E-Inj *)
  - exact IH.
  - exact IH.
  (* E-Case *)
  - destruct IH0 as (Hfc0 & Hfv0 & Hrv0). destruct IH1 as (Hfc1 & Hfv1 & Hrv1).
    destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split_and!.
      * eapply allfv_mono; [|exact Hfv0]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv1]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
      * eapply allfv_mono; [|exact Hfv2]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv0. exists T'. auto.
      * right. left. apply (Hrv1 (S x)). exists T'. auto.
  (* E-Exp *)
  - destruct (proj1 (term_wf_lenv_pinst _ _ _ _) IH) as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-Weak *)
  - destruct IH as (Hfc & Hfv & Hrv). split_and!; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros x Hx. eauto using lenv_wk_avail.
    + intros x Hx. apply Hrv. eauto using lenv_wk_avail_lin.
  (* E-Contract *)
  - destruct IH as (Hfc & Hfv & Hrv). split_and!.
    + by rewrite fchans_rename.
    + apply allfv_rename. eapply allfv_mono; [|exact Hfv].
      intros [|[|x]] (T' & HT'); simpl in *; by exists T'.
    + intros [|x] (T' & Hx & Hnb); simpl in Hx.
      * simplify_eq. by destruct (Hnb Hu).
      * apply (freevar_rename e (S (S x)) pred). apply Hrv. by exists T'.
  (* E-Conv *)
  - exact IH.
Qed.

Ltac frame_pinst :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?heads_pinst, ?opt_heads_pinst,
    <-?set_map_union_L, <-?sf_inst_union, <-?sf_pinst_union.

(** Frame instantiation and point substitution in one induction: the
    frame variables become frames above their hypotheses at a later
    world W₁, the point variables become points by σ. A box body is
    typed with its ιs as variables, so the box case substitutes the
    instance xs there and the outer σ beyond (plist_pup_shift). *)
Lemma typed_ityped W Φ Ψ Θ Δ F e T :
  typed W Φ Ψ Θ Δ F e T →
  ∀ W1 ρ σ, world_wf W → wext W W1 → inst_ok W1 (fhyps_pinst σ Φ) ρ →
  pcs_hold (w_lt W1) (pcs_inst σ Ψ) →
  ityped W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_inst ρ (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk Hks
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ Hs Hk
    |Φ Ψ Θ Δ F e T U ub lb φ Hφ Hlb Hb IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |Φ Ψ Δ F e m C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH]; intros W1 ρ σ HW HW1 Hρ HΨ;
    pose proof HW1 as (HN & He & Hl & HS).
  - rewrite tenv_pinst_empty. apply it_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply it_konst; [by apply lenv_empty_pinst|].
    apply (konst_ty_pinst W W1 σ HW HW1 (slt W Ψ)); [|done|done].
    intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
  - rewrite tenv_pinst_empty. apply it_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply it_chan; [by apply lenv_empty_pinst|done|by apply (pinst_eq W)].
  - cbn [pinst_ty]. apply it_lam.
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst W W1 σ HW HW1 Ψ).
    + intros W2 F' HW2 Hub'. rewrite <-(sf_inst_fresh ρ φ F'), <-(sf_pinst_fresh σ φ).
      apply (IH W2 _ σ HW (wext_trans _ _ _ HW1 HW2)).
      * apply inst_ok_pinst_insert; [exact (inst_ok_mono _ _ _ _ HW2 Hρ)|exact Hub'].
      * exact (pcs_hold_mono_w _ _ _ HW2 HΨ).
  - apply (it_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + apply (ub_below_s_inst W1 W1 (fhyps_pinst σ Φ)); [apply HS|exact (wext_refl _ HS)|done|].
      apply (ub_below_s_pinst W W1 σ Ψ []); [done|done| |done].
      intros p Hp. apply sl_w. by apply HΨ.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (it_pair W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (it_letu W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply IH2.
  - apply (it_letp W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. apply it_inj1. by apply IH.
  - cbn [pinst_ty]. apply it_inj2. by apply IH.
  - apply (it_case W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 W1 ρ σ).
    + by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. rewrite tenv_pinst_empty. apply it_box; [by apply lenv_unl_pinst| |].
    { pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ Hb) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf.
      change (term_wf ∅ (lenv_pinst σ (Some (TBox m C ub T) :: Δ)) e).
      by rewrite term_wf_lenv_pinst. }
    intros W2 xs F' HW2 Hxs HC Hub'.
    assert (∀ a, pt_inst (pt_inst (plist xs) ∘ pup m σ) (pshift m a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    assert (lenv_pinst (pt_inst (plist xs) ∘ pup m σ) (lenv_pinst (pshift m) (Some (TBox m C ub T) :: Δ))
            = lenv_pinst σ (Some (TBox m C ub T) :: Δ)) as E1.
    { rewrite lenv_pinst_comp. apply lenv_pinst_ext. exact Hsh. }
    assert (pinst_ty (pt_inst (plist xs) ∘ pup m σ) T = ty_inst xs (pinst_ty (pup m σ) T)) as E2.
    { unfold ty_inst. by rewrite pinst_ty_comp. }
    assert (fhyps_pinst (pt_inst (plist xs) ∘ pup m σ) (fhyps_pinst (pshift m) Φ)
            = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros i [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (pcs_inst (pt_inst (plist xs) ∘ pup m σ) (pcs_inst (pshift m) Ψ ++ C)
            = pcs_inst σ Ψ ++ pcs_inst (plist xs) (pcs_inst (pup m σ) C)) as E4.
    { rewrite pcs_inst_app, !pcs_comp. f_equal. apply pcs_inst_ext. intros a. apply Hsh. }
    pose proof (IH W2 (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                  (pt_inst (plist xs) ∘ pup m σ) HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    rewrite tenv_pinst_empty, sf_pinst_fresh, sf_inst_fresh, E1, E2, E4 in Hb'.
    apply Hb'.
    + apply inst_ok_pinst_insert.
      * rewrite E3. exact (inst_ok_mono _ _ _ _ HW2 Hρ).
      * destruct ub as [u|]; simpl in *; [|done]. by rewrite pt_inst_comp in Hub'.
    + intros p Hp. apply elem_of_app in Hp as [Hp|Hp].
      * exact (pcs_hold_mono_w _ _ _ HW2 HΨ p Hp).
      * exact (HC p Hp).
  - eapply it_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply it_contract; [by apply unlimited_pinst|by apply (IH W1 ρ σ)].
  - eapply it_conv; [by apply eqT_pinst|by apply IH].
Qed.


(** ** The substitution lemma on its own

    Instantiating point variables by points preserves derivations at
    the same world. [typed_ityped] composes this substitution with
    frame instantiation; the fundamental theorem needs only that. *)

Lemma kscoped_pinst peq plt pk k T σ :
  konst_ty peq plt pk k T → kscoped k T → kscoped k (pinst_ty σ T).
Proof. destruct 1; simpl; auto. Qed.

Lemma fhyps_pinst_insert σ Φ φ u :
  fhyps_pinst σ (<[φ := u]> Φ) = <[φ := pt_inst σ <$> u]> (fhyps_pinst σ Φ).
Proof. unfold fhyps_pinst. by rewrite fmap_insert. Qed.

Lemma fhyps_pinst_dom σ Φ : dom (fhyps_pinst σ Φ) = dom Φ.
Proof. unfold fhyps_pinst. by rewrite dom_fmap_L. Qed.

Lemma fhyps_pinst_comp_ext τ σ τ' σ' Φ :
  (∀ a, pt_inst τ (σ a) = pt_inst τ' (σ' a)) →
  fhyps_pinst τ (fhyps_pinst σ Φ) = fhyps_pinst τ' (fhyps_pinst σ' Φ).
Proof.
  intros H. unfold fhyps_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
  intros i [u|] _; simpl; [|done]. f_equal. rewrite !pt_inst_comp. by apply pt_inst_ext.
Qed.

Lemma pup_pshift m σ a : pt_inst (pup m σ) (pshift m a) = pt_inst (pshift m) (σ a).
Proof.
  unfold pshift. rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
  by replace (a + m - m) with a by lia.
Qed.

Lemma typed_pinst W Φ Ψ Θ Δ F e T :
  strict W → typed W Φ Ψ Θ Δ F e T →
  ∀ σ Ψ', pcs_hold (slt W Ψ') (pcs_inst σ Ψ) →
  typed W (fhyps_pinst σ Φ) Ψ' (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_pinst σ F) e (pinst_ty σ T).
Proof.
  intros HW. pose proof (proj1 HW) as Hwf. pose proof (wext_refl _ HW) as HWW.
  induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk Hks
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ Hs Hk
    |Φ Ψ Θ Δ F e T U ub lb φ Hφ Hlb Hb IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |Φ Ψ Δ F e m C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH]; intros σ Ψ' HΨ.
  - rewrite tenv_pinst_empty. apply t_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply t_konst; [by apply lenv_empty_pinst| |].
    + apply (konst_ty_pinst W W σ Hwf HWW (slt W Ψ)); [|done|done].
      intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
    + by apply (kscoped_pinst (w_eq W) (slt W Ψ) (pt_known W)).
  - rewrite tenv_pinst_empty. apply t_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply t_chan; [by apply lenv_empty_pinst|done|by apply (pinst_eq W)].
  - cbn [pinst_ty]. apply (t_lam W _ _ _ _ _ _ _ _ _ _ φ).
    + by rewrite fhyps_pinst_dom.
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst_s W W σ Hwf HWW Ψ).
    + pose proof (IH σ Ψ' HΨ) as H. by rewrite fhyps_pinst_insert, sf_pinst_fresh in H.
  - apply (t_app W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + by apply (ub_below_s_pinst W W σ Ψ Ψ').
    + frame_pinst. by apply (IH1 σ Ψ').
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (t_pair W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (t_letu W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply IH2.
  - apply (t_letp W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. apply t_inj1. by apply IH.
  - cbn [pinst_ty]. apply t_inj2. by apply IH.
  - apply (t_case W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst W).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 σ Ψ').
    + by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (t_box W _ _ _ _ _ _ _ _ _ φ); [by apply lenv_unl_pinst|by rewrite fhyps_pinst_dom|].
    assert (pcs_hold (slt W (pcs_inst (pshift m) Ψ' ++ pcs_inst (pup m σ) C))
              (pcs_inst (pup m σ) (pcs_inst (pshift m) Ψ ++ C))) as HΨ'.
    { rewrite pcs_inst_app, pcs_comp,
        (pcs_inst_ext (pt_inst (pup m σ) ∘ pshift m) (pt_inst (pshift m) ∘ σ) Ψ)
        by (intros a; apply pup_pshift).
      rewrite <-pcs_comp. intros p Hp. apply elem_of_app in Hp as [Hp|Hp].
      - apply (pcs_hold_inst (slt W Ψ') _ (pshift m) (pcs_inst σ Ψ)); [|exact HΨ|exact Hp].
        intros x y Hxy. apply (slt_pinst_s W W (pshift m) Hwf HWW Ψ'); [|exact Hxy].
        intros [x' y'] Hq. apply sl_h, elem_of_app. by left.
      - destruct p as [x y]. apply sl_h, elem_of_app. by right. }
    pose proof (IH (pup m σ) _ HΨ') as H.
    rewrite tenv_pinst_empty, sf_pinst_fresh, fhyps_pinst_insert in H.
    rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
    rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
      by apply pup_pshift.
    exact H.
  - eapply t_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply t_contract; [by apply unlimited_pinst|by apply (IH σ Ψ')].
  - eapply t_conv; [by apply eqT_pinst|by apply IH].
Qed.


(** A closed derivation: no frame variables, no hypotheses, and the
    identity substitution. *)
Lemma typed_ityped_closed W Θ Δ F e T :
  strict W → typed W ∅ [] Θ Δ (F, None) e T → ityped W Θ Δ F e T.
Proof.
  intros HW Ht.
  pose proof (typed_ityped _ _ _ _ _ _ _ _ Ht W (λ _, ∅) pvar (proj1 HW) (wext_refl _ HW)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  unfold sf_inst in H. simpl in H. rewrite union_empty_r_L in H.
  apply H.
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - intros p Hp. by apply elem_of_nil in Hp.
Qed.

Lemma typed_term_wf W Θ Δ F e T :
  typed W ∅ [] Θ Δ (F, None) e T → strict W → term_wf Θ Δ e.
Proof. intros Ht _. exact (typed_term_wf_s _ _ _ _ _ _ _ _ Ht). Qed.

(** ** The fundamental theorem for terms *)

Theorem fundamental W Θ Δ F e T :
  typed W ∅ [] Θ Δ (F, None) e T → strict W → sem_typed W Θ Δ F e T.
Proof. intros Ht HW. apply ifundamental; [|done]. by apply typed_ityped_closed. Qed.

(** ** Processes

    P-Term and P-Connect of §9. The side conditions are the implicit
    well-formedness of the spec: Θ_B holds both ends, dual at aliased
    points, of exactly the channels of C₀; the unions C₁ ⊍ C₂ ⊍ C₀ and
    Σ₁, Σ₂, Σ_C are disjoint; the cut ends are dual at aliased points. *)

Inductive ptyped (W : world) : senv → proc → ty → Prop :=
  | pt_term Σ ΘB C0 t T :                               (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W ∅ [] (tenv_of Σ ∪ ΘB) [] (∅, None) t T →
      ptyped W Σ (C0, {[+ t +]}) T
  | pt_connect Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :         (* P-Connect *)
      ptyped W (Σ1 ∪ ΣC) (C1, E1) T → ptyped W (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' → w_eq W e.2 e'.2 ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      ptyped W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma ptyped_prim W Σ p T : ptyped W Σ p T → prim T.
Proof. induction 1; auto. Qed.

(** One world for both components: W ⊔ W lies below W. *)
Lemma wext_join_self W : strict W → wext (wjoin W W) W.
Proof.
  intros HW.
  destruct (wgen_in_world W (λ x y, w_eq W x y ∨ w_eq W x y)
              (λ x y, w_lt W x y ∨ w_lt W x y)) as [Heq Hlt];
    [apply HW|naive_solver|naive_solver|].
  split_and!; [simpl; set_solver|exact Heq|exact Hlt|exact HW].
Qed.

Theorem fundamental_proc W Σ p T : ptyped W Σ p T → strict W → sem_ptyped W Σ p T.
Proof.
  induction 1 as [Σ ΘB C0 t T HT Hd Hdj Hb Hdu Ht
                 |Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ?]; intros HW.
  - apply (Prel_term W Σ ΘB C0); try done. by apply fundamental.
  - assert (strict (wjoin W W)) as HWW by (by apply wjoin_sub_strict, wext_refl).
    intros n. eapply Prel_mono; [apply HWW|by apply wext_join_self|].
    revert n. apply (Prel_connect W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
    + exact (ptyped_prim _ _ _ _ H1).
    + by apply IH1.
    + by apply IH2.
    + intros c e e' He He'. destruct (Hcut c e e' He He') as [Heq Hs].
      split; [by apply wjoin_l|done].
    + apply HW.
    + apply HW.
Qed.

(** ** Soundness: typed closed configurations are deadlock free *)

Theorem soundness W p T : strict W → ptyped W ∅ p T → deadlock_free p.
Proof. intros HW Hp. apply (adequacy W T p). by apply fundamental_proc. Qed.
