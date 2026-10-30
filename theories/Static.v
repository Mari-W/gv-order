(** * The static system (spec §9, with sharp edges 52 and 53)

    Θ; Δ ⊢^F_G t : T and Σ ⊢_G p : T. The facts G enter through the
    world W_G they generate: the judgments are indexed by a world W,
    and every side condition on points is read in W (≡_G as [w_eq W],
    ≺_G as [w_lt W]). Fundamental and soundness ask W strict.

    Sharp edges 53: the fresh point variables of E-Abs (μ, with only
    u ≺ μ) and of E-Exp (μ, with only u[ιs] ≺ μ, and the box's own ιs)
    are read as "every": the body is typed in every later world, under
    every frame above the (instantiated) upper point, at every instance
    of ιs. A fresh μ about which only u ≺ μ is known can be any frame
    above u, so the rule says the same, without fact schemas or a
    substitution lemma for derivations. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export TermRules2.

Set Default Proof Using "All".

(** ** Terms *)

Inductive typed (W : world) : tenv → lenv → gset point → expr → ty → Prop :=
  | t_unit Δ F :                                        (* E-Unit *)
      lenv_empty Δ →
      typed W ∅ Δ F EUnit TUnit
  | t_konst Δ F k T :                                   (* E-Const *)
      lenv_empty Δ → konst_ty (w_eq W) (w_lt W) (pt_known W) k T →
      typed W ∅ Δ F (Konst k) T
  | t_var Δ F x T :                                     (* E-LVar *)
      lenv_only Δ x T →
      typed W ∅ Δ F (Var x) T
  | t_chan Δ F c s k s' y :                             (* E-Ch, ι′ ≡_G ι *)
      lenv_empty Δ → seq s s' → w_eq W k y →
      typed W {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | t_lam Θ Δ F e T U ub lb :                           (* E-Abs *)
      lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
      (∀ W1 F', wext W W1 → ub_below W1 ub F' → typed W1 Θ (Some T :: Δ) F' e U) →
      typed W Θ Δ F (Lam e) (TLolli ub lb T U)
  | t_app Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :           (* E-App *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
      typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
      typed W Θ Δ F (App e1 e2) U
  | t_pair Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :                (* E-Pair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      typed W Θ2 Δ2 (F ∪ heads T) e2 U →
      typed W Θ Δ F (Pair e1 e2) (TProd T U)
  | t_letu Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :                  (* E-Let* *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      typed W Θ2 Δ2 F e2 T →
      typed W Θ Δ F (LetU e1 e2) T
  | t_letp Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :            (* E-LetPair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      typed W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      typed W Θ Δ F (LetP e1 e2) T
  | t_inj1 Θ Δ F e T U :                                (* E-Inj *)
      typed W Θ Δ F e T → typed W Θ Δ F (Inj1 e) (TSum T U)
  | t_inj2 Θ Δ F e T U :
      typed W Θ Δ F e U → typed W Θ Δ F (Inj2 e) (TSum T U)
  | t_case Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :          (* E-Case *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      typed W Θ2 (Some T1 :: Δ2) F e1 T →
      typed W Θ2 (Some T2 :: Δ2) F e2 T →
      typed W Θ Δ F (Case e e1 e2) T
  | t_box Δ F e m ub T :                                (* E-Exp *)
      lenv_unl Δ →
      (∀ W1 xs F', wext W W1 → length xs = m → ub_below W1 (pt_inst (plist xs) <$> ub) F' →
         typed W1 ∅ (Some (TBox m ub T) :: Δ) F' e (ty_inst xs T)) →
      typed W ∅ Δ F (EBox e) (TBox m ub T)
  | t_wk Θ Δ' Δ F e T :                                 (* E-Weak *)
      lenv_wk Δ' Δ → typed W Θ Δ' F e T → typed W Θ Δ F e T
  | t_contract Θ Δ U F e T :                            (* E-Contract *)
      unlimited U →
      typed W Θ (Some U :: Some U :: Δ) F e T →
      typed W Θ (Some U :: Δ) F (rename pred e) T
  | t_conv Θ Δ F e T T' :                               (* E-Conv *)
      teq T T' → typed W Θ Δ F e T → typed W Θ Δ F e T'.

(** E-Force is E-App at the constant force. *)
Lemma typed_force W Θ Δ F e m ub T xs :
  world_wf W → length xs = m → ub_below W (pt_inst (plist xs) <$> ub) F →
  typed W Θ Δ F e (TBox m ub T) →
  typed W Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs Hub He.
  eapply (t_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply t_konst; [apply lenv_empty_nones|]. by constructor.
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

Lemma typed_term_wf W Θ Δ F e T : typed W Θ Δ F e T → strict W → term_wf Θ Δ e.
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
    |W Δ F e m ub T HΔ _ IH
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
  - destruct (IH W (replicate m (pconst 0)) ∅ (wext_refl _ HW) (length_replicate _ _)
                (ub_below_empty _ _) HW) as (Hfc & Hfv & Hrv).
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

(** ** The fundamental theorem for terms *)

Theorem fundamental W Θ Δ F e T : typed W Θ Δ F e T → strict W → sem_typed W Θ Δ F e T.
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
    |W Δ F e m ub T HΔ Hb IH
    |W Θ Δ' Δ F e T Hwk H IH
    |W Θ Δ U F e T Hu H IH
    |W Θ Δ F e T T' Hteq H IH]; intros Ht0 HW.
  - by apply sem_typed_unit.
  - by apply sem_typed_konst.
  - by apply sem_typed_var.
  - by apply sem_typed_chan.
  - apply sem_typed_lam; [| |].
    + eapply (typed_term_wf W); [|exact HW].
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
  - apply sem_typed_box; [done| |].
    + eapply (typed_term_wf W); [|exact HW].
      apply (Hb W (replicate m (pconst 0)) ∅ (wext_refl _ HW) (length_replicate _ _)
               (ub_below_empty _ _)).
    + intros W1 xs F' HW1 Hxs Hub'. apply IH; [done..| |apply HW1]. by apply Hb.
  - eapply sem_typed_wk; [done|by apply IH].
  - apply sem_typed_contract; [done|by apply IH].
  - eapply sem_typed_teq; [done|by apply IH].
Qed.

(** ** Processes

    P-Term and P-Connect of §9. The side conditions are the implicit
    well-formedness of the spec: Θ_B holds both ends, dual at aliased
    points, of exactly the channels of C₀; the unions C₁ ⊍ C₂ ⊍ C₀ and
    Σ₁, Σ₂, Σ_C are disjoint; the cut ends are dual at aliased points. *)

Inductive ptyped (W : world) : senv → proc → ty → Prop :=
  | pt_term Σ ΘB C0 t T :                               (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
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
