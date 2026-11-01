(** * The fundamental theorem and soundness of the static system

    [typed_sem_rules] instantiates the frame variables and substitutes
    points in one induction, and yields the infinitary judgment of
    SemanticRules.v. [typed_pinst] is the substitution lemma on its own.
    [fundamental], [fundamental_proc] and [soundness] follow. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Typing.

Set Default Proof Using "All".

(** ** Small equations for fresh points *)

Lemma lenv_pinst_cons_some σ T Δ : lenv_pinst σ (Some T :: Δ) = Some (pinst_ty σ T) :: lenv_pinst σ Δ.
Proof. done. Qed.

Lemma pinst_ty_sess σ s x : pinst_ty σ (TSess s x) = TSess s (pt_inst σ x).
Proof. done. Qed.

Lemma pup1_pvar0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Lemma plist1_pup_pvar0 x σ : pt_inst (pt_inst (plist [x]) ∘ pup 1 σ) (pvar 0) = x.
Proof. rewrite pt_inst_pvar_at. unfold compose, pup. rewrite decide_True by lia. by rewrite pt_inst_pvar_at. Qed.

(** ** Helpers for E-Pack and E-Open (sharp edges 97) *)

Lemma lenv_pinst_insert σ Δ i o :
  lenv_pinst σ (<[i := o]> Δ) = <[i := pinst_ty σ <$> o]> (lenv_pinst σ Δ).
Proof. unfold lenv_pinst. apply list_fmap_insert. Qed.

Lemma unl_pinst_iff σ U : unlimited (pinst_ty σ U) ↔ unlimited U.
Proof. by destruct U. Qed.

(** The availability of an opened hypothesis is that of the
    existential one. *)
Lemma open_avail σ Δ i lb m C T x :
  Δ !! i = Some (Some (TEx lb m C T)) →
  lenv_avail (<[i := Some T]> (lenv_pinst σ Δ)) x ↔ lenv_avail Δ x.
Proof.
  intros Hi. unfold lenv_avail. destruct (decide (x = i)) as [->|Hne].
  - assert (<[i:=Some T]> (lenv_pinst σ Δ) !! i = Some (Some T)) as Heq.
    { apply list_lookup_insert_eq. unfold lenv_pinst. rewrite length_fmap. by eapply lookup_lt_Some. }
    split; intros _; eauto.
  - assert (<[i:=Some T]> (lenv_pinst σ Δ) !! x = lenv_pinst σ Δ !! x) as Heq
      by (apply list_lookup_insert_ne; congruence).
    rewrite Heq, lenv_pinst_lookup.
    destruct (Δ !! x) as [[T'|]|]; simpl; split; intros [U' HU']; simplify_eq; eauto.
Qed.

Lemma open_avail_lin σ Δ i lb m C T x :
  Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
  lenv_avail_lin (<[i := Some T]> (lenv_pinst σ Δ)) x ↔ lenv_avail_lin Δ x.
Proof.
  intros Hi Hnu. unfold lenv_avail_lin. destruct (decide (x = i)) as [->|Hne].
  - assert (<[i:=Some T]> (lenv_pinst σ Δ) !! i = Some (Some T)) as Heq.
    { apply list_lookup_insert_eq. unfold lenv_pinst. rewrite length_fmap. by eapply lookup_lt_Some. }
    split; intros _.
    + exists (TEx lb m C T). split; [done|]. intros [].
    + exists T. by split.
  - assert (<[i:=Some T]> (lenv_pinst σ Δ) !! x = lenv_pinst σ Δ !! x) as Heq
      by (apply list_lookup_insert_ne; congruence).
    rewrite Heq, lenv_pinst_lookup.
    destruct (Δ !! x) as [[T'|]|]; simpl; split; intros (U & HU & Hn); simplify_eq.
    + eexists. split; [reflexivity|]. by rewrite <-(unl_pinst_iff σ).
    + eexists. split; [reflexivity|]. by rewrite unl_pinst_iff.
Qed.

(** ** Lemmas on available variables, for [typed_term_wf_s] *)

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

(** ** Frame instantiation

    Replacing the frame variables by concrete frames that meet the
    hypotheses, at any later world, turns a derivation into one of the
    infinitary judgment. Monotonicity in W is folded in: typing reads W
    only through facts, and facts survive W ⊑ W₁. *)

Lemma sf_inst_union ρ F X : sf_inst ρ (sf_union F X) = sf_inst ρ F ∪ X.
Proof. destruct F as [P o]; unfold sf_inst, sf_union; simpl; set_solver. Qed.

(** The flag of a frame stands for [pbot] (sharp edges 103). *)
Lemma sf_inst_unionb ρ F X b : sf_inst ρ (sf_unionb F X b) = sf_inst ρ F ∪ (X ∪ bot_pts b).
Proof.
  destruct b; unfold sf_unionb; [|rewrite sf_inst_union; simpl; set_solver].
  destruct F as [P o]; unfold sf_inst; simpl. destruct o as [[]|]; simpl; set_solver.
Qed.

(** Frame instantiation: a node stands for the points it denotes. *)
Definition node_den (ρ : nat → gset point) (a : node) (z : point) : Prop :=
  match a with NP x => z = x | NV φ => z ∈ ρ φ end.

Lemma ub_below_s_inst W W1 Φ ρ ub F :
  world_wf W → wext W W1 → inst_ok W1 Φ ρ → ub_below_s W [] Φ ub F →
  ub_below W1 ub (sf_inst ρ F).
Proof.
  intros HW HW1 Hρ. destruct ub as [x|]; [|done]. intros (HP & Hφ & Hb). simpl.
  pose proof (wext_wf _ _ HW1) as Hwf. pose proof HW1 as (_ & He & Hl & _).
  assert (∀ a b, fl (FCtx W [] Φ) a b →
            ∀ a' b', node_den ρ a a' → node_den ρ b b' → w_lt W1 a' b') as Hm.
  { refine (proj2 (fl_map _ (w_eq W1)
      (λ a b, ∀ a' b', node_den ρ a a' → node_den ρ b b' → w_lt W1 a' b') id id
      _ _ _ _ _ _ _ _ _ _ _ _ _)); unfold id; simpl.
    - intros x0 y0 H. by apply He.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - apply (wf_eq_refl _ Hwf).
    - apply (wf_eq_sym _ Hwf).
    - apply (wf_eq_trans _ Hwf).
    - apply (wf_eq_shift _ Hwf).
    - apply (wf_eq_slot _ Hwf).
    - intros x0 y0 H ? ? -> ->. by apply Hl.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - intros φ u Hu ? b' -> Hb'. exact (Hρ φ (Some u) Hu b' Hb').
    - intros x0 x' b Hx H ? b' -> Hb'.
      exact (wf_lt_eq _ Hwf x0 x' b' b' Hx (H x' b' eq_refl Hb') (wf_eq_refl _ Hwf b')).
    - intros a y y' H Hy a' ? Ha' ->.
      exact (wf_lt_eq _ Hwf a' a' y y' (wf_eq_refl _ Hwf a') (H a' y' Ha' eq_refl) Hy).
    - intros a y b H1 H2 a' b' Ha' Hb'.
      exact (wf_lt_trans _ Hwf a' y b' (H1 a' y Ha' eq_refl) (H2 y b' eq_refl Hb')). }
  intros y Hy. unfold sf_inst in Hy. rewrite Hb in Hy. simpl in Hy.
  rewrite union_empty_r_L in Hy. apply elem_of_union in Hy as [Hy|Hy].
  - exact (Hm _ _ (HP y Hy) x y eq_refl eq_refl).
  - destruct (fs_var F.2) as [φ|] eqn:Hv; [|by apply elem_of_empty in Hy].
    exact (Hm _ _ (Hφ φ eq_refl) x y eq_refl Hy).
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
  sf_inst (λ ψ, if decide (ψ = φ) then F' else ρ ψ) (∅, Some (FVar φ)) = F'.
Proof. unfold sf_inst. simpl. rewrite decide_True; [|done]. by rewrite union_empty_l_L, union_empty_r_L. Qed.

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
    |Φ Ψ Θ Δ F e T T' _ _ IH
    |Φ Ψ Θ Δ F e lb m C T xs _ _ _ _ _ IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu _ IH
    |Φ Ψ Δ F v m C T Hv Hu _ IH
    |Φ Ψ Θ Δ F e m C T xs _ _ _ _ IH].
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
  (* E-Pack *)
  - exact IH.
  (* E-Open *)
  - destruct IH as (Hfc & Hfv & Hrv). split_and!.
    + rewrite Hfc. unfold tenv_pinst. by rewrite dom_fmap_L.
    + eapply allfv_mono; [|exact Hfv]. intros x. by apply (open_avail _ _ _ lb m C).
    + intros x Hx. apply Hrv. by apply (open_avail_lin _ _ _ lb m C).
  (* E-Gen *)
  - exact (proj1 (term_wf_lenv_pinst _ _ _ _) IH).
  (* E-Inst *)
  - exact IH.
Qed.

Ltac frame_pinst :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?heads_pinst, ?opt_heads_pinst,
    ?lenv_bot_pinst, ?hbot_pinst,
    <-?set_map_union_L, <-?sf_inst_unionb, <-?sf_inst_union, <-?sf_pinst_unionb, <-?sf_pinst_union.

(** Frame instantiation and point substitution in one induction: the
    frame variables become frames above their hypotheses at a later
    world W₁, the point variables become points by σ. A box body is
    typed with its ιs as variables, so the box case substitutes the
    instance xs there and the outer σ beyond (plist_pup_shift). *)
Lemma typed_sem_rules W Φ Ψ Θ Δ F e T :
  typed W Φ Ψ Θ Δ F e T →
  ∀ W1 ρ σ, world_wf W → wext W W1 → inst_ok W1 (fhyps_pinst σ Φ) ρ →
  hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
  sem_rules W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_inst ρ (sf_pinst σ F)) e (pinst_ty σ T).
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
    |Φ Ψ Θ Δ F e T T' Hteq H IH
    |Φ Ψ Θ Δ F e lb m C T xs Hxs HK HC Hlb H IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu Hb IH
    |Φ Ψ Δ F v m C T Hv Hu Hb IH
    |Φ Ψ Θ Δ F e m C T xs Hxs HK HC H IH]; intros W1 ρ σ HW HW1 Hρ HΨ;
    pose proof HW1 as (HN & He & Hl & HS).
  - rewrite tenv_pinst_empty. apply sr_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply sr_konst; [by apply lenv_empty_pinst|].
    apply (konst_ty_pinst W W1 σ HW HW1 (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
    + intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
    + intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    + intros x Hx. by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
  - rewrite tenv_pinst_empty. apply sr_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply sr_chan; [by apply lenv_empty_pinst|done|by apply (seqs_pinst W W1 σ HW HW1 Ψ)].
  - cbn [pinst_ty]. unfold lb_below_hb in Hlb. destruct (lenv_bot Δ) eqn:Hbot; [done|].
    apply sr_lam.
    + assert (term_wf Θ (lenv_pinst σ (Some T :: Δ)) e) as (Hfc & Hwf)
        by (rewrite term_wf_lenv_pinst; exact (typed_term_wf_s _ _ _ _ _ _ _ _ Hb)).
      split; [unfold tenv_pinst; by rewrite dom_fmap_L|exact Hwf].
    + by rewrite lenv_bot_pinst.
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst W W1 σ HW HW1 Ψ).
    + intros W2 F' HW2 Hub'. rewrite <-(sf_inst_fresh ρ φ F'), <-(sf_pinst_fresh σ φ).
      apply (IH W2 _ σ HW (wext_trans _ _ _ HW1 HW2)).
      * apply inst_ok_pinst_insert; [exact (inst_ok_mono _ _ _ _ HW2 Hρ)|exact Hub'].
      * exact (hyps_hold_wext _ _ _ HW2 HΨ).
  - apply (sr_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + apply (ub_below_s_inst W1 W1 (fhyps_pinst σ Φ)); [apply HS|exact (wext_refl _ HS)|done|].
      apply (ub_below_s_pinst W W1 σ Ψ []); [done|done| |done].
      by apply (hyps_hold_ground W W1 σ HW HW1).
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (sr_pair W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (sr_letu W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply IH2.
  - apply (sr_letp W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. apply sr_inj1. by apply IH.
  - cbn [pinst_ty]. apply sr_inj2. by apply IH.
  - apply (sr_case W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 W1 ρ σ).
    + by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. rewrite tenv_pinst_empty. apply sr_box; [by apply lenv_unl_pinst| |].
    { pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ Hb) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf.
      change (term_wf ∅ (lenv_pinst σ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) e).
      by rewrite term_wf_lenv_pinst. }
    intros W2 xs F' HW2 Hxs HC HK Hub'. subst m.
    assert (∀ a, pt_inst (pt_inst (plist xs) ∘ pup (length xs) σ) (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    set (m := length xs).
    assert (lenv_pinst (pt_inst (plist xs) ∘ pup m σ) (lenv_pinst (pshift m) (Some (TBox m C (TLolli ub None TUnit T)) :: Δ))
            = lenv_pinst σ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) as E1.
    { rewrite lenv_pinst_comp. apply lenv_pinst_ext. exact Hsh. }
    assert (pinst_ty (pt_inst (plist xs) ∘ pup m σ) T = ty_inst xs (pinst_ty (pup m σ) T)) as E2.
    { unfold ty_inst. by rewrite pinst_ty_comp. }
    assert (fhyps_pinst (pt_inst (plist xs) ∘ pup m σ) (fhyps_pinst (pshift m) Φ)
            = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros i [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst (pt_inst (plist xs) ∘ pup m σ)
              (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    pose proof (IH W2 (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                  (pt_inst (plist xs) ∘ pup m σ) HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    fold m in Hb'. rewrite tenv_pinst_empty, sf_pinst_fresh, sf_inst_fresh, E1, E2, E4 in Hb'.
    apply Hb'.
    + apply inst_ok_pinst_insert.
      * rewrite E3. exact (inst_ok_mono _ _ _ _ HW2 Hρ).
      * destruct ub as [u|]; simpl in *; [|done]. by rewrite pt_inst_comp in Hub'.
    + apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done.
  - eapply sr_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply sr_contract; [by apply unlimited_pinst|by apply (IH W1 ρ σ)].
  - eapply sr_conv; [by apply (steq_teqW W W1 σ HW HW1 Ψ)|by apply IH].
  - (* E-Pack *)
    cbn [pinst_ty].
    assert (pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)) as E.
    { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. symmetry.
      by apply plist_pup_comm. }
    apply (sr_pack W1 _ _ _ _ _ m _ _ (pt_inst σ <$> xs)).
    + by rewrite length_fmap.
    + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx.
      by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
    + apply (bcs_hold_inst (seqs W Ψ) _ (slt W Ψ)); [| |done].
      * intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
      * intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    + rewrite <-E, heads_pinst, hbot_pinst. by apply (lbx_below_h_pinst W W1 σ HW HW1 Ψ).
    + rewrite <-E. by apply IH.
  - (* E-Open *)
    apply (sr_open W1 _ _ _ _ i (lb_map (pt_inst σ) lb) m (bcs_inst σ C) (pinst_ty (pup m σ) T)).
    { by rewrite lenv_pinst_lookup, Hi. }
    intros W2 xs HW2 Hxs HK' HC'. subst m.
    set (σ' := pt_inst (plist xs) ∘ pup (length xs) σ).
    assert (∀ a, pt_inst σ' (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    pose proof (IH W2 ρ σ' HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    rewrite tenv_pinst_comp, (tenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite lenv_pinst_insert, lenv_pinst_comp, (lenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite sf_pinst_comp, (sf_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite pinst_ty_comp, (pinst_ty_ext _ _ σ) in Hb' by exact Hsh.
    assert (fhyps_pinst σ' (fhyps_pinst (pshift (length xs)) Φ) = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros j [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst σ' (hyps_inst (pshift (length xs)) Ψ ++
              [(bcs_inst (pshift (length xs)) C, ids (length xs))])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    rewrite E3, E4 in Hb'. cbn [fmap option_fmap option_map] in Hb'.
    assert (pinst_ty σ' T = ty_inst xs (pinst_ty (pup (length xs) σ) T)) as E2.
    { unfold ty_inst, σ'. by rewrite pinst_ty_comp. }
    rewrite E2 in Hb'. apply Hb'.
    + exact (inst_ok_mono _ _ _ _ HW2 Hρ).
    + apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done.
  - (* E-Gen *)
    cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (sr_gen W1 _ _ _ m (bcs_inst σ C) (pinst_ty (pup m σ) T)).
    + done.
    + by apply lenv_unl_pinst.
    + pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ Hb) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf. by rewrite term_wf_lenv_pinst.
    + intros W2 xs HW2 Hxs HK' HC'. subst m.
      set (σ' := pt_inst (plist xs) ∘ pup (length xs) σ).
      assert (∀ a, pt_inst σ' (pshift (length xs) a) = σ a) as Hsh
        by (intros a; by apply plist_pup_shift).
      pose proof (IH W2 ρ σ' HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
      rewrite tenv_pinst_empty in Hb'.
      rewrite lenv_pinst_comp, (lenv_pinst_ext _ σ) in Hb' by exact Hsh.
      rewrite sf_pinst_comp, (sf_pinst_ext _ σ) in Hb' by exact Hsh.
      assert (fhyps_pinst σ' (fhyps_pinst (pshift (length xs)) Φ) = fhyps_pinst σ Φ) as E3.
      { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
        intros j [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
        apply pt_inst_ext. exact Hsh. }
      assert (hyps_inst σ' (hyps_inst (pshift (length xs)) Ψ ++
                [(bcs_inst (pshift (length xs)) C, ids (length xs))])
              = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
      { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
        - apply hyps_inst_ext. exact Hsh.
        - f_equal. f_equal; [|apply ids_plist].
          rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
      rewrite E3, E4 in Hb'.
      assert (pinst_ty σ' T = ty_inst xs (pinst_ty (pup (length xs) σ) T)) as E2.
      { unfold ty_inst, σ'. by rewrite pinst_ty_comp. }
      rewrite E2 in Hb'. apply Hb'.
      * exact (inst_ok_mono _ _ _ _ HW2 Hρ).
      * apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
        intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done.
  - (* E-Inst *)
    assert (pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)) as E.
    { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. symmetry.
      by apply plist_pup_comm. }
    rewrite E. apply (sr_inst W1 _ _ _ _ m (bcs_inst σ C)).
    + by rewrite length_fmap.
    + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx.
      by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
    + apply (bcs_hold_inst (seqs W Ψ) _ (slt W Ψ)); [| |done].
      * intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
      * intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    + by apply (IH W1 ρ σ).
Qed.

(** ** The substitution lemma on its own

    Instantiating point variables by points preserves derivations at
    the same world. [typed_sem_rules] composes this substitution with
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

(** The hypotheses of an opened binder of m points survive a
    substitution lifted past it. *)
Lemma hyps_hold_open W Ψ Ψ' σ m C :
  strict W → hyps_hold (seqs W Ψ') (slt W Ψ') (skn W Ψ') (hyps_inst σ Ψ) →
  hyps_hold (seqs W (hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]))
    (slt W (hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]))
    (skn W (hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]))
    (hyps_inst (pup m σ) (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])).
Proof.
  intros HW HΨ. pose proof (proj1 HW) as Hwf. pose proof (wext_refl _ HW) as HWW.
  set (Ψt := hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]).
  assert (hyps_hold (seqs W Ψt) (slt W Ψt) (skn W Ψt) (hyps_inst (pshift m) Ψ')) as Hsub.
  { apply hyps_hold_sub. intros g Hg. apply elem_of_app. by left. }
  rewrite hyps_inst_app, hyps_comp,
    (hyps_inst_ext (pt_inst (pup m σ) ∘ pshift m) (pt_inst (pshift m) ∘ σ) Ψ)
    by (intros a; apply pup_pshift).
  rewrite <-hyps_comp. apply hyps_hold_app.
  - apply (hyps_hold_inst (seqs W Ψ') _ (slt W Ψ') _ (skn W Ψ') _ (pshift m)); [| | |exact HΨ].
    + intros x y Hxy. by apply (seqs_pinst_s W W (pshift m) Hwf HWW Ψ').
    + intros x y Hxy. by apply (slt_pinst_s W W (pshift m) Hwf HWW Ψ').
    + intros x Hx. by apply (skn_pinst_s W W (pshift m) Hwf HWW Ψ').
  - rewrite hyps_inst_single. apply hyps_hold_sub. intros g Hg.
    apply list_elem_of_singleton in Hg as ->. apply elem_of_app. right.
    apply list_elem_of_singleton. rewrite ids_pup, !bcs_comp. f_equal.
    apply bcs_inst_ext. intros a. unfold compose. apply pup_pshift.
Qed.

Lemma typed_pinst W Φ Ψ Θ Δ F e T :
  strict W → typed W Φ Ψ Θ Δ F e T →
  ∀ σ Ψ', hyps_hold (seqs W Ψ') (slt W Ψ') (skn W Ψ') (hyps_inst σ Ψ) →
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
    |Φ Ψ Θ Δ F e T T' Hteq H IH
    |Φ Ψ Θ Δ F e lb m C T xs Hxs HK HC Hlb H IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu Hb IH
    |Φ Ψ Δ F v m C T Hv Hu Hb IH
    |Φ Ψ Θ Δ F e m C T xs Hxs HK HC H IH]; intros σ Ψ' HΨ.
  - rewrite tenv_pinst_empty. apply t_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply t_konst; [by apply lenv_empty_pinst| |].
    + apply (konst_ty_pinst W W σ Hwf HWW (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
      * intros x y Hxy. by apply (seqs_pinst_s W W σ Hwf HWW Ψ).
      * intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
      * intros x Hx. by apply (skn_pinst_s W W σ Hwf HWW Ψ).
    + by apply (kscoped_pinst (seqs W Ψ) (slt W Ψ) (skn W Ψ)).
  - rewrite tenv_pinst_empty. apply t_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply t_chan; [by apply lenv_empty_pinst|done|by apply (seqs_pinst_s W W σ Hwf HWW Ψ)].
  - cbn [pinst_ty]. apply (t_lam W _ _ _ _ _ _ _ _ _ _ φ).
    + by rewrite fhyps_pinst_dom.
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L, lenv_bot_pinst.
      unfold lb_below_hb in *. destruct (lenv_bot Δ); [done|].
      by apply (lb_below_h_pinst_s W W σ Hwf HWW Ψ).
    + pose proof (IH σ Ψ' HΨ) as H. by rewrite fhyps_pinst_insert, sf_pinst_fresh in H.
  - apply (t_app W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + by apply (ub_below_s_pinst W W σ Ψ Ψ').
    + frame_pinst. by apply (IH1 σ Ψ').
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (t_pair W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (t_letu W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply IH2.
  - apply (t_letp W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. apply t_inj1. by apply IH.
  - cbn [pinst_ty]. apply t_inj2. by apply IH.
  - apply (t_case W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 σ Ψ').
    + by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (t_box W _ _ _ _ _ _ _ _ _ φ); [by apply lenv_unl_pinst|by rewrite fhyps_pinst_dom|].
    set (Ψt := hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]).
    assert (hyps_hold (seqs W Ψt) (slt W Ψt) (skn W Ψt)
              (hyps_inst (pup m σ) (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])))
      as HΨ'.
    { assert (hyps_hold (seqs W Ψt) (slt W Ψt) (skn W Ψt) (hyps_inst (pshift m) Ψ')) as Hsub.
      { apply hyps_hold_sub. intros g Hg. apply elem_of_app. by left. }
      rewrite hyps_inst_app, hyps_comp,
        (hyps_inst_ext (pt_inst (pup m σ) ∘ pshift m) (pt_inst (pshift m) ∘ σ) Ψ)
        by (intros a; apply pup_pshift).
      rewrite <-hyps_comp. apply hyps_hold_app.
      - apply (hyps_hold_inst (seqs W Ψ') _ (slt W Ψ') _ (skn W Ψ') _ (pshift m)); [| | |exact HΨ].
        + intros x y Hxy. by apply (seqs_pinst_s W W (pshift m) Hwf HWW Ψ').
        + intros x y Hxy. by apply (slt_pinst_s W W (pshift m) Hwf HWW Ψ').
        + intros x Hx. by apply (skn_pinst_s W W (pshift m) Hwf HWW Ψ').
      - rewrite hyps_inst_single. apply hyps_hold_sub. intros g Hg.
        apply list_elem_of_singleton in Hg as ->. apply elem_of_app. right.
        apply list_elem_of_singleton. rewrite ids_pup, !bcs_comp. f_equal.
        apply bcs_inst_ext. intros a. unfold compose. apply pup_pshift. }
    pose proof (IH (pup m σ) _ HΨ') as H.
    rewrite tenv_pinst_empty, sf_pinst_fresh, fhyps_pinst_insert in H.
    rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
    rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
      by apply pup_pshift.
    exact H.
  - eapply t_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply t_contract; [by apply unlimited_pinst|by apply (IH σ Ψ')].
  - eapply t_conv; [by apply (steq_pinst_s W W σ Hwf HWW Ψ)|by apply IH].
  - (* E-Pack *)
    cbn [pinst_ty].
    assert (pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)) as E.
    { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. symmetry.
      by apply plist_pup_comm. }
    apply (t_pack W _ _ _ _ _ _ _ m _ _ (pt_inst σ <$> xs)).
    + by rewrite length_fmap.
    + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx.
      by apply (skn_pinst_s W W σ Hwf HWW Ψ).
    + apply (bcs_hold_inst (seqs W Ψ) _ (slt W Ψ)); [| |done].
      * intros x y Hxy. by apply (seqs_pinst_s W W σ Hwf HWW Ψ).
      * intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
    + rewrite <-E, heads_pinst, hbot_pinst. by apply (lbx_below_h_pinst_s W W σ Hwf HWW Ψ).
    + rewrite <-E. by apply IH.
  - (* E-Open *)
    apply (t_open W _ _ _ _ _ _ i (lb_map (pt_inst σ) lb) m (bcs_inst σ C) (pinst_ty (pup m σ) T)).
    + by rewrite lenv_pinst_lookup, Hi.
    + by rewrite unlimited_pinst_iff.
    + pose proof (IH (pup m σ) _ (hyps_hold_open W Ψ Ψ' σ m C HW HΨ)) as H.
      rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
      rewrite tenv_pinst_comp, (tenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-tenv_pinst_comp in H
        by apply pup_pshift.
      rewrite lenv_pinst_insert in H. cbn [fmap option_fmap option_map] in H.
      rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
        by apply pup_pshift.
      rewrite sf_pinst_comp, (sf_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-sf_pinst_comp in H
        by apply pup_pshift.
      rewrite (pinst_ty_comp U), (pinst_ty_ext U _ (pt_inst (pshift m) ∘ σ)), <-pinst_ty_comp in H
        by apply pup_pshift.
      exact H.
  - (* E-Gen *)
    cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (t_gen W _ _ _ _ _ m (bcs_inst σ C) (pinst_ty (pup m σ) T)); [done|by apply lenv_unl_pinst|].
    pose proof (IH (pup m σ) _ (hyps_hold_open W Ψ Ψ' σ m C HW HΨ)) as H.
    rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
    rewrite tenv_pinst_empty in H.
    rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
      by apply pup_pshift.
    rewrite sf_pinst_comp, (sf_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-sf_pinst_comp in H
      by apply pup_pshift.
    exact H.
  - (* E-Inst *)
    assert (pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)) as E.
    { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. symmetry.
      by apply plist_pup_comm. }
    rewrite E. apply (t_inst W _ _ _ _ _ _ m (bcs_inst σ C)).
    + by rewrite length_fmap.
    + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx.
      by apply (skn_pinst_s W W σ Hwf HWW Ψ).
    + apply (bcs_hold_inst (seqs W Ψ) _ (slt W Ψ)); [| |done].
      * intros x y Hxy. by apply (seqs_pinst_s W W σ Hwf HWW Ψ).
      * intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
    + by apply IH.
Qed.

(** A closed derivation: no frame variables, no hypotheses, and the
    identity substitution. *)
Lemma typed_sem_rules_closed W Θ Δ F e T :
  strict W → typed W ∅ [] Θ Δ (F, None) e T → sem_rules W Θ Δ F e T.
Proof.
  intros HW Ht.
  pose proof (typed_sem_rules _ _ _ _ _ _ _ _ Ht W (λ _, ∅) pvar (proj1 HW) (wext_refl _ HW)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  unfold sf_inst in H. simpl in H. rewrite !union_empty_r_L in H.
  apply H.
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - intros C xs Hg. cbn in Hg. by apply elem_of_nil in Hg.
Qed.

(** ** The fundamental theorem for terms *)

Theorem fundamental W Θ Δ F e T :
  typed W ∅ [] Θ Δ (F, None) e T → strict W → sem_typed W Θ Δ F e T.
Proof. intros Ht HW. apply sem_rules_fundamental; [|done]. by apply typed_sem_rules_closed. Qed.

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
