(** * The fundamental theorem and soundness of the static system

    [typed_sem_rules] instantiates the future variables and substitutes
    points in one induction, and yields the infinitary judgment of
    SemanticRules.v. [typed_pinst] is the substitution lemma on its own.
    [fundamental], [fundamental_proc] and [soundness] follow. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Source.

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

(** ** Helpers for E-Exp over session variables (K6, sharp edges 73) *)

Lemma hcontractive_end : hcontractive SEnd.
Proof. intros [|n]; [done|]. by cbn. Qed.

(** Every session arity has a hereditarily contractive instance. *)
Lemma slist_witness k : ∃ ss, length ss = k ∧ Forall hcontractive ss.
Proof.
  exists (replicate k SEnd). split; [apply length_replicate|].
  apply Forall_replicate, hcontractive_end.
Qed.

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

(** ** Future instantiation

    Replacing the future variables by concrete futures that meet the
    hypotheses, at any later world, turns a derivation into one of the
    infinitary judgment. Monotonicity in W is folded in: typing reads W
    only through facts, and facts survive W ⊑ W₁. *)

Lemma sf_inst_union ρ F X : sf_inst ρ (sf_union F X) = sf_inst ρ F ∪ X.
Proof. destruct F as [P o]; unfold sf_inst, sf_union; simpl; set_solver. Qed.

(** The flag of a future stands for [pbot] (sharp edges 103). *)
Lemma sf_inst_unionb ρ F X b : sf_inst ρ (sf_unionb F X b) = sf_inst ρ F ∪ (X ∪ bot_pts b).
Proof.
  destruct b; unfold sf_unionb; [|rewrite sf_inst_union; simpl; set_solver].
  destruct F as [P o]; unfold sf_inst; simpl. destruct o as [[]|]; simpl; set_solver.
Qed.

(** Future instantiation: a node stands for the points it denotes. *)
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
      _ _ _ _ _ _ _ _ _ _ _ _ _ _)); unfold id; simpl.
    - intros x0 y0 H. by apply He.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - apply (wf_eq_refl _ Hwf).
    - apply (wf_eq_sym _ Hwf).
    - apply (wf_eq_trans _ Hwf).
    - apply (wf_eq_shift _ Hwf).
    - apply (wf_eq_payload _ Hwf).
    - intros x0 y0 H ? ? -> ->. by apply Hl.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - intros φ u Hu ? b' -> Hb'. exact (Hρ φ (Some u) Hu b' Hb').
    - intros x0 x' b Hx H ? b' -> Hb'.
      exact (wf_lt_eq _ Hwf x0 x' b' b' Hx (H x' b' eq_refl Hb') (wf_eq_refl _ Hwf b')).
    - intros a y y' H Hy a' ? Ha' ->.
      exact (wf_lt_eq _ Hwf a' a' y y' (wf_eq_refl _ Hwf a') (H a' y' Ha' eq_refl) Hy).
    - intros a y b H1 H2 a' b' Ha' Hb'.
      exact (wf_lt_trans _ Hwf a' y b' (H1 a' y Ha' eq_refl) (H2 y b' eq_refl Hb')).
    - intros x0 ? ? -> ->. apply (wf_lt_po _ Hwf). }
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
    |Φ Ψ Δ F e m k C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk _ IH
    |Φ Ψ Θ Δ U F e T Hu _ IH
    |Φ Ψ Θ Δ F e T T' _ _ IH
    |Φ Ψ Θ Δ F e lb m C T xs _ _ _ _ _ IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu _ IH].
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
  - destruct (slist_witness k) as (ss & Hss & Hsc).
    destruct (proj1 (term_wf_lenv_pinst _ _ _ _) (IH ss Hss Hsc)) as (Hfc & Hfv & Hrv).
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
Qed.

Ltac future_pinst :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?heads_pinst, ?opt_heads_pinst,
    ?lenv_bot_pinst, ?hbot_pinst,
    <-?set_map_union_L, <-?sf_inst_unionb, <-?sf_inst_union, <-?sf_pinst_unionb, <-?sf_pinst_union.

(** Future instantiation and point substitution in one induction: the
    future variables become futures above their hypotheses at a later
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
    |Φ Ψ Δ F e m k C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH
    |Φ Ψ Θ Δ F e lb m C T xs Hxs HK HC Hlb H IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu Hb IH]; intros W1 ρ σ HW HW1 Hρ HΨ;
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
    + future_pinst. by apply (IH1 W1 ρ σ).
    + future_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (sr_pair W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + future_pinst. by apply IH1.
    + future_pinst. by apply IH2.
  - apply (sr_letu W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH1 W1 ρ σ).
    + by apply IH2.
  - apply (sr_letp W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. apply sr_inj1. by apply IH.
  - cbn [pinst_ty]. apply sr_inj2. by apply IH.
  - apply (sr_case W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH0 W1 ρ σ).
    + by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. rewrite tenv_pinst_empty. apply sr_box; [by apply lenv_unl_pinst| |].
    { destruct (slist_witness k) as (ss0 & Hss0 & Hsc0).
      pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ (Hb ss0 Hss0 Hsc0)) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf.
      change (term_wf ∅ (lenv_pinst σ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) e).
      by rewrite term_wf_lenv_pinst. }
    intros W2 xs ss F' HW2 Hxs Hss Hsc HC HK Hub'. subst m.
    assert (∀ a, pt_inst (pt_inst (plist xs) ∘ pup (length xs) σ) (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    set (m := length xs).
    assert (lenv_pinst (pt_inst (plist xs) ∘ pup m σ) (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ))
            = lenv_pinst σ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) as E1.
    { rewrite lenv_pinst_comp. apply lenv_pinst_ext. exact Hsh. }
    assert (pinst_ty (pt_inst (plist xs) ∘ pup m σ) (sinst_ty (slist ss) T)
            = sinst_ty (slist ss) (ty_inst xs (pinst_ty (pup m σ) T))) as E2.
    { unfold ty_inst. by rewrite pinst_sinst, pinst_ty_comp. }
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
    pose proof (IH ss Hss Hsc W2 (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
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
Qed.

(** ** The substitution lemma on its own

    Instantiating point variables by points preserves derivations at
    the same world. [typed_sem_rules] composes this substitution with
    future instantiation; the fundamental theorem needs only that. *)

Lemma kscoped_pinst peq plt pk k T σ :
  konst_ty peq plt pk k T → kscoped k T → kscoped k (pinst_ty σ T).
Proof. destruct 1 as [? ? ? ? Hs ? ?|]; [destruct Hs|]; simpl; auto. Qed.

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
    |Φ Ψ Δ F e m k C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH
    |Φ Ψ Θ Δ F e lb m C T xs Hxs HK HC Hlb H IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu Hb IH]; intros σ Ψ' HΨ.
  - rewrite tenv_pinst_empty. apply t_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply t_const; [by apply lenv_empty_pinst| |].
    + apply (konst_ty_pinst W W σ Hwf HWW (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
      * intros x y Hxy. by apply (seqs_pinst_s W W σ Hwf HWW Ψ).
      * intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
      * intros x Hx. by apply (skn_pinst_s W W σ Hwf HWW Ψ).
    + by apply (kscoped_pinst (seqs W Ψ) (slt W Ψ) (skn W Ψ)).
  - rewrite tenv_pinst_empty. apply t_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply t_ch; [by apply lenv_empty_pinst|done|by apply (seqs_pinst_s W W σ Hwf HWW Ψ)].
  - cbn [pinst_ty]. apply (t_abs W _ _ _ _ _ _ _ _ _ _ φ).
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
    + future_pinst. by apply (IH1 σ Ψ').
    + future_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (t_pair W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + future_pinst. by apply IH1.
    + future_pinst. by apply IH2.
  - apply (t_letstar W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH1 σ Ψ').
    + by apply IH2.
  - apply (t_letpair W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. apply t_inj1. by apply IH.
  - cbn [pinst_ty]. apply t_inj2. by apply IH.
  - apply (t_case W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + future_pinst. by apply (IH0 σ Ψ').
    + by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (t_exp W _ _ _ _ _ _ _ _ _ _ φ); [by apply lenv_unl_pinst|by rewrite fhyps_pinst_dom|].
    intros ss Hss Hsc.
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
    pose proof (IH ss Hss Hsc (pup m σ) _ HΨ') as H.
    rewrite tenv_pinst_empty, sf_pinst_fresh, fhyps_pinst_insert, pinst_sinst in H.
    rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
    rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
      by apply pup_pshift.
    exact H.
  - eapply t_weak; [by apply lenv_wk_pinst|by apply IH].
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
Qed.

(** ** new at a known point (sharp edges 104)

    new has the one existential signature. At C = {ι ≡ x} it gives the
    old signature at a known point x on the encoded let of new. E-Open
    puts ι ≡ x into the hypotheses, E-Conv moves the opened pair from ι
    to x, and the body is the old one with the point variables shifted
    past ι ([typed_pinst]). The only premise on the context is that x
    is known, as for the old signature. *)

Definition alias_bcs (x : point) : bcs := BCs [x] (λ f, f = FEq (pvar 0) (pvar 1)).

Lemma alias_bcs_ok W Ψ x :
  skn W Ψ x →
  fresh_ok (alias_bcs x) ∧ Forall (skn W Ψ) (bc_env (alias_bcs x)) ∧
  fresh_between (slt W Ψ) (alias_bcs x).
Proof.
  intros Hx.
  assert (fresh_eq (alias_bcs x) (pvar 1)) as Hw by (split_and!; [done|cbn; lia|done]).
  split_and!.
  - right. exists (pvar 1). split; [done|]. intros f Hf _. by right; right.
  - by constructor.
  - split_and!.
    + intros Hlt. exfalso. by apply (fresh_lt_no_eq (alias_bcs x) (pvar 1)).
    + intros w u p _ (Hf & _). discriminate Hf.
    + intros w q v _ (Hf & _). discriminate Hf.
Qed.

(** The alias {ι ≡ x} is a creation constraint in every context. *)
Lemma cc_ok_alias peq plt x : cc_ok peq plt (alias_bcs x).
Proof.
  apply cc_ok_fresh.
  - assert (fresh_eq (alias_bcs x) (pvar 1)) as Hw by (split_and!; [done|cbn; lia|done]).
    right. exists (pvar 1). split; [done|]. intros f Hf _. by right; right.
  - split_and!.
    + intros Hlt. exfalso. apply (fresh_lt_no_eq (alias_bcs x) (pvar 1)); [done|].
      split_and!; [done|cbn; lia|done].
    + intros w u p _ (Hf & _). discriminate Hf.
    + intros w q v _ (Hf & _). discriminate Hf.
Qed.

Lemma t_new_at W Φ Ψ Θ Δ F e T S x :
  strict W → skn W Ψ x →
  typed W Φ Ψ Θ (Some (TSess (dual S) x) :: Some (TSess S x) :: None :: None :: Δ) F e T →
  typed W Φ Ψ Θ Δ F (let_new e) T.
Proof.
  intros HW Hx Hb. unfold let_new.
  destruct (alias_bcs_ok W Ψ x Hx) as (_ & HK & _).
  pose proof (cc_ok_alias (seqs W Ψ) (slt W Ψ) x) as HC.
  set (C := alias_bcs x).
  set (X := TEx LBot 1 C (TProd (TSess S (pvar 0)) (TSess (dual S) (pvar 0)))).
  (* let ⟨p, w⟩ = ⟨new ∗, ∗⟩ *)
  apply (t_letpair W Φ Ψ Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ X TUnit).
  { apply tenv_comp_empty_l, se_sym. }
  { apply lenv_split_nones_l. }
  { apply (t_pair W Φ Ψ ∅ ∅ ∅ (lenv_nones Δ) (lenv_nones Δ) (lenv_nones Δ)).
    - apply tenv_comp_empty_r.
    - apply lenv_split_nones_nones.
    - eapply (t_app W Φ Ψ ∅ ∅ ∅ _ _ _ _ _ _ None None TUnit).
      + apply tenv_comp_empty_r.
      + apply lenv_split_nones_l.
      + done.
      + apply t_const; [apply lenv_empty_nones| |done]. by apply KTNewEx.
      + apply t_unit. apply lenv_empty_nones.
    - apply t_unit. apply lenv_empty_nones. }
  (* let ∗ = w *)
  apply (t_letstar W Φ Ψ Θ ∅ Θ _ (Some TUnit :: None :: lenv_nones Δ) (None :: Some X :: Δ)).
  { apply tenv_comp_empty_l, se_sym. }
  { apply lsplit_l, lsplit_r, lenv_split_nones_l. }
  { apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [by simplify_eq|done|].
    exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
    apply fmap_Some in Hy as (? & _ & ?). congruence. }
  (* open p, with the hypothesis ι ≡ x *)
  apply (t_open W Φ Ψ Θ _ F _ 1 LBot 1 C
           (TProd (TSess S (pvar 0)) (TSess (dual S) (pvar 0))) T); [done|intros Hun; exact Hun|].
  cbn [lenv_pinst fmap list_fmap option_fmap option_map pinst_ty].
  change (<[1 := ?o]> (?a :: ?b :: ?l)) with (a :: o :: l).
  set (Ψ1 := hyps_inst (pshift 1) Ψ ++ [(bcs_inst (pshift 1) C, ids 1)]).
  assert (seqs W Ψ1 (pvar 0) (pt_inst (pshift 1) x)) as Hal.
  { assert ((bcs_inst (pshift 1) C, [pvar 0]) ∈ Ψ1) as Hg
      by (apply elem_of_app; right; by apply list_elem_of_singleton).
    pose proof (hyp_in_fact W Ψ1 (bcs_inst (pshift 1) C) [pvar 0] Hg) as HCg.
    specialize (HCg (FEq (pvar 0) (pt_inst (λ a', pvar (a' + 1)) (pt_inst (pshift 1) x)))).
    simpl in HCg. rewrite pt_inst_unshift in HCg. apply HCg.
    exists (FEq (pvar 0) (pvar 1)). split_and!; [done|cbn; lia|].
    simpl. rewrite !pt_inst_pvar_at. done. }
  (* let ⟨a, b⟩ = p, the pair moved from ι to x *)
  apply (t_letpair W _ _ _ ∅ (tenv_pinst (pshift 1) Θ) _
           (None :: Some (TProd (TSess S (pvar 0)) (TSess (dual S) (pvar 0)))
              :: lenv_nones (lenv_pinst (pshift 1) Δ))
           (None :: None :: lenv_pinst (pshift 1) Δ)
           _ _ _ (TSess S (pt_inst (pshift 1) x)) (TSess (dual S) (pt_inst (pshift 1) x))).
  - apply tenv_comp_empty_l, se_sym.
  - apply lsplit_none, lsplit_l, lenv_split_nones_l.
  - apply (t_conv W _ _ _ _ _ _ (TProd (TSess S (pvar 0)) (TSess (dual S) (pvar 0)))).
    { split; split; [exact Hal|apply seq_refl|exact Hal|apply seq_refl]. }
    apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [done|by simplify_eq|].
    exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
    apply fmap_Some in Hy as (? & _ & ?). congruence.
  - assert (hyps_hold (seqs W Ψ1) (slt W Ψ1) (skn W Ψ1) (hyps_inst (pshift 1) Ψ)) as HΨ.
    { apply hyps_hold_sub. intros g Hg. apply elem_of_app. by left. }
    exact (typed_pinst W _ _ _ _ _ _ _ HW Hb (pshift 1) Ψ1 HΨ).
Qed.

(** A closed derivation: no future variables, no hypotheses, and the
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

(** ** Programs start under a creation constraint (sharp edges 109)

    A source program starts with n top-level point variables 0, …, n-1
    under one constraint C₀ over them, and it is typed in the empty
    world [wnil] with the hypothesis (C₀, ids n). Knownness of a point
    then comes from the hypothesis alone. C₀ has no outer points, so the
    conservativity part of a creation constraint is empty and only
    acyclicity remains ([c0_acyclic]). The run starts in the world
    [wc0 n C₀], which realizes C₀ at the constants 0, …, n-1. It is the
    construction of [wext_cc] against the empty world. *)

(** [wnil] and the source instance [styped] are in static/Source.v. *)
Lemma styped_wnil Φ Ψ Δ F e T : typed wnil Φ Ψ ∅ Δ F e T → styped Φ Ψ Δ F e T.
Proof. intros H. exact H. Qed.

Definition c0_eq (n : nat) (C : bcs) : point → point → Prop := λ x y, bcs_open n C (FEq x y).
Definition c0_lt (n : nat) (C : bcs) : point → point → Prop := λ x y, bcs_open n C (FLt x y).

(** C₀ speaks of the top-level variables only, and its closure with
    program order has no cycle. *)
Definition c0_acyclic (n : nat) (C : bcs) : Prop :=
  bc_env C = [] ∧ ∀ p, ¬ glt (c0_eq n C) (c0_lt n C) p p.

Section c0_world.
  Context (n : nat) (C : bcs).

  Fixpoint c0_name (p : pname) : pname :=
    match p with
    | NVar a => if decide (a < n) then NConst a else NVar a
    | NConst a => NConst a
    | NPayload q b i => NPayload (c0_name q) b i
    end.

  Fixpoint c0_back (p : pname) : pname :=
    match p with
    | NConst a => if decide (a < n) then NVar a else NConst a
    | NVar a => NVar a
    | NPayload q b i => NPayload (c0_back q) b i
    end.

  Definition c0_pt (x : point) : point := Pt (c0_name (pt_name x)) (pt_off x).
  Definition c0_bpt (x : point) : point := Pt (c0_back (pt_name x)) (pt_off x).

  Definition c0_consts : list point := pconst <$> List.seq 0 n.

  Lemma c0_back_name p : pn_vb n p → c0_back (c0_name p) = p.
  Proof.
    induction p as [a|a|q IH b i]; simpl; intros H; [done| |by rewrite IH].
    rewrite decide_True by done. simpl. by rewrite decide_True.
  Qed.

  Lemma c0_name_root p : pn_vb n p → ∃ a, a < n ∧ pn_root (c0_name p) = NConst a.
  Proof.
    induction p as [a|a|q IH b i]; simpl; intros H; [done| |by apply IH].
    rewrite decide_True by done. by exists a.
  Qed.

  Lemma plist_consts a : a < n → plist c0_consts a = pconst a.
  Proof.
    intros Ha. unfold plist, c0_consts. rewrite list_lookup_fmap, lookup_seq_lt by done. done.
  Qed.

  Lemma pn_inst_consts p : pn_vb n p → pn_inst (plist c0_consts) p = Pt (c0_name p) 0.
  Proof.
    induction p as [a|a|q IH b i]; simpl; intros H; [done| |].
    - rewrite decide_True by done. by apply plist_consts.
    - rewrite IH by done. done.
  Qed.

  Lemma pt_inst_consts x : pn_vb n (pt_name x) → pt_inst (plist c0_consts) x = c0_pt x.
  Proof.
    destruct x as [p o]. simpl. intros H. unfold pt_inst. simpl. rewrite pn_inst_consts by done.
    done.
  Qed.

  (** Under the binder of n variables with no outer points, the facts of
      C are about the variables themselves. *)
  Lemma pn_inst_pup_vb σ p : pn_vb n p → pn_inst (pup n σ) p = Pt p 0.
  Proof.
    induction p as [a|a|q IH b i]; simpl; intros H; [done| |].
    - unfold pup. by rewrite decide_True.
    - rewrite IH by done. done.
  Qed.

  Lemma pt_inst_pup_vb σ x : pn_vb n (pt_name x) → pt_inst (pup n σ) x = x.
  Proof.
    destruct x as [p o]. simpl. intros H. unfold pt_inst. simpl. rewrite pn_inst_pup_vb by done.
    unfold pt_shift. simpl. done.
  Qed.

  Lemma c0_open_vb g :
    bc_env C = [] → bcs_open n C g →
    fact_scoped n g ∧ bc_facts C g.
  Proof.
    intros Henv (f & Hf & Hs & ->). rewrite Henv in Hs. simpl in Hs. rewrite Nat.add_0_r in Hs.
    destruct f as [x y|x y]; cbn [fact_map fact_scoped] in *; destruct Hs as [Hx Hy];
      rewrite !(pt_inst_pup_vb (plist (bc_env C))) by done; done.
  Qed.

  Definition wc0 : world :=
    wgen (list_to_set (NConst <$> List.seq 0 n))
      (λ x y, ∃ x0 y0, c0_eq n C x0 y0 ∧ x = c0_pt x0 ∧ y = c0_pt y0)
      (λ x y, ∃ x0 y0, c0_lt n C x0 y0 ∧ x = c0_pt x0 ∧ y = c0_pt y0).

  Lemma c0_pt_known x : pn_vb n (pt_name x) → pt_root (c0_pt x) ∈ list_to_set (C:=gset pname) (NConst <$> List.seq 0 n).
  Proof.
    intros H. destruct (c0_name_root _ H) as (a & Ha & E). unfold pt_root, c0_pt. simpl.
    rewrite E. apply elem_of_list_to_set, list_elem_of_fmap. exists a. split; [done|].
    apply elem_of_seq. lia.
  Qed.

  Lemma wc0_strict : c0_acyclic n C → strict wc0.
  Proof.
    intros [Henv Hacy]. split.
    - apply wgen_wf.
      + intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
      + intros x y (x0 & y0 & H & -> & ->). right.
        destruct (c0_open_vb _ Henv H) as [[Hx Hy] _]. split; by apply c0_pt_known.
      + intros x y (x0 & y0 & H & -> & ->). right.
        destruct (c0_open_vb _ Henv H) as [[Hx Hy] _]. split; by apply c0_pt_known.
    - destruct (gen_map (λ x y, ∃ x0 y0, c0_eq n C x0 y0 ∧ x = c0_pt x0 ∧ y = c0_pt y0)
                  (λ x y, ∃ x0 y0, c0_lt n C x0 y0 ∧ x = c0_pt x0 ∧ y = c0_pt y0)
                  (geq (c0_eq n C)) (glt (c0_eq n C) (c0_lt n C)) c0_bpt
                  (theory_gen _ _)) as [_ Gl]; [done|done| | |].
      + intros x y (x0 & y0 & H & -> & ->). destruct (c0_open_vb _ Henv H) as [[Hx Hy] _].
        unfold c0_bpt, c0_pt. simpl. rewrite !c0_back_name by done.
        destruct x0, y0. by apply geq_base.
      + intros x y (x0 & y0 & H & -> & ->). destruct (c0_open_vb _ Henv H) as [[Hx Hy] _].
        unfold c0_bpt, c0_pt. simpl. rewrite !c0_back_name by done.
        destruct x0, y0. by apply glt_base.
      + intros x Hx. exact (Hacy _ (Gl _ _ Hx)).
  Qed.

  Lemma wc0_ext : c0_acyclic n C → wext wnil wc0.
  Proof.
    intros HC. pose proof (wc0_strict HC) as HS.
    destruct (gen_map (λ _ _, False) (λ _ _, False) (w_eq wc0) (w_lt wc0) id
                (theory_world _ (proj1 HS))) as [Gq Gl]; [done|done|done|done|].

    split_and!; [simpl; set_solver|exact Gq|exact Gl|done].
  Qed.

  Lemma wc0_holds : c0_acyclic n C →
    hyps_hold (w_eq wc0) (w_lt wc0) (pt_known wc0) (hyps_inst (plist c0_consts) [(C, ids n)]).
  Proof.
    intros [Henv _] C' xs Hin. cbn in Hin. apply list_elem_of_singleton in Hin.
    injection Hin as -> ->.
    assert (pt_inst (plist c0_consts) <$> ids n = c0_consts) as Exs.
    { unfold ids, c0_consts. rewrite <-list_fmap_compose. apply list_fmap_ext.
      intros i a Ha. apply lookup_seq in Ha as [-> Ha]. simpl. unfold pt_inst. simpl.
      rewrite plist_consts by lia. done. }
    assert (bcs_inst (plist c0_consts) C = C) as EC.
    { destruct C as [env fs]. unfold bcs_inst. simpl in *. by subst env. }
    rewrite Exs, EC. split.
    - intros g Hg. assert (length c0_consts = n) as Hl by (unfold c0_consts; by rewrite length_fmap, List.length_seq).
      rewrite Hl in Hg. destruct (c0_open_vb _ Henv Hg) as [Hs _].
      destruct g as [x y|x y]; destruct Hs as [Hx Hy]; simpl; rewrite !pt_inst_consts by done.
      + apply glt_base. by exists x, y.
      + apply geq_base. by exists x, y.
    - apply Forall_forall. intros x Hx. unfold c0_consts in Hx.
      apply list_elem_of_fmap in Hx as (a & -> & Ha). apply elem_of_seq in Ha.
      unfold pt_known, pconst, pt_root. simpl. apply elem_of_list_to_set, list_elem_of_fmap.
      exists a. split; [done|]. apply elem_of_seq. lia.
  Qed.
End c0_world.

(** ** C₀ is the program's creation constraint (sharp edges 148)

    The empty context has no fact beyond equality and program order.
    Against it, a creation constraint over n variables
    ([creation_ok], the premise of new at n = 1) is exactly
    [c0_acyclic]. Its outer points must be known, and the empty context
    knows none, so C₀ has none. Conservativity holds for free, because
    every fact of C₀ is between variables, and acyclicity is the
    acyclicity of C₀ with program order. *)
Notation nofact := (λ _ _ : point, False).

Lemma glt_nofact x y : glt nofact nofact x y → pofs x y.
Proof.
  assert (∀ x y, geq nofact x y → x = y) as Hq by (induction 1; subst; done).
  induction 1 as [x y []|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
  - apply pofs_shift.
  - apply Hq in Hx, Hy. by subst.
  - by eapply pofs_trans.
Qed.

Lemma pofs_glt (E L : point → point → Prop) x y : pofs x y → glt E L x y.
Proof.
  destruct x as [p o], y as [q o']. intros [Hn Ho]. simpl in *. subst q.
  replace o' with (o + S (o' - o - 1)) by lia. generalize (o' - o - 1) as k. intros k.
  induction k as [|k IH].
  - replace (o + 1) with (pt_off (pt_shift 1 (Pt p o))) by (simpl; lia). apply glt_po.
  - eapply glt_trans; [exact IH|].
    replace (o + S (S k)) with (pt_off (pt_shift 1 (Pt p (o + S k)))) by (simpl; lia). apply glt_po.
Qed.

Section c0_creation.
  Context (n : nat) (C : bcs) (Henv : bc_env C = []).

  Lemma c0_cc_eq x y : cc_eq_at n nofact C x y → pn_vb n (pt_name x) ∧ pn_vb n (pt_name y).
  Proof.
    intros [(? & ? & [] & _)|H]. by destruct (c0_open_vb n C _ Henv H) as [[??] _].
  Qed.

  Lemma c0_cc_lt x y : cc_lt_at n nofact C x y → pn_vb n (pt_name x) ∧ pn_vb n (pt_name y).
  Proof.
    intros [(? & ? & [] & _)|H]. by destruct (c0_open_vb n C _ Henv H) as [[??] _].
  Qed.

  Lemma c0_geq x y :
    geq (cc_eq_at n nofact C) x y → x = y ∨ (pn_vb n (pt_name x) ∧ pn_vb n (pt_name y)).
  Proof.
    induction 1 as [x y H|x|x y _ IH|x y z _ IH1 _ IH2|x y _ IH|x y i _ IH].
    - right. by apply c0_cc_eq.
    - by left.
    - destruct IH as [->|[??]]; [by left|by right].
    - destruct IH1 as [->|[??]]; [done|]. destruct IH2 as [->|[??]]; by right.
    - destruct IH as [->|[??]]; [by left|by right].
    - destruct IH as [->|[??]]; [by left|by right].
  Qed.

  Lemma c0_glt x y :
    glt (cc_eq_at n nofact C) (cc_lt_at n nofact C) x y → ¬ pn_vb n (pt_name x) → pofs x y.
  Proof.
    induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2]; intros Hn.
    - by destruct (c0_cc_lt x y H).
    - apply pofs_shift.
    - destruct (c0_geq x x' Hx) as [<-|[??]]; [|done].
      destruct (IH Hn) as [E Ho].
      destruct (c0_geq y' y Hy) as [<-|[Hv _]]; [done|]. by rewrite <-E in Hv.
    - pose proof (IH1 Hn) as [E Ho]. eapply pofs_trans; [done|]. apply IH2. by rewrite <-E.
  Qed.
End c0_creation.

Lemma c0_creation_ok n C :
  creation_ok n nofact nofact (λ _, False) C ↔ c0_acyclic n C.
Proof.
  split.
  - intros [[Hacy _] Hk]. assert (bc_env C = []) as Henv.
    { destruct (bc_env C) as [|x xs]; [done|]. by apply Forall_cons in Hk as [[] _]. }
    split; [done|]. intros p Hp.
    assert (glt (cc_eq_at n nofact C) (cc_lt_at n nofact C) p p) as Hp'.
    { refine (proj2 (gen_mono _ _ _ _ _ _) p p Hp); intros ? ? ?; by right. }
    destruct (Hacy p Hp') as [x Hx].
    assert (glt nofact nofact x x) as Hx'.
    { refine (proj2 (gen_mono _ _ nofact nofact _ _) x x Hx); intros ? ? (? & ? & [] & _). }
    exact (pofs_irrefl x (glt_nofact x x Hx')).
  - intros [Henv Hacy]. split; [split|by rewrite Henv].
    + intros p Hp. exfalso. apply (Hacy p).
      refine (proj2 (gen_mono _ _ _ _ _ _) p p Hp); intros ? ? [(? & ? & [] & _)|H]; exact H.
    + split.
      * intros x y Hx _ H. destruct (c0_geq n C Henv x y H) as [->|[??]]; [apply geq_refl|done].
      * intros x y Hx _ H. by apply pofs_glt, (c0_glt n C Henv).
Qed.

Lemma c0_acyclic_creation n C :
  c0_acyclic n C → creation_ok n nofact nofact (λ _, False) C.
Proof. apply c0_creation_ok. Qed.

Lemma prim_pinst σ T : prim T → prim (pinst_ty σ T).
Proof.
  intros H. revert σ. induction H; intros σ; simpl;
    [apply prim_unit|by apply prim_prod|by apply prim_sum|apply prim_box, IHprim].
Qed.

(** Soundness for source programs. A closed term of the source
    judgment under the top-level constraint C₀ over n point variables is
    deadlock free, when C₀ is acyclic. The judgment reads no world
    (static/Source.v), and the two worlds of the proof, [wnil] for the
    facts and [wc0 n C₀] for the run, are internal to it. *)
Theorem soundness_source n C0 t T :
  creation_ok n nofact nofact (λ _, False) C0 → prim T →
  styped ∅ [(C0, ids n)] [] (∅, None) t T →
  deadlock_free (∅, {[+ t +]}).
Proof.
  intros HC HT Hs. apply c0_creation_ok in HC.
  pose proof (styped_typed wnil _ _ _ _ _ _ Hs) as Ht.
  pose proof (wc0_strict n C0 HC) as HS.
  set (σ := plist (c0_consts n)).
  assert (sem_rules (wc0 n C0) (tenv_pinst σ ∅) (lenv_pinst σ [])
            (sf_inst (λ _, ∅) (sf_pinst σ (∅, None))) t (pinst_ty σ T)) as H.
  { apply (typed_sem_rules _ _ _ _ _ _ _ _ Ht); [apply wnil_strict|by apply wc0_ext| |by apply wc0_holds].
    intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty. }
  rewrite tenv_pinst_empty in H.
  assert (sf_inst (λ _, ∅) (sf_pinst σ (∅, None)) = ∅) as E.
  { unfold sf_inst, sf_pinst. simpl. rewrite set_map_empty. set_solver. }
  rewrite E in H.
  apply (adequacy (wc0 n C0) (pinst_ty σ T)).
  apply (Prel_term _ ∅ ∅ ∅); [by apply prim_pinst|done|done|set_solver| | |].
  - intros c o Ho. by rewrite lookup_empty in Ho.
  - intros c e1 e2 He. by rewrite lookup_empty in He.
  - unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)).
    by apply sem_rules_fundamental.
Qed.
