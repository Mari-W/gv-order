(** * Point substitution for derivations (fx-gap, 2026-11-22)

      typed W N Θ Γ Δ F e T c ∧ Γ' ⊢ σ(Γ)
        ⟹  typed W N σ(Θ) Γ' σ(Δ) σ(F) e σ(T) c                 [typed_pinst]

    σ instantiates point variables. [hinst W σ Γ Γ'] says that Γ'
    derives the instance under σ of every hypothesis of Γ. The world W
    keeps its facts at constant roots ([facts_const]), which σ leaves
    alone. Terms mention no point and stay.

    Every premise of a rule that reads Γ survives, by [slt_hinst] for
    the order and by [hinst_open] under the binder of E-Box, E-Open and
    Sub-Ex, where σ lifts to [pup m σ]. Two premises need an argument.

    - (acyc-new) and (gen-new) of E-New read Γ only through [slt] at the
      context points of C, which σ moves together with C
      ([new_ok_hinst]).
    - [cons_open], the bridge condition of E-Open, asks Γ to derive
      the bridge of C between each two outer points. σ leaves the
      facts and the tree of C alone and moves its outer points, so a
      bridge of σ(C) is the instance of a bridge of C, a fact of Γ',
      by [hinst] ([cons_open_hinst]).

    [typed_open_inst] closes an opening: a derivation under
    [hc_open m C Γ] over shifted contexts gives one over Γ at any
    instance xs at which C holds. *)

From GV Require Export static.Inversion.

Definition hinst (W : sworld) (σ : nat → point) (Γ Γ' : hctx) : Prop :=
  ∀ u v, hyp_fact (hc_hyps Γ) (FLt u v) → slt W Γ' (pt_inst σ u) (pt_inst σ v).

(** ** Shifts *)

Lemma pup_shift_pt m σ x :
  pt_inst (pup m σ) (pt_inst (pshift m) x) = pt_inst (pshift m) (pt_inst σ x).
Proof.
  rewrite !pt_inst_comp. apply pt_inst_ext. intros a. unfold compose, pshift.
  rewrite pt_inst_pvar_at. apply pup_pshift.
Qed.

Lemma pup_shift_fn m σ a : (pt_inst (pup m σ) ∘ pshift m) a = (pt_inst (pshift m) ∘ σ) a.
Proof. unfold compose, pshift. rewrite pt_inst_pvar_at. apply pup_pshift. Qed.

Lemma pup_ids m σ : pt_inst (pup m σ) <$> ids m = ids m.
Proof.
  unfold ids. rewrite <-list_fmap_compose. apply list_fmap_ext. intros i a Hi.
  apply lookup_seq in Hi as [-> Hi]. unfold compose. rewrite pt_inst_pvar_at. unfold pup.
  by rewrite decide_True by lia.
Qed.

Lemma pup_shift_bcs m σ C :
  bcs_inst (pup m σ) (bcs_inst (pshift m) C) = bcs_inst (pshift m) (bcs_inst σ C).
Proof. rewrite !bcs_inst_comp. apply bcs_inst_ext. apply pup_shift_fn. Qed.

Lemma pup_shift_ty m σ T :
  pinst_ty (pup m σ) (pinst_ty (pshift m) T) = pinst_ty (pshift m) (pinst_ty σ T).
Proof. rewrite !pinst_ty_comp. apply pinst_ty_ext. apply pup_shift_fn. Qed.

Lemma pup_shift_lb m σ lb :
  lb_map (pt_inst (pup m σ)) (lb_map (pt_inst (pshift m)) lb) = lb_map (pt_inst (pshift m)) (lb_map (pt_inst σ) lb).
Proof. destruct lb; simpl; [done|done|]. f_equal. apply pup_shift_pt. Qed.

Lemma lenv_pinst_comp τ σ Δ : lenv_pinst τ (lenv_pinst σ Δ) = lenv_pinst (pt_inst τ ∘ σ) Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite pinst_ty_comp, IH. Qed.

Lemma lenv_pinst_ext σ τ Δ : (∀ a, σ a = τ a) → lenv_pinst σ Δ = lenv_pinst τ Δ.
Proof. intros H. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite (pinst_ty_ext T σ τ H), IH. Qed.

Lemma tenv_pinst_comp τ σ Θ : tenv_pinst τ (tenv_pinst σ Θ) = tenv_pinst (pt_inst τ ∘ σ) Θ.
Proof.
  unfold tenv_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext. intros _ e _.
  apply tentry_pinst_comp.
Qed.

Lemma tenv_pinst_ext σ τ Θ : (∀ a, σ a = τ a) → tenv_pinst σ Θ = tenv_pinst τ Θ.
Proof.
  intros H. unfold tenv_pinst. apply map_fmap_ext. intros _ [S x a t] _. unfold tentry_pinst. simpl.
  by rewrite (pt_inst_ext σ τ x H).
Qed.

Lemma frest_pinst_comp τ σ r : frest_pinst τ (frest_pinst σ r) = frest_pinst (pt_inst τ ∘ σ) r.
Proof. destruct r; simpl; [by rewrite pt_inst_comp|done]. Qed.

Lemma sf_pinst_comp τ σ F : sf_pinst τ (sf_pinst σ F) = sf_pinst (pt_inst τ ∘ σ) F.
Proof.
  destruct F as [X o]. unfold sf_pinst. simpl. f_equal.
  - apply set_eq. intros y. split.
    + intros (y1 & -> & Hy1)%elem_of_map. apply elem_of_map in Hy1 as (y0 & -> & Hy0).
      apply elem_of_map. exists y0. by rewrite pt_inst_comp.
    + intros (y0 & -> & Hy0)%elem_of_map. apply elem_of_map. exists (pt_inst σ y0).
      split; [by rewrite pt_inst_comp|]. apply elem_of_map. by exists y0.
  - destruct o as [r|]; simpl; by rewrite ?frest_pinst_comp.
Qed.

Lemma sf_pinst_ext σ τ F : (∀ a, σ a = τ a) → sf_pinst σ F = sf_pinst τ F.
Proof.
  intros H. destruct F as [X o]. unfold sf_pinst. simpl. f_equal.
  - apply set_eq. intros y. rewrite !elem_of_map. by setoid_rewrite (pt_inst_ext σ τ _ H).
  - destruct o as [[u|]|]; simpl; by rewrite ?(pt_inst_ext σ τ _ H).
Qed.

Lemma pup_shift_lenv m σ Δ :
  lenv_pinst (pup m σ) (lenv_pinst (pshift m) Δ) = lenv_pinst (pshift m) (lenv_pinst σ Δ).
Proof. rewrite !lenv_pinst_comp. apply lenv_pinst_ext. apply pup_shift_fn. Qed.

Lemma pup_shift_tenv m σ Θ :
  tenv_pinst (pup m σ) (tenv_pinst (pshift m) Θ) = tenv_pinst (pshift m) (tenv_pinst σ Θ).
Proof. rewrite !tenv_pinst_comp. apply tenv_pinst_ext. apply pup_shift_fn. Qed.

Lemma pup_shift_sf m σ F :
  sf_pinst (pup m σ) (sf_pinst (pshift m) F) = sf_pinst (pshift m) (sf_pinst σ F).
Proof. rewrite !sf_pinst_comp. apply sf_pinst_ext. apply pup_shift_fn. Qed.

Lemma lenv_pinst_pvar' Δ : lenv_pinst pvar Δ = Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite pinst_ty_pvar, IH. Qed.

Lemma tenv_pinst_pvar' Θ : tenv_pinst pvar Θ = Θ.
Proof.
  unfold tenv_pinst. rewrite <-(map_fmap_id Θ) at 2. apply map_fmap_ext.
  intros _ [S x a t] _. unfold tentry_pinst. simpl. by rewrite pt_inst_pvar.
Qed.

Lemma sf_pinst_pvar' F : sf_pinst pvar F = F.
Proof.
  destruct F as [X o]. unfold sf_pinst. simpl. f_equal; last first.
  { destruct o as [[u|]|]; simpl; by rewrite ?pt_inst_pvar. }
  apply set_eq. intros y. rewrite elem_of_map. split; [intros (y0 & -> & Hy); by rewrite pt_inst_pvar|].
  intros Hy. exists y. by rewrite pt_inst_pvar.
Qed.

(** Closing m shifted variables at xs undoes the shift. *)
Lemma plist_shift_fn xs m a : length xs = m → pt_inst (plist xs) (pshift m a) = pvar a.
Proof. intros Hl. unfold pshift. rewrite pt_inst_pvar_at. by apply plist_shift. Qed.

Lemma pshift_back_ty xs m T : length xs = m → pinst_ty (plist xs) (pinst_ty (pshift m) T) = T.
Proof.
  intros Hl. rewrite pinst_ty_comp, (pinst_ty_ext _ _ pvar), pinst_ty_pvar; [done|].
  intros a. by apply plist_shift_fn.
Qed.

Lemma pshift_back_lenv xs m Δ : length xs = m → lenv_pinst (plist xs) (lenv_pinst (pshift m) Δ) = Δ.
Proof.
  intros Hl. rewrite lenv_pinst_comp, (lenv_pinst_ext _ pvar), lenv_pinst_pvar'; [done|].
  intros a. by apply plist_shift_fn.
Qed.

Lemma pshift_back_tenv xs m Θ : length xs = m → tenv_pinst (plist xs) (tenv_pinst (pshift m) Θ) = Θ.
Proof.
  intros Hl. rewrite tenv_pinst_comp, (tenv_pinst_ext _ pvar), tenv_pinst_pvar'; [done|].
  intros a. by apply plist_shift_fn.
Qed.

Lemma pshift_back_sf xs m F : length xs = m → sf_pinst (plist xs) (sf_pinst (pshift m) F) = F.
Proof.
  intros Hl. rewrite sf_pinst_comp, (sf_pinst_ext _ pvar), sf_pinst_pvar'; [done|].
  intros a. by apply plist_shift_fn.
Qed.

(** ** The order under an instantiation *)

Lemma bcs_close xs m C : length xs = m → bcs_inst (plist xs) (bcs_inst (pshift m) C) = C.
Proof.
  intros Hl. rewrite bcs_inst_comp, (bcs_inst_ext _ pvar), bcs_inst_pvar; [done|].
  intros a. by apply plist_shift_fn.
Qed.

Lemma ids_close xs m : length xs = m → pt_inst (plist xs) <$> ids m = xs.
Proof.
  intros Hl. apply list_eq. intros i. rewrite list_lookup_fmap. destruct (decide (i < m)) as [Hi|Hi].
  - rewrite ids_lookup by done. simpl. rewrite pt_inst_pvar_at. unfold plist.
    destruct (xs !! i) eqn:E; [done|]. apply lookup_ge_None in E. lia.
  - rewrite (lookup_ge_None_2 (ids m)) by (rewrite length_ids; lia).
    rewrite lookup_ge_None_2 by lia. done.
Qed.

Section order.
  Context (W : sworld) (Hfc : facts_const W).

  Lemma slt_hinst σ Γ Γ' x y : hinst W σ Γ Γ' → slt W Γ x y → slt W Γ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros Hh H. by eapply slt_inst. Qed.

  Lemma sle_hinst σ Γ Γ' x y : hinst W σ Γ Γ' → sle W Γ x y → sle W Γ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros Hh [->|H]; [by left|right]. by eapply slt_hinst. Qed.

  Lemma hold_at_hinst σ Γ Γ' C xs : hinst W σ Γ Γ' → hold_at W Γ C xs →
    hold_at W Γ' (bcs_inst σ C) (pt_inst σ <$> xs).
  Proof.
    intros Hh HC x y H. apply bcs_at_inst in H as ([u v] & Hat & Heq). injection Heq as -> ->.
    by eapply slt_hinst, HC.
  Qed.

  Lemma lbx_below_h_hinst σ Γ Γ' lb H b : hinst W σ Γ Γ' → lbx_below_h W Γ lb H b →
    lbx_below_h W Γ' (lb_map (pt_inst σ) lb) (set_map (pt_inst σ) H) b.
  Proof.
    intros Hh. destruct lb as [| |x]; simpl; [|done|].
    - intros [-> ->]. by rewrite set_map_empty.
    - intros [Hle ->]. split; [|done]. intros y (y0 & -> & Hy0)%elem_of_map. by eapply sle_hinst, Hle.
  Qed.

  Lemma ub_below_s_hinst σ Γ Γ' ub F : hinst W σ Γ Γ' → ub_below_s W Γ ub F →
    ub_below_s W Γ' (pt_inst σ <$> ub) (sf_pinst σ F).
  Proof.
    intros Hh. destruct ub as [x|]; simpl; [|done]. intros (H1 & H2). destruct F as [X o].
    unfold sf_pinst. simpl in *. split.
    - intros y (y0 & -> & Hy0)%elem_of_map. by eapply slt_hinst, H1.
    - intros r Hr. destruct o as [r0|]; [|done]. simpl in Hr.
      injection Hr as <-. specialize (H2 r0 eq_refl). destruct r0; simpl in *; [|done].
      by eapply sle_hinst.
  Qed.

  Lemma ub_below_u_hinst σ Γ Γ' ub F : hinst W σ Γ Γ' → ub_below_u W Γ ub F →
    ub_below_u W Γ' (ub_map (pt_inst σ) ub) (sf_pinst σ F).
  Proof.
    intros Hh. destruct ub as [|x|]; simpl; [done| |].
    - intros H. by apply (ub_below_s_hinst σ Γ Γ' (Some x) F).
    - intros ->. unfold sf_pinst. simpl. by rewrite set_map_empty.
  Qed.

  (** A fact of Γ, shifted past m new variables, holds in the opened
      context. *)
  Lemma slt_open_shift m C Γ x y : slt W Γ x y →
    slt W (hc_open m C Γ) (pt_inst (pshift m) x) (pt_inst (pshift m) y).
  Proof.
    intros H. eapply slt_inst; [done|exact H|]. intros u v (C0 & ys & Hin & Hat).
    apply fl_h. exists (bcs_inst (pshift m) C0), (pt_inst (pshift m) <$> ys). split.
    - simpl. apply elem_of_app. left. apply list_elem_of_fmap. by exists (C0, ys).
    - apply bcs_at_inst. by exists (FLt u v).
  Qed.

  Lemma hinst_open σ Γ Γ' m C : hinst W σ Γ Γ' →
    hinst W (pup m σ) (hc_open m C Γ) (hc_open m (bcs_inst σ C) Γ').
  Proof.
    intros Hh u v (C' & ys & Hin & Hat). simpl in Hin. apply elem_of_app in Hin as [Hin|Hin].
    - apply list_elem_of_fmap in Hin as ([C0 ys0] & Heq & Hin). injection Heq as -> ->.
      apply bcs_at_inst in Hat as ([u0 v0] & Hat & Heq). injection Heq as -> ->.
      rewrite !pup_shift_pt. apply slt_open_shift. apply Hh. by exists C0, ys0.
    - apply list_elem_of_singleton in Hin. injection Hin as -> ->.
      apply fl_h. exists (bcs_inst (pshift m) (bcs_inst σ C)), (ids m). split.
      + simpl. apply elem_of_app. right. by apply list_elem_of_singleton.
      + rewrite <-pup_shift_bcs, <-(pup_ids m σ). apply bcs_at_inst. by exists (FLt u v).
  Qed.

  (** An instance at which C holds closes the opening. *)
  Lemma hinst_close Γ m C xs : length xs = m → hold_at W Γ C xs → hinst W (plist xs) (hc_open m C Γ) Γ.
  Proof.
    intros Hl HC u v (C' & ys & Hin & Hat). simpl in Hin. apply elem_of_app in Hin as [Hin|Hin].
    - apply list_elem_of_fmap in Hin as ([C0 ys0] & Heq & Hin). injection Heq as -> ->.
      apply bcs_at_inst in Hat as ([u0 v0] & Hat & Heq). injection Heq as -> ->.
      rewrite !pshift_back by done. apply fl_h. by exists C0, ys0.
    - apply list_elem_of_singleton in Hin. injection Hin as -> ->. apply HC.
      pose proof (bcs_close xs m C Hl) as Ec. pose proof (ids_close xs m Hl) as Ex.
      pose proof (proj2 (bcs_at_inst (plist xs) (bcs_inst (pshift m) C) (ids m)
        (FLt (pt_inst (plist xs) u) (pt_inst (plist xs) v)))) as H.
      rewrite Ec, Ex in H. apply H. by exists (FLt u v).
  Qed.
End order.

(** ** Subtyping, aging and creation under an instantiation *)

Lemma lb_lower_hinst W σ Γ Γ' n C lb lb' T : facts_const W →
  hinst W (pup n σ) (hc_open n C Γ) (hc_open n (bcs_inst σ C) Γ') →
  lb_lower W Γ n C lb lb' T →
  lb_lower W Γ' n (bcs_inst σ C) (lb_map (pt_inst σ) lb) (lb_map (pt_inst σ) lb') (pinst_ty (pup n σ) T).
Proof.
  intros Hfc Hh [->|H]; [by left|right].
  rewrite <-pup_shift_lb, heads_pinst, hbot_pinst. by eapply lbx_below_h_hinst.
Qed.

Lemma tsub_hinst W Γ T U : facts_const W → tsub W Γ T U →
  ∀ σ Γ', hinst W σ Γ Γ' → tsub W Γ' (pinst_ty σ T) (pinst_ty σ U).
Proof.
  intros Hfc. induction 1 as [Γ|Γ ub lb c T1 U a c' T1' U' a' Hc Ha _ IH1 _ IH2
    |Γ T1 U T1' U' _ IH1 _ IH2|Γ T1 U T1' U' _ IH1 _ IH2|Γ n k C ub c U U' c' Hc HU
    |Γ s s' x a a' mt Hs Ha|Γ lb lb' n C C' T T' HC Hlb _ IH]; intros σ Γ' Hh; simpl.
  - apply sub_unit.
  - apply sub_arr; [done|done|by apply IH1|by apply IH2].
  - apply sub_prod; [by apply IH1|by apply IH2].
  - apply sub_sum; [by apply IH1|by apply IH2].
  - apply sub_box; [done|]. destruct k as [|k].
    + by apply teq_pinst.
    + destruct HU as [->|(Heq & H1 & H2)]; [by left|right].
      split_and!; [by apply teq_pinst|by rewrite tcontr_pinst|by rewrite tcontr_pinst].
  - by apply sub_sess.
  - pose proof (hinst_open W Hfc σ Γ Γ' n C Hh) as Ho. apply sub_ex.
    + rewrite <-pup_shift_bcs, <-(pup_ids n σ). by eapply hold_at_hinst.
    + by eapply lb_lower_hinst.
    + by apply IH.
Qed.

Lemma tfree_pinst σ T : tfree T → tfree (pinst_ty σ T).
Proof. induction 1; simpl; constructor; done. Qed.

Lemma tage_pinst σ c T T' : tage c T T' → tage c (pinst_ty σ T) (pinst_ty σ T').
Proof.
  intros H. revert σ. induction H; intros σ; simpl.
  - by apply age_free, tfree_pinst.
  - by apply age_sess.
  - by apply age_idle.
  - by apply age_arr.
  - apply age_prod; auto.
  - apply age_sum; auto.
  - apply age_ex; auto.
Qed.

Lemma lage_pinst σ c Δ Δ' : lage c Δ Δ' → lage c (lenv_pinst σ Δ) (lenv_pinst σ Δ').
Proof. induction 1; simpl; constructor; try done. by apply tage_pinst. Qed.

Lemma thage_pinst σ c Θ Θ' : thage c Θ Θ' → thage c (tenv_pinst σ Θ) (tenv_pinst σ Θ').
Proof.
  intros H o. specialize (H o). unfold tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! o) as [e|], (Θ' !! o) as [e'|]; simpl; try done.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6). unfold tentry_pinst, pinst_sty. simpl.
  split_and!; try done; congruence.
Qed.

Lemma sf_pinst_abs_fut σ ub : sf_pinst σ (abs_fut ub) = abs_fut (ub_map (pt_inst σ) ub).
Proof. destruct ub; unfold sf_pinst; simpl; by rewrite set_map_empty. Qed.

(** ** The bridge condition under an instantiation

    σ moves the environment of C and leaves its facts and its tree
    alone, so a bridge of σ(C) is a bridge of C, and its outer points
    are the instances of the outer points of C. *)

Local Lemma outer_pt_inst' σ m C x : pn_vb (m + length (bc_env C)) (pt_name x) → ¬ in_tree m x →
  outer_pt m (bcs_inst σ C) x = pt_inst σ (outer_pt m C x).
Proof.
  intros Hs Hx. apply pn_vb_root in Hs as (j & Hj & Hjl).
  destruct (decide (j < m)) as [Hm|Hm].
  { exfalso. apply Hx. unfold in_tree. apply pn_vb_root. eauto. }
  destruct (lookup_lt_is_Some_2 (bc_env C) (j - m) ltac:(lia)) as [e He].
  unfold outer_pt. rewrite pt_inst_comp. apply pt_inst_ext_root. intros a Ha.
  change (pt_root x) with (pn_root (pt_name x)) in Ha. rewrite Hj in Ha. injection Ha as <-.
  unfold compose, plist. simpl.
  rewrite !lookup_app_r by (rewrite length_ids; lia). rewrite length_ids, list_lookup_fmap, He. done.
Qed.

Lemma cons_open_hinst W σ Γ Γ' m C : facts_const W → hinst W σ Γ Γ' →
  cons_open W Γ m C → cons_open W Γ' m (bcs_inst σ C).
Proof.
  intros Hfc Hh Hc z y Hb.
  assert (bridge_at m C z y) as Hb'.
  { unfold bridge_at, cfact_at, tree_step, cfact_at in *. simpl in Hb. rewrite length_fmap in Hb. exact Hb. }
  assert (pn_vb (m + length (bc_env C)) (pt_name z) ∧ pn_vb (m + length (bc_env C)) (pt_name y)) as [Hsz Hsy].
  { destruct Hb' as (_ & _ & [[_ Hsc]|(v & u & [_ Hs1] & _ & _ & [_ Hs2])]); [exact Hsc|].
    destruct Hs1, Hs2. by split. }
  pose proof Hb' as (Hz & Hy & _).
  rewrite !outer_pt_inst' by done. by eapply slt_hinst, Hc.
Qed.
Local Lemma ctx_pt_inst' σ C x : pn_vb (1 + length (bc_env C)) (pt_name x) → ¬ in_tree0 x →
  ctx_pt (bcs_inst σ C) x = pt_inst σ (ctx_pt C x).
Proof.
  intros Hs Hx. apply pn_vb_root in Hs as ([|j] & Hj & Hjl); [by destruct Hx|].
  simpl in Hjl. destruct (lookup_lt_is_Some_2 (bc_env C) j ltac:(lia)) as [e He].
  unfold ctx_pt. rewrite pt_inst_comp. apply pt_inst_ext_root. intros a Ha.
  change (pt_root x) with (pn_root (pt_name x)) in Ha. rewrite Hj in Ha. injection Ha as <-.
  unfold compose, plist. simpl. by rewrite list_lookup_fmap, He.
Qed.

Local Lemma new_step_inst' σ C : new_step (bcs_inst σ C) = new_step C.
Proof. destruct C as [env P]. unfold new_step, bcs_inst. simpl. by rewrite length_fmap. Qed.

Local Lemma cfact_inst' σ C x y : cfact (bcs_inst σ C) x y ↔ cfact C x y.
Proof. destruct C as [env P]. unfold cfact, bcs_inst. simpl. by rewrite length_fmap. Qed.

Lemma new_ok_hinst N W σ Γ Γ' C : facts_const W → hinst W σ Γ Γ' →
  new_ok N W Γ C → new_ok N W Γ' (bcs_inst σ C).
Proof.
  intros Hfc Hh [[Hcyc Hbr] Hrk]. split; [split|].
  - unfold tree_acyclic. by rewrite new_step_inst'.
  - by eapply cons_open_hinst.
  - intros HN. destruct (Hrk HN) as (Hwf & Sr & Hne & Hex & Hst & Hen).
    assert (∀ x y, cfact C x y → pn_vb (1 + length (bc_env C)) (pt_name x) ∧ pn_vb (1 + length (bc_env C)) (pt_name y))
      as Hsc by (intros x y [_ H]; exact H).
    split; [by rewrite new_step_inst'|].
    exists (λ u P, ∃ T, Sr u T ∧ P = pt_inst σ <$> T). split_and!.
    + intros s P (T & HT & ->). destruct T as [|t T]; [exfalso; by apply (Hne s [] HT)|cbn; congruence].
    + intros u y Hf Hu Hy. apply cfact_inst' in Hf. destruct (Hex u y Hf Hu Hy) as (T & HT & Hlt).
      exists (pt_inst σ <$> T). split; [eauto|]. rewrite ctx_pt_inst' by (try done; apply (Hsc u y Hf)).
      intros p (t & -> & Ht)%list_elem_of_fmap. by eapply slt_hinst, Hlt.
    + intros s P s' (T & HT & ->) Hs'. rewrite new_step_inst' in Hs'.
      destruct (Hst s T s' HT Hs') as (T' & HT' & Hlt). exists (pt_inst σ <$> T'). split; [eauto|].
      intros p (t' & -> & Ht')%list_elem_of_fmap. destruct (Hlt t' Ht') as (t & Ht & Hl).
      exists (pt_inst σ t). split; [by apply list_elem_of_fmap_2|]. by eapply slt_hinst.
    + intros s P z (T & HT & ->) Hf Hz. apply cfact_inst' in Hf.
      rewrite ctx_pt_inst' by (try done; apply (Hsc z s Hf)).
      destruct (Hen s T z HT Hf Hz) as (t & Ht & Hl).
      exists (pt_inst σ t). split; [by apply list_elem_of_fmap_2|]. by eapply slt_hinst.
Qed.




(** ** The substitution lemma *)

Lemma lb_heads_pinst σ lb : lb_heads (lb_map (pt_inst σ) lb) = set_map (pt_inst σ) (lb_heads lb).
Proof. destruct lb; simpl; set_solver. Qed.

Local Ltac fut_p H :=
  rewrite ?sf_pinst_unionb, ?set_map_union_L, <-?tenv_heads_pinst, <-?lenv_heads_pinst,
    <-?heads_pinst, <-?lb_heads_pinst in H.

Theorem typed_pinst W N Θ Γ Δ F e T c : facts_const W →
  typed W N Θ Γ Δ F e T c → ∀ σ Γ', hinst W σ Γ Γ' →
  typed W N (tenv_pinst σ Θ) Γ' (lenv_pinst σ Δ) (sf_pinst σ F) e (pinst_ty σ T) c.
Proof.
  intros Hfc. induction 1 as
    [Γ Δ F HΔ
    |Γ Δ F x T HΔ
    |Γ Δ F o S x a mt HΔ Hamt
    |Θ Θh Γ Δ Δh F e T U ub lb c a Hlb Hth Hlc HTc Hb IH
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 Hsp Hl Hub H1 IH1 Hta Hla H2 IH2 Hc
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hag
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
    |i Θ Γ Δ F e T U c HTc H IH
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 c1 c2 Hsp Hl H0 IH0 Hta Hla H1 IH1 H2 IH2
    |Γ Δ F e m k C ub c U HΔ HUc Hb IH
    |Θ Γ Δ F e m k C ub c U xs ss c0 Hxs HC Hss Hsi Hub H IH
    |Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 Hu Hsc [Hbot Hhd] Hub H IH Hag Hsub
    |Θ Γ Δ F e S0 x m T S a mS c0 Hu Hsc Hub H IH
    |Θ Γ Δ F e S0 x a mS c0 Hu Hub H IH
    |i Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
    |Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
    |Θ Γ Δ F e S x a1 m1 a2 m2 c0 H IH Hl1 Hl2
    |Θ Γ Δ F e ub lb c' a c0 H IH
    |Γ Δ F C S m1 m2 HΔ HC Htk HSc
    |Γ Δ F x κf S m1 m2 HΔ Htk HSc
    |Θ Γ Δ F e T T' c c' H IH Hsub Hc HTc
    |Θ Γ Δ F e lb m C T xs c Hxs HC Hlb Hwf H IH
    |Θ Γ Δ F e i lb m C T U c Hi Hun Hcons H IH]; intros σ Γ' Hh; cbn [pinst_ty].
  - rewrite tenv_pinst_empty. by apply e_unit, lenv_unl_pinst.
  - rewrite tenv_pinst_empty. by apply e_var, lenv_only_pinst.
  - rewrite tenv_pinst_singleton. by apply e_chan; [apply lenv_unl_pinst|].
  - (* E-Abs *)
    pose proof (IH σ Γ' Hh) as Hb'. rewrite sf_pinst_abs_fut in Hb'. cbn [lenv_pinst fmap list_fmap option_fmap option_map] in Hb'.
    eapply e_abs; [|by apply thage_pinst|by apply lage_pinst|by rewrite tcontr_pinst|exact Hb'].
    rewrite tenv_heads_pinst, lenv_heads_pinst, lenv_bot_pinst, <-set_map_union_L.
    eapply lbx_below_h_hinst; [done|exact Hh|exact Hlb].
  - (* E-App *)
    pose proof (IH1 σ Γ' Hh) as K1. pose proof (IH2 σ Γ' Hh) as K2. fut_p K1. fut_p K2.
    rewrite <-(lenv_bot_pinst σ Δ2) in K1. rewrite <-(lb_bot_map (pt_inst σ) lb) in K2.
    eapply e_app; [by apply tsplit_pinst|by apply lenv_split_pinst|eapply ub_below_u_hinst; [done|exact Hh|exact Hub]
      |exact K1|by apply thage_pinst|by apply lage_pinst|exact K2|done].
  - (* E-Pair *)
    pose proof (IH1 σ Γ' Hh) as K1. pose proof (IH2 σ Γ' Hh) as K2. fut_p K1. fut_p K2.
    rewrite <-(lenv_bot_pinst σ Δ2) in K1. rewrite <-(hbot_pinst σ T1) in K2.
    eapply e_pair; [by apply tsplit_pinst|by apply lenv_split_pinst|exact K1|by apply thage_pinst
      |by apply lage_pinst|exact K2|by apply tage_pinst].
  - (* E-LetU *)
    pose proof (IH1 σ Γ' Hh) as K1. pose proof (IH2 σ Γ' Hh) as K2. fut_p K1.
    rewrite <-(lenv_bot_pinst σ Δ2) in K1.
    eapply e_letu; [by apply tsplit_pinst|by apply lenv_split_pinst|exact K1|by apply thage_pinst
      |by apply lage_pinst|exact K2].
  - (* E-LetP *)
    pose proof (IH1 σ Γ' Hh) as K1. pose proof (IH2 σ Γ' Hh) as K2. fut_p K1.
    rewrite <-(lenv_bot_pinst σ Δ2) in K1.
    eapply e_letp; [by apply tsplit_pinst|by apply lenv_split_pinst|exact K1|by apply thage_pinst
      |by apply lage_pinst|exact K2].
  - (* E-Inj *)
    pose proof (IH σ Γ' Hh) as K. apply e_inj; [change (tcontr (pinst_ty σ (TSum T U))); by rewrite tcontr_pinst|].
    destruct i; exact K.
  - (* E-Case *)
    pose proof (IH0 σ Γ' Hh) as K0. pose proof (IH1 σ Γ' Hh) as K1. pose proof (IH2 σ Γ' Hh) as K2. fut_p K0.
    rewrite <-(lenv_bot_pinst σ Δ2) in K0.
    eapply e_case; [by apply tsplit_pinst|by apply lenv_split_pinst|exact K0|by apply thage_pinst
      |by apply lage_pinst|exact K1|exact K2].
  - (* E-Box *)
    rewrite tenv_pinst_empty. apply e_box; [by apply lenv_unl_pinst|by rewrite tcontr_pinst|].
    intros ss Hl Hs. pose proof (IH ss Hl Hs (pup m σ) _ (hinst_open W Hfc σ Γ Γ' m C Hh)) as K.
    rewrite tenv_pinst_empty, pup_shift_lenv, pinst_sinst in K.
    replace (sf_pinst (pup m σ) (∅, Some (rest_of ub))) with
      ((∅, Some (rest_of (pt_inst (pup m σ) <$> ub))) : sfuture) in K
      by (unfold sf_pinst; simpl; rewrite set_map_empty; by destruct ub).
    exact K.
  - (* E-Force *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. subst m.
    rewrite pinst_sinst, pinst_ty_inst.
    eapply e_force; [by rewrite length_fmap|eapply hold_at_hinst; [done|exact Hh|exact HC]|done|done| |exact K].
    rewrite <-option_fmap_compose. apply (ub_below_s_hinst W Hfc σ Γ Γ') in Hub; [|done].
    rewrite <-option_fmap_compose in Hub. erewrite option_fmap_ext; [exact Hub|].
    intros u. simpl. symmetry. apply pt_inst_plist_inst.
  - (* E-Send *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. rewrite pt_inst_shift.
    eapply e_send; [exact Hu|exact Hsc|split|by apply (ub_below_s_hinst W Hfc σ Γ Γ' (Some x))
      |exact K|by apply tage_pinst|].
    + rewrite hbot_payload_at in Hbot. by rewrite hbot_payload_at.
    + intros y Hy. rewrite <-pinst_payload_at, heads_pinst in Hy by done.
      apply elem_of_map in Hy as (y0 & -> & Hy0). by eapply slt_hinst, Hhd.
    + rewrite <-pinst_payload_at by done. eapply tsub_hinst; [done|exact Hsub|exact Hh].
  - (* E-Recv *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. rewrite pt_inst_shift, pinst_payload_at by done.
    eapply e_recv; [exact Hu|exact Hsc|by apply (ub_below_s_hinst W Hfc σ Γ Γ' (Some x))|exact K].
  - (* E-Close *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K.
    eapply e_close; [exact Hu|by apply (ub_below_s_hinst W Hfc σ Γ Γ' (Some x))|exact K].
  - (* E-Select *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. rewrite pt_inst_sel.
    eapply e_select; [exact Hu|by apply (ub_below_s_hinst W Hfc σ Γ Γ' (Some x))|exact K].
  - (* E-Branch *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. rewrite !pt_inst_bra.
    eapply e_branch; [exact Hu|by apply (ub_below_s_hinst W Hfc σ Γ Γ' (Some x))|exact K].
  - (* E-Link *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. rewrite pt_inst_dual in K.
    eapply e_link; [exact K|done|done].
  - (* E-Spawn *)
    pose proof (IH σ Γ' Hh) as K. cbn [pinst_ty] in K. by eapply e_spawn.
  - (* E-New *)
    rewrite tenv_pinst_empty, pt_inst_dual, pt_inst_pup1_0.
    apply e_new; [by apply lenv_unl_pinst|eapply new_ok_hinst; [done|exact Hh|exact HC]|done|done].
  - (* E-New-Field *)
    rewrite tenv_pinst_empty, pt_inst_dual, pt_inst_field.
    apply e_new_fld; [by apply lenv_unl_pinst|done|done].
  - (* E-Sub *)
    eapply e_sub; [exact (IH σ Γ' Hh)|eapply tsub_hinst; [done|exact Hsub|exact Hh]|done|by rewrite !tcontr_pinst].
  - (* E-Pack *)
    pose proof (IH σ Γ' Hh) as K. subst m. rewrite pinst_ty_inst in K.
    eapply (e_pack _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs)); [by rewrite length_fmap|eapply hold_at_hinst; [done|exact Hh|exact HC]
      | | |exact K].
    + rewrite <-pinst_ty_inst, heads_pinst, hbot_pinst. eapply lbx_below_h_hinst; [done|exact Hh|exact Hlb].
    + unfold ex_wf. rewrite <-pup_shift_lb, heads_pinst, hbot_pinst.
      eapply lbx_below_h_hinst; [done|by apply hinst_open|exact Hwf].
  - (* E-Open *)
    pose proof (IH (pup m σ) _ (hinst_open W Hfc σ Γ Γ' m C Hh)) as K.
    rewrite pup_shift_tenv, lenv_pinst_insert, pup_shift_lenv, pup_shift_sf, pup_shift_ty in K.
    eapply e_open; [rewrite lenv_pinst_lookup, Hi; done|by rewrite unlimited_pinst_iff
      |eapply cons_open_hinst; [done|exact Hh|exact Hcons]|exact K].
Qed.

(** ** Closing an opening

    A derivation under [hc_open m C Γ] over shifted contexts gives one
    over Γ at any instance xs at which C holds. *)
Corollary typed_open_inst W N Θ Γ Δ F e T c m C xs : facts_const W →
  length xs = m → hold_at W Γ C xs →
  typed W N (tenv_pinst (pshift m) Θ) (hc_open m C Γ) Δ (sf_pinst (pshift m) F) e (pinst_ty (pshift m) T) c →
  typed W N Θ Γ (lenv_pinst (plist xs) Δ) F e T c.
Proof.
  intros Hfc Hl HC H. pose proof (typed_pinst W N _ _ _ _ _ _ _ Hfc H (plist xs) Γ (hinst_close W Γ m C xs Hl HC)) as K.
  by rewrite pshift_back_tenv, pshift_back_sf, pshift_back_ty in K.
Qed.

(** A constraint that holds under an opening of C holds at every
    instance of C. *)
Lemma hold_close W Γ m C C' xs : facts_const W → length xs = m → hold_at W Γ C xs →
  hold_at W (hc_open m C Γ) (bcs_inst (pshift m) C') (ids m) → hold_at W Γ C' xs.
Proof.
  intros Hfc Hl HC H. pose proof (hold_at_hinst W Hfc _ _ _ _ _ (hinst_close W Γ m C xs Hl HC) H) as K.
  by rewrite bcs_close, ids_close in K.
Qed.

Lemma tsub_close W Γ m C xs T U : facts_const W → length xs = m → hold_at W Γ C xs →
  tsub W (hc_open m C Γ) T U → tsub W Γ (ty_inst xs T) (ty_inst xs U).
Proof. intros Hfc Hl HC H. exact (tsub_hinst W _ _ _ Hfc H (plist xs) Γ (hinst_close W Γ m C xs Hl HC)). Qed.
