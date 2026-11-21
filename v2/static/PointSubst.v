(** * Point substitution (stage S2)

    [typed_pinst]: a derivation over Γ instantiates along σ to a
    derivation over any Γ' that proves the instantiated hypotheses of Γ
    ([hinst]). Terms mention no point and stay. Session types carry no
    free point variable, so σ leaves them alone and commutes with
    unfolding and session substitution. A payload read at E-Send and
    E-Recv is point-closed below its binder ([pscoped]), so σ moves only
    its carrier ([pinst_payload_at]). The binders E-Box and E-Open lift σ
    to [pup m σ] over the context [hc_open m C Γ]. *)

From GV Require Export static.Weakening.

(** ** Points and constraints *)

(** Instantiating below m binders, then closing them with σ(xs), is
    closing them with xs, then instantiating. *)
Lemma plist_pup σ xs a :
  pt_inst (plist (pt_inst σ <$> xs)) (pup (length xs) σ a) = pt_inst σ (plist xs a).
Proof.
  unfold pup. case_decide.
  - rewrite pt_inst_pvar_at. unfold plist. rewrite list_lookup_fmap, length_fmap.
    destruct (xs !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
  - rewrite pt_inst_comp. unfold plist at 2. rewrite lookup_ge_None_2 by lia.
    rewrite pt_inst_pvar_at. rewrite (pt_inst_ext _ pvar), pt_inst_pvar; [done|].
    intros b. unfold compose. rewrite pt_inst_pvar_at. apply plist_shift. by rewrite length_fmap.
Qed.

Lemma pinst_ty_inst σ xs T :
  pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup (length xs) σ) T).
Proof.
  unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. unfold compose.
  by rewrite plist_pup.
Qed.

Lemma pt_inst_plist_inst σ xs u :
  pt_inst σ (pt_inst (plist xs) u) = pt_inst (plist (pt_inst σ <$> xs)) (pt_inst (pup (length xs) σ) u).
Proof.
  rewrite !pt_inst_comp. apply pt_inst_ext. intros a. unfold compose. by rewrite plist_pup.
Qed.

Lemma pt_inst_sel σ x i : pt_inst σ (sel_pt x i) = sel_pt (pt_inst σ x) i.
Proof. unfold sel_pt. by rewrite pt_inst_dual, pt_inst_field. Qed.

Lemma pt_inst_bra σ x i : pt_inst σ (bra_pt x i) = bra_pt (pt_inst σ x) i.
Proof. unfold bra_pt. by rewrite pt_inst_field. Qed.

Lemma fact_map_ext_scoped k σ τ g :
  fact_scoped k g → (∀ a, a < k → σ a = τ a) → fact_map (pt_inst σ) g = fact_map (pt_inst τ) g.
Proof.
  destruct g as [x y]. intros [Hx Hy] H. simpl. f_equal; apply pt_inst_ext_root; intros a Ha.
  - apply H. apply pn_vb_root in Hx as (b & Hb & ?). unfold pt_root in Ha. congruence.
  - apply H. apply pn_vb_root in Hy as (b & Hb & ?). unfold pt_root in Ha. congruence.
Qed.

Lemma plist_open xs env a :
  a < length xs + length env →
  pt_inst (plist xs) (pup (length xs) (plist env) a) = plist (xs ++ env) a.
Proof.
  intros Ha. unfold pup. case_decide.
  - rewrite pt_inst_pvar_at. unfold plist. rewrite lookup_app_l by lia.
    destruct (xs !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
  - rewrite pt_inst_comp. rewrite (pt_inst_ext _ pvar), pt_inst_pvar.
    + unfold plist. rewrite lookup_app_r by lia.
      destruct (env !! (a - length xs)) eqn:E; [done|]. apply lookup_ge_None in E. lia.
    + intros b. unfold compose. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma bcs_at_iff C xs g :
  bcs_at C xs g ↔ ∃ f0, bc_facts C f0 ∧ fact_scoped (length xs + length (bc_env C)) f0 ∧
    g = fact_map (pt_inst (plist (xs ++ bc_env C))) f0.
Proof.
  split.
  - intros (g0 & (f0 & Hf & Hs & ->) & ->). exists f0. split_and!; [done|done|].
    rewrite fact_map_comp, (fact_map_ext _ (pt_inst (pt_inst (plist xs) ∘ pup (length xs) (plist (bc_env C)))))
      by (intros; apply pt_inst_comp).
    apply fact_map_ext_scoped with (k := length xs + length (bc_env C)); [done|].
    intros a Ha. unfold compose. by apply plist_open.
  - intros (f0 & Hf & Hs & ->). eexists. split; [exists f0; split_and!; [done|done|done]|].
    symmetry. rewrite fact_map_comp, (fact_map_ext _ (pt_inst (pt_inst (plist xs) ∘ pup (length xs) (plist (bc_env C)))))
      by (intros; apply pt_inst_comp).
    apply fact_map_ext_scoped with (k := length xs + length (bc_env C)); [done|].
    intros a Ha. unfold compose. by apply plist_open.
Qed.

Lemma plist_inst_lookup σ l a :
  a < length l → plist (pt_inst σ <$> l) a = pt_inst σ (plist l a).
Proof.
  intros Ha. unfold plist. rewrite list_lookup_fmap.
  destruct (l !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
Qed.

Lemma bcs_at_inst τ C xs g :
  bcs_at (bcs_inst τ C) (pt_inst τ <$> xs) g ↔ ∃ g0, bcs_at C xs g0 ∧ g = fact_map (pt_inst τ) g0.
Proof.
  destruct C as [env P]. rewrite bcs_at_iff. setoid_rewrite bcs_at_iff. simpl.
  rewrite !length_fmap, <-fmap_app.
  assert (∀ f0, fact_scoped (length xs + length env) f0 →
            fact_map (pt_inst (plist (pt_inst τ <$> xs ++ env))) f0 =
            fact_map (pt_inst τ) (fact_map (pt_inst (plist (xs ++ env))) f0)) as Heq.
  { intros f0 Hs. symmetry. rewrite fact_map_comp, (fact_map_ext _ (pt_inst (pt_inst τ ∘ plist (xs ++ env))))
      by (intros; apply pt_inst_comp).
    apply fact_map_ext_scoped with (k := length xs + length env); [done|].
    intros a Ha. unfold compose. symmetry. apply plist_inst_lookup. rewrite length_app. lia. }
  split.
  - intros (f0 & Hf & Hs & ->). eexists. split; [exists f0; split_and!; [done|done|done]|].
    by apply Heq.
  - intros (g0 & (f0 & Hf & Hs & ->) & ->). exists f0. split_and!; [done|done|]. by rewrite Heq.
Qed.

(** ** Types *)

Lemma pscoped_ext T : ∀ k σ τ, pscoped k T → (∀ a, a < k → σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  assert (∀ k σ τ x, pt_pscoped k x → (∀ a, a < k → σ a = τ a) → pt_inst σ x = pt_inst τ x) as Hpt.
  { intros k σ τ x Hx H. apply pt_inst_ext_root. intros a Ha. by apply H, Hx. }
  assert (∀ k σ τ, (∀ a, a < k → σ a = τ a) → ∀ n a, a < n + k → pup n σ a = pup n τ a) as Hup.
  { intros k σ τ H n a Ha. unfold pup. case_decide; [done|]. rewrite H by lia. done. }
  induction T; intros k0 σ τ HT H; simpl in *; destruct_and?; try done.
  - f_equal; try by eauto.
    + destruct ub; simpl; try done. f_equal. eauto.
    + destruct lb; simpl; try done. f_equal. eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal.
    + destruct C as [env P]. unfold bcs_inst. simpl in *. f_equal.
      apply list_fmap_ext. intros i x Hi. eapply Hpt; [|done].
      by eapply Forall_lookup_1.
    + destruct ub; simpl; [|done]. f_equal. eapply Hpt; [by eauto|]. by apply Hup.
    + eapply IHT; [done|]. by apply Hup.
  - f_equal. eauto.
  - f_equal.
    + destruct lb; simpl; try done. f_equal. eauto.
    + destruct C as [env P]. unfold bcs_inst. simpl in *. f_equal.
      apply list_fmap_ext. intros i x Hi. eapply Hpt; [|done].
      by eapply Forall_lookup_1.
    + eapply IHT; [done|]. by apply Hup.
Qed.

Lemma pinst_payload_at σ m T x :
  pscoped m T → pinst_ty σ (payload_at m T x) = payload_at m T (pt_inst σ x).
Proof.
  intros HT. unfold payload_at, ty_inst. rewrite pinst_ty_comp.
  apply (pscoped_ext T m); [done|]. intros a Ha. unfold compose.
  assert (∀ y, payload_pts y m !! a = Some (y·a)) as Hl.
  { intros y. unfold payload_pts. rewrite list_lookup_fmap, lookup_seq_lt by done. done. }
  rewrite (plist_lookup _ _ _ (Hl x)), (plist_lookup _ _ _ (Hl (pt_inst σ x))). apply pt_inst_field.
Qed.

Lemma pinst_sinst T : ∀ σ τ, pinst_ty σ (sinst_ty τ T) = sinst_ty τ (pinst_ty σ T).
Proof. induction T; intros σ τ; simpl; congruence. Qed.

Lemma eqT_pinst ρ T : ∀ U σ, eqT ρ T U → eqT ρ (pinst_ty σ T) (pinst_ty σ U).
Proof.
  induction T; intros [] σ H; simpl in *; try done.
  all: destruct_and?; subst; split_and?; eauto.
  all: repeat case_match; subst; eauto.
Qed.

Lemma teq_pinst σ T U : teq T U → teq (pinst_ty σ T) (pinst_ty σ U).
Proof. apply eqT_pinst. Qed.

(** ** Contexts *)

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_pinst_singleton σ o S x a mt :
  tenv_pinst σ {[o := TE S x a mt]} = {[o := TE S (pt_inst σ x) a mt]}.
Proof. unfold tenv_pinst. by rewrite map_fmap_singleton. Qed.

Lemma tsplit_pinst σ Θ Θ1 Θ2 :
  tsplit Θ Θ1 Θ2 → tsplit (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
Proof.
  intros [Hd ->]. split; [by apply map_disjoint_fmap|]. unfold tenv_pinst. by rewrite map_fmap_union.
Qed.

Lemma tenv_heads_pinst σ Θ : tenv_heads (tenv_pinst σ Θ) = set_map (pt_inst σ) (tenv_heads Θ).
Proof.
  apply set_eq. intros y. rewrite elem_of_map, elem_of_tenv_heads. unfold tenv_pinst.
  setoid_rewrite elem_of_tenv_heads. setoid_rewrite lookup_fmap. split.
  - intros (o & e & He & ->). destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=.
    exists (te_pt e0)‾. split; [symmetry; apply pt_inst_dual|]. eauto.
  - intros (y0 & -> & o & e & He & ->). exists o, (tentry_pinst σ e). rewrite He.
    split; [done|]. apply pt_inst_dual.
Qed.

Lemma lenv_only_pinst σ Δ x T :
  lenv_only Δ x T → lenv_only (lenv_pinst σ Δ) x (pinst_ty σ T).
Proof.
  intros [Hx Hy]. split; [by rewrite lenv_pinst_lookup, Hx|].
  intros y σ' Hne Hσ. rewrite lenv_pinst_lookup in Hσ.
  destruct (Δ !! y) as [[T0|]|] eqn:E; simplify_eq/=.
  apply unlimited_pinst, (Hy y _ Hne E).
Qed.

Lemma lenv_split_pinst σ Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2).
Proof.
  induction 1; simpl; constructor; try done. by apply unlimited_pinst.
Qed.

Lemma lenv_unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
Proof.
  intros H o Ho. unfold lenv_pinst in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & -> & HU)]; [by left|right].
  eexists _. split; [done|]. by apply unlimited_pinst.
Qed.

Lemma lenv_heads_pinst σ Δ : lenv_heads (lenv_pinst σ Δ) = set_map (pt_inst σ) (lenv_heads Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [by rewrite set_map_empty|..|done].
  by rewrite set_map_union_L, heads_pinst, IH.
Qed.

Lemma lenv_bot_pinst σ Δ : lenv_bot (lenv_pinst σ Δ) = lenv_bot Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?hbot_pinst; congruence. Qed.

Lemma lenv_pinst_insert σ Δ i T :
  lenv_pinst σ (<[i := Some T]> Δ) = <[i := Some (pinst_ty σ T)]> (lenv_pinst σ Δ).
Proof. unfold lenv_pinst. by rewrite list_fmap_insert. Qed.

Lemma fs_var_pinst σ o : fs_var (futrest_pinst σ <$> o) = frest_pinst σ <$> fs_var o.
Proof. by destruct o as [[r|o']|]. Qed.

Lemma fs_bot_pinst σ o : fs_bot (futrest_pinst σ <$> o) = fs_bot o.
Proof. by destruct o as [[r|o']|]. Qed.

Lemma sf_pinst_unionb σ F X b :
  sf_pinst σ (sf_unionb F X b) = sf_unionb (sf_pinst σ F) (set_map (pt_inst σ) X) b.
Proof.
  destruct b; unfold sf_pinst, sf_unionb; simpl; rewrite set_map_union_L; [|done].
  by rewrite fs_var_pinst.
Qed.

Lemma sf_pinst_nil σ o : sf_pinst σ (∅, o) = (∅, futrest_pinst σ <$> o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** ** Facts *)

(** The facts of W sit at constant roots, the first half of [sworld_wf]. *)
Definition facts_const (W : sworld) : Prop :=
  ∀ x y, sw_facts W (FLt x y) → croot_in (sw_consts W) x ∧ croot_in (sw_consts W) y.

Lemma facts_const_wf W : sworld_wf W → facts_const W.
Proof. intros Hwf. exact (wf_facts _ Hwf). Qed.

Lemma sw_lt_pinst_fc W σ x y : facts_const W → W ⊢ₛ x ≺ y → W ⊢ₛ pt_inst σ x ≺ pt_inst σ y.
Proof.
  intros Hwf. apply tc_congruence. intros a b Hs.
  destruct Hs as [a b Hf|a|a].
  - destruct (Hwf a b Hf) as [[c [Hc _]] [d [Hd _]]].
    rewrite !pt_inst_novar by (intros ?; congruence). by apply ws_fact.
  - rewrite pt_inst_shift. apply ws_po.
  - rewrite pt_inst_shift, pt_inst_dual. apply ws_dpo.
Qed.

Lemma sw_lt_pinst W σ x y : sworld_wf W → W ⊢ₛ x ≺ y → W ⊢ₛ pt_inst σ x ≺ pt_inst σ y.
Proof. intros Hwf. by apply sw_lt_pinst_fc, facts_const_wf. Qed.

(** ** Conservativity of an opening

    [cons_of_hold]: an opening whose constraint holds at some instance is
    conservative. [cons_law]: the opening of the existential of E-New is
    [cons_new]: the opening of the existential of E-New is conservative
    under (wf-new), because every fact of its constraint ends in the tree
    of the new root, which no outer point reaches. Both ask only that the
    facts of W sit at constant roots. *)

Lemma pshift_back xs m x : length xs = m → pt_inst (plist xs) (pt_inst (pshift m) x) = x.
Proof.
  intros Hl. rewrite pt_inst_comp, (pt_inst_ext _ pvar); [apply pt_inst_pvar|].
  intros a. unfold compose, pshift. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma slt_inst W Γ Γ' τ x y : facts_const W → slt W Γ' x y →
  (∀ u v, hyp_fact (hc_hyps Γ') (FLt u v) → slt W Γ (pt_inst τ u) (pt_inst τ v)) →
  slt W Γ (pt_inst τ x) (pt_inst τ y).
Proof.
  intros Hwf H Hh. unfold slt in H. induction H as [x y Hw|x y Hf|x y z _ IH1 _ IH2].
  - apply sl_w. by apply sw_lt_pinst_fc.
  - by apply Hh.
  - eapply sl_trans; [apply IH1|apply IH2].
Qed.

Lemma length_ids m : length (ids m) = m.
Proof. unfold ids. by rewrite length_fmap, length_seq. Qed.

Lemma ids_lookup m a : a < m → ids m !! a = Some (pvar a).
Proof. intros Ha. unfold ids. rewrite list_lookup_fmap, lookup_seq_lt by done. done. Qed.

Lemma cons_of_hold W Γ m C xs : facts_const W → length xs = m → hold_at W Γ C xs → cons_open W Γ m C.
Proof.
  intros Hwf Hl HC x y H.
  rewrite <-(pshift_back xs m x), <-(pshift_back xs m y) by done.
  apply (slt_inst W Γ (hc_open m C Γ)); [done|done|].
  intros u v (C' & ys & Hin & Hat). simpl in Hin. apply elem_of_app in Hin as [Hin|Hin].
  - unfold hyps_inst in Hin. apply list_elem_of_fmap in Hin as ([C0 ys0] & Heq & Hin).
    injection Heq as -> ->.
    apply bcs_at_inst in Hat as ([u0 v0] & Hat & Heq). injection Heq as -> ->.
    rewrite !pshift_back by done. apply fl_h. by exists C0, ys0.
  - apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    apply HC. destruct C as [env P]. apply bcs_at_iff in Hat as (f0 & Hf & Hs & Heq).
    apply bcs_at_iff. simpl in *. rewrite length_ids, length_fmap in Hs.
    exists f0. split_and!; [done|by rewrite Hl|].
    change (FLt (pt_inst (plist xs) u) (pt_inst (plist xs) v)) with (fact_map (pt_inst (plist xs)) (FLt u v)).
    rewrite Heq, fact_map_comp, (fact_map_ext _ (pt_inst (pt_inst (plist xs) ∘ plist (ids m ++ (pt_inst (pshift m) <$> env)))))
      by (intros; apply pt_inst_comp).
    apply fact_map_ext_scoped with (k := m + length env); [done|].
    intros a Ha. unfold compose. unfold plist at 2 3.
    destruct (decide (a < m)) as [Hm|Hm].
    + rewrite lookup_app_l by (by rewrite length_ids). rewrite ids_lookup by done.
      rewrite lookup_app_l by lia. rewrite pt_inst_pvar_at. unfold plist.
      destruct (xs !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
    + rewrite lookup_app_r by (rewrite length_ids; lia). rewrite lookup_app_r by lia.
      rewrite length_ids, list_lookup_fmap, Hl.
      destruct (env !! (a - m)) eqn:E; simpl.
      * by apply pshift_back.
      * apply lookup_ge_None in E. lia.
Qed.

(** A chain of the world never leaves the tree of the variable 0. *)
Lemma sw_lt_tree0 W x y : facts_const W → W ⊢ₛ x ≺ y → in_tree0 x → in_tree0 y.
Proof.
  intros Hwf. induction 1 as [x y Hs|x y z Hs _ IH]; intros Hx.
  - destruct Hs as [x y Hf|x|x]; [|done|done].
    destruct (Hwf x y Hf) as [[c [Hc _]] _]. unfold in_tree0 in Hx. congruence.
  - apply IH. destruct Hs as [x y Hf|x|x]; [|done|done].
    destruct (Hwf x y Hf) as [[c [Hc _]] _]. unfold in_tree0 in Hx. congruence.
Qed.

Lemma pshift_not_tree0 x : ¬ in_tree0 (pt_inst (pshift 1) x).
Proof.
  unfold in_tree0. rewrite pt_root_inst_var. unfold pt_root at 2.
  induction (pt_name x) as [a|a|p IH b κ]; simpl; try done.
  unfold pshift. simpl. intros [=]. lia.
Qed.

(** Every fact of an opened (wf-new) constraint ends in the tree of 0. *)
Lemma wf_new_tree0 C x y :
  wf_new C → bcs_at (bcs_inst (pshift 1) C) (ids 1) (FLt x y) → in_tree0 y.
Proof.
  intros [HC _] Hat. destruct C as [env P].
  apply bcs_at_iff in Hat as ([x0 y0] & Hf & Hs & Heq). cbn [bcs_inst bc_env bc_facts] in *.
  rewrite length_fmap in Hs. injection Heq as -> ->.
  pose proof (HC x0 y0 Hf Hs) as Hy0.
  unfold in_tree0 in *. rewrite pt_root_inst_var, Hy0. done.
Qed.

Lemma slt_open_out W Γ C x y : facts_const W → wf_new C →
  slt W (hc_open 1 C Γ) x y → ¬ in_tree0 y →
  ¬ in_tree0 x ∧ ∀ z, slt W Γ (pt_inst (plist [z]) x) (pt_inst (plist [z]) y).
Proof.
  intros Hwf HC H. unfold slt in H. induction H as [x y Hw|x y Hf|x y w _ IH1 _ IH2]; intros Hy.
  - split; [intros Hx; by apply Hy, (sw_lt_tree0 W x y)|].
    intros z. apply sl_w. by apply sw_lt_pinst_fc.
  - destruct Hf as (C' & ys & Hin & Hat). simpl in Hin. apply elem_of_app in Hin as [Hin|Hin].
    + unfold hyps_inst in Hin. apply list_elem_of_fmap in Hin as ([C0 ys0] & Heq & Hin).
      injection Heq as -> ->.
      apply bcs_at_inst in Hat as ([u0 v0] & Hat & Heq). injection Heq as -> ->.
      split; [apply pshift_not_tree0|]. intros z.
      rewrite !pshift_back by done. apply fl_h. by exists C0, ys0.
    + apply list_elem_of_singleton in Hin. injection Hin as -> ->.
      exfalso. apply Hy. by apply (wf_new_tree0 C x y).
  - destruct (IH2 Hy) as [Hw IH2']. destruct (IH1 Hw) as [Hx IH1'].
    split; [done|]. intros z. eapply sl_trans; [apply IH1'|apply IH2'].
Qed.

(** Conservativity under (wf-new). *)
Lemma cons_new W Γ C : facts_const W → wf_new C → cons_open W Γ 1 C.
Proof.
  intros Hwf HC x y H.
  destruct (slt_open_out W Γ C _ _ Hwf HC H (pshift_not_tree0 y)) as [_ H'].
  specialize (H' (pvar 0)). by rewrite !pshift_back in H' by done.
Qed.

(** (wf-new) reads the facts and the number of outer points of C, which
    an instantiation keeps. *)
Lemma wf_new_inst σ C : wf_new C → wf_new (bcs_inst σ C).
Proof. destruct C as [env P]. unfold wf_new, new_step, bcs_inst. simpl. by rewrite length_fmap. Qed.

(** ** The substitution lemma *)

Lemma pt_inst_pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Local Ltac heads_p :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
    ?opt_heads_pinst, <-?set_map_union_L, <-?sf_pinst_unionb.

