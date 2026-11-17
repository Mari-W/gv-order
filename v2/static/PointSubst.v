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

Lemma pt_inst_pup_pshift m σ x :
  pt_inst (pup m σ) (pt_inst (pshift m) x) = pt_inst (pshift m) (pt_inst σ x).
Proof.
  rewrite !pt_inst_comp. apply pt_inst_ext. intros a. unfold compose.
  unfold pshift at 1. rewrite pt_inst_pvar_at, pup_pshift. done.
Qed.

Lemma pinst_pup_pshift m σ T :
  pinst_ty (pup m σ) (pinst_ty (pshift m) T) = pinst_ty (pshift m) (pinst_ty σ T).
Proof.
  rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. unfold compose.
  unfold pshift at 1. rewrite pt_inst_pvar_at, pup_pshift. done.
Qed.

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
    + destruct ub; simpl; [|done]. f_equal. eauto.
    + destruct lb; simpl; [|done]. f_equal. eauto.
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

Lemma tsub_pinst σ T a T' a' : tsub T a T' a' → tsub (pinst_ty σ T) a (pinst_ty σ T') a'.
Proof.
  intros H. revert σ. induction H; intros σ; simpl; constructor; auto using teq_pinst.
  - destruct k; [by apply teq_pinst|by subst].
  - simpl. by rewrite H.
Qed.

Definition pent (σ : nat → point) (p : ty * fuel) : ty * fuel := (pinst_ty σ p.1, p.2).

Lemma tage_pinst c p p' : tage c p p' → ∀ σ, tage c (pent σ p) (pent σ p').
Proof.
  induction 1; intros σ; simpl in *; constructor; auto using tfree_pinst.
  - apply (IHtage1 σ).
  - apply (IHtage2 σ).
  - apply (IHtage1 σ).
  - apply (IHtage2 σ).
  - apply (IHtage (pup n σ)).
Qed.

Lemma tcap_pinst h b p p' : tcap h b p p' → ∀ σ, tcap h b (pent σ p) (pent σ p').
Proof.
  induction 1; intros σ; simpl in *; constructor; auto using tfree_pinst.
  - apply (IHtcap1 σ).
  - apply (IHtcap2 σ).
  - apply (IHtcap1 σ).
  - apply (IHtcap2 σ).
  - apply (IHtcap (pup n σ)).
Qed.

(** ** Contexts *)

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_pinst_singleton σ o S x a :
  tenv_pinst σ {[o := TE S x a]} = {[o := TE S (pt_inst σ x) a]}.
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

Lemma thage_pinst σ c Θ Θ' : thage c Θ Θ' → thage c (tenv_pinst σ Θ) (tenv_pinst σ Θ').
Proof.
  intros H o. specialize (H o). unfold tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! o), (Θ' !! o); simpl in *; try done. destruct_and!. by split_and!; f_equal.
Qed.

Lemma thcap_pinst σ h b Θ Θ' : thcap h b Θ Θ' → thcap h b (tenv_pinst σ Θ) (tenv_pinst σ Θ').
Proof.
  intros H o. specialize (H o). unfold tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! o), (Θ' !! o); simpl in *; try done. destruct_and!. by split_and!; f_equal.
Qed.

Lemma tenv_pinst_pup_pshift m σ Θ :
  tenv_pinst (pup m σ) (tenv_pinst (pshift m) Θ) = tenv_pinst (pshift m) (tenv_pinst σ Θ).
Proof.
  unfold tenv_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
  intros _ [S x a] _. unfold tentry_pinst. simpl. by rewrite pt_inst_pup_pshift.
Qed.

Lemma lenv_pinst_cons σ o Δ :
  lenv_pinst σ (o :: Δ) = (fmap (M:=option) (λ '(T, a), (pinst_ty σ T, a)) o) :: lenv_pinst σ Δ.
Proof. done. Qed.

Lemma lenv_empty_pinst σ Δ : lenv_empty Δ → lenv_empty (lenv_pinst σ Δ).
Proof.
  intros H o Ho. unfold lenv_pinst in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  by rewrite (H o' Ho').
Qed.

Lemma lenv_only_pinst σ Δ x T a :
  lenv_only Δ x (T, a) → lenv_only (lenv_pinst σ Δ) x (pinst_ty σ T, a).
Proof.
  intros [Hx Hy]. split; [by rewrite lenv_pinst_lookup, Hx|].
  intros y σ' Hσ. rewrite lenv_pinst_lookup in Hσ.
  destruct (Δ !! y) as [[[T0 a0]|]|] eqn:E; simplify_eq/=.
  destruct (Hy y _ E) as [-> [= -> ->]]. done.
Qed.

Lemma lenv_split_pinst σ Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2).
Proof.
  induction 1 as [| | [T a] | [T a] |]; simpl; constructor; try done. by apply unlimited_pinst.
Qed.

Lemma lenv_wk_pinst σ Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_pinst σ Δ') (lenv_pinst σ Δ).
Proof. induction 1; simpl; constructor; try done. by apply unlimited_pinst. Qed.

Lemma lenv_unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
Proof.
  intros H o Ho. unfold lenv_pinst in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & a & -> & HU)]; [by left|right].
  eexists _, _. split; [done|]. by apply unlimited_pinst.
Qed.

Lemma lage_pinst σ c Δ Δ' : lage c Δ Δ' → lage c (lenv_pinst σ Δ) (lenv_pinst σ Δ').
Proof.
  induction 1 as [| |[T a] [T' a'] ? ? Ht]; simpl; constructor; try done.
  by apply (tage_pinst c (T, a) (T', a')).
Qed.

Lemma lcap_pinst σ h b Δ Δ' : lcap h b Δ Δ' → lcap h b (lenv_pinst σ Δ) (lenv_pinst σ Δ').
Proof.
  induction 1 as [| |[T a] [T' a'] ? ? Ht]; simpl; constructor; try done.
  by apply (tcap_pinst h b (T, a) (T', a')).
Qed.

Lemma lenv_heads_pinst σ Δ : lenv_heads (lenv_pinst σ Δ) = set_map (pt_inst σ) (lenv_heads Δ).
Proof.
  induction Δ as [|[[T a]|] Δ IH]; simpl; [by rewrite set_map_empty|..|done].
  by rewrite set_map_union_L, heads_pinst, IH.
Qed.

Lemma lenv_bot_pinst σ Δ : lenv_bot (lenv_pinst σ Δ) = lenv_bot Δ.
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; rewrite ?hbot_pinst; congruence. Qed.

Lemma lenv_pinst_pup_pshift m σ Δ :
  lenv_pinst (pup m σ) (lenv_pinst (pshift m) Δ) = lenv_pinst (pshift m) (lenv_pinst σ Δ).
Proof.
  induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal].
  by rewrite pinst_pup_pshift, IH.
Qed.

Lemma lenv_pinst_insert σ Δ i T a :
  lenv_pinst σ (<[i := Some (T, a)]> Δ) = <[i := Some (pinst_ty σ T, a)]> (lenv_pinst σ Δ).
Proof. unfold lenv_pinst. by rewrite list_fmap_insert. Qed.

Lemma sf_pinst_union σ F X : sf_pinst σ (sf_union F X) = sf_union (sf_pinst σ F) (set_map (pt_inst σ) X).
Proof. unfold sf_pinst, sf_union. simpl. by rewrite set_map_union_L. Qed.

Lemma sf_pinst_unionb σ F X b :
  sf_pinst σ (sf_unionb F X b) = sf_unionb (sf_pinst σ F) (set_map (pt_inst σ) X) b.
Proof. destruct b; unfold sf_pinst, sf_unionb, sf_union; simpl; by rewrite set_map_union_L. Qed.

Lemma sf_pinst_nil σ o : sf_pinst σ (∅, o) = (∅, o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

Lemma sf_pinst_pup_pshift m σ F :
  sf_pinst (pup m σ) (sf_pinst (pshift m) F) = sf_pinst (pshift m) (sf_pinst σ F).
Proof.
  unfold sf_pinst. simpl. f_equal. apply set_eq. intros y.
  rewrite !elem_of_map. setoid_rewrite elem_of_map. split.
  - intros (y0 & -> & z & -> & Hz). eexists. split; [apply pt_inst_pup_pshift|]. eauto.
  - intros (y0 & -> & z & -> & Hz). eexists. split; [symmetry; apply pt_inst_pup_pshift|]. eauto.
Qed.

(** ** Facts *)

Definition node_inst (σ : nat → point) (a : node) : node :=
  match a with NP x => NP (pt_inst σ x) | NV φ => NV φ end.

(** Γ' proves the hypotheses of Γ instantiated by σ: every fact of every
    instantiated box constraint, every future hypothesis u ≺ φ at σ(u),
    and Γ' has no future variable Γ lacks. *)
Definition hinst (W : world) (σ : nat → point) (Γ Γ' : hctx) : Prop :=
  (∀ C xs x y, (C, xs) ∈ hc_hyps Γ → bcs_at (bcs_inst σ C) (pt_inst σ <$> xs) (FLt x y) →
     slt W Γ' x y) ∧
  (∀ φ u, hc_fv Γ !! φ = Some (Some u) → fl W Γ' (NP (pt_inst σ u)) (NV φ)) ∧
  dom (hc_fv Γ') ⊆ dom (hc_fv Γ).

Lemma pn_root_law_inst ℓ g p a : pt_root (pn_inst (λ _, pgen ℓ g) p) ≠ NVar a.
Proof. induction p; simpl; try done. Qed.

Lemma w_lt_pinst W σ x y : world_wf W → W ⊢ x ≺ y → W ⊢ pt_inst σ x ≺ pt_inst σ y.
Proof.
  intros Hwf. apply tc_congruence. intros a b Hs.
  destruct Hs as [a b Hf|ℓ g a b Hℓ Hl|a|a].
  - destruct (wf_facts _ Hwf a b Hf) as [[c [Hc _]] [d [Hd _]]].
    rewrite !pt_inst_novar by (intros ?; congruence). by apply ws_fact.
  - rewrite !(pt_inst_novar σ (law_inst ℓ g _)); [by apply ws_law| |];
      intros a'; unfold law_inst; rewrite pt_root_inst_var; apply pn_root_law_inst.
  - rewrite pt_inst_shift. apply ws_po.
  - rewrite pt_inst_shift, pt_inst_dual. apply ws_dpo.
Qed.

Section facts.
  Context (W : world) (Hwf : world_wf W).

  Lemma fl_pinst σ Γ Γ' a b : hinst W σ Γ Γ' → fl W Γ a b → fl W Γ' (node_inst σ a) (node_inst σ b).
  Proof.
    intros (H1 & H2 & _).
    induction 1 as [x y H|x y (C & xs & HC & H)|φ u H|a y b _ IH1 _ IH2]; simpl.
    - apply fl_w. by apply w_lt_pinst.
    - eapply H1; [done|]. apply bcs_at_inst. by exists (FLt x y).
    - by apply H2.
    - eapply fl_trans; [exact IH1|exact IH2].
  Qed.

  Lemma slt_pinst σ Γ Γ' x y : hinst W σ Γ Γ' → slt W Γ x y → slt W Γ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros H. apply (fl_pinst σ Γ Γ' (NP x) (NP y) H). Qed.

  Lemma sle_pinst σ Γ Γ' x y : hinst W σ Γ Γ' → sle W Γ x y → sle W Γ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros H [->|Hl]; [by left|right; by eapply slt_pinst]. Qed.

  Lemma hold_at_pinst σ Γ Γ' C xs :
    hinst W σ Γ Γ' → hold_at W Γ C xs → hold_at W Γ' (bcs_inst σ C) (pt_inst σ <$> xs).
  Proof.
    intros Hi H x y Hf. apply bcs_at_inst in Hf as ([x0 y0] & Hf & [= -> ->]).
    by eapply slt_pinst, H.
  Qed.

  Lemma ub_below_s_pinst σ Γ Γ' ub F :
    hinst W σ Γ Γ' → ub_below_s W Γ ub F → ub_below_s W Γ' (pt_inst σ <$> ub) (sf_pinst σ F).
  Proof.
    intros Hi. destruct ub as [x|]; simpl; [|done]. intros (H1 & H2 & H3). split_and!; [| |done].
    - intros y Hy. apply elem_of_map in Hy as (y0 & -> & Hy). by eapply slt_pinst, H1.
    - intros φ Hφ. by apply (fl_pinst σ Γ Γ' (NP x) (NV φ) Hi), H2.
  Qed.

  Lemma lb_below_hb_pinst σ Γ Γ' lb H b :
    hinst W σ Γ Γ' → lb_below_hb W Γ lb H b →
    lb_below_hb W Γ' (pt_inst σ <$> lb) (set_map (pt_inst σ) H) b.
  Proof.
    intros Hi. unfold lb_below_hb, lb_below_h. destruct b; [done|]. destruct lb; simpl.
    - intros Hy y Hyy. apply elem_of_map in Hyy as (y0 & -> & Hy0). by eapply sle_pinst, Hy.
    - intros ->. by rewrite set_map_empty.
  Qed.

  Lemma lbx_below_h_pinst σ Γ Γ' lb H b :
    hinst W σ Γ Γ' → lbx_below_h W Γ lb H b →
    lbx_below_h W Γ' (lb_map (pt_inst σ) lb) (set_map (pt_inst σ) H) b.
  Proof.
    intros Hi. destruct lb; simpl; try done.
    - intros [-> ->]. by rewrite set_map_empty.
    - intros [Hy ->]. split; [|done]. intros y Hyy. apply elem_of_map in Hyy as (y0 & -> & Hy0).
      by eapply sle_pinst, Hy.
  Qed.

  (** A context that proves more facts and more future hypotheses. *)
  Lemma fl_mono Γ Γ2 a b :
    hc_hyps Γ2 = hc_hyps Γ → (∀ φ u, hc_fv Γ !! φ = Some u → hc_fv Γ2 !! φ = Some u) →
    fl W Γ a b → fl W Γ2 a b.
  Proof.
    intros Hh Hf. induction 1.
    - by apply fl_w.
    - apply fl_h. by rewrite Hh.
    - apply fl_v. by apply Hf.
    - by eapply fl_trans.
  Qed.

  Lemma hinst_fvar σ Γ Γ' φ ub :
    φ ∉ dom (hc_fv Γ) → hinst W σ Γ Γ' →
    hinst W σ (hc_fvar φ ub Γ) (hc_fvar φ (pt_inst σ <$> ub) Γ').
  Proof.
    intros Hφ (H1 & H2 & H3).
    assert (hc_fv Γ' !! φ = None) as Hφ' by (apply not_elem_of_dom; set_solver).
    assert (∀ a b, fl W Γ' a b → fl W (hc_fvar φ (pt_inst σ <$> ub) Γ') a b) as Hm.
    { intros a b. apply fl_mono; [done|]. intros φ' u Hu. simpl.
      rewrite lookup_insert_ne; [done|]. intros ->. congruence. }
    split_and!; simpl.
    - intros C xs x y HC Hf. apply Hm. by eapply H1.
    - intros φ' u Hu. destruct (decide (φ' = φ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hu. simplify_eq. apply fl_v. simpl. by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne in Hu by done. apply Hm. by apply H2.
    - rewrite !dom_insert_L. set_solver.
  Qed.

  Lemma hinst_pshift m C Γ : hinst W (pshift m) Γ (hc_open m C Γ).
  Proof.
    split_and!.
    - intros C0 xs0 x y HC Hf. apply fl_h. exists (bcs_inst (pshift m) C0), (pt_inst (pshift m) <$> xs0).
      split; [|done]. simpl. apply elem_of_app. left. apply list_elem_of_fmap. by exists (C0, xs0).
    - intros φ u Hu. apply fl_v. simpl. unfold fhyps_pinst. by rewrite lookup_fmap, Hu.
    - simpl. unfold fhyps_pinst. by rewrite dom_fmap_L.
  Qed.

  Lemma ids_pup m σ : pt_inst (pup m σ) <$> ids m = ids m.
  Proof.
    unfold ids. rewrite <-list_fmap_compose. apply list_fmap_ext. intros i a Hi.
    apply lookup_seq in Hi as [-> ?]. simpl. rewrite pt_inst_pvar_at. unfold pup.
    by rewrite decide_True by lia.
  Qed.

  Lemma bcs_inst_pup_pshift m σ C :
    bcs_inst (pup m σ) (bcs_inst (pshift m) C) = bcs_inst (pshift m) (bcs_inst σ C).
  Proof.
    rewrite !bcs_inst_comp. apply bcs_inst_ext. intros a. unfold compose.
    unfold pshift at 1. rewrite pt_inst_pvar_at, pup_pshift. done.
  Qed.

  Lemma hinst_open σ m C Γ Γ' :
    hinst W σ Γ Γ' → hinst W (pup m σ) (hc_open m C Γ) (hc_open m (bcs_inst σ C) Γ').
  Proof.
    intros Hi. pose proof Hi as (H1 & H2 & H3). split_and!.
    - intros C0 xs0 x y HC Hf. simpl in HC. apply elem_of_app in HC as [HC|HC].
      + apply list_elem_of_fmap in HC as ([C1 xs1] & [= -> ->] & HC1).
        rewrite <-list_fmap_compose, bcs_inst_pup_pshift in Hf.
        rewrite (list_fmap_ext _ (pt_inst (pshift m) ∘ pt_inst σ)) in Hf
          by (intros; apply pt_inst_pup_pshift).
        rewrite list_fmap_compose in Hf.
        apply bcs_at_inst in Hf as ([x0 y0] & Hf & [= -> ->]).
        apply (slt_pinst _ Γ' _ x0 y0 (hinst_pshift m (bcs_inst σ C) Γ')).
        by eapply H1.
      + apply list_elem_of_singleton in HC. simplify_eq.
        rewrite bcs_inst_pup_pshift, ids_pup in Hf.
        apply fl_h. eexists _, _. split; [|exact Hf]. simpl. apply elem_of_app. right. by left.
    - intros φ u Hu. simpl in Hu. unfold fhyps_pinst in Hu. rewrite lookup_fmap in Hu.
      destruct (hc_fv Γ !! φ) as [[u0|]|] eqn:E; simplify_eq/=.
      rewrite pt_inst_pup_pshift.
      apply (fl_pinst _ Γ' _ (NP (pt_inst σ u0)) (NV φ) (hinst_pshift m (bcs_inst σ C) Γ')).
      by apply H2.
    - simpl. unfold fhyps_pinst. rewrite !dom_fmap_L. done.
  Qed.
End facts.

(** ** The substitution lemma *)

Lemma tage_pinst2 σ c T a T' a' : tage c (T, a) (T', a') → tage c (pinst_ty σ T, a) (pinst_ty σ T', a').
Proof. intros H. apply (tage_pinst c (T, a) (T', a') H σ). Qed.

Lemma pt_inst_pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Local Ltac heads_p :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
    ?opt_heads_pinst, <-?set_map_union_L, <-?sf_pinst_unionb, <-?sf_pinst_union.

Theorem typed_pinst W N Θ Γ Δ F e T a c t :
  world_wf W → typed W N Θ Γ Δ F e T a c t →
  ∀ σ Γ', hinst W σ Γ Γ' →
  typed W N (tenv_pinst σ Θ) Γ' (lenv_pinst σ Δ) (sf_pinst σ F) e (pinst_ty σ T) a c t.
Proof.
  intros Hwf. induction 1; intros σ Γ' Hi; cbn [pinst_ty];
    rewrite ?tenv_pinst_empty, ?tenv_pinst_singleton.
  - by apply e_unit, lenv_empty_pinst.
  - by eapply e_var, lenv_only_pinst.
  - by apply e_chan, lenv_empty_pinst.
  - (* E-Abs *)
    eapply e_abs with (φ := φ); [destruct Hi as (_ & _ & Hd); set_solver| |by apply thcap_pinst
                                |by apply lcap_pinst|].
    + rewrite tenv_heads_pinst, lenv_heads_pinst, lenv_bot_pinst, <-set_map_union_L.
      by eapply lb_below_hb_pinst.
    + rewrite <-(sf_pinst_nil σ). apply IHtyped. by apply hinst_fvar.
  - (* E-App *)
    eapply e_app; [by apply tsplit_pinst|by apply lenv_split_pinst|by eapply ub_below_s_pinst| |
                   by apply thage_pinst|by apply lage_pinst| |done|done|done].
    + heads_p. by apply IHtyped1.
    + heads_p. by apply IHtyped2.
  - eapply e_pair; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply thage_pinst
                   |by apply lage_pinst| |by apply tage_pinst2|done].
    + heads_p. by apply IHtyped1.
    + heads_p. by apply IHtyped2.
  - eapply e_letu; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply thage_pinst
                   |by apply lage_pinst|by apply IHtyped2|done].
    heads_p. by apply IHtyped1.
  - eapply e_letp; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply thage_pinst
                   |by apply lage_pinst|by apply IHtyped2|done].
    heads_p. by apply IHtyped1.
  - eapply e_let; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply thage_pinst
                  |by apply lage_pinst|by apply IHtyped2|done].
    heads_p. by apply IHtyped1.
  - by eapply e_inj1, IHtyped.
  - by eapply e_inj2, IHtyped.
  - eapply e_case; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply thage_pinst
                   |by apply lage_pinst|by apply IHtyped2|by apply IHtyped3|done].
    heads_p. by apply IHtyped1.
  - (* E-Box *)
    pose proof (hinst_open W Hwf σ m C Γ Γ' Hi) as Ho.
    eapply e_box with (φ := φ); [by apply lenv_unl_pinst|destruct Ho as (_ & _ & Hd); set_solver|].
    intros ss Hk Hss.
    specialize (H2 ss Hk Hss (pup m σ) _ (hinst_fvar W Hwf _ _ _ φ ub H0 Ho)).
    rewrite tenv_pinst_empty, sf_pinst_nil, pinst_sinst, lenv_pinst_pup_pshift in H2.
    exact H2.
  - (* E-Force *)
    subst m. rewrite pinst_sinst, pinst_ty_inst.
    eapply e_force with (xs := pt_inst σ <$> xs);
      [by rewrite length_fmap|by eapply hold_at_pinst|done|done| |by apply IHtyped|done].
    assert (pt_inst σ <$> (pt_inst (plist xs) <$> ub) =
            pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup (length xs) σ) <$> ub)) as <-.
    { destruct ub; simpl; [|done]. f_equal. apply pt_inst_plist_inst. }
    by eapply ub_below_s_pinst.
  - (* E-Send *)
    rewrite pt_inst_shift.
    eapply e_send with (x := pt_inst σ x) (m := m) (T := T) (b := b) (S := S) (S0 := S0);
      [done|done|done| |by apply (ub_below_s_pinst W Hwf σ Γ Γ' (Some x))| | |].
    + intros y. rewrite <-pinst_payload_at, heads_pinst by done.
      intros (y0 & -> & Hy)%elem_of_map. by eapply slt_pinst, H2.
    + rewrite <-pinst_payload_at by done. by apply IHtyped.
    + rewrite <-pinst_payload_at by done. by apply tage_pinst2.
    + rewrite <-pinst_payload_at by done. by apply tsub_pinst.
  - (* E-Recv *)
    rewrite pinst_payload_at, pt_inst_shift by done.
    eapply e_recv with (x := pt_inst σ x);
      [done|done|by apply (ub_below_s_pinst W Hwf σ Γ Γ' (Some x))|by apply IHtyped].
  - eapply e_close with (x := pt_inst σ x);
      [done|by apply (ub_below_s_pinst W Hwf σ Γ Γ' (Some x))|by apply IHtyped].
  - (* E-Select *)
    rewrite pt_inst_sel.
    eapply e_select with (x := pt_inst σ x);
      [done| |by apply (ub_below_s_pinst W Hwf σ Γ Γ' (Some x))|by apply IHtyped].
    rewrite <-pt_inst_field. by eapply slt_pinst.
  - (* E-Branch *)
    rewrite !pt_inst_bra.
    eapply e_branch with (x := pt_inst σ x);
      [done| | |by apply (ub_below_s_pinst W Hwf σ Γ Γ' (Some x))|by apply IHtyped].
    + rewrite <-pt_inst_sel. by eapply slt_pinst.
    + rewrite <-pt_inst_sel. by eapply slt_pinst.
  - (* E-Link *)
    specialize (IHtyped σ Γ' Hi). cbn [pinst_ty] in IHtyped. rewrite pt_inst_dual in IHtyped.
    eapply e_link; [exact IHtyped|done].
  - eapply e_spawn_lam; [by apply thage_pinst|by apply lage_pinst|].
    rewrite <-(sf_pinst_nil σ). by apply IHtyped.
  - eapply e_spawn; [by apply IHtyped|done|done].
  - (* E-New *)
    rewrite pt_inst_dual, pt_inst_pup1_0.
    change (bcs_inst σ (bcs_of (w_laws W ℓ))) with (bcs_of (w_laws W ℓ)).
    apply e_new; [by apply lenv_empty_pinst|done].
  - rewrite pt_inst_dual, pt_inst_field. eapply e_new_at with (x := pt_inst σ x). by apply IHtyped.
  - eapply e_sub; [by apply IHtyped|by apply tsub_pinst|done|done].
  - eapply e_weak; [by apply lenv_wk_pinst|by apply IHtyped].
  - eapply e_contract; [by apply unlimited_pinst|by apply IHtyped].
  - (* E-Pack *)
    subst m. eapply e_pack with (xs := pt_inst σ <$> xs); [by rewrite length_fmap|by eapply hold_at_pinst| |].
    + rewrite <-pinst_ty_inst, heads_pinst, hbot_pinst. by eapply lbx_below_h_pinst.
    + rewrite <-pinst_ty_inst. by apply IHtyped.
  - (* E-Open *)
    eapply e_open with (i := i) (lb := lb_map (pt_inst σ) lb) (m := m) (C := bcs_inst σ C)
      (T := pinst_ty (pup m σ) T) (aT := aT) (a := a);
      [by rewrite lenv_pinst_lookup, H|by rewrite unlimited_pinst_iff|].
    specialize (IHtyped (pup m σ) _ (hinst_open W Hwf σ m C Γ Γ' Hi)).
    rewrite tenv_pinst_pup_pshift, lenv_pinst_insert, lenv_pinst_pup_pshift, sf_pinst_pup_pshift,
      pinst_pup_pshift in IHtyped.
    exact IHtyped.
Qed.
