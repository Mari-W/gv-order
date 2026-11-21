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

Lemma tsub_pinst σ T T' : tsub T T' → tsub (pinst_ty σ T) (pinst_ty σ T').
Proof.
  intros H. revert σ. induction H; intros σ; simpl; constructor; auto using teq_pinst.
  - destruct k; [by apply teq_pinst|by subst].
  - simpl. by rewrite H.
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

Lemma sf_pinst_unionb σ F X b :
  sf_pinst σ (sf_unionb F X b) = sf_unionb (sf_pinst σ F) (set_map (pt_inst σ) X) b.
Proof. destruct b; unfold sf_pinst, sf_unionb; simpl; by rewrite set_map_union_L. Qed.

Lemma sf_pinst_nil σ o : sf_pinst σ (∅, o) = (∅, o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** ** Facts *)

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

End facts.

(** ** The substitution lemma *)

Lemma pt_inst_pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Local Ltac heads_p :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
    ?opt_heads_pinst, <-?set_map_union_L, <-?sf_pinst_unionb.

