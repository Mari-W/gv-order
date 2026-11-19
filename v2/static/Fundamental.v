(** * The fundamental theorems for terms (stage S5, Appendix A.3)

      strict W ∧ Θ ; ∅ ; Δ ⊢^F_W t : T  ⟹  Θ ; Δ ⊨^F_W t : T        [fundamental]
      strict W ∧ Θ ; ∅ ; Δ ⊢^F_W t : T ∧ ∅ ⊢▷ t  ⟹  Θ ; Δ ⊫^F_W t : T
                                                          [live_fundamental]

    One induction on the merged judgment at any refill N ([typed_sem])
    instantiates the point variables of Γ by σ and its future variables
    by ρ, in any world W1 ⊒ W where the instantiated hypotheses of Γ hold
    ([hsat]), and reads the ⊥ flag as any set B. It is generic in the
    cost table κ and in a predicate G that says which marks L the
    induction carries into a term. Each case is a rule with marks
    [later_*] of compat/LiveRules.v.

    - The DF instance ([typed_sem_df]) carries no marks. A box leaves
      its self unmarked and pays β ([gen_e_box]).
    - The live instance ([typed_sem_live]) carries the marks of the
      guard. A box marks its self ([later_box]), a frame keeps the marks
      or clears them after an acting hole ([cmarks], [kmarks]).
    - E-Abs and E-Box extend ρ by the future of the body, any set above
      the upper point u of the arrow or the box. E-Box and E-Open lift σ
      under the m point variables and close them with the instance xs of
      the relation, τ = σ(xs) ∘ (σ ↑ m).
    - Aging and capture change annotations only, and V is blind to
      annotations ([sem_later_ctx]).

    DF typing is the merged judgment at N = ∞ with the annotations of
    N = ∞, and [sem_later_undf] reads the result at the given contexts. *)

From GV Require Export compat.LiveRules static.Conservativity.
From GV Require Import compat.Conv.

(** ** Facts of a DF derivation *)

Lemma tfacts_pinst σ Θ Δ e : tfacts Θ Δ e → tfacts (tenv_pinst σ Θ) (lenv_pinst σ Δ) e.
Proof.
  intros (Hf & H1 & H2). split; [unfold tenv_pinst; by rewrite dom_fmap_L|split].
  - intros x Hx. destruct (H1 x Hx) as [[T a] Hσ]. exists (pinst_ty σ T, a).
    by rewrite lenv_pinst_lookup, Hσ.
  - intros x U a Hx Hu. rewrite lenv_pinst_lookup in Hx.
    destruct (Δ !! x) as [[[U0 a0]|]|] eqn:E; simplify_eq/=.
    apply (H2 x U0 _ E). by rewrite <-(unlimited_pinst_iff σ).
Qed.

(** ** Static futures read through ρ and B *)

Lemma den_nil ρ B σ o : sf_den ρ B (sf_pinst σ (∅, o)) = sf_den ρ B (∅, o).
Proof. by rewrite sf_pinst_nil. Qed.

Lemma den_none ρ B : sf_den ρ B (∅, None) = ∅.
Proof. unfold sf_den. simpl. set_solver. Qed.

Lemma den_fresh ρ B φ F' :
  sf_den (λ ψ, if decide (ψ = φ) then F' else ρ ψ) B (∅, Some (FVar φ)) = F'.
Proof. unfold sf_den. simpl. rewrite decide_True by done. set_solver. Qed.

Lemma den_union ρ B σ F (X : gset point) :
  sf_den ρ B (sf_pinst σ (sf_union F X)) = sf_den ρ B (sf_pinst σ F) ∪ set_map (D:=gset point) (pt_inst σ) X.
Proof. by rewrite sf_pinst_union, sf_den_union. Qed.

Lemma den_unionb ρ (B B' : gset point) σ F (X : gset point) (b : bool) :
  sf_den ρ B (sf_pinst σ F) ∪ set_map (D:=gset point) (pt_inst σ) X ∪ (if b then B' else ∅) ⊆
  sf_den ρ (B ∪ B') (sf_pinst σ (sf_unionb F X b)).
Proof.
  rewrite sf_pinst_unionb, sf_den_unionb. unfold sf_den. destruct b, (fs_bot (sf_pinst σ F).2); set_solver.
Qed.

(** ** The hypotheses of Γ, instantiated *)

(** Every instantiated fact of Γ holds in W, and every future variable
    stands for a set above its instantiated upper point. *)
Definition hsat (W : world) (σ : nat → point) (ρ : nat → gset point) (Γ : hctx) : Prop :=
  (∀ C xs x y, (C, xs) ∈ hc_hyps Γ → bcs_at (bcs_inst σ C) (pt_inst σ <$> xs) (FLt x y) →
     W ⊢ x ≺ y) ∧
  (∀ φ u, hc_fv Γ !! φ = Some (Some u) → ∀ y, y ∈ ρ φ → W ⊢ pt_inst σ u ≺ y).

Lemma hsat_empty W σ ρ : hsat W σ ρ hc_empty.
Proof. split; [intros ? ? ? ? []%elem_of_nil|intros φ u; simpl; by rewrite lookup_empty]. Qed.

Lemma hsat_mono W W' σ ρ Γ : W ⊑ W' → hsat W σ ρ Γ → hsat W' σ ρ Γ.
Proof.
  intros HW [H1 H2]. split.
  - intros C xs x y HC Hf. eapply w_lt_mono; [exact HW|]. by eapply H1.
  - intros φ u Hu y Hy. eapply w_lt_mono; [exact HW|]. by eapply H2.
Qed.

Definition node_den (σ : nat → point) (ρ : nat → gset point) (a : node) (z : point) : Prop :=
  match a with NP x => z = pt_inst σ x | NV φ => z ∈ ρ φ end.

Section facts.
  Context (W0 W : world) (Hwf : world_wf W0) (HW : W0 ⊑ W).

  Lemma fl_sem σ ρ Γ a b :
    hsat W σ ρ Γ → fl W0 Γ a b → ∀ a' b', node_den σ ρ a a' → node_den σ ρ b b' → W ⊢ a' ≺ b'.
  Proof.
    intros [H1 H2]. induction 1 as [x y H|x y (C & xs & HC & H)|φ u H|a y b _ IH1 _ IH2];
      intros a' b' Ha Hb; simpl in Ha, Hb; subst.
    - eapply w_lt_mono; [exact HW|]. by apply w_lt_pinst.
    - eapply H1; [exact HC|]. apply bcs_at_inst. by exists (FLt x y).
    - by eapply H2.
    - eapply w_lt_trans; [apply IH1; [done|simpl; done]|by apply IH2].
  Qed.

  Lemma slt_sem σ ρ Γ x y : hsat W σ ρ Γ → slt W0 Γ x y → W ⊢ pt_inst σ x ≺ pt_inst σ y.
  Proof. intros Hs H. by apply (fl_sem σ ρ Γ (NP x) (NP y) Hs H). Qed.

  Lemma sle_sem σ ρ Γ x y : hsat W σ ρ Γ → sle W0 Γ x y → w_le W (pt_inst σ x) (pt_inst σ y).
  Proof. intros Hs [->|H]; [by left|right; by eapply slt_sem]. Qed.

  Lemma hold_sem σ ρ Γ C xs :
    hsat W σ ρ Γ → hold_at W0 Γ C xs → wholds W (bcs_inst σ C) (pt_inst σ <$> xs).
  Proof.
    intros Hs H x y Hf. apply bcs_at_inst in Hf as ([x0 y0] & Hf & [= -> ->]).
    by eapply slt_sem, H.
  Qed.

  Lemma ub_sem σ ρ B Γ ub F :
    hsat W σ ρ Γ → ub_below_s W0 Γ ub F → ub_lt W (pt_inst σ <$> ub) (sf_den ρ B (sf_pinst σ F)).
  Proof.
    intros Hs. destruct ub as [x|]; simpl; [|done]. intros (H1 & H2 & H3) y Hy.
    unfold sf_den, sf_pinst in Hy. simpl in Hy. rewrite H3 in Hy.
    apply elem_of_union in Hy as [Hy|Hy]; [apply elem_of_union in Hy as [Hy|Hy]|set_solver].
    - apply elem_of_map in Hy as (y0 & -> & Hy0). by eapply slt_sem, H1.
    - destruct (fs_var F.2) as [φ|] eqn:Hφ; simpl in Hy; [|set_solver].
      by apply (fl_sem σ ρ Γ (NP x) (NV φ) Hs (H2 φ eq_refl)).
  Qed.

  Lemma lb_sem σ ρ Γ lb H b :
    hsat W σ ρ Γ → lb_below_hb W0 Γ lb H b →
    b = false ∧ lb_le W (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros Hs. unfold lb_below_hb. destruct b; [done|]. intros Hl. split; [done|].
    destruct lb as [l|]; simpl in *.
    - intros y (y0 & -> & Hy0)%elem_of_map. by eapply sle_sem, Hl.
    - by rewrite Hl, set_map_empty.
  Qed.

  Lemma lbx_sem σ ρ Γ lb X :
    hsat W σ ρ Γ → lbx_below_h W0 Γ lb (heads X) (hbot X) →
    lbx_ok W (lb_map (pt_inst σ) lb) (pinst_ty σ X).
  Proof.
    intros Hs. rewrite <-(hbot_pinst σ X). destruct lb as [| |l]; simpl; try done.
    - intros [Hh ->]. by rewrite heads_pinst, Hh, set_map_empty.
    - intros [Hh ->]. split; [|done]. intros y. rewrite heads_pinst.
      intros (y0 & -> & Hy0)%elem_of_map. by eapply sle_sem, Hh.
  Qed.
End facts.

Lemma hsat_fvar W σ ρ Γ φ ub F' :
  φ ∉ dom (hc_fv Γ) → hsat W σ ρ Γ → ub_lt W (pt_inst σ <$> ub) F' →
  hsat W σ (λ ψ, if decide (ψ = φ) then F' else ρ ψ) (hc_fvar φ ub Γ).
Proof.
  intros Hφ [H1 H2] Hub. split; [done|]. intros ψ u Hu y Hy. simpl in Hu.
  destruct (decide (ψ = φ)) as [->|Hne].
  - rewrite lookup_insert_eq in Hu. simplify_eq. by apply Hub.
  - rewrite lookup_insert_ne in Hu by done. by eapply H2.
Qed.

(** ** Instances under a binder of m points *)

(** τ = σ(xs) ∘ (σ ↑ m) closes the m variables with xs and maps the
    variables beyond by σ. *)
Definition pclose (xs : list point) (m : nat) (σ : nat → point) : nat → point :=
  λ a, pt_inst (plist xs) (pup m σ a).

Lemma pclose_shift xs m σ : length xs = m → ∀ a, pt_inst (pclose xs m σ) (pshift m a) = σ a.
Proof.
  intros Hm a. unfold pshift. rewrite pt_inst_pvar_at. unfold pclose. rewrite pup_pshift, pt_inst_comp.
  rewrite (pt_inst_ext _ pvar); [apply pt_inst_pvar|]. intros b. unfold compose.
  unfold pshift. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma pclose_ids xs m σ : length xs = m → pt_inst (pclose xs m σ) <$> ids m = xs.
Proof.
  intros <-. apply list_eq. intros i. unfold ids. rewrite !list_lookup_fmap.
  destruct (decide (i < length xs)) as [Hi|Hi].
  - rewrite lookup_seq_lt by done. simpl. rewrite pt_inst_pvar_at. unfold pclose, pup.
    rewrite decide_True by done. rewrite pt_inst_pvar_at. unfold plist.
    destruct (xs !! i) eqn:E; [done|]. apply lookup_ge_None in E. lia.
  - rewrite lookup_seq_ge by lia. simpl. symmetry. apply lookup_ge_None. lia.
Qed.

Lemma pclose_ty xs m σ T : pinst_ty (pclose xs m σ) T = ty_inst xs (pinst_ty (pup m σ) T).
Proof. unfold ty_inst. rewrite pinst_ty_comp. apply pinst_ty_ext. done. Qed.

Lemma pclose_pt xs m σ x : pt_inst (pclose xs m σ) x = pt_inst (plist xs) (pt_inst (pup m σ) x).
Proof. rewrite pt_inst_comp. apply pt_inst_ext. done. Qed.

Section unshift.
  Context (τ σ : nat → point) (m : nat) (Hτ : ∀ a, pt_inst τ (pshift m a) = σ a).

  Lemma pt_unshift x : pt_inst τ (pt_inst (pshift m) x) = pt_inst σ x.
  Proof. rewrite pt_inst_comp. apply pt_inst_ext. apply Hτ. Qed.

  Lemma ty_unshift T : pinst_ty τ (pinst_ty (pshift m) T) = pinst_ty σ T.
  Proof. rewrite pinst_ty_comp. apply pinst_ty_ext. apply Hτ. Qed.

  Lemma tenv_unshift Θ : tenv_pinst τ (tenv_pinst (pshift m) Θ) = tenv_pinst σ Θ.
  Proof.
    unfold tenv_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
    intros _ [S x a] _. unfold tentry_pinst. simpl. by rewrite pt_unshift.
  Qed.

  Lemma lenv_unshift Δ : lenv_pinst τ (lenv_pinst (pshift m) Δ) = lenv_pinst σ Δ.
  Proof.
    induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal].
    by rewrite ty_unshift, IH.
  Qed.

  Lemma sf_unshift F : sf_pinst τ (sf_pinst (pshift m) F) = sf_pinst σ F.
  Proof.
    unfold sf_pinst. simpl. f_equal. apply set_eq. intros y.
    rewrite !elem_of_map. setoid_rewrite elem_of_map. split.
    - intros (y0 & -> & z & -> & Hz). exists z. split; [apply pt_unshift|done].
    - intros (z & -> & Hz). exists (pt_inst (pshift m) z). split; [symmetry; apply pt_unshift|].
      by exists z.
  Qed.

  Lemma bcs_unshift C : bcs_inst τ (bcs_inst (pshift m) C) = bcs_inst σ C.
  Proof. rewrite bcs_inst_comp. apply bcs_inst_ext. apply Hτ. Qed.

  Lemma list_unshift (xs : list point) : pt_inst τ <$> (pt_inst (pshift m) <$> xs) = pt_inst σ <$> xs.
  Proof. rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_unshift. Qed.
End unshift.

Lemma hsat_open W σ ρ Γ m C xs :
  length xs = m → hsat W σ ρ Γ → wholds W (bcs_inst σ C) xs →
  hsat W (pclose xs m σ) ρ (hc_open m C Γ).
Proof.
  intros Hm [H1 H2] HC. pose proof (pclose_shift xs m σ Hm) as Hτ. split.
  - intros C0 xs0 x y HC0 Hf. simpl in HC0. apply elem_of_app in HC0 as [HC0|HC0].
    + apply list_elem_of_fmap in HC0 as ([C1 xs1] & [= -> ->] & HC1). simpl in Hf.
      rewrite (bcs_unshift _ σ m Hτ), (list_unshift _ σ m Hτ) in Hf. by eapply H1.
    + apply list_elem_of_singleton in HC0. injection HC0 as -> ->.
      rewrite (bcs_unshift _ σ m Hτ), (pclose_ids xs m σ Hm) in Hf. by apply HC.
  - intros φ u Hu y Hy. simpl in Hu. unfold fhyps_pinst in Hu. rewrite lookup_fmap in Hu.
    destruct (hc_fv Γ !! φ) as [[u0|]|] eqn:E; simpl in Hu; try discriminate.
    injection Hu as <-. rewrite (pt_unshift _ σ m Hτ). by eapply H2.
Qed.

(** ** Identity instances *)

Lemma tenv_pinst_pvar Θ : tenv_pinst pvar Θ = Θ.
Proof.
  unfold tenv_pinst. rewrite <-(map_fmap_id Θ) at 2. apply map_fmap_ext.
  intros _ [S x a] _. unfold tentry_pinst. simpl. by rewrite pt_inst_pvar.
Qed.

Lemma lenv_pinst_pvar Δ : lenv_pinst pvar Δ = Δ.
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal]. by rewrite pinst_ty_pvar, IH. Qed.

Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal. apply set_eq. intros y.
  rewrite elem_of_map. split; [intros (y0 & -> & Hy); by rewrite pt_inst_pvar|].
  intros Hy. exists y. by rewrite pt_inst_pvar.
Qed.

(** ** The judgment with marks reads its contexts up to annotations *)

Lemma GrelL_df κ n W Θ Δ Δ' L γ :
  lenv_df Δ' = lenv_df Δ → GrelL κ n W Θ Δ L γ → GrelL κ n W Θ Δ' L γ.
Proof.
  revert Θ Δ' L γ. induction Δ as [|o Δ IH]; intros Θ [|o' Δ'] L γ HE; try done; simpl.
  rewrite !lenv_df_cons in HE. injection HE as Ho HE.
  destruct o as [[T a]|], o' as [[T' a']|]; simpl in Ho; try discriminate; simpl; [|by apply IH].
  unfold ent_df in Ho. simpl in Ho. injection Ho as HT _.
  destruct (L 0).
  - intros [(Hu & Hf & HV) HG]. split; [|by apply IH]. split_and!.
    + by rewrite <-unlimited_df, HT, unlimited_df.
    + done.
    + intros j Hj. rewrite (Vrel_blind κ _ _ _ T' T); [by apply HV|done].
  - intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; [done|done| |by apply IH].
    by rewrite (Vrel_blind κ _ _ _ T' T).
Qed.

Lemma sem_later_ctx κ W Θ Θ' Δ Δ' L F t T :
  tenv_erase Θ' = tenv_erase Θ → lenv_df Δ' = lenv_df Δ →
  sem_later κ W Θ' Δ' L F t T → sem_later κ W Θ Δ L F t T.
Proof.
  intros HΘ HΔ H n W' Θ0 γ HW Hd HG. rewrite <-HΘ. apply H; [done|by rewrite HΘ|].
  by eapply GrelL_df.
Qed.

Lemma sem_later_undf κ W Θ Δ L F t T :
  sem_later κ W (tenv_df Θ) (lenv_df Δ) L F t (ty_df T) → sem_later κ W Θ Δ L F t T.
Proof.
  intros H n W' Θ0 γ HW Hd HG.
  assert (tenv_erase (tenv_df Θ) ##ₘ Θ0) as Hd'.
  { rewrite map_disjoint_dom in Hd |- *. unfold tenv_erase, tenv_df in *. by rewrite !dom_fmap_L in *. }
  specialize (H n W' Θ0 γ HW Hd' (GrelL_df κ _ _ _ _ _ _ _ (lenv_df_idem Δ) HG)).
  apply (Erel_blind _ _ _ _ (ty_df T)); [by rewrite ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). apply senv_eqv_union; [|apply senv_eqv_refl].
  intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem.
  apply sequiv_refl.
Qed.

Lemma sem_later_unmarked κ W Θ Δ L F t T :
  (∀ x, L x = false) → sem_later κ W Θ Δ L F t T ↔ sem_typed_at κ W Θ Δ F t T.
Proof.
  intros HL. rewrite <-sem_later_empty.
  split; intros H n W' Θ' γ HW Hd HG; apply H; try done; (eapply GrelL_ext; [| |exact HG]); done.
Qed.

Lemma thage_erase σ c Θ Θ' : thage c Θ Θ' → tenv_erase (tenv_pinst σ Θ') = tenv_erase (tenv_pinst σ Θ).
Proof.
  intros H. apply map_eq. intros o. specialize (H o). unfold tenv_erase, tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! o) as [[S x a]|], (Θ' !! o) as [[S' x' a']|]; try done.
  simpl in *. destruct_and!. by subst.
Qed.

Lemma thcap_erase σ h a Θ Θ' : thcap h a Θ Θ' → tenv_erase (tenv_pinst σ Θ') = tenv_erase (tenv_pinst σ Θ).
Proof.
  intros H. apply map_eq. intros o. specialize (H o). unfold tenv_erase, tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! o) as [[S x a0]|], (Θ' !! o) as [[S' x' a']|]; try done.
  simpl in *. destruct_and!. by subst.
Qed.

Lemma lenv_df_pinst_eq σ Δ Δ' : lenv_df Δ' = lenv_df Δ → lenv_df (lenv_pinst σ Δ') = lenv_df (lenv_pinst σ Δ).
Proof. intros H. by rewrite !lenv_df_pinst, H. Qed.

Lemma lenv_df_cons_eq o Δ Δ' : lenv_df Δ' = lenv_df Δ → lenv_df (o :: Δ') = lenv_df (o :: Δ).
Proof. intros H. by rewrite !lenv_df_cons, H. Qed.

(** ** The box rule at a mark

    A box marks its self with m. The live table marks it ([later_box]),
    the DF table leaves it unmarked and pays β ([gen_e_box]). *)

Definition box_rule (κ : ctable) (L : nat → bool) (mk : bool) : Prop :=
  ∀ W Δ F e m kk C ub c t U aU a,
    tfacts ∅ Δ (EBox e) → lenv_unl Δ →
    (∀ W1 xs ss F', W ⊑ W1 → length xs = m → length ss = kk → Forall hcontractive ss →
       wholds W1 C xs → ub_lt W1 (pt_inst (plist xs) <$> ub) F' →
       sem_later κ W1 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) (mk .: L) F' e
         (sinst_ty (slist ss) (ty_inst xs U))) →
    sem_later κ W ∅ Δ L F (EBox e) (TBox m kk C ub c t U aU).

(** ** The induction, generic over the cost table and the guard

    G L e says which marks L the induction may carry into e. Each
    hypothesis below reads the marks of the subterms off G. The DF
    instance takes no marks, the live instance the guard [lguard]. *)

Section fund.
  Context (κ : ctable) (G : (nat → bool) → expr → Prop).
  Context (HGvar : ∀ L y, G L (Var y) → L y = false).
  Context (HGlam : ∀ L b, G L (Lam b) → G (false .: L) b).
  Context (HGbox : ∀ L b, G L (EBox b) → ∃ mk, G (mk .: L) b ∧ box_rule κ L mk).
  Context (HGop : ∀ L k e, G L (Op k e) → G L e).
  Context (HGapp : ∀ L e1 e2, G L (App e1 e2) → ∃ L', cmarks κ L L' e1 ∧ G L e1 ∧ G L' e2).
  Context (HGpair : ∀ L e1 e2, G L (Pair e1 e2) → ∃ L', cmarks κ L L' e1 ∧ G L e1 ∧ G L' e2).
  Context (HGletu : ∀ L e1 e2, G L (LetU e1 e2) → ∃ L', cmarks κ L L' e1 ∧ G L e1 ∧ G L' e2).
  Context (HGletp : ∀ L e1 e2, G L (LetP e1 e2) →
             ∃ L', cmarks κ L L' e1 ∧ G L e1 ∧ G (false .: false .: L') e2).
  Context (HGinj1 : ∀ L e, G L (Inj1 e) → G L e).
  Context (HGinj2 : ∀ L e, G L (Inj2 e) → G L e).
  Context (HGcase : ∀ L e e1 e2, G L (Case e e1 e2) →
             ∃ L', cmarks κ L L' e ∧ G L e ∧ G (false .: L') e1 ∧ G (false .: L') e2).

  Local Ltac heads_p :=
    rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
      ?opt_heads_pinst.

  Local Ltac fut := etrans; [|apply den_unionb]; rewrite ?set_map_union_L; set_solver.

  Theorem typed_sem W N Θ Γ Δ F e T a c t :
    world_wf W → typed W N Θ Γ Δ F e T a c t →
    ∀ L, G L e → ∀ W1 σ ρ B, W ⊑ W1 → hsat W1 σ ρ Γ →
    sem_later κ W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) L (sf_den ρ B (sf_pinst σ F)) e (pinst_ty σ T).
  Proof.
    intros Hwf. induction 1 as
      [Γ Δ F HΔ
      |Γ Δ F x T a HΔ
      |Γ Δ F o S x a HΔ
      |Θ Θh Γ Δ Δh F e T aT U aU ub lb c t h a φ Hφ Hlb Hth Hlc Hb IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c t h T aT U aU a1 c1 t1 c2 t2 Hsp Hl Hub H1 IH1 Hta Hla H2 IH2 Hc Ht1 Ht2
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T1' a1' T2 a2 c1 t1 c2 t2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hag Hok
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 a T aT c1 t1 c2 t2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hok
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T2 a2 a T aT c1 t1 c2 t2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hok
      |Θ Γ Δ F e T a U b c t H IH
      |Θ Γ Δ F e T a U b c t H IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 a1 T2 a2 a T aT c0 t0 c1 t1 c2 t2 Hsp Hl H0 IH0 Hta Hla H1 IH1 H2 IH2 Hok
      |Γ Δ F e m k C ub c t U aU φ HΔ Hφ Hb IH
      |Θ Γ Δ F e m k C ub c t U aU a xs ss c0 t0 Hxs HC Hss Hsi Hub H IH Hok
      |Θ Γ Δ F e S0 x m T b S ap aS a0 Tp' ap' c0 t0 Hu Hsc Hbot Hh Hub H IH Hag Hsub
      |Θ Γ Δ F e S0 x m T b S a c0 t0 Hu Hsc Hub H IH
      |Θ Γ Δ F e S0 x a c0 t0 Hu Hub H IH
      |i Θ Γ Δ F e S0 x S1 S2 a c0 t0 Hu Hub H IH
      |Θ Γ Δ F e S0 x S1 S2 a c0 t0 Hu Hub H IH
      |Θ Γ Δ F e S x a1 a2 a0 c0 t0 H IH Hok
      |Θ Θ' Γ Δ Δ' F e a1 aU c' t' Hta Hla H IH
      |Θ Γ Δ F e ub lb c' t' h a1 aU a c0 t0 H IH Hle Hok
      |Γ Δ F ℓ S HΔ Hℓ
      |Θ Γ Δ F e κf S0 x a S c0 t0 H IH
      |Θ Γ Δ F e T a T' a' c c' t t' H IH Hsub Hc Ht
      |Θ Γ Δ F e lb m C T xs a c t Hxs HC Hlbx H IH
      |Θ Γ Δ F e i lb m C T aT a U aU c t Hi Hnu H IH];
      intros L Hgl W1 σ ρ B HW Hs; cbn [pinst_ty]; rewrite ?tenv_pinst_empty, ?tenv_pinst_singleton.
    - (* E-Unit *)
      by apply later_unit, lenv_unl_pinst.
    - (* E-Var *)
      by eapply later_var; [apply lenv_only_pinst|apply HGvar].
    - (* E-Chan *)
      by apply later_chan, lenv_unl_pinst.
    - (* E-Abs *)
      assert (tfacts Θ Δ (Lam e)) as Htf by (eapply (typed_tfacts W N _ _ _ F), e_abs; eassumption).
      destruct (lb_sem W W1 Hwf HW σ ρ Γ _ _ _ Hs Hlb) as [Hbot Hlb'].
      apply later_abs.
      + by apply tfacts_pinst.
      + by rewrite lenv_bot_pinst.
      + heads_p. rewrite <-set_map_union_L. exact Hlb'.
      + intros W2 F' HW2 Hub'.
        pose proof (IH _ (HGlam _ _ Hgl) W2 σ _ B (wext_trans _ _ _ HW HW2)
                      (hsat_fvar _ _ _ _ _ _ _ Hφ (hsat_mono _ _ _ _ _ HW2 Hs) Hub')) as Hb'.
        rewrite den_nil, den_fresh in Hb'.
        eapply sem_later_ctx; [exact (thcap_erase _ _ _ _ _ Hth)| |exact Hb'].
        apply (lenv_df_pinst_eq σ (Some (T, aT) :: Δ) (Some (T, aT) :: Δh)), lenv_df_cons_eq.
        exact (lcap_df_eq _ _ _ _ Hlc).
    - (* E-App *)
      destruct (HGapp _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply later_app; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst
                        |exact (ub_sem W W1 Hwf HW σ ρ B Γ ub F Hs Hub)| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + eapply sem_later_future; [|eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|apply (IH2 L' Hg2 W1 σ ρ B HW Hs)]].
        rewrite den_union, opt_heads_pinst. done.
    - (* E-Pair *)
      destruct (HGpair _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      apply tage_df_eq in Hag. simpl in Hag.
      eapply (sem_later_blind κ _ _ _ _ _ _ (TProd (pinst_ty σ T1) a1 (pinst_ty σ T2) a2)); [|eapply later_pair; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |]].
      + assert (ty_df (pinst_ty σ T1') = ty_df (pinst_ty σ T1)) as E1 by (by rewrite !ty_df_pinst, Hag).
        assert (cr_df (pinst_ty σ T1') = cr_df (pinst_ty σ T1)) as E2
          by (rewrite !cr_df_pinst, <-(cr_df_df T1'), Hag; apply cr_df_df).
        cbn [ty_df]. by rewrite E1, E2.
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + intros B'. eapply sem_later_future; [|eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|apply (IH2 L' Hg2 W1 σ ρ (B ∪ B') HW Hs)]].
        heads_p. fut.
    - (* E-LetU *)
      destruct (HGletu _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply later_letu; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|by apply IH2].
    - (* E-LetP *)
      destruct (HGletp _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply (later_letp κ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 (fadd a a1) (fadd a a2));
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + pose proof (IH2 _ Hg2 W1 σ ρ B HW Hs) as IH2'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH2'].
        apply (lenv_df_pinst_eq σ (Some (T2, fadd a a2) :: Some (T1, fadd a a1) :: Δ2)
          (Some (T2, fadd a a2) :: Some (T1, fadd a a1) :: Δ2')), lenv_df_cons_eq, lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
    - (* E-Inj1 *)
      apply later_inj1. exact (IH L (HGinj1 _ _ Hgl) W1 σ ρ B HW Hs).
    - (* E-Inj2 *)
      apply later_inj2. exact (IH L (HGinj2 _ _ Hgl) W1 σ ρ B HW Hs).
    - (* E-Case *)
      destruct (HGcase _ _ _ _ Hgl) as (L' & Hk & Hg0 & Hg1 & Hg2).
      eapply (later_case κ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 (fadd a a1) (fadd a a2));
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| | |].
      + intros B'. eapply sem_later_future; [|apply (IH0 L Hg0 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + pose proof (IH1 _ Hg1 W1 σ ρ B HW Hs) as IH'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH'].
        apply (lenv_df_pinst_eq σ (Some (T1, fadd a a1) :: Δ2) (Some (T1, fadd a a1) :: Δ2')), lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
      + pose proof (IH2 _ Hg2 W1 σ ρ B HW Hs) as IH'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH'].
        apply (lenv_df_pinst_eq σ (Some (T2, fadd a a2) :: Δ2) (Some (T2, fadd a a2) :: Δ2')), lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
    - (* E-Box *)
      destruct (HGbox _ _ Hgl) as (mk & Hgb & Hbox).
      assert (tfacts ∅ Δ (EBox e)) as Htf by (eapply (typed_tfacts W N _ _ _ F), e_box; eassumption).
      apply (tfacts_pinst σ) in Htf. rewrite tenv_pinst_empty in Htf.
      apply (Hbox _ _ _ _ _ _ _ _ _ _ _ _ None); [exact Htf|by apply lenv_unl_pinst|].
      intros W2 xs ss F' HW2 Hxs Hss Hsc HC Hub'.
      assert (∀ a, pt_inst (pclose xs m σ) (pshift m a) = σ a) as Hτ by (by apply pclose_shift).
      assert (sinsts N (sty_df <$> ss)) as Hss'
        by (apply sinsts_inf, (sinsts_df (Some 0)); split; [done|discriminate]).
      assert (hsat W2 (pclose xs m σ) (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                (hc_fvar φ ub (hc_open m C Γ))) as Hs'.
      { apply hsat_fvar; [done|apply hsat_open; [exact Hxs|exact (hsat_mono _ _ _ _ _ HW2 Hs)|exact HC]|].
        destruct ub as [u|]; [|done]. simpl in Hub' |- *. by rewrite pclose_pt. }
      pose proof (IH (sty_df <$> ss) ltac:(by rewrite length_fmap) Hss' _ Hgb W2 (pclose xs m σ) _ B
                    (wext_trans _ _ _ HW HW2) Hs') as Hb'.
      rewrite tenv_pinst_empty, den_nil, den_fresh, (lenv_unshift _ σ m Hτ) in Hb'.
      rewrite pinst_sinst, pclose_ty in Hb'.
      eapply sem_later_blind; [|exact Hb'].
      rewrite !ty_df_sinst_map, <-list_fmap_compose.
      f_equal. f_equal. apply list_fmap_ext. intros _ s _. apply sty_df_idem.
    - (* E-Force *)
      subst m. rewrite pinst_sinst, pinst_ty_inst.
      eapply (later_force κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|done|exact (proj1 Hsi)|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)|
         |exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs)].
      assert (pt_inst σ <$> (pt_inst (plist xs) <$> ub) =
              pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup (length xs) σ) <$> ub)) as <-.
      { destruct ub; simpl; [|done]. f_equal. apply pt_inst_plist_inst. }
      exact (ub_sem W W1 Hwf HW σ ρ B Γ _ F Hs Hub).
    - (* E-Send *)
      rewrite pt_inst_shift.
      eapply (later_send κ _ _ _ _ _ _ S0 (pt_inst σ x) m T b S ap aS Hu).
      + rewrite <-(pinst_payload_at σ) by done. rewrite hbot_pinst. unfold payload_at, ty_inst.
        by rewrite hbot_pinst.
      + intros y. rewrite <-(pinst_payload_at σ), heads_pinst by done.
        intros (y0 & -> & Hy)%elem_of_map. by eapply slt_sem, Hh.
      + exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub).
      + rewrite <-(pinst_payload_at σ) by done. exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs).
    - (* E-Recv *)
      rewrite pinst_payload_at, pt_inst_shift by done.
      eapply later_recv; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs)].
    - (* E-Close *)
      eapply later_close; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs)].
    - (* E-Select *)
      rewrite pt_inst_sel.
      eapply later_select; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs)].
    - (* E-Branch *)
      rewrite !pt_inst_bra.
      eapply later_branch; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|].
      exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs).
    - (* E-Link *)
      pose proof (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs) as IH'. cbn [pinst_ty] in IH'.
      rewrite pt_inst_dual in IH'. eapply later_link, IH'.
    - (* E-SpawnLam *)
      assert (tfacts Θ Δ (ESpawn (Lam e))) as Htf by (eapply (typed_tfacts W N _ _ _ F), e_spawn_lam; eassumption).
      apply (later_spawn_lam κ _ _ _ _ _ _ a1).
      + apply tfacts_pinst. destruct Htf as [Hf Hv]. by split.
      + intros W2 HW2.
        pose proof (IH _ (HGlam _ _ (HGop _ _ _ Hgl)) W2 σ ρ B (wext_trans _ _ _ HW HW2)
                      (hsat_mono _ _ _ _ _ HW2 Hs)) as H'.
        rewrite den_nil, den_none in H'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact H'].
        apply (lenv_df_pinst_eq σ (Some (TUnit, a1) :: Δ) (Some (TUnit, a1) :: Δ')), lenv_df_cons_eq. exact (lage_df_eq _ _ _ Hla).
    - (* E-Spawn *)
      pose proof (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs) as IH'. cbn [pinst_ty] in IH'.
      eapply later_spawn, IH'.
    - (* E-New *)
      rewrite pt_inst_dual, pt_inst_pup1_0.
      change (bcs_inst σ (bcs_of (w_laws W ℓ))) with (bcs_of (w_laws W ℓ)).
      apply later_new_ext; [done|by apply lenv_unl_pinst|done].
    - (* E-NewAt *)
      rewrite pt_inst_dual, pt_inst_field. eapply later_new_at. exact (IH L (HGop _ _ _ Hgl) W1 σ ρ B HW Hs).
    - (* E-Sub *)
      eapply (later_conv κ _ _ _ _ _ _ (pinst_ty σ T)); [|by apply IH].
      rewrite !ty_df_pinst. apply tsub_pinst. exact (tsub_df _ _ _ _ Hsub).
    - (* E-Pack *)
      subst m. eapply (later_pack κ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)| |].
      + rewrite <-pinst_ty_inst. exact (lbx_sem W W1 Hwf HW σ ρ Γ lb (ty_inst xs T) Hs Hlbx).
      + rewrite <-pinst_ty_inst. by apply IH.
    - (* E-Open *)
      intros n W' Θ' γ HW' Hd HG.
      assert (lenv_pinst σ Δ !! i = Some (Some (TEx (lb_map (pt_inst σ) lb) m (bcs_inst σ C)
                (pinst_ty (pup m σ) T) aT, a))) as Hi' by (by rewrite lenv_pinst_lookup, Hi).
      destruct (GrelL_pick κ _ _ _ _ _ _ _ _ _ Hi' ltac:(intros []) HG) as (Θi & HVi & Hk).
      apply Vrel_ex_iff in HVi as (_ & xs & Hxs & HC & HVi).
      pose proof (pclose_shift xs m σ Hxs) as Hτ.
      pose proof (IH L Hgl W' (pclose xs m σ) ρ B (wext_trans _ _ _ HW HW')
                    (hsat_open _ _ _ _ _ _ _ Hxs (hsat_mono _ _ _ _ _ HW' Hs) HC)) as Hb'.
      rewrite (tenv_unshift _ σ m Hτ), lenv_pinst_insert, (lenv_unshift _ σ m Hτ),
        (sf_unshift _ σ m Hτ), (ty_unshift _ σ m Hτ), pclose_ty in Hb'.
      apply (Hb' n W' Θ' γ (wext_refl _) Hd). by apply Hk.
  Qed.
End fund.

(** ** The DF instance: no marks, β costs one *)

Definition nomarks (L : nat → bool) (_ : expr) : Prop := ∀ x, L x = false.

Lemma typed_sem_df W N Θ Γ Δ F e T a c t :
  world_wf W → typed W N Θ Γ Δ F e T a c t →
  ∀ W1 σ ρ B, W ⊑ W1 → hsat W1 σ ρ Γ →
  sem_typed_at κ_DF W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_den ρ B (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  intros Hwf Ht W1 σ ρ B HW Hs. apply sem_later_empty.
  refine (typed_sem κ_DF nomarks _ _ _ _ _ _ _ _ _ _ _ W N Θ Γ Δ F e T a c t Hwf Ht ∅ _ W1 σ ρ B HW Hs);
    [..|done]; unfold nomarks.
  - intros L y H. apply H.
  - intros L b H [|x]; [done|apply H].
  - intros L b H. exists false. split; [intros [|x]; [done|apply H]|].
    intros W0 Δ0 F0 e0 m kk C ub c0 t0 U aU a0 Htf Hu Hb.
    apply (proj2 (sem_later_unmarked _ _ _ _ _ _ _ _ H)).
    apply (gen_e_box _ _ _ _ _ _ _ _ _ _ _ _ _ a0); [simpl; lia|done|done|]. intros W2 xs ss F2 HW2 Hxs Hss Hsc HC Hub.
    assert (∀ x, (false .: L) x = false) as HL by (intros [|x]; [done|apply H]).
    apply (proj1 (sem_later_unmarked _ _ _ _ _ _ _ _ HL)). by apply Hb.
  - done.
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|intros [|[|x]]; [done|done|apply H]].
  - done.
  - done.
  - intros L e0 e1 e2 H. exists L. split_and!; [by left|done|intros [|x]; [done|apply H]|intros [|x]; [done|apply H]].
Qed.

(** ** The live instance: the marks of the guard *)

Lemma typed_sem_live W N Θ Γ Δ F e T a c t :
  world_wf W → typed W N Θ Γ Δ F e T a c t → ∅ ⊢▷ e →
  ∀ W1 σ ρ B, W ⊑ W1 → hsat W1 σ ρ Γ →
  sem_typed_at κ_L W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_den ρ B (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  intros Hwf Ht Hgd W1 σ ρ B HW Hs. apply sem_later_empty.
  refine (typed_sem κ_L lguard _ _ _ _ _ _ _ _ _ _ _ W N Θ Γ Δ F e T a c t Hwf Ht ∅ Hgd W1 σ ρ B HW Hs).
  - intros L y H. by inversion H.
  - intros L b H. by inversion H.
  - intros L b H. exists true. split; [by inversion H|]. intros ?????????????. apply later_box.
  - intros L k e0 H. by inversion H.
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e0 H. by inversion H.
  - intros L e0 H. by inversion H.
  - intros L e0 e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done|done]. apply kmarks_cmarks; [simpl; lia|done].
Qed.

(** ** The theorems *)

Theorem fundamental W Θ Δ F t T :
  strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → Θ ; Δ ⊨^F _ W t : T.
Proof.
  intros HW Ht ρ B.
  pose proof (typed_sem_df W None _ hc_empty _ F t _ _ _ _ (proj1 HW) Ht W pvar ρ B (wext_refl _) (hsat_empty _ _ _)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  apply sem_later_empty, sem_later_undf, sem_later_empty, H.
Qed.

(** The merged judgment at any refill, through its DF erasure. *)
Theorem fundamental_typed W N Θ Δ F t T a c ϑ :
  strict W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ^ a ▷ c ; ϑ →
  tenv_df Θ ; lenv_df Δ ⊨^F _ W t : ty_df T.
Proof. intros HW Ht. apply fundamental; [done|]. exact (typed_dftyped _ _ _ _ _ _ _ _ _ _ _ Ht). Qed.

Theorem live_fundamental W Θ Δ F t T :
  strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → ∅ ⊢▷ t → Θ ; Δ ⊫^F _ W t : T.
Proof.
  intros HW Ht Hgd ρ B.
  pose proof (typed_sem_live W None _ hc_empty _ F t _ _ _ _ (proj1 HW) Ht Hgd W pvar ρ B (wext_refl _)
                (hsat_empty _ _ _)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  apply sem_later_empty, sem_later_undf, sem_later_empty, H.
Qed.

Theorem live_fundamental_typed W N Θ Δ F t T a c ϑ :
  strict W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ^ a ▷ c ; ϑ → ∅ ⊢▷ t →
  tenv_df Θ ; lenv_df Δ ⊫^F _ W t : ty_df T.
Proof.
  intros HW Ht Hgd. apply live_fundamental; [done| |done].
  exact (typed_dftyped _ _ _ _ _ _ _ _ _ _ _ Ht).
Qed.
