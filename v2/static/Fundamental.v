(** * The fundamental theorem for terms (stage S5, Appendix A.3)

      strict W ∧ Θ ; ∅ ; Δ ⊢^F_W t : T  ⟹  Θ ; Δ ⊨^F_W t : T        [fundamental]

    One induction on the DF derivation ([dftyped]) instantiates the
    point variables of Γ by σ and its future variables by ρ, in any
    world W1 ⊒ W where the instantiated hypotheses of Γ hold ([hsat]),
    and reads the ⊥ flag as any set B. Each case is a [gen_e_*] rule of
    compat/Rules.v or compat/TermRules.v. A derivation at any refill N
    erases to a DF derivation ([typed_dftyped]), so [fundamental_typed]
    covers the merged judgment of Q11.

    - D-Abs and D-Box extend ρ by the future of the body, any set above
      the upper point u of the arrow or the box.
    - D-Box and D-Open lift σ under the m point variables of the box or
      the existential and close them with the instance xs of the
      relation, τ = σ(xs) ∘ (σ ↑ m).
    - D-Box quantifies over the session instances of N = ∞, V at a box
      over every hereditarily contractive instance. The two agree after
      erasure, and the relation is blind to annotations
      ([sem_typed_at_blind]).
    - D-Conv is subtyping of the erasures ([gen_e_conv]).

    D-SpawnLam is the rule E-SpawnLam ([spawn_lam_rule], valid at every
    cost table by [gen_e_spawn_lam]). The induction takes it as a
    parameter, so that the cases read the same for both tables. *)

From GV Require Export compat.TermRules static.Conservativity.

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

Lemma tfacts_unpinst σ Θ Δ e : tfacts (tenv_pinst σ Θ) (lenv_pinst σ Δ) e → tfacts Θ Δ e.
Proof.
  intros (Hf & H1 & H2). split; [unfold tenv_pinst in Hf; by rewrite dom_fmap_L in Hf|split].
  - intros x Hx. destruct (H1 x Hx) as [σ' Hσ]. rewrite lenv_pinst_lookup in Hσ.
    destruct (Δ !! x) as [[[U0 a0]|]|]; simplify_eq/=. eauto.
  - intros x U a Hx Hu. apply (H2 x (pinst_ty σ U) a); [by rewrite lenv_pinst_lookup, Hx|].
    by rewrite unlimited_pinst_iff.
Qed.

Lemma tfacts_df Θ Δ e : tfacts (tenv_df Θ) (lenv_df Δ) e → tfacts Θ Δ e.
Proof.
  intros (Hf & H1 & H2). split; [unfold tenv_df in Hf; by rewrite dom_fmap_L in Hf|split].
  - intros x Hx. destruct (H1 x Hx) as [σ' Hσ]. rewrite lenv_df_lookup in Hσ.
    destruct (Δ !! x) as [[[U0 a0]|]|]; simplify_eq/=. eauto.
  - intros x U a Hx Hu. apply (H2 x (ty_df U) (cr_df U)); [by rewrite lenv_df_lookup, Hx|].
    by rewrite unlimited_df.
Qed.

Lemma dftyped_tfacts W Θ Γ Δ F e T : Θ ; Γ ; Δ ⊢^F _ W e : T → tfacts Θ Δ e.
Proof. intros H. apply tfacts_df. eapply typed_tfacts. by apply dftyped_typed. Qed.

Lemma tfacts_lam Θ o Δ e : tfacts Θ (o :: Δ) e → tfacts Θ Δ (Lam e).
Proof. intros (Hf & Hv). split; [done|]. exact (vfacts_under _ _ (λ x, freevar x e) Hv). Qed.

Lemma tfacts_box Θ o Δ e : tfacts Θ (o :: Δ) e → tfacts Θ Δ (EBox e).
Proof. intros (Hf & Hv). split; [done|]. exact (vfacts_under _ _ (λ x, freevar x e) Hv). Qed.

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

(** ** E-New in a later world *)

Lemma gen_e_new_ext κ (ℓ : family) W0 W Δ F S a1 a2 a3 :
  W0 ⊑ W → lenv_empty Δ → ℓ ∈ w_fams W0 →
  sem_typed_at κ W ∅ Δ F (ENew ℓ)
    (TEx LBot 1 (bcs_of (w_laws W0 ℓ)) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3).
Proof.
  intros HW0 HΔ Hℓ n W' Θ' γ HW Hd HG. simpl.
  rewrite (Grel_empty κ _ _ _ _ _ HΔ HG), tenv_erase_empty, map_union_empty.
  assert (W0 ⊑ W') as HW0' by by eapply wext_trans.
  apply Erel_new_sub.
  - by apply (wext_fams _ _ HW0').
  - intros f Hf. by apply (wext_laws _ _ HW0').
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

Lemma slist_witness_inf k : ∃ ss, length ss = k ∧ sinsts None ss.
Proof. exists (repeat SEnd k). split; [apply repeat_length|apply sinsts_end]. Qed.

(** ** The semantic rule E-SpawnLam *)

Definition spawn_lam_rule (κ : ctable) : Prop :=
  ∀ W Θ Δ F e a1,
    tfacts Θ Δ (Lam e) →
    (∀ W1, W ⊑ W1 → sem_typed_at κ W1 Θ (Some (TUnit, a1) :: Δ) ∅ e TUnit) →
    sem_typed_at κ W Θ Δ F (ESpawn (Lam e)) TUnit.

Lemma spawn_lam_valid κ : spawn_lam_rule κ.
Proof. intros W Θ Δ F e a1. apply gen_e_spawn_lam. Qed.

(** ** The induction *)

Section fund.
  Context (κ : ctable) (Hβ : 1 ≤ c_beta κ) (Hsl : spawn_lam_rule κ).

  Local Ltac heads_p :=
    rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
      ?opt_heads_pinst.

  Local Ltac fut := etrans; [|apply den_unionb]; rewrite ?set_map_union_L; set_solver.

  Theorem dftyped_sem W Θ Γ Δ F e T :
    world_wf W → Θ ; Γ ; Δ ⊢^F _ W e : T →
    ∀ W1 σ ρ B, W ⊑ W1 → hsat W1 σ ρ Γ →
    sem_typed_at κ W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_den ρ B (sf_pinst σ F)) e (pinst_ty σ T).
  Proof.
    intros Hwf. induction 1 as
      [Γ Δ F HΔ
      |Γ Δ F x T a HΔ
      |Γ Δ F o S x a HΔ
      |Θ Γ Δ F e T aT U aU ub lb c t h φ Hφ Hlb Hb IH
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 ub lb c t h T aT U aU Hsp Hl Hub H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 Hsp Hl H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T Hsp Hl H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 b1 b2 T Hsp Hl H1 IH1 H2 IH2
      |Θ Γ Δ F e T a U b H IH
      |Θ Γ Δ F e T a U b H IH
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e e1 e2 T1 a1 T2 a2 b1 b2 T Hsp Hl H0 IH0 H1 IH1 H2 IH2
      |Γ Δ F e m k C ub c t U aU a φ HΔ Hφ Hb IH
      |Θ Γ Δ F e m k C ub c t U aU xs ss Hxs HC Hss Hsi Hub H IH
      |Θ Γ Δ F e S0 x m T b S ap aS Hu Hsc Hbot Hh Hub H IH
      |Θ Γ Δ F e S0 x m T b S b' a' Hu Hsc Hub H IH
      |Θ Γ Δ F e S0 x Hu Hub H IH
      |i Θ Γ Δ F e S0 x S1 S2 Hu Hf Hub H IH
      |Θ Γ Δ F e S0 x S1 S2 a1 a2 Hu Hf1 Hf2 Hub H IH
      |Θ Γ Δ F e S x a1 a2 H IH
      |Θ Γ Δ F e a1 H IH
      |Θ Γ Δ F e ub lb c' t' h a1 aU H IH
      |Γ Δ F ℓ S a1 a2 a3 HΔ Hℓ
      |Θ Γ Δ F e κf S0 x S a a1 a2 a3 H IH
      |Θ Γ Δ F e T T' a a' Hsub H IH
      |Θ Γ Δ' Δ F e T Hwk H IH
      |Θ Γ Δ U aU F e T Hu H IH
      |Θ Γ Δ F e lb m C T aT xs Hxs HC Hlbx H IH
      |Θ Γ Δ F e i lb m C T aT a b U Hi Hnu H IH];
      intros W1 σ ρ B HW Hs; cbn [pinst_ty]; rewrite ?tenv_pinst_empty, ?tenv_pinst_singleton.
    - (* D-Unit *)
      by apply gen_e_unit, lenv_empty_pinst.
    - (* D-Var *)
      by eapply gen_e_var, lenv_only_pinst.
    - (* D-Chan *)
      by apply gen_e_chan, lenv_empty_pinst.
    - (* D-Abs *)
      destruct (lb_sem W W1 Hwf HW σ ρ Γ _ _ _ Hs Hlb) as [Hbot Hlb'].
      apply gen_e_abs.
      + apply tfacts_pinst, (tfacts_lam _ (Some (T, aT))). exact (dftyped_tfacts _ _ _ _ _ _ _ Hb).
      + by rewrite lenv_bot_pinst.
      + heads_p. rewrite <-set_map_union_L. exact Hlb'.
      + intros W2 F' HW2 Hub'.
        pose proof (IH W2 σ _ B (wext_trans _ _ _ HW HW2)
                      (hsat_fvar _ _ _ _ _ _ _ Hφ (hsat_mono _ _ _ _ _ HW2 Hs) Hub')) as Hb'.
        rewrite den_nil, den_fresh in Hb'. exact Hb'.
    - (* D-App *)
      eapply gen_e_app; [by apply tsplit_pinst|by apply lenv_split_pinst
                        |exact (ub_sem W W1 Hwf HW σ ρ B Γ ub F Hs Hub)| |].
      + intros B'. eapply sem_typed_at_future; [|apply (IH1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + eapply sem_typed_at_future; [|apply (IH2 W1 σ ρ B HW Hs)].
        rewrite den_union, opt_heads_pinst. done.
    - (* D-Pair *)
      eapply gen_e_pair; [by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_typed_at_future; [|apply (IH1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + intros B'. eapply sem_typed_at_future; [|apply (IH2 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
    - (* D-LetU *)
      eapply gen_e_letu; [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH2].
      intros B'. eapply sem_typed_at_future; [|apply (IH1 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-LetP *)
      eapply (gen_e_letp _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 b1 b2);
        [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH2].
      intros B'. eapply sem_typed_at_future; [|apply (IH1 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-Inj1 *)
      by apply gen_e_inj1, IH.
    - (* D-Inj2 *)
      by apply gen_e_inj2, IH.
    - (* D-Case *)
      eapply (gen_e_case _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 b1 b2);
        [by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH1|by apply IH2].
      intros B'. eapply sem_typed_at_future; [|apply (IH0 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-Box *)
      destruct (slist_witness_inf k) as [ss0 [Hl0 Hs0]].
      pose proof (dftyped_tfacts _ _ _ _ _ _ _ (Hb ss0 Hl0 Hs0)) as Htf.
      rewrite <-(tenv_pinst_empty (pshift m)) in Htf.
      apply tfacts_unpinst, tfacts_box, (tfacts_pinst σ) in Htf. rewrite tenv_pinst_empty in Htf.
      apply gen_e_box with (a := a); [done|exact Htf|by apply lenv_unl_pinst|].
      intros W2 xs ss F' HW2 Hxs Hss Hsc HC Hub'.
      assert (∀ a, pt_inst (pclose xs m σ) (pshift m a) = σ a) as Hτ by (by apply pclose_shift).
      assert (sinsts None (sty_df <$> ss)) as Hss'
        by (apply (sinsts_df (Some 0)); split; [done|discriminate]).
      assert (hsat W2 (pclose xs m σ) (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                (hc_fvar φ ub (hc_open m C Γ))) as Hs'.
      { apply hsat_fvar; [done|apply hsat_open; [exact Hxs|exact (hsat_mono _ _ _ _ _ HW2 Hs)|exact HC]|].
        destruct ub as [u|]; [|done]. simpl in Hub' |- *. by rewrite pclose_pt. }
      pose proof (IH (sty_df <$> ss) ltac:(by rewrite length_fmap) Hss' W2 (pclose xs m σ) _ B
                    (wext_trans _ _ _ HW HW2) Hs') as Hb'.
      rewrite tenv_pinst_empty, den_nil, den_fresh, (lenv_unshift _ σ m Hτ) in Hb'.
      rewrite pinst_sinst, pclose_ty in Hb'.
      eapply sem_typed_at_blind; [|exact Hb'].
      rewrite !ty_df_sinst_map, <-list_fmap_compose.
      f_equal. f_equal. apply list_fmap_ext. intros _ s _. apply sty_df_idem.
    - (* D-Force *)
      subst m. rewrite pinst_sinst, pinst_ty_inst.
      eapply (gen_e_force κ _ _ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|done|exact (proj1 Hsi)|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)| |by apply IH].
      assert (pt_inst σ <$> (pt_inst (plist xs) <$> ub) =
              pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup (length xs) σ) <$> ub)) as <-.
      { destruct ub; simpl; [|done]. f_equal. apply pt_inst_plist_inst. }
      exact (ub_sem W W1 Hwf HW σ ρ B Γ _ F Hs Hub).
    - (* D-Send *)
      rewrite pt_inst_shift.
      eapply (gen_e_send κ _ _ _ _ _ S0 (pt_inst σ x) m T b S ap aS Hu).
      + rewrite <-(pinst_payload_at σ) by done. rewrite hbot_pinst. unfold payload_at, ty_inst.
        by rewrite hbot_pinst.
      + intros y. rewrite <-(pinst_payload_at σ), heads_pinst by done.
        intros (y0 & -> & Hy)%elem_of_map. by eapply slt_sem, Hh.
      + exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub).
      + rewrite <-(pinst_payload_at σ) by done. by apply IH.
    - (* D-Recv *)
      rewrite pinst_payload_at, pt_inst_shift by done.
      eapply gen_e_recv; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Close *)
      eapply gen_e_close; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Select *)
      rewrite pt_inst_sel.
      eapply gen_e_select; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Branch *)
      rewrite !pt_inst_bra.
      eapply gen_e_branch; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|].
      specialize (IH W1 σ ρ B HW Hs). exact IH.
    - (* D-Link *)
      specialize (IH W1 σ ρ B HW Hs). cbn [pinst_ty] in IH. rewrite pt_inst_dual in IH.
      eapply gen_e_link, IH.
    - (* D-SpawnLam *)
      apply (Hsl W1 _ _ _ e a1).
      + apply tfacts_pinst, (tfacts_lam _ (Some (TUnit, a1))). exact (dftyped_tfacts _ _ _ _ _ _ _ H).
      + intros W2 HW2. pose proof (IH W2 σ ρ B (wext_trans _ _ _ HW HW2) (hsat_mono _ _ _ _ _ HW2 Hs)) as H'.
        by rewrite den_nil, den_none in H'.
    - (* D-Spawn *)
      specialize (IH W1 σ ρ B HW Hs). cbn [pinst_ty] in IH. eapply gen_e_spawn, IH.
    - (* D-New *)
      rewrite pt_inst_dual, pt_inst_pup1_0.
      change (bcs_inst σ (bcs_of (w_laws W ℓ))) with (bcs_of (w_laws W ℓ)).
      apply gen_e_new_ext; [done|by apply lenv_empty_pinst|done].
    - (* D-NewAt *)
      rewrite pt_inst_dual, pt_inst_field. eapply gen_e_new_at. by apply IH.
    - (* D-Conv *)
      eapply (gen_e_conv κ _ _ _ _ _ (pinst_ty σ T)); [|by apply IH].
      rewrite !ty_df_pinst. by apply tsub_pinst.
    - (* D-Weak *)
      eapply gen_e_weak; [by apply lenv_wk_pinst|by apply IH].
    - (* D-Contract *)
      change (lenv_pinst σ (Some (U, aU) :: Δ)) with (Some (pinst_ty σ U, aU) :: lenv_pinst σ Δ).
      apply gen_e_contract; [by apply unlimited_pinst|]. exact (IH W1 σ ρ B HW Hs).
    - (* D-Pack *)
      subst m. eapply (gen_e_pack κ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)| |].
      + rewrite <-pinst_ty_inst. exact (lbx_sem W W1 Hwf HW σ ρ Γ lb (ty_inst xs T) Hs Hlbx).
      + rewrite <-pinst_ty_inst. by apply IH.
    - (* D-Open *)
      intros n W' Θ' γ HW' Hd HG.
      assert (lenv_pinst σ Δ !! i = Some (Some (TEx (lb_map (pt_inst σ) lb) m (bcs_inst σ C)
                (pinst_ty (pup m σ) T) aT, a))) as Hi' by (by rewrite lenv_pinst_lookup, Hi).
      destruct (Grel_pick κ _ _ _ _ _ _ _ _ Hi' HG) as (Θi & HVi & Hk).
      apply Vrel_ex_iff in HVi as (_ & xs & Hxs & HC & HVi).
      pose proof (pclose_shift xs m σ Hxs) as Hτ.
      pose proof (IH W' (pclose xs m σ) ρ B (wext_trans _ _ _ HW HW')
                    (hsat_open _ _ _ _ _ _ _ Hxs (hsat_mono _ _ _ _ _ HW' Hs) HC)) as Hb'.
      rewrite (tenv_unshift _ σ m Hτ), lenv_pinst_insert, (lenv_unshift _ σ m Hτ),
        (sf_unshift _ σ m Hτ), (ty_unshift _ σ m Hτ), pclose_ty in Hb'.
      apply (Hb' n W' Θ' γ (wext_refl _) Hd). by apply Hk.
  Qed.
End fund.

(** ** The theorems *)

Theorem fundamental W Θ Δ F t T :
  strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → Θ ; Δ ⊨^F _ W t : T.
Proof.
  intros HW Ht ρ B.
  pose proof (dftyped_sem κ_DF ltac:(simpl; lia) (spawn_lam_valid κ_DF) W Θ hc_empty Δ F t T
                (proj1 HW) Ht W pvar ρ B (wext_refl _) (hsat_empty _ _ _)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H. exact H.
Qed.

(** The merged judgment at any refill, through its DF erasure. *)
Theorem fundamental_typed W N Θ Δ F t T a c ϑ :
  strict W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ^ a ▷ c ; ϑ →
  tenv_df Θ ; lenv_df Δ ⊨^F _ W t : ty_df T.
Proof. intros HW Ht. apply fundamental; [done|]. exact (typed_dftyped _ _ _ _ _ _ _ _ _ _ _ Ht). Qed.
