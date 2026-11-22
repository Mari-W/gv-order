(** * The fundamental theorems for terms (stage S5, Appendix A.3)

      Θ ; ∅ ; Δ ⊢^F_W t : T ∧ R ⊨ W  ⟹  Θ ; Δ ⊨^F_R t : T        [fundamental]
      Θ ; ∅ ; Δ ⊢^F_W t : T ∧ ∅ ⊢▷ t ∧ R ⊨ W  ⟹  Θ ; Δ ⊫^F_R t : T
                                                          [live_fundamental]

    One induction on the merged judgment at any bound N ([typed_sem])
    instantiates the point variables of Γ by σ, in any ranked world W1
    that models the static world W ([wmodels]) and where the instantiated
    hypotheses of Γ hold ([hsat]), reads the rest
    of the future as any set ρ above its instantiated upper point
    ([rest_ok]). It is generic in the
    cost table κ and in a predicate G that says which marks L the
    induction carries into a term. Each case is a rule with marks
    [later_*] of compat/LiveRules.v.

    - The DF instance ([typed_sem_df]) carries no marks. A box leaves
      its self unmarked and pays β ([gen_e_box]).
    - The live instance ([typed_sem_live]) carries the marks of the
      guard. A box marks its self ([later_box]), a frame keeps the marks
      or clears them after an acting hole ([cmarks], [kmarks]).
    - E-Abs and E-Box extend ρ by the future of the body, any set above
      the upper point u of the arrow or the box. E-Box aod E-Open lift σ
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
  - intros x Hx. destruct (H1 x Hx) as [T Hσ]. exists (pinst_ty σ T).
    by rewrite lenv_pinst_lookup, Hσ.
  - intros x U Hx Hu. rewrite lenv_pinst_lookup in Hx.
    destruct (Δ !! x) as [[U0|]|] eqn:E; simplify_eq/=.
    apply (H2 x U0 E). by rewrite <-(unlimited_pinst_iff σ).
Qed.

(** ** Static futures read through R *)

Lemma den_none ρ : sf_den ρ (∅, None) = ∅.
Proof. unfold sf_den. simpl. set_solver. Qed.

Lemma den_rest ρ r : sf_den ρ (∅, Some r) = ρ.
Proof. unfold sf_den. simpl. set_solver. Qed.

Lemma den_rest_pinst σ ρ r : sf_den ρ (sf_pinst σ (∅, Some r)) = ρ.
Proof. unfold sf_den, sf_pinst. simpl. set_solver. Qed.

Lemma den_none_pinst σ ρ : sf_den ρ (sf_pinst σ (∅, None)) = ∅.
Proof. unfold sf_den, sf_pinst. simpl. set_solver. Qed.

Lemma rest_ok_unionb W σ F X b ρ :
  rest_ok W (sf_pinst σ F) ρ → rest_ok W (sf_pinst σ (sf_unionb F X b)) ρ.
Proof.
  intros H u Hu. apply H. rewrite sf_pinst_unionb in Hu. destruct b; [|done].
  unfold sf_unionb in Hu. simpl in Hu. done.
Qed.

(** Under a hidden end the rest is everything, which takes any set. *)
Lemma rest_ok_unionb_b W σ F X (b : bool) ρ B' :
  rest_ok W (sf_pinst σ F) ρ → rest_ok W (sf_pinst σ (sf_unionb F X b)) (ρ ∪ (if b then B' else ∅)).
Proof.
  intros H u Hu y Hy. rewrite sf_pinst_unionb in Hu. destruct b; [done|].
  apply (H u Hu). set_solver.
Qed.

Lemma rest_ok_mono W W' F ρ : W ⊑ W' → rest_ok W F ρ → rest_ok W' F ρ.
Proof. intros HW H u Hu y Hy. eapply w_lt_mono; [exact HW|]. by eapply H. Qed.

Lemma den_union ρ σ F (X : gset point) :
  sf_den ρ (sf_pinst σ (sf_unionb F X false)) = sf_den ρ (sf_pinst σ F) ∪ set_map (D:=gset point) (pt_inst σ) X.
Proof. by rewrite sf_pinst_unionb, sf_den_unionb. Qed.

Lemma den_unionb ρ (B' : gset point) σ F (X : gset point) (b : bool) :
  sf_den ρ (sf_pinst σ F) ∪ set_map (D:=gset point) (pt_inst σ) X ∪ (if b then B' else ∅) ⊆
  sf_den (ρ ∪ (if b then B' else ∅)) (sf_pinst σ (sf_unionb F X b)).
Proof.
  rewrite sf_pinst_unionb, sf_den_unionb. unfold sf_den. destruct b, (sf_pinst σ F).2; simpl; set_solver.
Qed.

(** ** The hypotheses of Γ, instantiated *)

(** Every instantiated fact of Γ holds in W. *)
Definition hsat (W : world) (σ : nat → point) (Γ : hctx) : Prop :=
  ∀ C xs x y, (C, xs) ∈ hc_hyps Γ → bcs_at (bcs_inst σ C) (pt_inst σ <$> xs) (FLt x y) →
    W ⊢ x ≺ y.

Lemma hsat_empty W σ : hsat W σ hc_empty.
Proof. intros ? ? ? ? []%elem_of_nil. Qed.

Lemma hsat_mono W W' σ Γ : W ⊑ W' → hsat W σ Γ → hsat W' σ Γ.
Proof. intros HW H1 C xs x y HC Hf. eapply w_lt_mono; [exact HW|]. by eapply H1. Qed.

Section facts.
  Context (W0 : sworld) (W : world) (Hwf : sworld_wf W0) (HW : wmodels W W0).

  Lemma slt_sem σ Γ x y : hsat W σ Γ → slt W0 Γ x y → W ⊢ pt_inst σ x ≺ pt_inst σ y.
  Proof.
    intros H1. induction 1 as [x y H|x y (C & xs & HC & H)|x y z _ IH1 _ IH2].
    - eapply wmodels_lt; [exact HW|]. by apply sw_lt_pinst.
    - eapply H1; [exact HC|]. apply bcs_at_inst. by exists (FLt x y).
    - by eapply w_lt_trans.
  Qed.

  Lemma sle_sem σ Γ x y : hsat W σ Γ → sle W0 Γ x y → w_le W (pt_inst σ x) (pt_inst σ y).
  Proof. intros Hs [->|H]; [by left|right; by eapply slt_sem]. Qed.

  Lemma hold_sem σ Γ C xs :
    hsat W σ Γ → hold_at W0 Γ C xs → wholds W (bcs_inst σ C) (pt_inst σ <$> xs).
  Proof.
    intros Hs H x y Hf. apply bcs_at_inst in Hf as ([x0 y0] & Hf & [= -> ->]).
    by eapply slt_sem, H.
  Qed.

  Lemma ub_sem σ ρ Γ ub F :
    hsat W σ Γ → rest_ok W (sf_pinst σ F) ρ → ub_below_s W0 Γ ub F →
    ub_lt W (pt_inst σ <$> ub) (sf_den ρ (sf_pinst σ F)).
  Proof.
    intros Hs Hr. destruct ub as [x|]; simpl; [|done]. intros (H1 & H2) y Hy.
    destruct F as [X o]. unfold rest_ok, sf_pinst in Hr. simpl in Hr.
    unfold sf_den, sf_pinst in Hy. simpl in Hy, H1, H2.
    apply elem_of_union in Hy as [Hy|Hy].
    - apply elem_of_map in Hy as (y0 & -> & Hy0). by eapply slt_sem, H1.
    - destruct o as [r|]; simpl in Hy; [|set_solver].
      specialize (H2 r eq_refl). destruct r as [u|]; [|done]. simpl in H2.
      assert (W ⊢ pt_inst σ u ≺ y) as Hy' by (by apply (Hr (pt_inst σ u))).
      destruct (sle_sem σ Γ x u Hs H2) as [->|Hlt]; [done|by eapply w_lt_trans].
  Qed.

  Lemma ubu_sem σ ρ Γ ub F :
    hsat W σ Γ → rest_ok W (sf_pinst σ F) ρ → ub_below_u W0 Γ ub F →
    ub_ltu W (ub_map (pt_inst σ) ub) (sf_den ρ (sf_pinst σ F)).
  Proof.
    intros Hs Hr. destruct ub as [|x|]; simpl; [done| |].
    - intros H. exact (ub_sem σ ρ Γ (Some x) F Hs Hr H).
    - intros ->. apply den_none_pinst.
  Qed.

  Lemma lbu_sem σ Γ lb H b :
    hsat W σ Γ → lbx_below_h W0 Γ lb H b →
    lb_map (pt_inst σ) lb = LBot ∨ (b = false ∧ lbx_le W (lb_map (pt_inst σ) lb) (set_map (pt_inst σ) H)).
  Proof.
    intros Hs. destruct lb as [| |l]; simpl; [intros [Hl ->]|by left|intros [Hl ->]]; right; split; try done.
    - by rewrite Hl, set_map_empty.
    - intros y (y0 & -> & Hy0)%elem_of_map. by eapply sle_sem, Hl.
  Qed.


  Lemma lbx_sem σ Γ lb X :
    hsat W σ Γ → lbx_below_h W0 Γ lb (heads X) (hbot X) →
    lbx_ok W (lb_map (pt_inst σ) lb) (pinst_ty σ X).
  Proof.
    intros Hs. rewrite <-(hbot_pinst σ X). destruct lb as [| |l]; simpl; try done.
    - intros [Hh ->]. by rewrite heads_pinst, Hh, set_map_empty.
    - intros [Hh ->]. split; [|done]. intros y. rewrite heads_pinst.
      intros (y0 & -> & Hy0)%elem_of_map. by eapply sle_sem, Hh.
  Qed.
End facts.

(** The body of E-Abs, below a point, no point or ⊤ (entry 12): the
    caller's future F' is a rest above the upper point. *)
Lemma rest_abs W σ ub F' :
  ub_ltu W (ub_map (pt_inst σ) ub) F' →
  rest_ok W (sf_pinst σ (abs_fut ub)) F' ∧ sf_den F' (sf_pinst σ (abs_fut ub)) = F'.
Proof.
  destruct ub as [|x|]; simpl; intros Hub.
  - split; [by intros u Hu|apply den_rest_pinst].
  - split; [|apply den_rest_pinst].
    intros u Hu. simpl in Hu. injection Hu as <-. exact Hub.
  - subst F'. split; [by intros u Hu|apply den_none_pinst].
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
    induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal].
    by rewrite ty_unshift, IH.
  Qed.

  Lemma sf_unshift F : sf_pinst τ (sf_pinst (pshift m) F) = sf_pinst σ F.
  Proof.
    unfold sf_pinst. simpl. f_equal; last first.
    { destruct F as [X [[u|]|]]; simpl; by rewrite ?pt_unshift. }
    apply set_eq. intros y.
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

Lemma hsat_open W σ Γ m C xs :
  length xs = m → hsat W σ Γ → wholds W (bcs_inst σ C) xs →
  hsat W (pclose xs m σ) (hc_open m C Γ).
Proof.
  intros Hm H1 HC. pose proof (pclose_shift xs m σ Hm) as Hτ.
  intros C0 xs0 x y HC0 Hf. simpl in HC0. apply elem_of_app in HC0 as [HC0|HC0].
  - apply list_elem_of_fmap in HC0 as ([C1 xs1] & [= -> ->] & HC1). simpl in Hf.
    rewrite (bcs_unshift _ σ m Hτ), (list_unshift _ σ m Hτ) in Hf. by eapply H1.
  - apply list_elem_of_singleton in HC0. injection HC0 as -> ->.
    rewrite (bcs_unshift _ σ m Hτ), (pclose_ids xs m σ Hm) in Hf. by apply HC.
Qed.

(** ** Subtyping in the relation

    A value of T is a value of T' when W ; Γ ⊢ T ≤ T' and the facts of Γ
    hold under σ. Sub-Ex reads the facts of the new constraint off the
    old one and Γ at the witnesses of the value. *)

Lemma Vrel_tsub κ W0 Γ T T' : tsub W0 Γ T T' → sworld_wf W0 → ∀ σ n W Θ v,
  wmodels W W0 → hsat W σ Γ → Vrel κ n W Θ (pinst_ty σ T) v → Vrel κ n W Θ (pinst_ty σ T') v.
Proof.
  induction 1 as [Γ
    |Γ ub lb c T1 U a c' T1' U' a' _ _ _ IH1 _ IH2
    |Γ T1 U T1' U' _ IH1 _ IH2
    |Γ T1 U T1' U' _ IH1 _ IH2
    |Γ m kk C ub c U U' c' _ HU
    |Γ s s' x a a' mt Hss _
    |Γ lb lb' m C C' T T' Hhold Hlo _ IH]; intros Hwf σ n W Θ v HW Hs; simpl.
  - done.
  - rewrite !Vrel_lolli_iff. intros (e & -> & Hfe & Hlb & H). exists e. split_and!; [done|done|done|].
    intros W' j Θ' w F HW' Hj Hd Hub Hw.
    eapply Erel_ty_mono; [|apply H; [done..|]].
    + intros m' W2 Θ2 v' HW2 _. apply IH2; [done| | ].
      * apply (wmodels_mono W). { by eapply wext_trans. } done.
      * apply (hsat_mono W). { by eapply wext_trans. } done.
    + apply IH1; [done|by apply (wmodels_mono W)|by apply (hsat_mono W)|done].
  - rewrite !Vrel_prod_iff. intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
    exists v1, v2, Θ1, Θ2. split_and!; eauto.
  - rewrite !Vrel_sum_iff. intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
  - rewrite !Vrel_box_iff. intros (-> & e & -> & Hfe & H). split; [done|]. exists e. split_and!; [done|done|].
    intros W' xs ss HW' Hxs Hss' Hsc HC. specialize (H W' xs ss HW' Hxs Hss' Hsc HC).
    destruct kk as [|kk]; simpl in HU.
    2: { destruct HU as [->|(HU & HcU & HcU')]; [done|].
         eapply Vrel_teq; [|exact H]. apply teq_thunk. apply teq_df.
         unfold ty_inst. apply teq_sinst; [apply scontr_slist, Hsc|by rewrite !tcontr_pinst|by rewrite !tcontr_pinst|].
         by apply teq_pinst, teq_pinst, teq_sym. }
    destruct ss; [|simpl in Hss'; lia]. rewrite !sinst_ty_slist_nil in H |- *.
    eapply Vrel_teq; [|exact H]. apply teq_thunk. rewrite <-!ty_inst_df. apply teq_pinst.
    rewrite !ty_df_pinst. apply teq_pinst. apply teq_df. by apply teq_sym.
  - rewrite !Vrel_sess_iff. intros (o & s0 & -> & -> & Hs0). exists o, s0. split_and!; [done|done|].
    unfold seqv in *. eapply sequiv_trans; [exact Hs0|]. by apply sequiv_df.
  - rewrite !Vrel_ex_iff. intros (Hlb & xs & Hxs & HC & H).
    pose proof (hsat_open W σ Γ m C xs Hxs Hs HC) as Hs'.
    split.
    { destruct Hlo as [->|Hlo]; [done|].
      rewrite <-pclose_ty in H. pose proof (Vrel_heads κ n W Θ _ v H) as Hh.
      rewrite hbot_pinst, heads_pinst in Hh.
      pose proof (pt_unshift _ σ m (pclose_shift xs m σ Hxs)) as Hu.
      destruct lb' as [| |x']; simpl in Hlo |- *; [|done|].
      - destruct Hlo as [Hht Hhb]. apply set_eq. intros y. split; [|set_solver].
        intros (o & S & x & Ho & ->)%elem_of_senv_heads. destruct (Hh Hhb o S x Ho) as (h & Hin & _).
        rewrite Hht in Hin. set_solver.
      - destruct Hlo as [Hle Hhb]. intros y (o & S & x & Ho & ->)%elem_of_senv_heads.
        destruct (Hh Hhb o S x Ho) as (h & Hin & Hhy).
        apply elem_of_map in Hin as (h0 & -> & Hh0).
        eapply w_le_trans; [|exact Hhy]. rewrite <-Hu.
        exact (sle_sem W0 W Hwf HW _ _ _ _ Hs' (Hle h0 Hh0)). }
    exists xs. split_and!; [done| |].
    + pose proof (hold_sem W0 W Hwf HW (pclose xs m σ) _ _ _ Hs' Hhold) as H2.
      by rewrite (bcs_unshift _ σ m (pclose_shift xs m σ Hxs)), (pclose_ids xs m σ Hxs) in H2.
    + rewrite <-!pclose_ty in H |- *. exact (IH Hwf (pclose xs m σ) n W Θ v HW Hs' H).
Qed.

Lemma later_conv_tsub κ W0 Γ σ W1 Θ Δ L F e T T' :
  sworld_wf W0 → tsub W0 Γ (ty_df T) (ty_df T') → wmodels W1 W0 → hsat W1 σ Γ →
  sem_later κ W1 Θ Δ L F e (pinst_ty σ T) → sem_later κ W1 Θ Δ L F e (pinst_ty σ T').
Proof.
  intros Hwf Hsub HW Hs. apply later_conv. intros m W2 Θ2 v HW2. rewrite !ty_df_pinst.
  apply (Vrel_tsub κ W0 Γ (ty_df T) (ty_df T')); [done|done|by apply (wmodels_mono W1)|by apply (hsat_mono W1)].
Qed.

(** ** (gen-new) in a ranked world

    The static premise of E-New gives its semantic form at every model of
    W and Γ, each partner set read as its instance under σ. *)

Lemma ctx_pt_inst σ C x : pn_vb (1 + length (bc_env C)) (pt_name x) → ¬ in_tree0 x →
  ctx_pt (bcs_inst σ C) x = pt_inst σ (ctx_pt C x).
Proof.
  intros Hs Hx. apply pn_vb_root in Hs as ([|j] & Hj & Hjl); [by destruct Hx|].
  simpl in Hjl. destruct (lookup_lt_is_Some_2 (bc_env C) j ltac:(lia)) as [e He].
  unfold ctx_pt. rewrite pt_inst_comp. apply pt_inst_ext_root. intros a Ha.
  change (pt_root x) with (pn_root (pt_name x)) in Ha. rewrite Hj in Ha. injection Ha as <-.
  unfold compose, plist. simpl. by rewrite list_lookup_fmap, He.
Qed.

Lemma new_step_inst σ C : new_step (bcs_inst σ C) = new_step C.
Proof. destruct C as [env P]. unfold new_step, bcs_inst. simpl. by rewrite length_fmap. Qed.

Lemma cfact_inst σ C x y : cfact (bcs_inst σ C) x y ↔ cfact C x y.
Proof. destruct C as [env P]. unfold cfact, bcs_inst. simpl. by rewrite length_fmap. Qed.

Lemma gen_new_sem_of W0 W Γ σ C : sworld_wf W0 → wmodels W W0 → hsat W σ Γ →
  gen_new W0 Γ C → gen_new_sem W (bcs_inst σ C).
Proof.
  intros Hwf HW Hs (Hwn & Hcc & Sr & Hne & Hex & Hst & Hen).
  assert (∀ x y, cfact C x y → pn_vb (1 + length (bc_env C)) (pt_name x) ∧ pn_vb (1 + length (bc_env C)) (pt_name y))
    as Hsc by (intros x y [_ H]; exact H).
  split_and!.
  - by rewrite new_step_inst.
  - intros x y Hf Hx Hy. apply cfact_inst in Hf. destruct (Hsc x y Hf) as [Hsx Hsy].
    rewrite !ctx_pt_inst by done. by eapply slt_sem, Hcc.
  - exists (λ u P, ∃ T, Sr u T ∧ P = pt_inst σ <$> T). split_and!.
    + intros s P (T & HT & ->). destruct T as [|t T]; [exfalso; by apply (Hne s [] HT)|cbn; congruence].
    + intros u y Hf Hu Hy. apply cfact_inst in Hf. destruct (Hex u y Hf Hu Hy) as (T & HT & Hlt).
      exists (pt_inst σ <$> T). split; [eauto|]. rewrite ctx_pt_inst by (try done; apply (Hsc u y Hf)).
      intros p (t & -> & Ht)%list_elem_of_fmap. by eapply slt_sem, Hlt.
    + intros s P s' (T & HT & ->) Hs'. rewrite new_step_inst in Hs'.
      destruct (Hst s T s' HT Hs') as (T' & HT' & Hlt). exists (pt_inst σ <$> T'). split; [eauto|].
      intros p (t' & -> & Ht')%list_elem_of_fmap. destruct (Hlt t' Ht') as (t & Ht & Hl).
      exists (pt_inst σ t). split; [by apply list_elem_of_fmap_2|]. by eapply slt_sem.
    + intros s P z (T & HT & ->) Hf Hz. apply cfact_inst in Hf.
      rewrite ctx_pt_inst by (try done; apply (Hsc z s Hf)).
      destruct (Hen s T z HT Hf Hz) as (t & Ht & Hl).
      exists (pt_inst σ t). split; [by apply list_elem_of_fmap_2|]. by eapply slt_sem.
Qed.

(** ** (acyc-new) in a world

    The static premise of E-New at N = ∞ gives its semantic form at
    every model of W and Γ. *)
Lemma cbridge_inst σ C z y : cbridge (bcs_inst σ C) z y ↔ cbridge C z y.
Proof. unfold cbridge. by setoid_rewrite cfact_inst; rewrite new_step_inst. Qed.

Lemma acyc_new_sem_of W0 W Γ σ C : sworld_wf W0 → wmodels W W0 → hsat W σ Γ →
  acyc_new W0 Γ C → acyc_new_sem W (bcs_inst σ C).
Proof.
  intros Hwf HW Hs [Hcyc Hbr]. split.
  - rewrite new_step_inst. done.
  - intros z y Hb. apply (proj1 (cbridge_inst σ C z y)) in Hb.
    assert (pn_vb (1 + length (bc_env C)) (pt_name z) ∧ pn_vb (1 + length (bc_env C)) (pt_name y)) as [Hsz Hsy].
    { destruct Hb as (_ & _ & [[_ Hsc]|(v & u & [_ Hs1] & _ & _ & [_ Hs2])]); [exact Hsc|].
      destruct Hs1, Hs2. by split. }
    pose proof Hb as (Hz & Hy & _).
    rewrite !ctx_pt_inst by done. by eapply slt_sem, (proj1 (cons_open_1 _ _ _) Hbr).
Qed.

(** The worlds a derivation at N is read at. At N = ∞ the world is
    strict. At a finite N it may also be ranked, where a creation takes
    excluded middle ([Erel_new]). *)
Definition wfit (N : fuel) (W : world) : Prop :=
  wstrict W ∨ (wranked W ∧ is_Some N ∧ excluded_middle).

Lemma wfit_mono N W W' : W ⊑ W' → wfit N W → wfit N W'.
Proof.
  intros HW [H|(H & HN & EM)]; [left; by apply (wext_strict W W')|right; split_and!; [by apply (wext_ranked W W')|done|done]].
Qed.

Lemma wfit_em N W : wfit N W → wranked W → excluded_middle.
Proof. intros [H|(_ & _ & EM)] Hr; [by destruct (wranked_strict W Hr H)|done]. Qed.

Lemma new_sem_of N W0 W Γ σ C : sworld_wf W0 → wmodels W W0 → hsat W σ Γ → wfit N W →
  new_ok N W0 Γ C → new_sem W (bcs_inst σ C).
Proof.
  intros Hwf HW Hs HK HC. split; [by eapply acyc_new_sem_of, new_ok_acyc|].
  intros Hr. destruct HK as [HS|(_ & [k ->] & _)]; [by destruct (wranked_strict W Hr HS)|].
  eapply gen_new_sem_of; [done|done|done|]. by apply (new_ok_gen (Some k)).
Qed.

(** ** Identity instances *)

Lemma tenv_pinst_pvar Θ : tenv_pinst pvar Θ = Θ.
Proof.
  unfold tenv_pinst. rewrite <-(map_fmap_id Θ) at 2. apply map_fmap_ext.
  intros _ [S x a] _. unfold tentry_pinst. simpl. by rewrite pt_inst_pvar.
Qed.

Lemma lenv_pinst_pvar Δ : lenv_pinst pvar Δ = Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite pinst_ty_pvar, IH. Qed.

Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal; last first.
  { destruct o as [[u|]|]; simpl; by rewrite ?pt_inst_pvar. }
  apply set_eq. intros y.
  rewrite elem_of_map. split; [intros (y0 & -> & Hy); by rewrite pt_inst_pvar|].
  intros Hy. exists y. by rewrite pt_inst_pvar.
Qed.

(** ** The judgment with marks reads its contexts up to annotations *)

Lemma GrelL_df κ n W Θ Δ Δ' L γ :
  lenv_df Δ' = lenv_df Δ → GrelL κ n W Θ Δ L γ → GrelL κ n W Θ Δ' L γ.
Proof.
  revert Θ Δ' L γ. induction Δ as [|o Δ IH]; intros Θ [|o' Δ'] L γ HE; try done; simpl.
  rewrite !lenv_df_cons in HE. injection HE as Ho HE.
  destruct o as [T|], o' as [T'|]; simpl in Ho; try discriminate; simpl; [|by apply IH].
  simpl in Ho. injection Ho as HT.
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

Lemma lenv_df_pinst_eq σ Δ Δ' : lenv_df Δ' = lenv_df Δ → lenv_df (lenv_pinst σ Δ') = lenv_df (lenv_pinst σ Δ).
Proof. intros H. by rewrite !lenv_df_pinst, H. Qed.

Lemma lenv_df_cons_eq o Δ Δ' : lenv_df Δ' = lenv_df Δ → lenv_df (o :: Δ') = lenv_df (o :: Δ).
Proof. intros H. by rewrite !lenv_df_cons, H. Qed.

(** ** The box rule at a mark

    A box marks its self with m. The live table marks it ([later_box]),
    the DF table leaves it unmarked and pays β ([gen_e_box]). *)

Definition box_rule (κ : ctable) (L : nat → bool) (mk : bool) : Prop :=
  ∀ W Δ F e m kk C ub c U,
    tfacts ∅ Δ (EBox e) → lenv_unl Δ →
    (∀ W1 xs ss F', W ⊑ W1 → length xs = m → length ss = kk → Forall contractive ss ∧ Forall sscoped ss →
       wholds W1 C xs → ub_lt W1 (pt_inst (plist xs) <$> ub) F' →
       sem_later κ W1 ∅ (Some (TBox m kk C ub c U) :: Δ) (mk .: L) F' e
         (sinst_ty (slist ss) (ty_inst xs U))) →
    sem_later κ W ∅ Δ L F (EBox e) (TBox m kk C ub c U).

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
  Context (HGinj : ∀ L b e, G L (Inj b e) → G L e).
  Context (HGcase : ∀ L e e1 e2, G L (Case e e1 e2) →
             ∃ L', cmarks κ L L' e ∧ G L e ∧ G (false .: L') e1 ∧ G (false .: L') e2).

  Local Ltac heads_p :=
    rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
      ?opt_heads_pinst.

  Local Ltac fut := etrans; [|apply den_unionb]; rewrite ?set_map_union_L; set_solver.
  Local Ltac rest_tac :=
    first [ assumption | apply rest_ok_unionb; assumption | apply rest_ok_unionb_b; assumption ].

  Theorem typed_sem W N Θ Γ Δ F e T c :
    sworld_wf W → typed W N Θ Γ Δ F e T c →
    ∀ L, G L e → ∀ W1 σ ρ, wmodels W1 W → wfit N W1 → hsat W1 σ Γ → rest_ok W1 (sf_pinst σ F) ρ →
    sem_later κ W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) L (sf_den ρ (sf_pinst σ F)) e (pinst_ty σ T).
  Proof.
    intros Hwf. induction 1 as
      [Γ Δ F HΔ
      |Γ Δ F x T HΔ
      |Γ Δ F o S x a mt HΔ
      |Θ Θh Γ Δ Δh F e T U ub lb c a Hlb Hth Hlc HTc Hb IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 Hsp Hl Hub H1 IH1 Hta Hla H2 IH2 Hc
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hag
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
      |i Θ Γ Δ F e T U c HTc H IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 c1 c2 Hsp Hl H0 IH0 Hta Hla H1 IH1 H2 IH2
      |Γ Δ F e m k C ub c U HΔ HUc Hb IH
      |Θ Γ Δ F e m k C ub c U xs ss c0 Hxs HC Hss Hsi Hub H IH
      |Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 Hu Hsc [Hbot Hh] Hub H IH Hag Hsub
      |Θ Γ Δ F e S0 x m T S a mS c0 Hu Hsc Hub H IH
      |Θ Γ Δ F e S0 x a mS c0 Hu Hub H IH
      |i Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
      |Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
      |Θ Γ Δ F e S x a1 m1 a2 m2 c0 H IH Hl1 Hl2
      |Θ Γ Δ F e ub lb c' a c0 H IH
      |Γ Δ F C S m1 m2 HΔ HC Htk HSc
      |Γ Δ F x κf S m1 m2 HΔ Htk HSc
      |Θ Γ Δ F e T T' c c' H IH Hsub Hc HTc
      |Θ Γ Δ F e lb m C T xs c Hxs HC Hlbx Hexw H IH
      |Θ Γ Δ F e i lb m C T U c Hi Hnu _ H IH];
      intros L Hgl W1 σ ρ HW HK Hs Hr; cbn [pinst_ty]; rewrite ?tenv_pinst_empty, ?tenv_pinst_singleton.
    - (* E-Unit *)
      by apply later_unit, lenv_unl_pinst.
    - (* E-Var *)
      by eapply later_var; [apply lenv_only_pinst|apply HGvar].
    - (* E-Chan *)
      by apply later_chan, lenv_unl_pinst.
    - (* E-Abs *)
      assert (tfacts Θ Δ (Lam e)) as Htf by (eapply (typed_tfacts W N _ _ _ F), e_abs; eassumption).
      apply later_abs.
      + by apply tfacts_pinst.
      + destruct (lbu_sem W W1 Hwf HW σ Γ _ _ _ Hs Hlb) as [Hl|[Hbot Hlb']]; [by left|right].
        split; [by rewrite lenv_bot_pinst|]. heads_p. rewrite <-set_map_union_L. exact Hlb'.
      + intros W2 F' HW2 Hub'.
        destruct (rest_abs W2 σ ub F' Hub') as [Hr' Hden].
        pose proof (IH _ (HGlam _ _ Hgl) W2 σ F' (wmodels_mono _ _ _ HW2 HW) (wfit_mono _ _ _ HW2 HK) (hsat_mono _ _ _ _ HW2 Hs) Hr') as Hb'.
        rewrite Hden in Hb'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hth)| |exact Hb'].
        apply (lenv_df_pinst_eq σ (Some T :: Δ) (Some T :: Δh)), lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hlc).
    - (* E-App *)
      destruct (HGapp _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply later_app; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst
                        |exact (ubu_sem W W1 Hwf HW σ ρ Γ ub F Hs Hr Hub)| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ (ρ ∪ (if lenv_bot Δ2 then B' else ∅)) HW HK Hs ltac:(rest_tac))].
        heads_p. fut.
      + intros B'. eapply sem_later_future; [|eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|apply (IH2 L' Hg2 W1 σ (ρ ∪ (if lb_bot lb then B' else ∅)) HW HK Hs ltac:(rest_tac))]].
        rewrite lb_bot_map. assert (lb_heads (lb_map (pt_inst σ) lb) = set_map (pt_inst σ) (lb_heads lb)) as ->
          by (destruct lb; simpl; set_solver). fut.
    - (* E-Pair *)
      destruct (HGpair _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      apply tage_df_eq in Hag. simpl in Hag.
      eapply (sem_later_blind κ _ _ _ _ _ _ (TProd (pinst_ty σ T1) (pinst_ty σ T2))); [|eapply later_pair; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |]].
      + assert (ty_df (pinst_ty σ T1') = ty_df (pinst_ty σ T1)) as E1 by (by rewrite !ty_df_pinst, Hag).
        cbn [ty_df]. by rewrite E1.
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ (ρ ∪ (if lenv_bot Δ2 then B' else ∅)) HW HK Hs ltac:(rest_tac))].
        heads_p. fut.
      + intros B'. eapply sem_later_future; [|eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|apply (IH2 L' Hg2 W1 σ (ρ ∪ (if hbot T1 then B' else ∅)) HW HK Hs ltac:(rest_tac))]].
        heads_p. fut.
    - (* E-LetU *)
      destruct (HGletu _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply later_letu; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ (ρ ∪ (if lenv_bot Δ2 then B' else ∅)) HW HK Hs ltac:(rest_tac))].
        heads_p. fut.
      + eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)
          |exact (lenv_df_pinst_eq _ _ _ (lage_df_eq _ _ _ Hla))|by apply IH2].
    - (* E-LetP *)
      destruct (HGletp _ _ _ Hgl) as (L' & Hk & Hg1 & Hg2).
      eapply (later_letp κ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2));
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ (ρ ∪ (if lenv_bot Δ2 then B' else ∅)) HW HK Hs ltac:(rest_tac))].
        heads_p. fut.
      + pose proof (IH2 _ Hg2 W1 σ ρ HW HK Hs ltac:(rest_tac)) as IH2'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH2'].
        apply (lenv_df_pinst_eq σ (Some T2 :: Some T1 :: Δ2)
          (Some T2 :: Some T1 :: Δ2')), lenv_df_cons_eq, lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
    - (* E-Inj *)
      apply later_inj. destruct i; exact (IH L (HGinj _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac)).
    - (* E-Case *)
      destruct (HGcase _ _ _ _ Hgl) as (L' & Hk & Hg0 & Hg1 & Hg2).
      eapply (later_case κ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2));
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| | |].
      + intros B'. eapply sem_later_future; [|apply (IH0 L Hg0 W1 σ (ρ ∪ (if lenv_bot Δ2 then B' else ∅)) HW HK Hs ltac:(rest_tac))].
        heads_p. fut.
      + pose proof (IH1 _ Hg1 W1 σ ρ HW HK Hs ltac:(rest_tac)) as IH'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH'].
        apply (lenv_df_pinst_eq σ (Some T1 :: Δ2) (Some T1 :: Δ2')), lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
      + pose proof (IH2 _ Hg2 W1 σ ρ HW HK Hs ltac:(rest_tac)) as IH'.
        eapply sem_later_ctx; [exact (thage_erase _ _ _ _ Hta)| |exact IH'].
        apply (lenv_df_pinst_eq σ (Some T2 :: Δ2) (Some T2 :: Δ2')), lenv_df_cons_eq.
        exact (lage_df_eq _ _ _ Hla).
    - (* E-Box *)
      destruct (HGbox _ _ Hgl) as (mk & Hgb & Hbox).
      assert (tfacts ∅ Δ (EBox e)) as Htf by (eapply (typed_tfacts W N _ _ _ F), e_box; eassumption).
      apply (tfacts_pinst σ) in Htf. rewrite tenv_pinst_empty in Htf.
      apply (Hbox _ _ _ _ _ _ _ _ _ _); [exact Htf|by apply lenv_unl_pinst|].
      intros W2 xs ss F' HW2 Hxs Hss Hsc HC Hub'.
      assert (∀ a, pt_inst (pclose xs m σ) (pshift m a) = σ a) as Hτ by (by apply pclose_shift).
      assert (sinsts N (sty_df <$> ss)) as Hss'
        by (apply sinsts_inf, (sinsts_df (Some 0)); split; [done|discriminate]).
      assert (hsat W2 (pclose xs m σ) (hc_open m C Γ)) as Hs'.
      { apply hsat_open; [exact Hxs|exact (hsat_mono _ _ _ _ HW2 Hs)|exact HC]. }
      assert (rest_ok W2 (sf_pinst (pclose xs m σ) (∅, Some (rest_of ub))) F') as Hr'.
      { intros u Hu y Hy. destruct ub as [u0|]; simpl in Hu; [|done]. injection Hu as <-.
        simpl in Hub'. rewrite pclose_pt. by apply Hub'. }
      pose proof (IH (sty_df <$> ss) ltac:(by rewrite length_fmap) Hss' _ Hgb W2 (pclose xs m σ) F'
                    (wmodels_mono _ _ _ HW2 HW) (wfit_mono _ _ _ HW2 HK) Hs' Hr') as Hb'.
      rewrite tenv_pinst_empty, den_rest_pinst, (lenv_unshift _ σ m Hτ) in Hb'.
      rewrite pinst_sinst, pclose_ty in Hb'.
      eapply sem_later_blind; [|exact Hb'].
      rewrite !ty_df_sinst_map, <-list_fmap_compose.
      f_equal. f_equal. apply list_fmap_ext. intros _ s _. apply sty_df_idem.
    - (* E-Force *)
      subst m. rewrite pinst_sinst, pinst_ty_inst.
      eapply (later_force κ _ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|done|exact (proj1 Hsi)|exact (hold_sem W W1 Hwf HW σ Γ C xs Hs HC)|
         |exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac))].
      assert (pt_inst σ <$> (pt_inst (plist xs) <$> ub) =
              pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup (length xs) σ) <$> ub)) as <-.
      { destruct ub; simpl; [|done]. f_equal. apply pt_inst_plist_inst. }
      exact (ub_sem W W1 Hwf HW σ ρ Γ _ F Hs Hr Hub).
    - (* E-Send *)
      rewrite pt_inst_shift.
      eapply (later_send κ _ _ _ _ _ _ _ S0 (pt_inst σ x) m T S aS _ _ Hu).
      + rewrite <-(pinst_payload_at σ) by done. by rewrite hbot_pinst.
      + intros y. rewrite <-(pinst_payload_at σ), heads_pinst by done.
        intros (y0 & -> & Hy)%elem_of_map. by eapply slt_sem, Hh.
      + exact (ub_sem W W1 Hwf HW σ ρ Γ (Some x) F Hs Hr Hub).
      + rewrite <-(pinst_payload_at σ) by done.
        eapply (later_conv_tsub κ W Γ σ _ _ _ _ _ _ (TProd Tp (TSess S0 x aS mS)) (TProd (payload_at m T x) (TSess S0 x aS mS)));
          [exact Hwf| |exact HW|exact Hs|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac))].
        cbn [ty_df]. apply sub_prod; [|apply tsub_refl].
        rewrite <-(tage_df_eq _ _ _ Hag). exact (tsub_df _ _ _ _ Hsub).
    - (* E-Recv *)
      rewrite pinst_payload_at, pt_inst_shift by done.
      eapply later_recv; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ Γ (Some x) F Hs Hr Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac))].
    - (* E-Close *)
      eapply later_close; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ Γ (Some x) F Hs Hr Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac))].
    - (* E-Select *)
      rewrite pt_inst_sel.
      eapply later_select; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ Γ (Some x) F Hs Hr Hub)|exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac))].
    - (* E-Branch *)
      rewrite !pt_inst_bra.
      eapply later_branch; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ Γ (Some x) F Hs Hr Hub)|].
      exact (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac)).
    - (* E-Link *)
      pose proof (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac)) as IH'. cbn [pinst_ty] in IH'.
      rewrite pt_inst_dual in IH'. eapply later_link, IH'.
    - (* E-Spawn *)
      pose proof (IH L (HGop _ _ _ Hgl) W1 σ ρ HW HK Hs ltac:(rest_tac)) as IH'. cbn [pinst_ty] in IH'.
      eapply later_spawn, IH'.
    - (* E-New *)
      rewrite pt_inst_dual, pt_inst_pup1_0.
      apply later_new; [exact (wfit_em N W1 HK)|by apply lenv_unl_pinst|by apply (new_sem_of N W W1 Γ σ C)].
    - (* E-New at a field *)
      rewrite pt_inst_dual. apply later_new_fld. by apply lenv_unl_pinst.
    - (* E-Sub *)
      eapply (later_conv_tsub κ W Γ σ _ _ _ _ _ _ T T'); [exact Hwf|exact (tsub_df _ _ _ _ Hsub)|exact HW|exact Hs|by apply IH].
    - (* E-Pack *)
      subst m. eapply (later_pack κ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|exact (hold_sem W W1 Hwf HW σ Γ C xs Hs HC)| |].
      + rewrite <-pinst_ty_inst. exact (lbx_sem W W1 Hwf HW σ Γ lb (ty_inst xs T) Hs Hlbx).
      + rewrite <-pinst_ty_inst. by apply IH.
    - (* E-Open *)
      intros n W' Θ' γ HW' Hd HG.
      assert (lenv_pinst σ Δ !! i = Some (Some (TEx (lb_map (pt_inst σ) lb) m (bcs_inst σ C)
                (pinst_ty (pup m σ) T)))) as Hi' by (by rewrite lenv_pinst_lookup, Hi).
      destruct (GrelL_pick κ _ _ _ _ _ _ _ _ Hi' ltac:(intros []) HG) as (Θi & HVi & Hk).
      apply Vrel_ex_iff in HVi as (_ & xs & Hxs & HC & HVi).
      pose proof (pclose_shift xs m σ Hxs) as Hτ.
      pose proof (IH L Hgl W' (pclose xs m σ) ρ (wmodels_mono _ _ _ HW' HW) (wfit_mono _ _ _ HW' HK)
                    (hsat_open _ _ _ _ _ _ Hxs (hsat_mono _ _ _ _ HW' Hs) HC)
                    ltac:(rewrite (sf_unshift _ σ m Hτ); by eapply rest_ok_mono)) as Hb'.
      rewrite (tenv_unshift _ σ m Hτ), lenv_pinst_insert, (lenv_unshift _ σ m Hτ),
        (sf_unshift _ σ m Hτ), (ty_unshift _ σ m Hτ), pclose_ty in Hb'.
      apply (Hb' n W' Θ' γ (wext_refl _) Hd). by apply Hk.
    Unshelve. all: exact None.
  Qed.
End fund.

(** ** The DF instance: no marks, β costs one *)

Definition nomarks (L : nat → bool) (_ : expr) : Prop := ∀ x, L x = false.

Lemma typed_sem_df W N Θ Γ Δ F e T c :
  sworld_wf W → typed W N Θ Γ Δ F e T c →
  ∀ W1 σ ρ, wmodels W1 W → wfit N W1 → hsat W1 σ Γ → rest_ok W1 (sf_pinst σ F) ρ →
  sem_typed_at κ_DF W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_den ρ (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  intros Hwf Ht W1 σ ρ HW HK Hs Hr. apply sem_later_empty.
  refine (typed_sem κ_DF nomarks _ _ _ _ _ _ _ _ _ _ W N Θ Γ Δ F e T c Hwf Ht ∅ _ W1 σ ρ HW HK Hs Hr);
    [..|done]; unfold nomarks.
  - intros L y H. apply H.
  - intros L b H [|x]; [done|apply H].
  - intros L b H. exists false. split; [intros [|x]; [done|apply H]|].
    intros W0 Δ0 F0 e0 m kk C ub c0 U Htf Hu Hb.
    apply (proj2 (sem_later_unmarked _ _ _ _ _ _ _ _ H)).
    apply (gen_e_box _ _ _ _ _ _ _ _ _ _ _); [simpl; lia|done|done|]. intros W2 xs ss F2 HW2 Hxs Hss Hsc HC Hub.
    assert (∀ x, (false .: L) x = false) as HL by (intros [|x]; [done|apply H]).
    apply (proj1 (sem_later_unmarked _ _ _ _ _ _ _ _ HL)). by apply Hb.
  - done.
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|done].
  - intros L e1 e2 H. exists L. split_and!; [by left|done|intros [|[|x]]; [done|done|apply H]].
  - done.
  - intros L e0 e1 e2 H. exists L. split_and!; [by left|done|intros [|x]; [done|apply H]|intros [|x]; [done|apply H]].
Qed.

(** ** The live instance: the marks of the guard *)

Lemma typed_sem_live W N Θ Γ Δ F e T c :
  sworld_wf W → typed W N Θ Γ Δ F e T c → ∅ ⊢▷ e →
  ∀ W1 σ ρ, wmodels W1 W → wfit N W1 → hsat W1 σ Γ → rest_ok W1 (sf_pinst σ F) ρ →
  sem_typed_at κ_L W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_den ρ (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  intros Hwf Ht Hgd W1 σ ρ HW HK Hs Hr. apply sem_later_empty.
  refine (typed_sem κ_L lguard _ _ _ _ _ _ _ _ _ _ W N Θ Γ Δ F e T c Hwf Ht ∅ Hgd W1 σ ρ HW HK Hs Hr).
  - intros L y H. by inversion H.
  - intros L b H. by inversion H.
  - intros L b H. exists true. split; [by inversion H|]. intros ??????????. apply later_box.
  - intros L k e0 H. by inversion H.
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done]. apply kmarks_cmarks; [simpl; lia|done].
  - intros L b0 e0 H. by inversion H.
  - intros L e0 e1 e2 H. inversion H; subst. eexists; split_and!; [|done|done|done]. apply kmarks_cmarks; [simpl; lia|done].
Qed.

(** ** The theorems

    The deadlock-free and live theorems read strict worlds and take no
    excluded middle. A derivation at a finite N is read at any world,
    and at a ranked world it takes excluded middle
    ([live_fundamental_ranked]), which the lock-free threads use. *)

Theorem fundamental W R Θ Δ F t T :
  sworld_wf W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → wmodels R W → wstrict R → Θ ; Δ ⊨^F _ R t : T.
Proof.
  intros HW Ht HR HS ρ Hr.
  pose proof (typed_sem_df W None _ hc_empty _ F t _ _ HW Ht R pvar ρ HR (or_introl HS) (hsat_empty _ _)
                ltac:(by rewrite sf_pinst_pvar)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  apply sem_later_empty, sem_later_undf, sem_later_empty, H.
Qed.

(** The merged judgment at any refill, through its DF erasure. *)
Theorem fundamental_typed W R N Θ Δ F t T c :
  sworld_wf W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ▷ c → wmodels R W → wstrict R →
  tenv_df Θ ; lenv_df Δ ⊨^F _ R t : ty_df T.
Proof. intros HW Ht HR HS. apply (fundamental W); [done| |done|done]. exact (typed_dftyped _ _ _ _ _ _ _ _ _ Ht). Qed.

Theorem live_fundamental W R Θ Δ F t T :
  sworld_wf W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → ∅ ⊢▷ t → wmodels R W → wstrict R → Θ ; Δ ⊫^F _ R t : T.
Proof.
  intros HW Ht Hgd HR HS ρ Hr.
  pose proof (typed_sem_live W None _ hc_empty _ F t _ _ HW Ht Hgd R pvar ρ HR (or_introl HS)
                (hsat_empty _ _) ltac:(by rewrite sf_pinst_pvar)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  apply sem_later_empty, sem_later_undf, sem_later_empty, H.
Qed.

Theorem live_fundamental_typed W R N Θ Δ F t T c :
  sworld_wf W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ▷ c → ∅ ⊢▷ t → wmodels R W → wstrict R →
  tenv_df Θ ; lenv_df Δ ⊫^F _ R t : ty_df T.
Proof.
  intros HW Ht Hgd HR HS. apply (live_fundamental W); [done| |done|done|done].
  exact (typed_dftyped _ _ _ _ _ _ _ _ _ Ht).
Qed.

(** The relation reads a context and a type through their erasure. *)
Lemma sem_later_df κ W Θ Δ L F t T :
  sem_later κ W Θ Δ L F t T → sem_later κ W (tenv_df Θ) (lenv_df Δ) L F t (ty_df T).
Proof.
  intros H n W' Θ0 γ HW Hd HG.
  assert (tenv_erase Θ ##ₘ Θ0) as Hd'.
  { rewrite map_disjoint_dom in Hd |- *. unfold tenv_erase, tenv_df in *. by rewrite !dom_fmap_L in *. }
  specialize (H n W' Θ0 γ HW Hd' (GrelL_df κ _ _ _ _ _ _ _ (eq_sym (lenv_df_idem Δ)) HG)).
  apply (Erel_blind _ _ _ _ T); [by rewrite ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). apply senv_eqv_union; [|apply senv_eqv_refl].
  intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem.
  apply sequiv_refl.
Qed.

(** A derivation of the lock-free judgment at a finite N, read directly
    at any world. At a ranked world its creations take (gen-new) and
    excluded middle. The lock-free threads use this theorem. *)
Theorem live_fundamental_ranked (EM : excluded_middle) W R N Θ Δ F t T c :
  sworld_wf W → Θ ; hc_empty ; Δ ⊢^F _{W,Some N} t : T ▷ c → ∅ ⊢▷ t → wmodels R W →
  tenv_df Θ ; lenv_df Δ ⊫^F _ R t : ty_df T.
Proof.
  intros HW Ht Hgd HR ρ Hr.
  assert (wfit (Some N) R) as HK.
  { destruct (wkind_dec R) as [Hr'|Hs']; [right; split_and!; [done|by eexists|done]|by left]. }
  pose proof (typed_sem_live W (Some N) _ hc_empty _ F t _ _ HW Ht Hgd R pvar ρ HR HK
                (hsat_empty _ _) ltac:(by rewrite sf_pinst_pvar)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  apply sem_later_empty, sem_later_df, sem_later_empty, H.
Qed.
