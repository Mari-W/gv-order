(** * Conservativity: deadlock-freedom typing is the instance N = ∞ (stage S2)

    Decision Q11 replaces typing and the cost judgment by one judgment
    and claims that deadlock-freedom typing is its instance N = ∞
    (proposal §2.17). DF typing [dftyped] is defined as the instance
    N = ∞ with the annotations of N = ∞ ([ty_df]) and cost ∞.

    - The DF rules [d_*] are lemmas: each lifts its premises to N = ∞
      and concludes by the rule [e_*] of the merged judgment.
    - [typed_dftyped]: a derivation at any bound N, in particular at
      N = ∞, erases to a DF derivation.
    - [dftyped_typed]: the definition read as a statement.

    Two choices of the merged judgment make the lifting go through, and
    they are deviations from the text of §2.17 (docs/redesign/progress.md).
    The credit a of an arrow ranges over ℕ ∪ {∞} and the lifting takes
    a = ∞, because E-Abs ages the captured context by a, which every
    credit ∞ of N = ∞ covers. And at N = ∞ box
    bodies and forces meet only session instances with the annotations
    of N = ∞ ([sinsts]). *)

From GV Require Export static.Typing types.Erasure.

(** ** Contexts *)

Lemma tenv_df_empty : tenv_df ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_df_singleton o S x a m : tenv_df {[o := TE S x a m]} = {[o := TE (sty_df S) x None None]}.
Proof. unfold tenv_df. by rewrite map_fmap_singleton. Qed.

Lemma tsplit_df Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tsplit (tenv_df Θ) (tenv_df Θ1) (tenv_df Θ2).
Proof. intros [Hd ->]. split; [by apply map_disjoint_fmap|]. unfold tenv_df. by rewrite map_fmap_union. Qed.

Lemma tenv_heads_df Θ : tenv_heads (tenv_df Θ) = tenv_heads Θ.
Proof.
  apply set_eq. intros y. rewrite !elem_of_tenv_heads. unfold tenv_df.
  setoid_rewrite lookup_fmap. split.
  - intros (o & e & He & ->). destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=. eauto.
  - intros (o & e & He & ->). exists o, (tentry_df e). by rewrite He.
Qed.

Lemma tenv_df_pinst σ Θ : tenv_df (tenv_pinst σ Θ) = tenv_pinst σ (tenv_df Θ).
Proof.
  unfold tenv_df, tenv_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
  intros _ [S x a m] _. unfold tentry_df, tentry_pinst. simpl. by rewrite sty_df_pinst.
Qed.

Lemma lenv_df_cons o Δ : lenv_df (o :: Δ) = (ty_df <$> o) :: lenv_df Δ.
Proof. done. Qed.

Lemma lenv_df_lookup Δ i : lenv_df Δ !! i = fmap (M:=option) ty_df <$> Δ !! i.
Proof. unfold lenv_df. by rewrite list_lookup_fmap. Qed.

Lemma lenv_only_df Δ x T : lenv_only Δ x T → lenv_only (lenv_df Δ) x (ty_df T).
Proof.
  intros [Hx Hy]. split; [by rewrite lenv_df_lookup, Hx|].
  intros y σ' Hne Hσ. rewrite lenv_df_lookup in Hσ.
  destruct (Δ !! y) as [[U|]|] eqn:E; simplify_eq/=. apply unlimited_df. exact (Hy y U Hne E).
Qed.

Lemma lenv_split_df Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lenv_df Δ) (lenv_df Δ1) (lenv_df Δ2).
Proof.
  induction 1 as [|? ? ? _ IH|T ? ? ? _ IH|T ? ? ? _ IH|U ? ? ? HU _ IH];
    simpl; constructor; try done. by apply unlimited_df.
Qed.

Lemma lenv_wk_df Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_df Δ') (lenv_df Δ).
Proof.
  induction 1 as [|o ? ? _ IH|U ? ? HU _ IH]; rewrite ?lenv_df_cons; simpl; constructor; try done.
  by apply unlimited_df.
Qed.

Lemma lenv_unl_df Δ : lenv_unl Δ → lenv_unl (lenv_df Δ).
Proof.
  intros H o Ho. unfold lenv_df in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & -> & HU)]; [by left|right].
  eexists _. split; [done|]. by apply unlimited_df.
Qed.

Lemma lenv_heads_df Δ : lenv_heads (lenv_df Δ) = lenv_heads Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?heads_df; congruence. Qed.

Lemma lenv_bot_df Δ : lenv_bot (lenv_df Δ) = lenv_bot Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?hbot_df; congruence. Qed.

Lemma lenv_df_pinst σ Δ : lenv_df (lenv_pinst σ Δ) = lenv_pinst σ (lenv_df Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal].
  rewrite ty_df_pinst. by f_equal.
Qed.

Lemma lenv_df_insert Δ i o : lenv_df (<[i := o]> Δ) = <[i := fmap (M:=option) ty_df o]> (lenv_df Δ).
Proof. unfold lenv_df. by rewrite list_fmap_insert. Qed.

Lemma tenv_df_idem Θ : tenv_df (tenv_df Θ) = tenv_df Θ.
Proof.
  unfold tenv_df. rewrite <-map_fmap_compose. apply map_fmap_ext.
  intros _ [S x a m] _. unfold tentry_df. simpl. by rewrite sty_df_idem.
Qed.

Lemma lenv_df_idem Δ : lenv_df (lenv_df Δ) = lenv_df Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite ty_df_idem, IH. Qed.

(** ** Aging of contexts with the annotations of N = ∞ *)

Lemma tage_df c T : tage c (ty_df T) (ty_df T).
Proof.
  induction T; simpl.
  - apply age_free. constructor.
  - exact (age_arr c _ _ _ _ _ None (fle_inf c)).
  - by apply age_prod.
  - by apply age_sum.
  - apply age_free. constructor.
  - exact (age_sess c _ _ None None (fle_inf c)).
  - by apply age_ex.
Qed.

Lemma lage_df c Δ : lage c (lenv_df Δ) (lenv_df Δ).
Proof. induction Δ as [|[T|] Δ IH]; simpl; constructor; auto using tage_df. Qed.

Lemma thage_df c Θ : thage c (tenv_df Θ) (tenv_df Θ).
Proof.
  intros o. unfold tenv_df. rewrite lookup_fmap. destruct (Θ !! o); simpl; [|done].
  split_and!; try done. apply fle_inf.
Qed.

(** ** Subtyping *)

Lemma hold_open_self W Γ n C : hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C) (ids n).
Proof.
  intros x y Hf. apply fl_h. exists (bcs_inst (pshift n) C), (ids n). split; [|done].
  unfold hc_open. simpl. apply elem_of_app. right. by left.
Qed.

Lemma tsub_refl W Γ T : tsub W Γ T T.
Proof.
  revert Γ. induction T; intros Γ.
  - apply sub_unit.
  - apply sub_arr; auto using fle_refl.
  - apply sub_prod; auto.
  - apply sub_sum; auto.
  - apply sub_box; [apply fle_refl|]. destruct k; [apply teq_refl|by left].
  - apply sub_sess; [apply sequiv_refl|apply fle_refl].
  - apply sub_ex; [apply hold_open_self|by left|auto].
Qed.

(** Opening x : ∃^l ιs. C. T and packing it at ιs with a constraint C'
    and a lower bound l′ that Γ and C entail is one step of Sub-Ex, so
    e and let x = e in x type alike for this pattern. *)
Lemma tsub_open_pack W Γ lb lb' n C C' T :
  hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C') (ids n) →
  lbx_below_h W (hc_open n C Γ) (lb_map (pt_inst (pshift n)) lb') (heads T) (hbot T) →
  tsub W Γ (TEx lb n C T) (TEx lb' n C' T).
Proof. intros H1 H2. apply sub_ex; [done|by right|apply tsub_refl]. Qed.

Lemma tsub_df W Γ T T' : tsub W Γ T T' → tsub W Γ (ty_df T) (ty_df T').
Proof.
  induction 1; cbn [ty_df].
  - apply sub_unit.
  - apply sub_arr; auto using fle_refl.
  - by apply sub_prod.
  - by apply sub_sum.
  - apply sub_box; [apply fle_refl|]. destruct k; [by apply teq_df|].
    destruct H0 as [->|(? & ? & ?)]; [by left|right]. rewrite !tcontr_df. split_and!; [by apply teq_df|done|done].
  - apply sub_sess; [by apply sequiv_df|apply fle_refl].
  - apply sub_ex; [done| |done]. destruct H0 as [->|H0]; [by left|right].
    by rewrite heads_df, hbot_df.
Qed.

(** ** Instances of session variables *)

Lemma ahc_df n : ∀ s, ahc n s → ahc n (sty_df s).
Proof.
  induction n as [|n IH]; intros s H; [done|]. simpl in *. unfold hc_step in *.
  rewrite hd_df. destruct (hd s); simpl in *; naive_solver.
Qed.

Lemma hcontractive_df s : hcontractive s → hcontractive (sty_df s).
Proof. intros H n. by apply ahc_df. Qed.

Lemma slist_df ss a : slist (sty_df <$> ss) a = (sty_df ∘ slist ss) a.
Proof.
  unfold slist, compose. rewrite list_lookup_fmap, length_fmap.
  by destruct (ss !! a).
Qed.

Lemma sinsts_df N ss : sinsts N ss → sinsts None (sty_df <$> ss).
Proof.
  intros [[Hc Hsc] _]. split; [split|].
  - apply Forall_fmap. apply Forall_forall. intros s Hs. change (contractive (sty_df s)). unfold contractive. rewrite scontr_df.
    by eapply Forall_forall in Hc.
  - apply Forall_fmap. apply Forall_forall. intros s Hs. apply (proj2 (proj2 df_pscoped_mut s)).
    by eapply Forall_forall in Hsc.
  - intros _. apply Forall_fmap. apply Forall_forall. intros s _. apply sty_df_idem.
Qed.

Lemma sinsts_inf N ss : sinsts None ss → sinsts N ss.
Proof. intros [Hc Hd]. split; [done|]. intros _. by apply Hd. Qed.

Lemma ty_df_sinst_map ss T :
  ty_df (sinst_ty (slist ss) T) = sinst_ty (slist (sty_df <$> ss)) (ty_df T).
Proof. rewrite ty_df_sinst. apply sinst_ty_ext. intros a. by rewrite slist_df. Qed.

(** ** Every DF derivation lifts to N = ∞ *)

Lemma typed_to_inf W Θ Γ Δ F e T c :
  typed W None Θ Γ Δ F e T c → typed W None Θ Γ Δ F e T None.
Proof. intros H. eapply e_sub; [exact H|apply tsub_refl|apply fle_inf|by intros]. Qed.

Local Ltac heads_df := rewrite ?tenv_heads_df, ?lenv_heads_df, ?lenv_bot_df, ?heads_df, ?hbot_df.

(** ** The rules of DF typing

    Each rule [d_*] of Θ ; Γ ; Δ ⊢^F_W e : T is a lemma: the premises lift
    to N = ∞ with the annotations of N = ∞, and the rule [e_*] of the
    merged judgment concludes at cost ∞. *)

Local Ltac dfr := unfold dftyped in *; eapply typed_to_inf;
  rewrite ?tenv_df_empty, ?tenv_df_singleton; cbn [ty_df].

Lemma d_unit W Γ Δ F : lenv_unl Δ → dftyped W ∅ Γ Δ F EUnit TUnit.
Proof. intros HΔ. dfr. by eapply e_unit, lenv_unl_df. Qed.

Lemma d_var W Γ Δ F x T : lenv_only Δ x T → dftyped W ∅ Γ Δ F (Var x) T.
Proof. intros HΔ. dfr. eapply e_var. by eapply lenv_only_df. Qed.

Lemma d_chan W Γ Δ F o S x a a' m m' : lenv_unl Δ → dftyped W {[o := TE S x a m]} Γ Δ F (Chan o) (TSess S x a' m').
Proof. intros HΔ. dfr. by eapply e_chan, lenv_unl_df. Qed.

Lemma d_abs W Θ Γ Δ F e T U ub lb c a :
  lbx_below_h W Γ lb (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) → tcontr T →
  dftyped W Θ Γ (Some T :: Δ) (abs_fut ub) e U →
  dftyped W Θ Γ Δ F (Lam e) (TLolli ub lb c T U a).
Proof.
  intros Hlb HT Hb. dfr.
  eapply (e_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ None); [|apply thage_df|apply lage_df| |].
  - by heads_df.
  - by rewrite tcontr_df.
  - exact Hb.
Qed.

Lemma d_app W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 ub lb c T U a :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_u W Γ ub F →
  dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
    (TLolli ub lb c T U a) →
  dftyped W Θ2 Γ Δ2 (sf_unionb F (lb_heads lb) (lb_bot lb)) e2 T →
  dftyped W Θ Γ Δ F (App e1 e2) U.
Proof.
  intros Hs Hl Hub H1 H2. dfr.
  eapply e_app; [by apply tsplit_df|by apply lenv_split_df|done| | | |exact H2
                |apply fle_inf].
  - heads_df. exact H1.
  - apply thage_df.
  - apply lage_df.
Qed.

Lemma d_pair W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 T2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 →
  dftyped W Θ2 Γ Δ2 (sf_unionb F (heads T1) (hbot T1)) e2 T2 →
  dftyped W Θ Γ Δ F (Pair e1 e2) (TProd T1 T2).
Proof.
  intros Hs Hl H1 H2. dfr.
  eapply e_pair; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df| |apply tage_df].
  - heads_df. exact H1.
  - heads_df. exact H2.
Qed.

Lemma d_letu W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
  dftyped W Θ2 Γ Δ2 F e2 T →
  dftyped W Θ Γ Δ F (LetU e1 e2) T.
Proof.
  intros Hs Hl H1 H2. dfr.
  eapply e_letu; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df|exact H2].
  heads_df. exact H1.
Qed.

Lemma d_letp W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 T2 T :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
  dftyped W Θ2 Γ (Some T2 :: Some T1 :: Δ2) F e2 T →
  dftyped W Θ Γ Δ F (LetP e1 e2) T.
Proof.
  intros Hs Hl H1 H2. dfr.
  eapply e_letp; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df|exact H2].
  heads_df. exact H1.
Qed.

Lemma d_inj W (i : bool) Θ Γ Δ F e T U :
  tcontr (TSum T U) →
  dftyped W Θ Γ Δ F e (if i then U else T) → dftyped W Θ Γ Δ F (Inj i e) (TSum T U).
Proof.
  intros HT H. dfr. assert (tcontr (TSum (ty_df T) (ty_df U))) by (change (tcontr (ty_df (TSum T U))); by rewrite tcontr_df).
  destruct i; [apply (e_inj _ _ true)|apply (e_inj _ _ false)]; done.
Qed.

Lemma d_case W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
  dftyped W Θ2 Γ (Some T1 :: Δ2) F e1 T →
  dftyped W Θ2 Γ (Some T2 :: Δ2) F e2 T →
  dftyped W Θ Γ Δ F (Case e e1 e2) T.
Proof.
  intros Hs Hl H0 H1 H2. dfr.
  eapply e_case; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df|exact H1|exact H2].
  heads_df. exact H0.
Qed.

Lemma d_box W Γ Δ F e m k C ub c U :
  lenv_unl Δ → tcontr U →
  (∀ ss, length ss = k → sinsts None ss →
     dftyped W ∅ (hc_open m C Γ)
       (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ))
       (∅, Some (FRest (rest_of ub))) e (sinst_ty (slist ss) U)) →
  dftyped W ∅ Γ Δ F (EBox e) (TBox m k C ub c U).
Proof.
  intros HΔ HU H2. dfr.
  eapply e_box; [by apply lenv_unl_df|by rewrite tcontr_df|].
  intros ss Hk Hss. specialize (H2 ss Hk Hss).
  rewrite (ty_df_sinst_slist ss) in H2 by apply (proj2 Hss eq_refl).
  rewrite lenv_df_pinst, tenv_df_empty in H2. exact H2.
Qed.

Lemma d_force W Θ Γ Δ F e m k C ub c U xs ss :
  length xs = m → hold_at W Γ C xs → length ss = k → sinsts None ss →
  ub_below_s W Γ (pt_inst (plist xs) <$> ub) F →
  dftyped W Θ Γ Δ F e (TBox m k C ub c U) →
  dftyped W Θ Γ Δ F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)).
Proof.
  intros Hxs HC Hk H2 Hub H. dfr.
  rewrite (ty_df_sinst_slist ss), <-ty_inst_df by (by apply (proj2 H2 eq_refl)).
  eapply e_force; [done|done|done|exact H2|done|exact H].
Qed.

Lemma d_send W Θ Γ Δ F e S0 x m T S aS mS mS' :
  unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  ub_below_s W Γ (Some x) F →
  dftyped W Θ Γ Δ F e (TProd (payload_at m T x) (TSess S0 x aS mS)) →
  dftyped W Θ Γ Δ F (ESend e) (TSess S x⁺ aS mS').
Proof.
  intros Hu Hsc Hb Hh Hub H. dfr.
  eapply e_send with (T := ty_df T) (m := m) (S := sty_df S);
    [by rewrite unfoldS_df, Hu|by apply pscoped_df|by rewrite hbot_df|by rewrite payload_at_df, heads_df|done| | |].
  - exact H.
  - apply tage_df.
  - rewrite payload_at_df. apply tsub_refl.
Qed.

Lemma d_recv W Θ Γ Δ F e S0 x m T S a a' mS mS' :
  unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
  ub_below_s W Γ (Some x) F →
  dftyped W Θ Γ Δ F e (TSess S0 x a mS) →
  dftyped W Θ Γ Δ F (ERecv e) (TProd (payload_at m T x) (TSess S x⁺ a' mS')).
Proof.
  intros Hu Hsc Hub H. dfr.
  rewrite <-payload_at_df.
  eapply e_recv; [by rewrite unfoldS_df, Hu|by apply pscoped_df|done|exact H].
Qed.

Lemma d_close W Θ Γ Δ F e S0 x a mS :
  unfoldS S0 = SEnd → ub_below_s W Γ (Some x) F →
  dftyped W Θ Γ Δ F e (TSess S0 x a mS) →
  dftyped W Θ Γ Δ F (EClose e) TUnit.
Proof. intros Hu Hub H. dfr. eapply e_close; [by rewrite unfoldS_df, Hu|done|exact H]. Qed.

Lemma d_select W (i : bool) Θ Γ Δ F e S0 x S1 S2 a a' mS mS' :
  unfoldS S0 = SPlus S1 S2 → ub_below_s W Γ (Some x) F →
  dftyped W Θ Γ Δ F e (TSess S0 x a mS) →
  dftyped W Θ Γ Δ F (ESel i e) (TSess (if i then S2 else S1) (sel_pt x i) a' mS').
Proof.
  intros Hu Hub H. dfr.
  assert (sty_df (if i then S2 else S1) = if i then sty_df S2 else sty_df S1) as -> by (by destruct i).
  eapply e_select; [by rewrite unfoldS_df, Hu|done|exact H].
Qed.

Lemma d_branch W Θ Γ Δ F e S0 x S1 S2 a a1 a2 mS m1 m2 :
  unfoldS S0 = SWith S1 S2 →
  ub_below_s W Γ (Some x) F →
  dftyped W Θ Γ Δ F e (TSess S0 x a mS) →
  dftyped W Θ Γ Δ F (EBra e) (TSum (TSess S1 (bra_pt x false) a1 m1) (TSess S2 (bra_pt x true) a2 m2)).
Proof. intros Hu Hub H. dfr. eapply e_branch; [by rewrite unfoldS_df, Hu|done|exact H]. Qed.

Lemma d_link W Θ Γ Δ F e S x a1 a2 m1 m2 :
  dftyped W Θ Γ Δ F e (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) →
  dftyped W Θ Γ Δ F (ELink e) TUnit.
Proof.
  intros H. dfr.
  assert (typed W None (tenv_df Θ) Γ (lenv_df Δ) F e
            (TProd (TSess (sty_df S) x None None) (TSess (dual (sty_df S)) x‾ None None)) None) as I
    by (rewrite <-sty_df_dual; exact H).
  eapply e_link; [exact I|done|done].
Qed.

Lemma d_spawn W Θ Γ Δ F e ub lb c' a :
  dftyped W Θ Γ Δ F e (TLolli ub lb c' TUnit TUnit a) →
  dftyped W Θ Γ Δ F (ESpawn e) TUnit.
Proof. intros H. dfr. eapply e_spawn. exact H. Qed.

(** D-SpawnLam is admissible (entry 12): E-Abs at upper point ⊤ and lower
    point ⊥ followed by E-Spawn. *)
Lemma d_spawn_lam W Θ Γ Δ F e :
  dftyped W Θ Γ (Some TUnit :: Δ) (∅, None) e TUnit →
  dftyped W Θ Γ Δ F (ESpawn (Lam e)) TUnit.
Proof.
  intros H.
  apply (d_spawn _ _ _ _ _ _ UTop LBot None None).
  apply (d_abs _ _ _ _ _ _ _ _ _ _ _ _); [done|done|exact H].
Qed.

(** E-New of the DF judgment asks (acyc-new). *)
Lemma d_new_acyc W Γ Δ F C S a1 a2 m1 m2 :
  lenv_unl Δ → acyc_new W Γ C → scontr S →
  dftyped W ∅ Γ Δ F ENew
    (TEx LBot 1 C (TProd (TSess S (pvar 0) a1 m1) (TSess (dual S) (pvar 0)‾ a2 m2))).
Proof. intros HΔ HC HS. dfr. rewrite sty_df_dual. eapply e_new; [by apply lenv_unl_df|done|done|by rewrite scontr_df]. Qed.

(** (gen-new) suffices, through Lemma C ([gen_new_acyc]). *)
Lemma d_new W Γ Δ F C S a1 a2 m1 m2 :
  lenv_unl Δ → gen_new W Γ C → scontr S →
  dftyped W ∅ Γ Δ F ENew
    (TEx LBot 1 C (TProd (TSess S (pvar 0) a1 m1) (TSess (dual S) (pvar 0)‾ a2 m2))).
Proof. intros HΔ HC HS. apply d_new_acyc; [done|by apply gen_new_acyc|done]. Qed.

Lemma d_new_fld W Γ Δ F x κ S a1 a2 m1 m2 :
  lenv_unl Δ → scontr S →
  dftyped W ∅ Γ Δ F ENew (TProd (TSess S (x·κ) a1 m1) (TSess (dual S) (x·κ)‾ a2 m2)).
Proof. intros HΔ HS. dfr. rewrite sty_df_dual. eapply e_new_fld; [by apply lenv_unl_df|done|by rewrite scontr_df]. Qed.

Lemma d_conv W Θ Γ Δ F e T T' :
  tsub W Γ (ty_df T) (ty_df T') → (tcontr T → tcontr T') →
  dftyped W Θ Γ Δ F e T → dftyped W Θ Γ Δ F e T'.
Proof.
  intros Hs HT H. dfr. eapply e_sub; [exact H| |apply fle_refl|by rewrite !tcontr_df].
  apply tsub_df in Hs. by rewrite !ty_df_idem in Hs.
Qed.

Lemma d_pack W Θ Γ Δ F e lb m C T xs :
  length xs = m → hold_at W Γ C xs →
  lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  ex_wf W Γ lb m C T →
  dftyped W Θ Γ Δ F e (ty_inst xs T) →
  dftyped W Θ Γ Δ F e (TEx lb m C T).
Proof.
  intros Hxs HC Hlb Hwf H. dfr. eapply e_pack; [done|done| | |].
  - rewrite ty_inst_df. by heads_df.
  - unfold ex_wf. by heads_df.
  - rewrite ty_inst_df. exact H.
Qed.

Lemma d_open W Θ Γ Δ F e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T → cons_open W Γ m C →
  dftyped W (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
    (<[i := Some T]> (lenv_pinst (pshift m) Δ))
    (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
  dftyped W Θ Γ Δ F e U.
Proof.
  intros Hi Hu Hc H. dfr.
  eapply e_open; [by rewrite lenv_df_lookup, Hi|by rewrite unlimited_df|exact Hc|].
  rewrite <-tenv_df_pinst, <-lenv_df_pinst.
  rewrite lenv_df_insert in H. rewrite <-ty_df_pinst. exact H.
Qed.

(** By definition. *)
Theorem dftyped_typed W Θ Γ Δ F e T :
  dftyped W Θ Γ Δ F e T →
  typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) None.
Proof. done. Qed.


(** ** Every derivation erases to a DF derivation *)

Lemma tage_df_eq c T T' : tage c T T' → ty_df T' = ty_df T.
Proof. induction 1; simpl in *; congruence. Qed.

Lemma lage_df_eq c Δ Δ' : lage c Δ Δ' → lenv_df Δ' = lenv_df Δ.
Proof.
  induction 1 as [|? ? _ IH|T T' ? ? Ht _ IH]; simpl; [done|by f_equal|].
  apply tage_df_eq in Ht. rewrite Ht. by f_equal.
Qed.

Lemma thage_df_eq c Θ Θ' : thage c Θ Θ' → tenv_df Θ' = tenv_df Θ.
Proof.
  intros H. apply map_eq. intros o. specialize (H o). unfold tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [[S x a m]|], (Θ' !! o) as [[S' x' a' m']|]; try done.
  simpl in *. destruct_and!. subst. done.
Qed.

Lemma ty_df_if (i : bool) S1 S2 : sty_df (if i then S2 else S1) = if i then sty_df S2 else sty_df S1.
Proof. by destruct i. Qed.

Local Ltac df_ctx :=
  rewrite ?lenv_df_cons in *;
  repeat match goal with
  | Hl : lage _ ?Δ ?Δ', IH : context [lenv_df ?Δ'] |- _ => rewrite (lage_df_eq _ _ _ Hl) in IH
  | Ht : thage _ ?Θ ?Θ', IH : context [tenv_df ?Θ'] |- _ => rewrite (thage_df_eq _ _ _ Ht) in IH
  end.

Theorem typed_dftyped W N Θ Γ Δ F e T c :
  typed W N Θ Γ Δ F e T c → dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T).
Proof.
  induction 1; rewrite ?tenv_df_empty, ?tenv_df_singleton; cbn [ty_df].
  - by apply d_unit, lenv_unl_df.
  - eapply d_var. by eapply lenv_only_df.
  - eapply d_chan. by apply lenv_unl_df.
  - df_ctx.
    eapply d_abs; [|by rewrite tcontr_df|exact IHtyped]. by heads_df.
  - df_ctx.
    eapply d_app; [by apply tsplit_df|by apply lenv_split_df|done| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - df_ctx.
    match goal with Ha : tage _ _ _ |- _ => apply tage_df_eq in Ha; rename Ha into Hg end.
    rewrite Hg.
    eapply d_pair; [by apply tsplit_df|by apply lenv_split_df| |].
    + heads_df. exact IHtyped1.
    + heads_df. exact IHtyped2.
  - df_ctx.
    eapply d_letu; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - df_ctx.
    eapply d_letp; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - destruct i; [apply (d_inj _ true)|apply (d_inj _ false)];
      first [exact IHtyped|change (tcontr (ty_df (TSum T U))); by rewrite tcontr_df].
  - df_ctx.
    eapply d_case; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2|exact IHtyped3].
    heads_df. exact IHtyped1.
  - eapply d_box; [by apply lenv_unl_df|by rewrite tcontr_df|].
    intros ss Hk Hss. specialize (H2 ss Hk (sinsts_inf N ss Hss)).
    rewrite (ty_df_sinst_slist ss), lenv_df_pinst, tenv_df_empty in H2 by apply (proj2 Hss eq_refl).
    exact H2.
  - rewrite ty_df_sinst_map, <-ty_inst_df.
    eapply d_force; [done|done|by rewrite length_fmap|by eapply sinsts_df|done|exact IHtyped].
  - eapply d_send with (T := ty_df T) (S := sty_df S);
      [by rewrite unfoldS_df, H|by apply pscoped_df|by rewrite hbot_df|by rewrite payload_at_df, heads_df|done|].
    rewrite payload_at_df. eapply d_conv; [| |exact IHtyped].
    + cbn [ty_df]. rewrite !ty_df_idem.
      apply sub_prod; [|apply tsub_refl].
      rewrite <-(tage_df_eq _ _ _ H5). by apply tsub_df.
    + cbn [tcontr]. intros HC. apply Is_true_andb in HC as [_ HC]. apply Is_true_andb. split; [|done].
      rewrite tcontr_df. unfold payload_at. rewrite tcontr_ty_inst.
      rewrite scontr_df in HC. pose proof (hd_contr _ HC) as Hv. unfold hd in Hv. rewrite H in Hv. apply Hv.
  - rewrite <-payload_at_df.
    eapply d_recv with (T := ty_df T); [by rewrite unfoldS_df, H|by apply pscoped_df|done|exact IHtyped].
  - eapply d_close; [by rewrite unfoldS_df, H|done|exact IHtyped].
  - rewrite ty_df_if. eapply d_select; [by rewrite unfoldS_df, H|done|exact IHtyped].
  - eapply d_branch; [by rewrite unfoldS_df, H|done|exact IHtyped].
  - assert (dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e
              (TProd (TSess (sty_df S) x None None) (TSess (dual (sty_df S)) x‾ None None))) as I
      by (rewrite <-sty_df_dual; exact IHtyped).
    eapply d_link, I.
  - eapply d_spawn, IHtyped.
  - rewrite sty_df_dual. eapply d_new_acyc; [by apply lenv_unl_df|by eapply new_ok_acyc|by rewrite scontr_df].
  - rewrite sty_df_dual. eapply d_new_fld; [by apply lenv_unl_df|by rewrite scontr_df].
  - eapply d_conv; [| |exact IHtyped]; rewrite ?tcontr_df; [|done]. rewrite !ty_df_idem. by eapply tsub_df.
  - eapply d_pack; [done|done| | |].
    + rewrite ty_inst_df. by heads_df.
    + unfold ex_wf in *. by heads_df.
    + rewrite ty_inst_df. exact IHtyped.
  - rewrite lenv_df_insert, lenv_df_pinst, tenv_df_pinst, ty_df_pinst in IHtyped.
    eapply d_open; [by rewrite lenv_df_lookup, H|by rewrite unlimited_df|done|exact IHtyped].
  Unshelve. all: exact None.
Qed.

(** Conservativity in one statement: a DF derivation exists iff a
    derivation at N = ∞ with the annotations of N = ∞ exists. *)
Theorem conservative W Θ Γ Δ F e T :
  (∃ c, typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) c) ↔
  dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T).
Proof.
  split.
  - intros (c & H). apply typed_dftyped in H.
    by rewrite tenv_df_idem, lenv_df_idem, ty_df_idem in H.
  - intros H. apply dftyped_typed in H. rewrite tenv_df_idem, lenv_df_idem, ty_df_idem in H. eauto.
Qed.
