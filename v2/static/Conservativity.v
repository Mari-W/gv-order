(** * Conservativity: deadlock-freedom typing is the instance N = ∞ (stage S2)

    Decision Q11 replaces typing and the cost judgment by one judgment
    and claims that deadlock-freedom typing is its instance N = ∞
    (proposal §2.17, listed as unchecked in §5 Q11). Two theorems check
    the claim against the deadlock-freedom projection [dftyped].

    - [typed_dftyped]: a derivation at any refill N, in particular at
      N = ∞, erases to a DF derivation.
    - [dftyped_typed]: every DF derivation lifts to a derivation at
      N = ∞ with the annotations of N = ∞ ([ty_df], [cr_df]), cost ∞
      and transformer (∞, ∞).

    Two choices of the merged judgment make the lifting go through, and
    they are deviations from the text of §2.17 (docs/redesign/progress.md).
    The floor h of an arrow ranges over ℕ ∪ {∞} and the lifting takes
    h = ∞, because E-Abs restates a captured end at credit h and an end
    at credit 0 cannot be aged by ∞ inside the body. And at N = ∞ box
    bodies and forces meet only session instances with the annotations
    of N = ∞ ([sinsts]). *)

From GV Require Export static.Typing types.Erasure.

(** ** Contexts *)

Lemma tenv_df_empty : tenv_df ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_df_singleton o S x a : tenv_df {[o := TE S x a]} = {[o := TE (sty_df S) x None]}.
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
  intros _ [S x a] _. unfold tentry_df, tentry_pinst. simpl. by rewrite sty_df_pinst.
Qed.

Definition ent_df (σ : ty * fuel) : ty * fuel := (ty_df σ.1, cr_df σ.1).

Lemma lenv_df_cons o Δ : lenv_df (o :: Δ) = (ent_df <$> o) :: lenv_df Δ.
Proof. by destruct o as [[T a]|]. Qed.

Lemma lenv_df_lookup Δ i : lenv_df Δ !! i = fmap (M:=option) ent_df <$> Δ !! i.
Proof.
  unfold lenv_df. rewrite list_lookup_fmap. destruct (Δ !! i) as [[[T a]|]|]; done.
Qed.

Lemma lenv_empty_df Δ : lenv_empty Δ → lenv_empty (lenv_df Δ).
Proof.
  intros H o Ho. unfold lenv_df in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  by rewrite (H o' Ho').
Qed.

Lemma lenv_only_df Δ x T a : lenv_only Δ x (T, a) → lenv_only (lenv_df Δ) x (ty_df T, cr_df T).
Proof.
  intros [Hx Hy]. split; [by rewrite lenv_df_lookup, Hx|].
  intros y σ' Hσ. rewrite lenv_df_lookup in Hσ.
  destruct (Δ !! y) as [[σ0|]|] eqn:E; simplify_eq/=.
  destruct (Hy y σ0 E) as [-> ->]. done.
Qed.

Lemma lenv_split_df Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lenv_df Δ) (lenv_df Δ1) (lenv_df Δ2).
Proof.
  induction 1 as [|? ? ? _ IH|[T a] ? ? ? _ IH|[T a] ? ? ? _ IH|U a ? ? ? HU _ IH];
    simpl; constructor; try done. by apply unlimited_df.
Qed.

Lemma lenv_wk_df Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_df Δ') (lenv_df Δ).
Proof.
  induction 1 as [|o ? ? _ IH|U a ? ? HU _ IH]; rewrite ?lenv_df_cons; simpl; constructor; try done.
  by apply unlimited_df.
Qed.

Lemma lenv_unl_df Δ : lenv_unl Δ → lenv_unl (lenv_df Δ).
Proof.
  intros H o Ho. unfold lenv_df in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & a & -> & HU)]; [by left|right].
  eexists _, _. split; [done|]. by apply unlimited_df.
Qed.

Lemma lenv_heads_df Δ : lenv_heads (lenv_df Δ) = lenv_heads Δ.
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; rewrite ?heads_df; congruence. Qed.

Lemma lenv_bot_df Δ : lenv_bot (lenv_df Δ) = lenv_bot Δ.
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; rewrite ?hbot_df; congruence. Qed.

Lemma lenv_df_pinst σ Δ : lenv_df (lenv_pinst σ Δ) = lenv_pinst σ (lenv_df Δ).
Proof.
  induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal].
  rewrite ty_df_pinst, cr_df_pinst. by f_equal.
Qed.

Lemma lenv_df_insert Δ i o : lenv_df (<[i := o]> Δ) = <[i := fmap (M:=option) ent_df o]> (lenv_df Δ).
Proof.
  unfold lenv_df. rewrite list_fmap_insert. f_equal. by destruct o as [[T a]|].
Qed.

Lemma tenv_df_idem Θ : tenv_df (tenv_df Θ) = tenv_df Θ.
Proof.
  unfold tenv_df. rewrite <-map_fmap_compose. apply map_fmap_ext.
  intros _ [S x a] _. unfold tentry_df. simpl. by rewrite sty_df_idem.
Qed.

Lemma lenv_df_idem Δ : lenv_df (lenv_df Δ) = lenv_df Δ.
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal]. by rewrite ty_df_idem, cr_df_df, IH. Qed.

(** ** Aging and capture of contexts with the annotations of N = ∞ *)

Lemma tage_df c T : tage c (ty_df T, cr_df T) (ty_df T, cr_df T).
Proof.
  induction T; simpl.
  - apply age_free. constructor.
  - exact (age_credit c _ None (fle_inf c)).
  - apply age_prod; by rewrite fadd_0_l.
  - apply age_sum; by rewrite fadd_0_l.
  - apply age_free. constructor.
  - exact (age_credit c _ None (fle_inf c)).
  - apply age_ex. by rewrite fadd_0_l.
Qed.

Lemma lage_df c Δ : lage c (lenv_df Δ) (lenv_df Δ).
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; constructor; auto using tage_df. Qed.

Lemma thage_df c Θ : thage c (tenv_df Θ) (tenv_df Θ).
Proof.
  intros o. unfold tenv_df. rewrite lookup_fmap. destruct (Θ !! o); simpl; [|done].
  split_and!; try done. apply fle_inf.
Qed.

Lemma tcap_df T : tcap None None (ty_df T, cr_df T) (ty_df T, cr_df T).
Proof.
  induction T; simpl.
  - apply cap_free. constructor.
  - exact (cap_arr None None _ _ _ _ None _ _ _ _ None I I).
  - apply cap_prod; by rewrite fadd_0_l.
  - apply cap_sum; by rewrite fadd_0_l.
  - apply cap_free. constructor.
  - exact (cap_sess None None _ _ None I).
  - apply cap_ex. by rewrite fadd_0_l.
Qed.

Lemma lcap_df Δ : lcap None None (lenv_df Δ) (lenv_df Δ).
Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; constructor; auto using tcap_df. Qed.

Lemma thcap_df Θ : thcap None None (tenv_df Θ) (tenv_df Θ).
Proof.
  intros o. unfold tenv_df. rewrite lookup_fmap. destruct (Θ !! o); simpl; [|done].
  split_and!; done.
Qed.

(** ** Subtyping *)

Lemma tsub_refl T : ∀ a, tsub T a T a.
Proof.
  induction T; intros a0.
  - apply sub_unit, fle_refl.
  - apply sub_arr; auto using fle_refl, tle_refl.
  - apply sub_prod; auto.
  - apply sub_sum; auto.
  - apply sub_box; [apply fle_refl|apply tle_refl|]. destruct k; [apply teq_refl|done].
  - apply sub_sess; [apply sequiv_refl|apply fle_refl].
  - apply sub_ex; [done|done|apply teq_refl|apply fle_refl].
Qed.

Lemma tsub_df T a T' a' : tsub T a T' a' → tsub (ty_df T) (cr_df T) (ty_df T') (cr_df T').
Proof.
  induction 1; cbn [ty_df cr_df].
  - apply sub_unit, fle_refl.
  - apply sub_arr; auto using fle_refl, tle_refl.
  - apply sub_prod; by rewrite !fadd_0_l.
  - apply sub_sum; by rewrite !fadd_0_l.
  - assert (cr_df U = cr_df U') as ->.
    { destruct k; [by eapply eqT_cr_df|by subst]. }
    apply sub_box; [apply fle_refl|apply tle_refl|]. destruct k; [by apply teq_df|by subst].
  - apply sub_sess; [by apply sequiv_df|apply fle_refl].
  - apply sub_ex; [done|done|by apply teq_df|].
    rewrite (eqT_cr_df _ _ _ H1). apply fle_refl.
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
  intros [Hc _]. split.
  - apply Forall_fmap. apply Forall_forall. intros s Hs. apply hcontractive_df.
    by eapply Forall_forall in Hc.
  - intros _. apply Forall_fmap. apply Forall_forall. intros s _. apply sty_df_idem.
Qed.

Lemma sinsts_inf N ss : sinsts None ss → sinsts N ss.
Proof. intros [Hc Hd]. split; [done|]. intros _. by apply Hd. Qed.

Lemma ty_df_sinst_map ss T :
  ty_df (sinst_ty (slist ss) T) = sinst_ty (slist (sty_df <$> ss)) (ty_df T).
Proof. rewrite ty_df_sinst. apply sinst_ty_ext. intros a. by rewrite slist_df. Qed.

(** ** Every DF derivation lifts to N = ∞ *)

Lemma typed_to_inf W Θ Γ Δ F e T a c t :
  typed W None Θ Γ Δ F e T a c t → typed W None Θ Γ Δ F e T a None tinf.
Proof. intros H. eapply e_sub; [exact H|apply tsub_refl|apply fle_inf|apply tle_tinf]. Qed.

Lemma tok_inf t : tok tinf t.
Proof. right. by right. Qed.

Local Ltac heads_df := rewrite ?tenv_heads_df, ?lenv_heads_df, ?lenv_bot_df, ?heads_df, ?hbot_df.

Theorem dftyped_typed W Θ Γ Δ F e T :
  dftyped W Θ Γ Δ F e T →
  typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) (cr_df T) None tinf.
Proof.
  induction 1; eapply typed_to_inf; rewrite ?tenv_df_empty, ?tenv_df_singleton; cbn [ty_df cr_df].
  - by eapply e_unit, lenv_empty_df.
  - eapply e_var. by eapply lenv_only_df.
  - by eapply e_chan, lenv_empty_df.
  - eapply (e_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ None None φ); [done| |apply thcap_df|apply lcap_df|].
    + by heads_df.
    + exact IHdftyped.
  - eapply e_app; [by apply tsplit_df|by apply lenv_split_df|done| | | |exact IHdftyped2
                  |apply fle_inf|apply tok_inf|apply tok_inf].
    + heads_df. exact IHdftyped1.
    + apply thage_df.
    + apply lage_df.
  - eapply e_pair; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df| |apply tage_df
                   |apply tok_inf].
    + heads_df. exact IHdftyped1.
    + heads_df. exact IHdftyped2.
  - eapply e_letu; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df|exact IHdftyped2
                   |apply tok_inf].
    heads_df. exact IHdftyped1.
  - eapply e_letp; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df| |apply tok_inf].
    + heads_df. exact IHdftyped1.
    + rewrite !fadd_0_l. exact IHdftyped2.
  - by eapply e_inj1.
  - by eapply e_inj2.
  - eapply e_case; [by apply tsplit_df|by apply lenv_split_df| |apply thage_df|apply lage_df| | |apply tok_inf].
    + heads_df. exact IHdftyped1.
    + rewrite !fadd_0_l. exact IHdftyped2.
    + rewrite !fadd_0_l. exact IHdftyped3.
  - eapply e_box with (φ := φ); [by apply lenv_unl_df|done|].
    intros ss Hk Hss. specialize (H2 ss Hk Hss).
    rewrite (ty_df_sinst_slist ss) in H2 by apply (proj2 Hss eq_refl).
    rewrite lenv_df_pinst, tenv_df_empty, cr_df_sinst in H2. exact H2.
  - rewrite (ty_df_sinst_slist ss), <-ty_inst_df by (by apply (proj2 H2 eq_refl)). rewrite cr_df_sinst.
    unfold ty_inst. rewrite cr_df_pinst.
    eapply e_force; [done|done|done|exact H2|done|exact IHdftyped|apply tok_inf].
  - eapply e_send with (T := ty_df T) (m := m) (S := sty_df S);
      [by rewrite unfoldS_df, H|by apply pscoped_df|by rewrite hbot_df|by rewrite payload_at_df, heads_df|done| | |].
    + rewrite payload_at_df. exact IHdftyped.
    + rewrite payload_at_df, fadd_0_l. apply tage_df.
    + rewrite payload_at_df. unfold payload_at at 2, ty_inst. rewrite cr_df_pinst. apply tsub_refl.
  - rewrite <-payload_at_df. unfold payload_at at 2, ty_inst. rewrite cr_df_pinst.
    eapply e_recv; [by rewrite unfoldS_df, H|by apply pscoped_df|done|exact IHdftyped].
  - eapply e_close; [by rewrite unfoldS_df, H|done|exact IHdftyped].
  - assert (sty_df (if i then S2 else S1) = if i then sty_df S2 else sty_df S1) as -> by (by destruct i).
    eapply e_select; [by rewrite unfoldS_df, H| |done|exact IHdftyped]. done.
  - eapply e_branch; [by rewrite unfoldS_df, H|done|done|done|exact IHdftyped].
  - assert (typed W None (tenv_df Θ) Γ (lenv_df Δ) F e
              (TProd (TSess (sty_df S) x) None (TSess (dual (sty_df S)) x‾) None) (Some 0) None tinf) as I
      by (rewrite <-sty_df_dual; exact IHdftyped).
    eapply e_link; [exact I|apply tok_inf].
  - eapply e_spawn_lam; [apply thage_df|apply lage_df|exact IHdftyped].
  - eapply e_spawn; [exact IHdftyped|done|apply tok_inf].
  - rewrite sty_df_dual. eapply e_new; [by apply lenv_empty_df|done].
  - rewrite sty_df_dual. eapply e_new_at, IHdftyped.
  - eapply e_sub; [exact IHdftyped| |apply fle_refl|apply tle_refl].
    apply tsub_df in H. by rewrite !ty_df_idem, !cr_df_df in H.
  - eapply e_weak; [by apply lenv_wk_df|exact IHdftyped].
  - eapply e_contract; [by apply unlimited_df|exact IHdftyped].
  - eapply e_pack; [done|done| |].
    + rewrite ty_inst_df. by heads_df.
    + rewrite ty_inst_df, <-(cr_df_pinst (plist xs) T). exact IHdftyped.
  - eapply e_open; [by rewrite lenv_df_lookup, H|by rewrite unlimited_df|].
    rewrite <-tenv_df_pinst, <-lenv_df_pinst, fadd_0_l.
    rewrite lenv_df_insert in IHdftyped. rewrite <-ty_df_pinst, <-(cr_df_pinst (pshift m) U).
    exact IHdftyped.
Qed.

(** ** Every derivation erases to a DF derivation *)

Lemma tage_df_eq c σ σ' : tage c σ σ' → ty_df σ'.1 = ty_df σ.1.
Proof.
  induction 1; simpl in *; try done.
  all: try (rewrite IHtage1, IHtage2; f_equal; [by rewrite <-(cr_df_df T1'), IHtage1, cr_df_df
                                              |by rewrite <-(cr_df_df T2'), IHtage2, cr_df_df]).
  rewrite IHtage. f_equal. by rewrite <-(cr_df_df T'), IHtage, cr_df_df.
Qed.

Lemma tcap_df_eq h a σ σ' : tcap h a σ σ' → ty_df σ'.1 = ty_df σ.1.
Proof.
  induction 1; simpl in *; try done.
  all: try (rewrite IHtcap1, IHtcap2; f_equal; [by rewrite <-(cr_df_df T1'), IHtcap1, cr_df_df
                                              |by rewrite <-(cr_df_df T2'), IHtcap2, cr_df_df]).
  rewrite IHtcap. f_equal. by rewrite <-(cr_df_df T'), IHtcap, cr_df_df.
Qed.

Lemma lage_df_eq c Δ Δ' : lage c Δ Δ' → lenv_df Δ' = lenv_df Δ.
Proof.
  induction 1 as [|? ? _ IH|[T a] [T' a'] ? ? Ht _ IH]; simpl; [done|by f_equal|].
  apply tage_df_eq in Ht. simpl in Ht. rewrite Ht, <-(cr_df_df T'), Ht, cr_df_df. by f_equal.
Qed.

Lemma lcap_df_eq h a Δ Δ' : lcap h a Δ Δ' → lenv_df Δ' = lenv_df Δ.
Proof.
  induction 1 as [|? ? _ IH|[T a0] [T' a'] ? ? Ht _ IH]; simpl; [done|by f_equal|].
  apply tcap_df_eq in Ht. simpl in Ht. rewrite Ht, <-(cr_df_df T'), Ht, cr_df_df. by f_equal.
Qed.

Lemma thage_df_eq c Θ Θ' : thage c Θ Θ' → tenv_df Θ' = tenv_df Θ.
Proof.
  intros H. apply map_eq. intros o. specialize (H o). unfold tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [[S x a]|], (Θ' !! o) as [[S' x' a']|]; try done.
  simpl in *. destruct_and!. subst. done.
Qed.

Lemma thcap_df_eq h a Θ Θ' : thcap h a Θ Θ' → tenv_df Θ' = tenv_df Θ.
Proof.
  intros H. apply map_eq. intros o. specialize (H o). unfold tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [[S x a0]|], (Θ' !! o) as [[S' x' a']|]; try done.
  simpl in *. destruct_and!. subst. done.
Qed.

Lemma ty_df_if (i : bool) S1 S2 : sty_df (if i then S2 else S1) = if i then sty_df S2 else sty_df S1.
Proof. by destruct i. Qed.

Local Ltac df_ctx :=
  rewrite ?lenv_df_cons in *;
  repeat match goal with
  | Hl : lage _ ?Δ ?Δ', IH : context [lenv_df ?Δ'] |- _ => rewrite (lage_df_eq _ _ _ Hl) in IH
  | Ht : thage _ ?Θ ?Θ', IH : context [tenv_df ?Θ'] |- _ => rewrite (thage_df_eq _ _ _ Ht) in IH
  | Hl : lcap _ _ ?Δ ?Δ', IH : context [lenv_df ?Δ'] |- _ => rewrite (lcap_df_eq _ _ _ _ Hl) in IH
  | Ht : thcap _ _ ?Θ ?Θ', IH : context [tenv_df ?Θ'] |- _ => rewrite (thcap_df_eq _ _ _ _ Ht) in IH
  end.

Theorem typed_dftyped W N Θ Γ Δ F e T a c t :
  typed W N Θ Γ Δ F e T a c t → dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T).
Proof.
  induction 1; rewrite ?tenv_df_empty, ?tenv_df_singleton; cbn [ty_df cr_df].
  - by apply d_unit, lenv_empty_df.
  - eapply d_var. by eapply lenv_only_df.
  - eapply d_chan. by apply lenv_empty_df.
  - df_ctx.
    eapply d_abs; [done| |exact IHtyped]. by heads_df.
  - df_ctx.
    eapply d_app; [by apply tsplit_df|by apply lenv_split_df|done| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - df_ctx.
    match goal with Ha : tage _ _ _ |- _ => apply tage_df_eq in Ha; simpl in Ha; rename Ha into Hg end.
    rewrite Hg, <-(cr_df_df T1'), Hg, cr_df_df.
    eapply d_pair; [by apply tsplit_df|by apply lenv_split_df| |].
    + heads_df. exact IHtyped1.
    + heads_df. exact IHtyped2.
  - df_ctx.
    eapply d_letu; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - df_ctx.
    eapply d_letp; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2].
    heads_df. exact IHtyped1.
  - by eapply d_inj1.
  - by eapply d_inj2.
  - df_ctx.
    eapply d_case; [by apply tsplit_df|by apply lenv_split_df| |exact IHtyped2|exact IHtyped3].
    heads_df. exact IHtyped1.
  - eapply d_box with (φ := φ) (a := None); [by apply lenv_unl_df|done|].
    intros ss Hk Hss. specialize (H2 ss Hk (sinsts_inf N ss Hss)).
    rewrite (ty_df_sinst_slist ss), lenv_df_pinst, tenv_df_empty in H2 by apply (proj2 Hss eq_refl).
    exact H2.
  - rewrite ty_df_sinst_map, <-ty_inst_df.
    eapply d_force; [done|done|by rewrite length_fmap|by eapply sinsts_df|done|exact IHtyped].
  - eapply d_send with (T := ty_df T) (S := sty_df S);
      [by rewrite unfoldS_df, H|by apply pscoped_df|by rewrite hbot_df|by rewrite payload_at_df, heads_df|done|].
    rewrite payload_at_df. exact IHtyped.
  - rewrite <-payload_at_df.
    eapply d_recv with (T := ty_df T); [by rewrite unfoldS_df, H|by apply pscoped_df|done|exact IHtyped].
  - eapply d_close; [by rewrite unfoldS_df, H|done|exact IHtyped].
  - rewrite ty_df_if. eapply d_select; [by rewrite unfoldS_df, H|done|done|exact IHtyped].
  - eapply d_branch; [by rewrite unfoldS_df, H|done|done|done|exact IHtyped].
  - assert (dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e
              (TProd (TSess (sty_df S) x) None (TSess (dual (sty_df S)) x‾) None)) as I
      by (rewrite <-sty_df_dual; exact IHtyped).
    eapply d_link, I.
  - df_ctx.
    eapply d_spawn_lam, IHtyped.
  - eapply d_spawn, IHtyped.
  - rewrite sty_df_dual. eapply d_new; [by apply lenv_empty_df|done].
  - rewrite sty_df_dual. eapply d_new_at, IHtyped.
  - eapply (d_conv _ _ _ _ _ _ _ _ (cr_df T) (cr_df T')); [|exact IHtyped]. rewrite !ty_df_idem. by eapply tsub_df.
  - eapply d_weak; [by apply lenv_wk_df|exact IHtyped].
  - eapply d_contract; [by apply unlimited_df|exact IHtyped].
  - eapply d_pack; [done|done| |].
    + rewrite ty_inst_df. by heads_df.
    + rewrite ty_inst_df. exact IHtyped.
  - rewrite lenv_df_insert, lenv_df_pinst, tenv_df_pinst, ty_df_pinst in IHtyped.
    eapply d_open; [by rewrite lenv_df_lookup, H|by rewrite unlimited_df|exact IHtyped].
Qed.

(** Conservativity in one statement: a DF derivation exists iff a
    derivation at N = ∞ with the annotations of N = ∞ exists. *)
Theorem conservative W Θ Γ Δ F e T :
  (∃ a c t, typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) a c t) ↔
  dftyped W (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T).
Proof.
  split.
  - intros (a & c & t & H). apply typed_dftyped in H.
    by rewrite tenv_df_idem, lenv_df_idem, ty_df_idem in H.
  - intros H. apply dftyped_typed in H. rewrite tenv_df_idem, lenv_df_idem, ty_df_idem in H. eauto.
Qed.
