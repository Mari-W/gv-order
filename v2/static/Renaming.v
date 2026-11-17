(** * Renamings of ends, families and generated roots (stage S2)

    - [typed_emap]: an injective renaming g of ends maps a derivation
      over Θ and e to one over [kmap g Θ] and [emap g e]. Points do not
      change.
    - [typed_gmap]: a renaming r of generated roots that sends the roots
      of every family ℓ of W into the family f ℓ maps a derivation at W
      to one at [wfrename f W], with every point renamed by r and every
      [new_ℓ] of the term relabelled to [new_(f ℓ)]. The box rule
      quantifies over all session instances, so r needs a right inverse
      r' (r ∘ r' = id): the instance ss at [wfrename f W] comes from the
      instance r'(ss) at W.
    - [typed_grename]: the instance f = id, renaming roots inside their
      families, stays at W. *)

From GV Require Export static.Weakening types.Erasure.

(** ** Renaming of ends *)

Section emap.
  Context (g : cend → cend) `{!Inj eq eq g}.

  Local Abbreviation km Θ := (kmap (M2:=gmap cend) g Θ : tenv).

  Lemma kmap_lookup_cases (Θ Θ' : tenv) (o' : cend) :
    (km Θ !! o' = None ∧ km Θ' !! o' = None) ∨
    ∃ o, km Θ !! o' = Θ !! o ∧ km Θ' !! o' = Θ' !! o.
  Proof.
    destruct (km Θ !! o') eqn:E1.
    - apply lookup_kmap_Some in E1 as (o & -> & E1); last apply _. right. exists o.
      rewrite E1. split; [done|by rewrite lookup_kmap].
    - destruct (km Θ' !! o') eqn:E2; [|by left].
      apply lookup_kmap_Some in E2 as (o & -> & E2); last apply _. right. exists o.
      rewrite E2. split; [|done]. by rewrite lookup_kmap in E1.
  Qed.

  Lemma tsplit_kmap Θ Θ1 Θ2 :
    tsplit Θ Θ1 Θ2 → tsplit (km Θ) (km Θ1) (km Θ2).
  Proof. intros [Hd ->]. split; [by apply map_disjoint_kmap|by rewrite kmap_union]. Qed.

  Lemma tenv_heads_kmap Θ : tenv_heads (km Θ) = tenv_heads Θ.
  Proof.
    apply set_eq. intros y. rewrite !elem_of_tenv_heads. split.
    - intros (o' & e & He & ->). apply lookup_kmap_Some in He as (o & -> & He); last apply _. eauto.
    - intros (o & e & He & ->). exists (g o), e. by rewrite lookup_kmap.
  Qed.

  Lemma thage_kmap c Θ Θ' : thage c Θ Θ' → thage c (km Θ) (km Θ').
  Proof.
    intros H o'. destruct (kmap_lookup_cases Θ Θ' o') as [[-> ->]|(o & -> & ->)]; [done|apply H].
  Qed.

  Lemma thcap_kmap h a Θ Θ' : thcap h a Θ Θ' → thcap h a (km Θ) (km Θ').
  Proof.
    intros H o'. destruct (kmap_lookup_cases Θ Θ' o') as [[-> ->]|(o & -> & ->)]; [done|apply H].
  Qed.

  Lemma tenv_pinst_kmap σ Θ : tenv_pinst σ (km Θ) = km (tenv_pinst σ Θ).
  Proof. unfold tenv_pinst. by rewrite kmap_fmap. Qed.

  Theorem typed_emap W N Θ Γ Δ F e T a c t :
    typed W N Θ Γ Δ F e T a c t → typed W N (kmap g Θ) Γ Δ F (emap g e) T a c t.
  Proof.
    induction 1; simpl; rewrite ?kmap_empty, ?kmap_singleton.
    - by apply e_unit.
    - by eapply e_var.
    - by apply e_chan.
    - eapply e_abs; [done| |by apply thcap_kmap|done|done]. by rewrite tenv_heads_kmap.
    - eapply e_app; [by apply tsplit_kmap|done|done| |by apply thage_kmap|done|done|done|done|done].
      by rewrite tenv_heads_kmap.
    - eapply e_pair; [by apply tsplit_kmap|done| |by apply thage_kmap|done|done|done|done].
      by rewrite tenv_heads_kmap.
    - eapply e_letu; [by apply tsplit_kmap|done| |by apply thage_kmap|done|done|done].
      by rewrite tenv_heads_kmap.
    - eapply e_letp; [by apply tsplit_kmap|done| |by apply thage_kmap|done|done|done].
      by rewrite tenv_heads_kmap.
    - eapply e_let; [by apply tsplit_kmap|done| |by apply thage_kmap|done|done|done].
      by rewrite tenv_heads_kmap.
    - by eapply e_inj1.
    - by eapply e_inj2.
    - eapply e_case; [by apply tsplit_kmap|done| |by apply thage_kmap|done|done|done|done].
      by rewrite tenv_heads_kmap.
    - eapply e_box; [done|done|]. intros ss Hk Hss. specialize (H2 ss Hk Hss).
      by rewrite kmap_empty in H2.
    - eapply e_force; eauto.
    - eapply e_send; eauto.
    - eapply e_recv; eauto.
    - eapply e_close; eauto.
    - eapply e_select; eauto.
    - eapply e_branch; eauto.
    - eapply e_link; eauto.
    - eapply e_spawn_lam; [by apply thage_kmap|done|done].
    - eapply e_spawn; eauto.
    - by apply e_new.
    - eapply e_new_at; eauto.
    - eapply e_sub; eauto.
    - eapply e_weak; eauto.
    - rewrite emap_rename. by eapply e_contract.
    - eapply e_pack; eauto.
    - eapply e_open; [done|done|]. by rewrite tenv_pinst_kmap.
  Qed.
End emap.

(** ** Renaming of generated roots in types *)

Section gmap_types.
  Context (r : family * nat → family * nat).

  Fixpoint gmap_ty (T : ty) : ty :=
    match T with
    | TUnit => TUnit
    | TLolli ub lb c t h T1 a1 U a2 =>
        TLolli (pt_gmap r <$> ub) (pt_gmap r <$> lb) c t h (gmap_ty T1) a1 (gmap_ty U) a2
    | TProd T1 a1 U a2 => TProd (gmap_ty T1) a1 (gmap_ty U) a2
    | TSum T1 a1 U a2 => TSum (gmap_ty T1) a1 (gmap_ty U) a2
    | TBox n k C ub c t U a => TBox n k (bcs_gmap r C) (pt_gmap r <$> ub) c t (gmap_ty U) a
    | TSess s x => TSess (gmap_sty s) (pt_gmap r x)
    | TEx lb n C T1 a => TEx (lb_map (pt_gmap r) lb) n (bcs_gmap r C) (gmap_ty T1) a
    end
  with gmap_sty (s : sty) : sty :=
    match s with
    | SRcv m T b => SRcv m (gmap_ty T) b
    | SSnd m T b => SSnd m (gmap_ty T) b
    | SMu s' => SMu (gmap_sty s')
    | SSeq s1 s2 => SSeq (gmap_sty s1) (gmap_sty s2)
    | SPlus s1 s2 => SPlus (gmap_sty s1) (gmap_sty s2)
    | SWith s1 s2 => SWith (gmap_sty s1) (gmap_sty s2)
    | s => s
    end.

  (** *** Points *)

  Lemma pt_gmap_pvar a : pt_gmap r (pvar a) = pvar a.
  Proof. done. Qed.

  Lemma pt_gmap_pup n σ a : pt_gmap r (pup n σ a) = pup n (pt_gmap r ∘ σ) a.
  Proof.
    unfold pup. case_decide; [done|]. rewrite pt_gmap_inst. simpl.
    apply pt_inst_ext. intros b. done.
  Qed.

  Lemma pt_gmap_pshift m a : pt_gmap r (pshift m a) = pshift m a.
  Proof. done. Qed.

  Lemma pt_gmap_plist xs a : pt_gmap r (plist xs a) = plist (pt_gmap r <$> xs) a.
  Proof.
    unfold plist. rewrite list_lookup_fmap, length_fmap. by destruct (xs !! a).
  Qed.

  Lemma bcs_gmap_inst σ C : bcs_gmap r (bcs_inst σ C) = bcs_inst (pt_gmap r ∘ σ) (bcs_gmap r C).
  Proof.
    destruct C as [env P]. unfold bcs_gmap, bcs_inst. simpl. f_equal.
    rewrite <-!list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_gmap_inst.
  Qed.

  Lemma opt_gmap_inst σ (o : option point) :
    pt_gmap r <$> (pt_inst σ <$> o) = pt_inst (pt_gmap r ∘ σ) <$> (pt_gmap r <$> o).
  Proof. destruct o; simpl; [by rewrite pt_gmap_inst|done]. Qed.

  Lemma gmap_pinst_ty σ T : gmap_ty (pinst_ty σ T) = pinst_ty (pt_gmap r ∘ σ) (gmap_ty T).
  Proof.
    revert σ. induction T; intros σ; simpl; try done.
    - by rewrite IHT1, IHT2, !opt_gmap_inst.
    - by rewrite IHT1, IHT2.
    - by rewrite IHT1, IHT2.
    - rewrite IHT, bcs_gmap_inst, opt_gmap_inst. f_equal.
      + apply option_fmap_ext. intros x. apply pt_inst_ext. intros ?; apply pt_gmap_pup.
      + apply pinst_ty_ext. intros ?; apply pt_gmap_pup.
    - by rewrite pt_gmap_inst.
    - rewrite IHT, bcs_gmap_inst, lb_map_comp. f_equal.
      + rewrite lb_map_comp. apply lb_map_ext. intros x. apply pt_gmap_inst.
      + apply pinst_ty_ext. intros ?; apply pt_gmap_pup.
  Qed.

  Lemma gmap_pinst_sty σ s : gmap_sty (pinst_sty σ s) = pinst_sty (pt_gmap r ∘ σ) (gmap_sty s).
  Proof. done. Qed.

  Lemma pt_pscoped_gmap k x : pt_pscoped k x → pt_pscoped k (pt_gmap r x).
  Proof.
    intros H a Ha. apply H. rewrite pt_root_gmap in Ha.
    destruct (pt_root x); simpl in Ha; congruence.
  Qed.

  Lemma Forall_pscoped_gmap k l : Forall (pt_pscoped k) l → Forall (pt_pscoped k) (pt_gmap r <$> l).
  Proof. induction 1; simpl; constructor; auto using pt_pscoped_gmap. Qed.

  Lemma gmap_pscoped_mut :
    (∀ T k, pscoped k T → pscoped k (gmap_ty T)) ∧ (∀ s, sscoped s → sscoped (gmap_sty s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl in *; destruct_and?; split_and?; auto using pt_pscoped_gmap.
    all: try (intros ? Hx; destruct ub; simpl in Hx; simplify_eq; by auto using pt_pscoped_gmap).
    all: try (intros ? Hx; destruct lb; simpl in Hx; simplify_eq; by auto using pt_pscoped_gmap).
    all: by apply Forall_pscoped_gmap.
  Qed.

  Lemma pscoped_gmap k T : pscoped k T → pscoped k (gmap_ty T).
  Proof. apply gmap_pscoped_mut. Qed.

  Lemma gmap_pshift_ty m T : gmap_ty (pinst_ty (pshift m) T) = pinst_ty (pshift m) (gmap_ty T).
  Proof. rewrite gmap_pinst_ty. by apply pinst_ty_ext. Qed.

  Lemma gmap_ty_inst xs T : gmap_ty (ty_inst xs T) = ty_inst (pt_gmap r <$> xs) (gmap_ty T).
  Proof. unfold ty_inst. rewrite gmap_pinst_ty. apply pinst_ty_ext. intros a. apply pt_gmap_plist. Qed.

  Lemma gmap_payload_pts x m : pt_gmap r <$> payload_pts x m = payload_pts (pt_gmap r x) m.
  Proof. unfold payload_pts. rewrite <-list_fmap_compose. done. Qed.

  Lemma gmap_payload_at m T x : gmap_ty (payload_at m T x) = payload_at m (gmap_ty T) (pt_gmap r x).
  Proof. unfold payload_at. by rewrite gmap_ty_inst, gmap_payload_pts. Qed.

  (** *** Heads, kinds, annotations *)

  Lemma heads_gmap T : heads (gmap_ty T) = set_map (pt_gmap r) (heads T).
  Proof.
    induction T; simpl; rewrite ?set_map_union_L, ?IHT1, ?IHT2; try set_solver.
    - destruct lb; simpl; set_solver.
    - by rewrite set_map_singleton_L.
    - destruct lb; simpl; set_solver.
  Qed.

  Lemma hbot_gmap T : hbot (gmap_ty T) = hbot T.
  Proof. induction T; simpl; try done; try congruence. by destruct lb. Qed.

  Lemma unlimited_gmap T : unlimited (gmap_ty T) ↔ unlimited T.
  Proof. by destruct T. Qed.

  Lemma tfree_gmap T : tfree T → tfree (gmap_ty T).
  Proof. induction 1; simpl; constructor; auto. Qed.

  Lemma prim_gmap T : prim T → prim (gmap_ty T).
  Proof. induction 1; simpl; constructor; auto. Qed.

  Lemma gmap_df_mut :
    (∀ T, gmap_ty (ty_df T) = ty_df (gmap_ty T) ∧ cr_df (gmap_ty T) = cr_df T) ∧
    (∀ s, gmap_sty (sty_df s) = sty_df (gmap_sty s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; split_and?; destruct_and?; try congruence.
  Qed.

  Lemma sty_df_gmap s : sty_df (gmap_sty s) = gmap_sty (sty_df s).
  Proof. symmetry. apply gmap_df_mut. Qed.

  (** *** Session operations *)

  Lemma gmap_sren_mut :
    (∀ T ρ, gmap_ty (sren_ty ρ T) = sren_ty ρ (gmap_ty T)) ∧
    (∀ s ρ, gmap_sty (sren ρ s) = sren ρ (gmap_sty s)).
  Proof. apply ty_sty_mut_ind; intros; simpl; congruence. Qed.

  Lemma gmap_sflip_mut :
    (∀ T k, gmap_ty (sflip_ty k T) = sflip_ty k (gmap_ty T)) ∧
    (∀ s k, gmap_sty (sflip k s) = sflip k (gmap_sty s)).
  Proof. apply ty_sty_mut_ind; intros; simpl; try congruence; by case_decide. Qed.

  Lemma gmap_dual s : gmap_sty (dual s) = dual (gmap_sty s).
  Proof. induction s; simpl; try congruence. by rewrite (proj2 gmap_sflip_mut), IHs. Qed.

  Lemma gmap_sty_up σ a : gmap_sty (sty_up σ a) = sty_up (gmap_sty ∘ σ) a.
  Proof. destruct a; simpl; [done|]. unfold compose. apply gmap_sren_mut. Qed.

  Lemma gmap_iter_sty_up k σ a :
    gmap_sty (Nat.iter k sty_up σ a) = Nat.iter k sty_up (gmap_sty ∘ σ) a.
  Proof.
    revert σ a. induction k as [|k IH]; intros σ a; simpl; [done|].
    rewrite gmap_sty_up. apply sty_up_ext. intros b. apply IH.
  Qed.

  Lemma gmap_sinst_mut :
    (∀ T σ, gmap_ty (sinst_ty σ T) = sinst_ty (gmap_sty ∘ σ) (gmap_ty T)) ∧
    (∀ s σ, gmap_sty (sinst σ s) = sinst (gmap_sty ∘ σ) (gmap_sty s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; try congruence.
    all: try apply gmap_dual.
    all: try (rewrite H; f_equal; apply sinst_ty_ext; intros a; apply gmap_iter_sty_up).
    all: try (rewrite H; f_equal; apply sinst_ext; intros a; apply gmap_sty_up).
  Qed.

  Lemma gmap_sinst_ty σ T : gmap_ty (sinst_ty σ T) = sinst_ty (gmap_sty ∘ σ) (gmap_ty T).
  Proof. apply gmap_sinst_mut. Qed.

  Lemma gmap_slist ss a : gmap_sty (slist ss a) = slist (gmap_sty <$> ss) a.
  Proof. unfold slist. rewrite list_lookup_fmap, length_fmap. by destruct (ss !! a). Qed.

  Lemma gmap_sinst_slist ss T :
    gmap_ty (sinst_ty (slist ss) T) = sinst_ty (slist (gmap_sty <$> ss)) (gmap_ty T).
  Proof. rewrite gmap_sinst_ty. apply sinst_ty_ext. intros a. apply gmap_slist. Qed.

  Lemma gmap_unroll b : gmap_sty (unroll b) = unroll (gmap_sty b).
  Proof. unfold unroll. rewrite (proj2 gmap_sinst_mut). apply sinst_ext. by intros [|a]. Qed.

  Lemma gmap_hseq h s2 : gmap_sty (hseq h s2) = hseq (gmap_sty h) (gmap_sty s2).
  Proof. destruct h as [| | | | | | |o q| |]; try done. destruct q; done. Qed.

  Lemma sfuel_gmap s : sfuel (gmap_sty s) = sfuel s.
  Proof. induction s; simpl; auto. Qed.

  Lemma unrN_gmap k : ∀ s, unrN k (gmap_sty s) = gmap_sty <$> unrN k s.
  Proof.
    induction k as [|k IH]; intros s; [done|].
    destruct s; cbn [gmap_sty unrN]; try done.
    - by rewrite <-gmap_unroll, IH.
    - rewrite IH. destruct (unrN k s1) as [h|]; cbn [fmap option_fmap option_map]; [|done].
      destruct h; cbn [gmap_sty]; try apply IH.
      all: match goal with |- _ = _ <$> Some (hseq ?h ?s) => exact (f_equal Some (eq_sym (gmap_hseq h s))) end.
  Qed.

  Lemma unfoldS_gmap s : unfoldS (gmap_sty s) = gmap_sty (unfoldS s).
  Proof. unfold unfoldS. rewrite sfuel_gmap, unrN_gmap. by destruct (unrN (sfuel s) s). Qed.

  Definition hview_gmap (h : hview) : hview :=
    match h with
    | HRcv m T b s => HRcv m (gmap_ty T) b (gmap_sty s)
    | HSnd m T b s => HSnd m (gmap_ty T) b (gmap_sty s)
    | HVar a s => HVar a (gmap_sty s)
    | HVarD a s => HVarD a (gmap_sty s)
    | HPlus a b => HPlus (gmap_sty a) (gmap_sty b)
    | HWith a b => HWith (gmap_sty a) (gmap_sty b)
    | HStuck u => HStuck (gmap_sty u)
    | h => h
    end.

  Lemma view_gmap u : view (gmap_sty u) = hview_gmap (view u).
  Proof. destruct u as [| | | | | | |o q| |]; try done. by destruct o. Qed.

  Lemma hd_gmap s : hd (gmap_sty s) = hview_gmap (hd s).
  Proof. unfold hd. by rewrite unfoldS_gmap, view_gmap. Qed.

  Lemma ahc_gmap n : ∀ s, ahc n s → ahc n (gmap_sty s).
  Proof.
    induction n as [|n IH]; intros s H; [done|]. simpl in *. unfold hc_step in *.
    rewrite hd_gmap. destruct (hd s); simpl in *; naive_solver.
  Qed.

  Lemma hcontractive_gmap s : hcontractive s → hcontractive (gmap_sty s).
  Proof. intros H n. by apply ahc_gmap. Qed.

  Lemma sinsts_gmap N ss : sinsts N ss → sinsts N (gmap_sty <$> ss).
  Proof.
    intros [Hc Hd]. split.
    - apply Forall_fmap, Forall_forall. intros s Hs. apply hcontractive_gmap.
      by eapply Forall_forall in Hc.
    - intros HN. apply Forall_fmap, Forall_forall. intros s Hs. simpl.
      rewrite sty_df_gmap. f_equal. by eapply Forall_forall in Hd; [|done|].
  Qed.

  (** *** ≈ and subtyping *)

  Lemma eqT_gmap (ρ ρ' : sty → sty → Prop) T : ∀ U,
    (∀ s q, ρ s q → ρ' (gmap_sty s) (gmap_sty q)) → eqT ρ T U → eqT ρ' (gmap_ty T) (gmap_ty U).
  Proof.
    induction T; intros [] Hρ H; simpl in *; try done.
    all: destruct_and?; subst; split_and?; eauto.
    all: repeat case_match; subst; eauto.
  Qed.

  Lemma sequiv_gmap s q : sequiv s q → sequiv (gmap_sty s) (gmap_sty q).
  Proof.
    intros H. apply (sequiv_coind (λ s q, ∃ s0 q0, s = gmap_sty s0 ∧ q = gmap_sty q0 ∧ sequiv s0 q0));
      [|eauto].
    clear. intros s q (s0 & q0 & -> & -> & H). apply sequiv_step in H.
    unfold eq_step in *. rewrite !hd_gmap.
    hd_cases s0; hd_cases q0; simpl; try done.
    all: destruct_and?; subst; split_and?; eauto.
    all: try (eapply eqT_gmap; [|done]; intros a b Hab; eauto).
    all: congruence.
  Qed.

  Lemma teq_gmap T U : teq T U → teq (gmap_ty T) (gmap_ty U).
  Proof. apply eqT_gmap, sequiv_gmap. Qed.

  Lemma tsub_gmap T a T' a' : tsub T a T' a' → tsub (gmap_ty T) a (gmap_ty T') a'.
  Proof.
    induction 1; simpl; constructor; auto using sequiv_gmap, teq_gmap.
    - destruct k; [by apply teq_gmap|by subst].
    - simpl. by f_equal.
  Qed.

  Definition gent (σ : ty * fuel) : ty * fuel := (gmap_ty σ.1, σ.2).

  Lemma tage_gmap c σ σ' : tage c σ σ' → tage c (gent σ) (gent σ').
  Proof. induction 1; simpl in *; constructor; auto using tfree_gmap. Qed.

  Lemma tcap_gmap h b σ σ' : tcap h b σ σ' → tcap h b (gent σ) (gent σ').
  Proof. induction 1; simpl in *; constructor; auto using tfree_gmap. Qed.
End gmap_types.

Lemma opt_gmap_comp r r' (o : option point) : pt_gmap r <$> (pt_gmap r' <$> o) = pt_gmap (r ∘ r') <$> o.
Proof. destruct o; simpl; [by rewrite pt_gmap_comp|done]. Qed.

Lemma lb_gmap_comp r r' lb : lb_map (pt_gmap r) (lb_map (pt_gmap r') lb) = lb_map (pt_gmap (r ∘ r')) lb.
Proof. destruct lb; simpl; [done|done|by rewrite pt_gmap_comp]. Qed.

Lemma bcs_gmap_comp r r' C : bcs_gmap r (bcs_gmap r' C) = bcs_gmap (r ∘ r') C.
Proof.
  destruct C as [env P]. unfold bcs_gmap. simpl. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros. apply pt_gmap_comp.
Qed.

Lemma gmap_comp_mut r r' :
  (∀ T, gmap_ty r (gmap_ty r' T) = gmap_ty (r ∘ r') T) ∧
  (∀ s, gmap_sty r (gmap_sty r' s) = gmap_sty (r ∘ r') s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; rewrite ?H, ?H0, ?opt_gmap_comp, ?lb_gmap_comp, ?bcs_gmap_comp,
    ?pt_gmap_comp; done.
Qed.

Lemma gmap_sty_comp r r' s : gmap_sty r (gmap_sty r' s) = gmap_sty (r ∘ r') s.
Proof. apply gmap_comp_mut. Qed.

Lemma gmap_id_mut r :
  (∀ lg, r lg = lg) → (∀ T, gmap_ty r T = T) ∧ (∀ s, gmap_sty r s = s).
Proof.
  intros Hr. assert (∀ x, pt_gmap r x = x) as Hp by (intros; by apply pt_gmap_id).
  assert (∀ o : option point, pt_gmap r <$> o = o) as Ho by (intros []; simpl; by rewrite ?Hp).
  assert (∀ C, bcs_gmap r C = C) as Hc.
  { intros [env P]. unfold bcs_gmap. simpl. f_equal.
    rewrite <-(list_fmap_id env) at 2. apply list_fmap_ext. intros. apply Hp. }
  apply ty_sty_mut_ind; intros; simpl; rewrite ?H, ?H0, ?Ho, ?Hc, ?Hp; try done.
  by rewrite lb_map_id.
Qed.

Lemma gmap_sty_id r s : (∀ lg, r lg = lg) → gmap_sty r s = s.
Proof. intros Hr. by apply gmap_id_mut. Qed.

(** ** Renaming of generated roots in contexts *)

Section gmap_ctx.
  Context (r : family * nat → family * nat).

  Definition tentry_gmap (e : tentry) : tentry :=
    TE (gmap_sty r (te_sty e)) (pt_gmap r (te_pt e)) (te_cr e).
  Definition tenv_gmap (Θ : tenv) : tenv := tentry_gmap <$> Θ.
  Definition lenv_gmap (Δ : lenv) : lenv := fmap (M:=option) (gent r) <$> Δ.
  Definition sf_gmap (F : sfuture) : sfuture := (set_map (pt_gmap r) F.1, F.2).
  Definition hyps_gmap (Ψ : hyps) : hyps :=
    (λ g : bcs * list point, (bcs_gmap r g.1, pt_gmap r <$> g.2)) <$> Ψ.
  Definition fhyps_gmap (Φ : fhyps) : fhyps := fmap (M:=option) (pt_gmap r) <$> Φ.
  Definition hc_gmap (Γ : hctx) : hctx := HCtx (hyps_gmap (hc_hyps Γ)) (fhyps_gmap (hc_fv Γ)).

  Lemma pt_gmap_inst_pshift m x : pt_gmap r (pt_inst (pshift m) x) = pt_inst (pshift m) (pt_gmap r x).
  Proof. rewrite pt_gmap_inst. by apply pt_inst_ext. Qed.

  (** *** Θ *)

  Lemma tenv_gmap_empty : tenv_gmap ∅ = ∅.
  Proof. apply fmap_empty. Qed.

  Lemma tenv_gmap_singleton o S x a :
    tenv_gmap {[o := TE S x a]} = {[o := TE (gmap_sty r S) (pt_gmap r x) a]}.
  Proof. unfold tenv_gmap. by rewrite map_fmap_singleton. Qed.

  Lemma tsplit_gmap Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tsplit (tenv_gmap Θ) (tenv_gmap Θ1) (tenv_gmap Θ2).
  Proof.
    intros [Hd ->]. split; [by apply map_disjoint_fmap|]. unfold tenv_gmap. by rewrite map_fmap_union.
  Qed.

  Lemma tenv_heads_gmap Θ : tenv_heads (tenv_gmap Θ) = set_map (pt_gmap r) (tenv_heads Θ).
  Proof.
    apply set_eq. intros y. rewrite elem_of_map, elem_of_tenv_heads. unfold tenv_gmap.
    setoid_rewrite elem_of_tenv_heads. setoid_rewrite lookup_fmap. split.
    - intros (o & e & He & ->). destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=.
      exists (te_pt e0)‾. split; [done|]. eauto.
    - intros (y0 & -> & o & e & He & ->). exists o, (tentry_gmap e). by rewrite He.
  Qed.

  Lemma thage_gmap c Θ Θ' : thage c Θ Θ' → thage c (tenv_gmap Θ) (tenv_gmap Θ').
  Proof.
    intros H o. specialize (H o). unfold tenv_gmap. rewrite !lookup_fmap.
    destruct (Θ !! o), (Θ' !! o); simpl in *; try done. destruct_and!. by split_and!; f_equal.
  Qed.

  Lemma thcap_gmap h b Θ Θ' : thcap h b Θ Θ' → thcap h b (tenv_gmap Θ) (tenv_gmap Θ').
  Proof.
    intros H o. specialize (H o). unfold tenv_gmap. rewrite !lookup_fmap.
    destruct (Θ !! o), (Θ' !! o); simpl in *; try done. destruct_and!. by split_and!; f_equal.
  Qed.

  Lemma tenv_gmap_pshift m Θ : tenv_gmap (tenv_pinst (pshift m) Θ) = tenv_pinst (pshift m) (tenv_gmap Θ).
  Proof.
    unfold tenv_gmap, tenv_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
    intros _ [S x a] _. unfold tentry_gmap, tentry_pinst. simpl. f_equal.
    apply pt_gmap_inst_pshift.
  Qed.

  (** *** Δ *)

  Lemma lenv_gmap_lookup Δ x : lenv_gmap Δ !! x = fmap (M:=option) (gent r) <$> Δ !! x.
  Proof. unfold lenv_gmap. by rewrite list_lookup_fmap. Qed.

  Lemma lenv_gmap_cons o Δ : lenv_gmap (o :: Δ) = (gent r <$> o) :: lenv_gmap Δ.
  Proof. done. Qed.

  Lemma lenv_empty_gmap Δ : lenv_empty Δ → lenv_empty (lenv_gmap Δ).
  Proof.
    intros H o Ho. unfold lenv_gmap in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
    by rewrite (H o' Ho').
  Qed.

  Lemma lenv_only_gmap Δ x T a : lenv_only Δ x (T, a) → lenv_only (lenv_gmap Δ) x (gmap_ty r T, a).
  Proof.
    intros [Hx Hy]. split; [by rewrite lenv_gmap_lookup, Hx|].
    intros y σ' Hσ. rewrite lenv_gmap_lookup in Hσ.
    destruct (Δ !! y) as [[σ0|]|] eqn:E; simplify_eq/=.
    destruct (Hy y σ0 E) as [-> ->]. done.
  Qed.

  Lemma lenv_split_gmap Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lenv_gmap Δ) (lenv_gmap Δ1) (lenv_gmap Δ2).
  Proof.
    induction 1; simpl; constructor; try done. by apply unlimited_gmap.
  Qed.

  Lemma lenv_wk_gmap Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_gmap Δ') (lenv_gmap Δ).
  Proof. induction 1; simpl; constructor; try done. by apply unlimited_gmap. Qed.

  Lemma lenv_unl_gmap Δ : lenv_unl Δ → lenv_unl (lenv_gmap Δ).
  Proof.
    intros H o Ho. unfold lenv_gmap in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
    destruct (H o' Ho') as [->|(U & a & -> & HU)]; [by left|right].
    eexists _, _. split; [done|]. by apply unlimited_gmap.
  Qed.

  Lemma lage_gmap c Δ Δ' : lage c Δ Δ' → lage c (lenv_gmap Δ) (lenv_gmap Δ').
  Proof. induction 1; simpl; constructor; auto using tage_gmap. Qed.

  Lemma lcap_gmap h b Δ Δ' : lcap h b Δ Δ' → lcap h b (lenv_gmap Δ) (lenv_gmap Δ').
  Proof. induction 1; simpl; constructor; auto using tcap_gmap. Qed.

  Lemma lenv_heads_gmap Δ : lenv_heads (lenv_gmap Δ) = set_map (pt_gmap r) (lenv_heads Δ).
  Proof.
    induction Δ as [|[[T a]|] Δ IH]; simpl; [by rewrite set_map_empty|..|done].
    by rewrite set_map_union_L, heads_gmap, IH.
  Qed.

  Lemma lenv_bot_gmap Δ : lenv_bot (lenv_gmap Δ) = lenv_bot Δ.
  Proof. induction Δ as [|[[T a]|] Δ IH]; simpl; rewrite ?hbot_gmap; congruence. Qed.

  Lemma lenv_gmap_pshift m Δ : lenv_gmap (lenv_pinst (pshift m) Δ) = lenv_pinst (pshift m) (lenv_gmap Δ).
  Proof.
    induction Δ as [|[[T a]|] Δ IH]; simpl; [done| |by f_equal].
    unfold gent. simpl. rewrite gmap_pshift_ty. by f_equal.
  Qed.

  Lemma lenv_gmap_insert Δ i o : lenv_gmap (<[i := o]> Δ) = <[i := gent r <$> o]> (lenv_gmap Δ).
  Proof. unfold lenv_gmap. by rewrite list_fmap_insert. Qed.

  (** *** F *)

  Lemma sf_gmap_union F X : sf_gmap (sf_union F X) = sf_union (sf_gmap F) (set_map (pt_gmap r) X).
  Proof. unfold sf_gmap, sf_union. simpl. by rewrite set_map_union_L. Qed.

  Lemma sf_gmap_unionb F X b :
    sf_gmap (sf_unionb F X b) = sf_unionb (sf_gmap F) (set_map (pt_gmap r) X) b.
  Proof. destruct b; unfold sf_gmap, sf_unionb, sf_union; simpl; by rewrite set_map_union_L. Qed.

  Lemma sf_gmap_nil o : sf_gmap (∅, o) = (∅, o).
  Proof. unfold sf_gmap. simpl. by rewrite set_map_empty. Qed.

  Lemma sf_gmap_pshift m F : sf_gmap (sf_pinst (pshift m) F) = sf_pinst (pshift m) (sf_gmap F).
  Proof.
    unfold sf_gmap, sf_pinst. simpl. f_equal. apply set_eq. intros y.
    rewrite !elem_of_map. setoid_rewrite elem_of_map. split.
    - intros (y0 & -> & z & -> & Hz). eexists. split; [apply pt_gmap_inst_pshift|]. eauto.
    - intros (y0 & -> & z & -> & Hz). eexists. split; [symmetry; apply pt_gmap_inst_pshift|]. eauto.
  Qed.

  Lemma opt_heads_gmap o : opt_heads (pt_gmap r <$> o) = set_map (pt_gmap r) (opt_heads o).
  Proof. destruct o; simpl; [by rewrite set_map_singleton_L|by rewrite set_map_empty]. Qed.

  (** *** Γ *)

  Lemma ids_gmap m : pt_gmap r <$> ids m = ids m.
  Proof. unfold ids. rewrite <-list_fmap_compose. done. Qed.

  Lemma hyps_gmap_pshift m Ψ : hyps_gmap (hyps_inst (pshift m) Ψ) = hyps_inst (pshift m) (hyps_gmap Ψ).
  Proof.
    unfold hyps_gmap, hyps_inst. rewrite <-!list_fmap_compose. apply list_fmap_ext.
    intros _ [C xs] _. simpl. f_equal.
    - rewrite bcs_gmap_inst. by apply bcs_inst_ext.
    - rewrite <-!list_fmap_compose. apply list_fmap_ext. intros. apply pt_gmap_inst_pshift.
  Qed.

  Lemma fhyps_gmap_pshift m Φ : fhyps_gmap (fhyps_pinst (pshift m) Φ) = fhyps_pinst (pshift m) (fhyps_gmap Φ).
  Proof.
    unfold fhyps_gmap, fhyps_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
    intros _ [x|] _; simpl; [by rewrite pt_gmap_inst_pshift|done].
  Qed.

  Lemma hc_gmap_open m C Γ : hc_gmap (hc_open m C Γ) = hc_open m (bcs_gmap r C) (hc_gmap Γ).
  Proof.
    unfold hc_gmap, hc_open. simpl. f_equal; [|apply fhyps_gmap_pshift].
    unfold hyps_gmap at 1. rewrite fmap_app. f_equal; [apply hyps_gmap_pshift|].
    simpl. f_equal. f_equal; [|apply ids_gmap]. rewrite bcs_gmap_inst. by apply bcs_inst_ext.
  Qed.

  Lemma hc_gmap_fvar φ ub Γ : hc_gmap (hc_fvar φ ub Γ) = hc_fvar φ (pt_gmap r <$> ub) (hc_gmap Γ).
  Proof. unfold hc_gmap, hc_fvar. simpl. f_equal. unfold fhyps_gmap. by rewrite fmap_insert. Qed.

  Lemma dom_hc_gmap Γ : dom (hc_fv (hc_gmap Γ)) = dom (hc_fv Γ).
  Proof. apply dom_fmap_L. Qed.
End gmap_ctx.

(** ** Facts under a renaming of generated roots *)

Section gmap_facts.
  Context (W : world) (f : family → family) (r : family * nat → family * nat).
  Context (Hwf : world_wf W) (Hr : ∀ ℓ g, ℓ ∈ w_fams W → (r (ℓ, g)).1 = f ℓ).

  Local Abbreviation W' := (wfrename f W).

  (** [w_lt_gmap] asks the family condition only at the families of W. *)
  Lemma w_lt_gmap_fams x y : W ⊢ x ≺ y → W' ⊢ pt_gmap r x ≺ pt_gmap r y.
  Proof.
    apply tc_congruence. intros a b Hs.
    destruct Hs as [a b Hf|ℓ g a b Hℓ Hl|a|a].
    - destruct (wf_facts _ Hwf a b Hf) as [[c [Hc _]] [d [Hd _]]].
      rewrite !pt_gmap_nogen by (intros ??; congruence). by apply ws_fact.
    - destruct (wf_laws _ Hwf ℓ a b Hℓ Hl) as [Ha Hb].
      rewrite !law_inst_gmap by done. rewrite Hr by done. apply ws_law; [set_solver|].
      exists ℓ. split_and!; done.
    - apply ws_po.
    - apply ws_dpo.
  Qed.

  Lemma pt_gmap_scoped k z : pn_vb k (pt_name z) → pt_gmap r z = z.
  Proof.
    intros Hz. apply pt_gmap_nogen. intros ℓ g. apply pn_vb_root in Hz as (a & Ha & _).
    unfold pt_root. by rewrite Ha.
  Qed.

  Lemma pt_gmap_inst2 xs n env z :
    pn_vb (n + length env) (pt_name z) →
    pt_gmap r (pt_inst (plist xs) (pt_inst (pup n (plist env)) z)) =
    pt_inst (plist (pt_gmap r <$> xs)) (pt_inst (pup n (plist (pt_gmap r <$> env))) z).
  Proof.
    intros Hz. rewrite !pt_gmap_inst, (pt_gmap_scoped _ z Hz).
    rewrite (pt_inst_ext _ (plist (pt_gmap r <$> xs))) by (intros; apply pt_gmap_plist).
    f_equal. apply pt_inst_ext. intros a. unfold compose. rewrite pt_gmap_pup. apply pup_ext. intros. apply pt_gmap_plist.
  Qed.

  Lemma bcs_at_gmap C xs g :
    bcs_at C xs g → bcs_at (bcs_gmap r C) (pt_gmap r <$> xs) (fact_map (pt_gmap r) g).
  Proof.
    intros (g0 & (f0 & Hf & Hs & ->) & ->).
    exists (fact_map (pt_inst (pup (length xs) (plist (pt_gmap r <$> bc_env C)))) f0).
    split.
    - exists f0. rewrite length_fmap. destruct C as [env P]. simpl in *. rewrite length_fmap. done.
    - destruct f0 as [x y]. destruct Hs as [Hx Hy]. simpl.
      by rewrite !pt_gmap_inst2.
  Qed.

  Lemma bcs_at_gmap_inv C xs g :
    bcs_at (bcs_gmap r C) (pt_gmap r <$> xs) g → ∃ g0, bcs_at C xs g0 ∧ g = fact_map (pt_gmap r) g0.
  Proof.
    intros (g1 & (f0 & Hf & Hs & ->) & ->). destruct C as [env P]. simpl in *.
    rewrite !length_fmap in Hs. rewrite length_fmap.
    exists (fact_map (pt_inst (plist xs)) (fact_map (pt_inst (pup (length xs) (plist env))) f0)).
    split.
    - eexists. split; [|done]. exists f0. simpl. done.
    - destruct f0 as [x y]. destruct Hs as [Hx Hy]. simpl. by rewrite !pt_gmap_inst2.
  Qed.

  Definition node_gmap (a : node) : node :=
    match a with NP x => NP (pt_gmap r x) | NV φ => NV φ end.

  Lemma fl_gmap Γ a b : fl W Γ a b → fl W' (hc_gmap r Γ) (node_gmap a) (node_gmap b).
  Proof.
    induction 1 as [x y H|x y (C & xs & HC & H)|φ u H|a y b _ IH1 _ IH2]; simpl.
    - apply fl_w. by apply w_lt_gmap_fams.
    - apply fl_h. exists (bcs_gmap r C), (pt_gmap r <$> xs). split.
      + apply list_elem_of_fmap. exists (C, xs). done.
      + by apply (bcs_at_gmap C xs (FLt x y)).
    - apply fl_v. simpl. unfold fhyps_gmap. by rewrite lookup_fmap, H.
    - eapply fl_trans; [exact IH1|exact IH2].
  Qed.

  Lemma slt_gmap Γ x y : slt W Γ x y → slt W' (hc_gmap r Γ) (pt_gmap r x) (pt_gmap r y).
  Proof. apply (fl_gmap Γ (NP x) (NP y)). Qed.

  Lemma sle_gmap Γ x y : sle W Γ x y → sle W' (hc_gmap r Γ) (pt_gmap r x) (pt_gmap r y).
  Proof. intros [->|H]; [by left|right; by apply slt_gmap]. Qed.

  Lemma hold_at_gmap Γ C xs : hold_at W Γ C xs → hold_at W' (hc_gmap r Γ) (bcs_gmap r C) (pt_gmap r <$> xs).
  Proof.
    intros H x y Hf. apply bcs_at_gmap_inv in Hf as ([x0 y0] & Hf & [= -> ->]).
    by apply slt_gmap, H.
  Qed.

  Lemma ub_below_s_gmap Γ ub F :
    ub_below_s W Γ ub F → ub_below_s W' (hc_gmap r Γ) (pt_gmap r <$> ub) (sf_gmap r F).
  Proof.
    destruct ub as [x|]; simpl; [|done]. intros (H1 & H2 & H3). split_and!; [| |done].
    - intros y Hy. apply elem_of_map in Hy as (y0 & -> & Hy). by apply slt_gmap, H1.
    - intros φ Hφ. by apply (fl_gmap Γ (NP x) (NV φ)), H2.
  Qed.

  Lemma lb_below_hb_gmap Γ lb H b :
    lb_below_hb W Γ lb H b → lb_below_hb W' (hc_gmap r Γ) (pt_gmap r <$> lb) (set_map (pt_gmap r) H) b.
  Proof.
    unfold lb_below_hb, lb_below_h. destruct b; [done|]. destruct lb; simpl.
    - intros Hy y Hyy. apply elem_of_map in Hyy as (y0 & -> & Hy0). by apply sle_gmap, Hy.
    - intros ->. by rewrite set_map_empty.
  Qed.

  Lemma lbx_below_h_gmap Γ lb H b :
    lbx_below_h W Γ lb H b → lbx_below_h W' (hc_gmap r Γ) (lb_map (pt_gmap r) lb) (set_map (pt_gmap r) H) b.
  Proof.
    destruct lb; simpl; try done.
    - intros [-> ->]. by rewrite set_map_empty.
    - intros [Hy ->]. split; [|done]. intros y Hyy. apply elem_of_map in Hyy as (y0 & -> & Hy0).
      by apply sle_gmap, Hy.
  Qed.
End gmap_facts.

(** ** Relabelling families in terms *)

Fixpoint relabel (f : family → family) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Chan o => Chan o
  | Lam e => Lam (relabel f e)
  | App e1 e2 => App (relabel f e1) (relabel f e2)
  | Pair e1 e2 => Pair (relabel f e1) (relabel f e2)
  | LetU e1 e2 => LetU (relabel f e1) (relabel f e2)
  | LetP e1 e2 => LetP (relabel f e1) (relabel f e2)
  | Inj1 e => Inj1 (relabel f e)
  | Inj2 e => Inj2 (relabel f e)
  | Case e e1 e2 => Case (relabel f e) (relabel f e1) (relabel f e2)
  | EBox e => EBox (relabel f e)
  | ENew ℓ => ENew (f ℓ)
  | Op k e => Op k (relabel f e)
  end.

Lemma relabel_rename f ρ e : relabel f (rename ρ e) = rename ρ (relabel f e).
Proof. revert ρ. induction e; intros ρ; simpl; f_equal; auto. Qed.

Lemma relabel_id e : relabel id e = e.
Proof. induction e; simpl; f_equal; auto. Qed.

(** ** The renaming theorem *)

Section gmap_typed.
  Context (W : world) (f : family → family) (r r' : family * nat → family * nat).
  Context (Hwf : world_wf W) (Hr : ∀ ℓ g, ℓ ∈ w_fams W → (r (ℓ, g)).1 = f ℓ).
  Context (Hrr : ∀ lg, r (r' lg) = lg).

  Local Abbreviation W' := (wfrename f W).

  Local Ltac heads_g :=
    rewrite ?tenv_heads_gmap, ?lenv_heads_gmap, ?lenv_bot_gmap, ?heads_gmap, ?hbot_gmap,
      ?opt_heads_gmap, <-?set_map_union_L, <-?sf_gmap_unionb, <-?sf_gmap_union.

  Theorem typed_gmap N Θ Γ Δ F e T a c t :
    typed W N Θ Γ Δ F e T a c t →
    typed W' N (tenv_gmap r Θ) (hc_gmap r Γ) (lenv_gmap r Δ) (sf_gmap r F) (relabel f e)
      (gmap_ty r T) a c t.
  Proof.
    induction 1; cbn [relabel gmap_ty gmap_sty]; rewrite ?tenv_gmap_empty, ?tenv_gmap_singleton.
    - by apply e_unit, lenv_empty_gmap.
    - by eapply e_var, lenv_only_gmap.
    - by apply e_chan, lenv_empty_gmap.
    - (* E-Abs *)
      eapply e_abs; [by rewrite dom_hc_gmap| |by apply thcap_gmap|by apply lcap_gmap|].
      + rewrite tenv_heads_gmap, lenv_heads_gmap, lenv_bot_gmap, <-set_map_union_L.
        by apply lb_below_hb_gmap.
      + rewrite <-hc_gmap_fvar, <-(sf_gmap_nil r). exact IHtyped.
    - (* E-App *)
      eapply e_app; [by apply tsplit_gmap|by apply lenv_split_gmap|by apply ub_below_s_gmap| |
                     by apply thage_gmap|by apply lage_gmap| |done|done|done].
      + heads_g. exact IHtyped1.
      + heads_g. exact IHtyped2.
    - eapply e_pair; [by apply tsplit_gmap|by apply lenv_split_gmap| |by apply thage_gmap
                     |by apply lage_gmap| |by apply (tage_gmap r c2 (T1, a1) (T1', a1'))|done].
      + heads_g. exact IHtyped1.
      + heads_g. exact IHtyped2.
    - eapply e_letu; [by apply tsplit_gmap|by apply lenv_split_gmap| |by apply thage_gmap
                     |by apply lage_gmap|exact IHtyped2|done].
      heads_g. exact IHtyped1.
    - eapply e_letp; [by apply tsplit_gmap|by apply lenv_split_gmap| |by apply thage_gmap
                     |by apply lage_gmap| |done].
      + heads_g. exact IHtyped1.
      + exact IHtyped2.
    - eapply e_let; [by apply tsplit_gmap|by apply lenv_split_gmap| |by apply thage_gmap
                    |by apply lage_gmap|exact IHtyped2|done].
      heads_g. exact IHtyped1.
    - by eapply e_inj1.
    - by eapply e_inj2.
    - eapply e_case; [by apply tsplit_gmap|by apply lenv_split_gmap| |by apply thage_gmap
                     |by apply lage_gmap|exact IHtyped2|exact IHtyped3|done].
      heads_g. exact IHtyped1.
    - (* E-Box *)
      eapply e_box with (φ := φ); [by apply lenv_unl_gmap|by rewrite <-hc_gmap_open, dom_hc_gmap|].
      intros ss Hk Hss.
      assert (gmap_sty r <$> (gmap_sty r' <$> ss) = ss) as Hid.
      { rewrite <-list_fmap_compose. rewrite <-(list_fmap_id ss) at 2. apply list_fmap_ext.
        intros _ s _. simpl. rewrite gmap_sty_comp. by apply gmap_sty_id. }
      specialize (H2 (gmap_sty r' <$> ss) ltac:(by rewrite length_fmap) (sinsts_gmap r' N ss Hss)).
      rewrite tenv_gmap_empty, hc_gmap_fvar, hc_gmap_open, lenv_gmap_pshift, lenv_gmap_cons,
        sf_gmap_nil, gmap_sinst_slist, Hid in H2.
      exact H2.
    - (* E-Force *)
      rewrite gmap_sinst_slist, gmap_ty_inst.
      eapply e_force; [by rewrite length_fmap|by apply hold_at_gmap|by rewrite length_fmap
                      |by apply sinsts_gmap| |exact IHtyped|done].
      assert ((pt_gmap r <$> (pt_inst (plist xs) <$> ub)) =
              pt_inst (plist (pt_gmap r <$> xs)) <$> (pt_gmap r <$> ub)) as <-.
      { rewrite opt_gmap_inst. apply option_fmap_ext. intros x. apply pt_inst_ext.
        intros ?. apply pt_gmap_plist. }
      by apply ub_below_s_gmap.
    - (* E-Send *)
      eapply e_send with (x := pt_gmap r x) (m := m) (T := gmap_ty r T) (b := b) (S := gmap_sty r S);
        [by rewrite unfoldS_gmap, H|by apply pscoped_gmap|by rewrite hbot_gmap| |by apply (ub_below_s_gmap W f r Hwf Hr _ (Some x))| | |].
      + intros y. rewrite <-gmap_payload_at, heads_gmap. intros (y0 & -> & Hy)%elem_of_map.
        by apply slt_gmap, H2.
      + rewrite <-gmap_payload_at. exact IHtyped.
      + rewrite <-gmap_payload_at. by apply (tage_gmap r _ (payload_at m T x, fadd a0 ap) (Tp', ap')).
      + rewrite <-gmap_payload_at. by apply tsub_gmap.
    - (* E-Recv *)
      rewrite gmap_payload_at.
      eapply e_recv with (x := pt_gmap r x); [by rewrite unfoldS_gmap, H|by apply pscoped_gmap|by apply (ub_below_s_gmap W f r Hwf Hr _ (Some x))|exact IHtyped].
    - eapply e_close with (x := pt_gmap r x); [by rewrite unfoldS_gmap, H|by apply (ub_below_s_gmap W f r Hwf Hr _ (Some x))|exact IHtyped].
    - (* E-Select *)
      assert (gmap_sty r (if i then S2 else S1) = if i then gmap_sty r S2 else gmap_sty r S1) as ->
        by (by destruct i).
      eapply e_select with (x := pt_gmap r x); [by rewrite unfoldS_gmap, H|by apply (slt_gmap W f r Hwf Hr _ x (x·(bfield i)))
                       |by apply (ub_below_s_gmap W f r Hwf Hr _ (Some x))|exact IHtyped].
    - eapply e_branch with (x := pt_gmap r x); [by rewrite unfoldS_gmap, H
                       |by apply (slt_gmap W f r Hwf Hr _ x (sel_pt x false))
                       |by apply (slt_gmap W f r Hwf Hr _ x (sel_pt x true))
                       |by apply (ub_below_s_gmap W f r Hwf Hr _ (Some x))|exact IHtyped].
    - eapply e_link with (x := pt_gmap r x); [|done]. rewrite <-gmap_dual. exact IHtyped.
    - eapply e_spawn_lam; [by apply thage_gmap|by apply lage_gmap|].
      rewrite <-(sf_gmap_nil r). exact IHtyped.
    - eapply e_spawn; [exact IHtyped|done|done].
    - (* E-New *)
      rewrite gmap_dual.
      eapply e_sub; [eapply e_new; [by apply lenv_empty_gmap|]| |apply fle_refl|apply tle_refl].
      + simpl. by apply elem_of_map_2.
      + apply sub_ex; [done| |apply teq_refl|apply fle_refl].
        intros g Hg. simpl in *. exists ℓ. split_and!; done.
    - rewrite gmap_dual. eapply e_new_at with (x := pt_gmap r x), IHtyped.
    - eapply e_sub; [exact IHtyped|by apply tsub_gmap|done|done].
    - eapply e_weak; [by apply lenv_wk_gmap|exact IHtyped].
    - rewrite relabel_rename. eapply e_contract; [by apply unlimited_gmap|exact IHtyped].
    - (* E-Pack *)
      eapply e_pack with (xs := pt_gmap r <$> xs); [by rewrite length_fmap|by apply hold_at_gmap| |].
      + rewrite <-gmap_ty_inst, heads_gmap, hbot_gmap. by apply lbx_below_h_gmap.
      + rewrite <-gmap_ty_inst. exact IHtyped.
    - (* E-Open *)
      eapply e_open with (i := i) (lb := lb_map (pt_gmap r) lb) (m := m) (C := bcs_gmap r C)
        (T := gmap_ty r T) (aT := aT) (a := a); [by rewrite lenv_gmap_lookup, H|by rewrite unlimited_gmap|].
      rewrite <-tenv_gmap_pshift, <-hc_gmap_open, <-lenv_gmap_pshift, <-sf_gmap_pshift,
        <-gmap_pshift_ty.
      rewrite lenv_gmap_insert in IHtyped. exact IHtyped.
  Qed.
End gmap_typed.

(** Renaming generated roots inside their families stays at W. *)
Lemma wfrename_id_wext W : wfrename id W ⊑ W.
Proof.
  split; simpl; [done|done| |].
  - intros ℓ Hℓ. apply elem_of_map in Hℓ as (ℓ0 & -> & ?). done.
  - by intros ℓ g _ (ℓ0 & -> & _ & ?).
Qed.

Theorem typed_grename W N Θ Γ Δ F e T a c t r r' :
  world_wf W → (∀ ℓ g, ℓ ∈ w_fams W → (r (ℓ, g)).1 = ℓ) → (∀ lg, r (r' lg) = lg) →
  typed W N Θ Γ Δ F e T a c t →
  typed W N (tenv_gmap r Θ) (hc_gmap r Γ) (lenv_gmap r Δ) (sf_gmap r F) e (gmap_ty r T) a c t.
Proof.
  intros Hwf Hr Hrr H. rewrite <-(relabel_id e).
  eapply typed_wext; [apply wfrename_id_wext|]. by eapply (typed_gmap W id r r').
Qed.
