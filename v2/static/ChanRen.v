(** * Renaming the channels of a derivation (fx-open, 2026-11-22)

    An injective renaming h of channel names renames every end by
    [cmap h], which keeps the sign of the end and commutes with the
    partner ([cmap_edual]). A typed term stays typed when its ends are
    renamed by [emap (cmap h)] and the keys of Θ by [kmap (cmap h)]
    ([typed_cren]). A typed process stays typed when the keys of its
    interface, its restricted channels and its threads are renamed
    ([ptyped_cren]). Worlds, points and types do not mention channels,
    so they stay. Together with the renaming of constants
    ([ptyped_ren], examples/CopycatTwo.v) this moves a typed partner
    from one end and point to another. *)

From GV Require Export static.Typing.

Section cren.
  Context (h : chan → chan) (Hh : base.Inj eq eq h).
  Local Existing Instance Hh.
  Local Abbreviation g := (cmap h).

  Global Instance cmap_inj : base.Inj eq eq g.
  Proof. intros [c|c] [c'|c']; simpl; intros E; try discriminate; injection E as E; by rewrite (inj h _ _ E). Qed.

  Local Lemma lk_Some {A} (m : gmap cend A) j x : (kmap g m : gmap cend A) !! j = Some x ↔ ∃ i, j = g i ∧ m !! i = Some x.
  Proof. apply (lookup_kmap_Some g). Qed.
  Local Lemma lk_None {A} (m : gmap cend A) j : (kmap g m : gmap cend A) !! j = None ↔ ∀ i, j = g i → m !! i = None.
  Proof. apply (lookup_kmap_None g). Qed.
  Local Lemma lk {A} (m : gmap cend A) i : (kmap g m : gmap cend A) !! g i = m !! i.
  Proof. apply (lookup_kmap g). Qed.
  Local Lemma kunion {A} (m1 m2 : gmap cend A) : kmap g (m1 ∪ m2) =@{gmap cend A} kmap g m1 ∪ kmap g m2.
  Proof. apply (kmap_union g). Qed.
  Local Lemma kdisj {A} (m1 m2 : gmap cend A) : (kmap g m1 : gmap cend A) ##ₘ (kmap g m2 : gmap cend A) ↔ m1 ##ₘ m2.
  Proof. apply (map_disjoint_kmap g). Qed.
  Local Lemma kfmap {A B} (f : A → B) (m : gmap cend A) : kmap g (f <$> m) =@{gmap cend B} f <$> kmap g m.
  Proof. apply (kmap_fmap g). Qed.
  Local Lemma ksingle {A} i (x : A) : kmap g {[i := x]} =@{gmap cend A} {[g i := x]}.
  Proof. apply (kmap_singleton g). Qed.
  Local Lemma kdom {A} (m : gmap cend A) : dom (kmap g m : gmap cend A) = set_map g (dom m).
  Proof. apply (dom_kmap_L g). Qed.

  (** ** Contexts *)

  Lemma tsplit_cren Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tsplit (kmap g Θ) (kmap g Θ1) (kmap g Θ2).
  Proof. intros [Hd ->]. split; [by apply kdisj|apply kunion]. Qed.

  Lemma thage_cren c Θ Θ' : thage c Θ Θ' → thage c (kmap g Θ) (kmap g Θ').
  Proof.
    intros H o. destruct (kmap g Θ !! o) as [e|] eqn:E1.
    - apply lk_Some in E1 as (o' & -> & E1).
      rewrite lk. specialize (H o'). by rewrite E1 in H.
    - destruct (kmap g Θ' !! o) as [e'|] eqn:E2; [|done].
      apply lk_Some in E2 as (o' & -> & E2).
      rewrite lk in E1. specialize (H o'). by rewrite E1, E2 in H.
  Qed.

  Lemma tenv_heads_cren Θ : tenv_heads (kmap g Θ) = tenv_heads Θ.
  Proof.
    apply set_eq. intros y. rewrite !elem_of_tenv_heads. split.
    - intros (o & e & He & ->). apply lk_Some in He as (o' & -> & He). eauto.
    - intros (o & e & He & ->). exists (g o), e. split; [|done]. by rewrite lk.
  Qed.

  Lemma tenv_pinst_cren σ Θ : tenv_pinst σ (kmap g Θ) = kmap g (tenv_pinst σ Θ).
  Proof. unfold tenv_pinst. by rewrite kfmap. Qed.

  (** ** Terms *)

  Theorem typed_cren W N Θ Γ Δ F e T c :
    typed W N Θ Γ Δ F e T c → typed W N (kmap g Θ) Γ Δ F (emap g e) T c.
  Proof.
    induction 1; cbn [emap]; rewrite ?kmap_empty;
      try (rewrite <-(tenv_heads_cren Θ2) in IHtyped1).
    - by apply e_unit.
    - by apply e_var.
    - rewrite ksingle. by apply e_chan.
    - eapply e_abs; [|by apply thage_cren|eassumption|done|exact IHtyped]. by rewrite tenv_heads_cren.
    - eapply e_app; eauto using tsplit_cren, thage_cren.
    - eapply e_pair; eauto using tsplit_cren, thage_cren.
    - eapply e_letu; eauto using tsplit_cren, thage_cren.
    - eapply e_letp; eauto using tsplit_cren, thage_cren.
    - by apply e_inj.
    - eapply e_case; eauto using tsplit_cren, thage_cren.
    - apply e_box; [done|done|]. intros ss Hl Hs.
      match goal with Hb : ∀ ss, _ → _ → typed _ _ (kmap _ ∅) _ _ _ _ _ _ |- _ =>
        pose proof (Hb ss Hl Hs) as Hb'; rewrite kmap_empty in Hb'; exact Hb' end.
    - by eapply e_force.
    - by eapply e_send.
    - by eapply e_recv.
    - by eapply e_close.
    - by eapply e_select.
    - by eapply e_branch.
    - by eapply e_link.
    - by eapply e_spawn.
    - by apply e_new.
    - by apply e_new_fld.
    - by eapply e_sub.
    - by eapply e_pack.
    - rewrite <-tenv_pinst_cren in IHtyped. by eapply e_open.
  Qed.

  (** ** Interfaces *)

  Lemma lookup_senv_dual (Σ : senv) o :
    senv_dual Σ !! o = (λ e : sty * point, (dual e.1, e.2‾)) <$> Σ !! edual o.
  Proof.
    rewrite <-(edual_edual o) at 1. unfold senv_dual.
    rewrite (lookup_kmap edual), lookup_fmap. done.
  Qed.

  Lemma senv_dual_cren (Σ : senv) : senv_dual (kmap g Σ) = kmap g (senv_dual Σ).
  Proof.
    apply map_eq. intros o. rewrite lookup_senv_dual.
    destruct (kmap g (senv_dual Σ) !! o) as [v|] eqn:E.
    - apply lk_Some in E as (o' & -> & E). rewrite <-cmap_edual, lk.
      by rewrite lookup_senv_dual in E.
    - rewrite lk_None in E. destruct (kmap g Σ !! edual o) as [v|] eqn:E2; [|done].
      apply lk_Some in E2 as (i & Ei & E2). exfalso.
      assert (o = g (edual i)) as Eo by (by rewrite cmap_edual, <-Ei, edual_edual).
      specialize (E (edual i) Eo). rewrite lookup_senv_dual, edual_edual, E2 in E. discriminate.
  Qed.

  Lemma chans_of_cren (Σ : senv) : chans_of (kmap g Σ) = set_map h (chans_of Σ).
  Proof.
    unfold chans_of. rewrite kdom. apply set_eq. intros c.
    rewrite !elem_of_map. split.
    - intros (o & -> & Ho). apply elem_of_map in Ho as (o' & -> & Ho). exists (ech o').
      split; [apply ech_cmap|]. by apply elem_of_map_2.
    - intros (c' & -> & Hc). apply elem_of_map in Hc as (o & -> & Ho). exists (g o).
      split; [by rewrite ech_cmap|]. by apply elem_of_map_2.
  Qed.

  Lemma set_map_h_disj (A B : gset chan) : A ## B → set_map h A ## set_map (D:=gset chan) h B.
  Proof.
    intros H c Ha Hb. apply elem_of_map in Ha as (a & -> & Ha). apply elem_of_map in Hb as (b & E & Hb).
    apply (inj h) in E. subst b. exact (H a Ha Hb).
  Qed.

  Lemma set_map_h_union (A B : gset chan) : set_map (D:=gset chan) h (A ∪ B) = set_map h A ∪ set_map h B.
  Proof. apply set_map_union_L. Qed.

  Lemma pfree_cren Σ : pfree Σ → pfree (kmap g Σ).
  Proof.
    intros H o Ho Hd. rewrite !kdom in Ho, Hd.
    apply elem_of_map in Ho as (o' & -> & Ho). rewrite <-cmap_edual in Hd.
    apply elem_of_map in Hd as (o'' & E & Hd). apply (inj g) in E. subst o''.
    exact (H o' Ho Hd).
  Qed.

  Lemma tenv_of_cren a (Σ : senv) : tenv_of a (kmap g Σ) = kmap g (tenv_of a Σ).
  Proof. unfold tenv_of. by rewrite kfmap. Qed.

  Lemma tenv_ofk_cren (η η' : iann) (Σ : senv) : (∀ o, η' (g o) = η o) →
    tenv_ofk η' (kmap g Σ) = kmap g (tenv_ofk η Σ).
  Proof.
    intros Hη. apply map_eq. intros o. rewrite lookup_tenv_ofk.
    destruct (kmap g Σ !! o) as [v|] eqn:E.
    - apply lk_Some in E as (o' & -> & E). rewrite lk, lookup_tenv_ofk, E. simpl. by rewrite Hη.
    - simpl. symmetry. apply lk_None. intros i ->. rewrite lookup_tenv_ofk.
      rewrite lk in E. by rewrite E.
  Qed.

  Lemma iface_cren (Σ : senv) T : iface (kmap g Σ) T = iface Σ T.
  Proof.
    unfold iface. f_equal. apply set_eq. intros a. rewrite !elem_of_senv_consts. split.
    - intros (o & s & x & Ho & Ha). apply lk_Some in Ho as (o' & -> & Ho). eauto.
    - intros (o & s & x & Ho & Ha). exists (g o), s, x. split; [by rewrite lk|done].
  Qed.

  (** ** Processes *)

  Theorem ptyped_cren N (η η' : iann) W Σ p T : (∀ o, η' (g o) = η o) →
    ptyped N η W Σ p T → ptyped N η' W (kmap g Σ) (set_map h p.1, emapE g p.2) T.
  Proof.
    intros Hη.
    induction 1 as [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Htk Ht HW
                   |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 H12 H1C H2C HC HC1 HC2 Hts HS];
      cbn [fst snd] in *.
    - rewrite emapE_singleton, <-(iface_cren Σ). apply (p_term N η' W _ (kmap g ΘB) _ (emap g t) T c).
      + done.
      + intros o. rewrite kdom. split.
        * intros Ho. apply elem_of_map in Ho as (o' & -> & Ho). rewrite ech_cmap.
          apply elem_of_map_2. by apply HB.
        * intros Ho. apply elem_of_map in Ho as (c' & E & Hc').
          destruct o as [c0|c0]; simpl in E; subst c0.
          -- change (EPos (h c')) with (g (EPos c')). apply elem_of_map_2. apply HB. done.
          -- change (ENeg (h c')) with (g (ENeg c')). apply elem_of_map_2. apply HB. done.
      + rewrite chans_of_cren. by apply set_map_h_disj.
      + by apply pfree_cren.
      + intros o e He. apply lk_Some in He as (o' & -> & He). exact (HΣc o' e He).
      + intros c' Hc'. apply elem_of_map in Hc' as (c0 & -> & Hc0).
        destruct (Hd c0 Hc0) as (S & x & m & m' & Hm & HS & H1 & H2).
        exists S, x, m, m'. split_and!; [done|done| |].
        * change (EPos (h c0)) with (g (EPos c0)). by rewrite lk.
        * change (ENeg (h c0)) with (g (ENeg c0)). by rewrite lk.
      + intros o Ho. rewrite kdom in Ho. apply elem_of_map in Ho as (o' & -> & Ho). rewrite Hη. by apply Htk.
      + rewrite (tenv_ofk_cren η η' _ Hη), <-kunion. exact (typed_cren _ _ _ _ _ _ _ _ _ Ht).
      + done.
    - rewrite <-(iface_cren (Σ1 ∪ Σ2)), kunion. rewrite !set_map_h_union, <-(chans_of_cren ΣC), emapE_disj_union.
      rewrite !kunion in IH1, IH2. rewrite <-senv_dual_cren in IH2.
      apply p_connect; [exact IH1|exact IH2
        |by rewrite !chans_of_cren; apply set_map_h_disj|by rewrite !chans_of_cren; apply set_map_h_disj
        |by rewrite !chans_of_cren; apply set_map_h_disj|by apply set_map_h_disj
        |rewrite !chans_of_cren, <-set_map_h_union; by apply set_map_h_disj
        |rewrite !chans_of_cren, <-set_map_h_union; by apply set_map_h_disj| |exact HS].
      intros o Ho. rewrite kdom in Ho. apply elem_of_map in Ho as (o' & -> & Ho).
      rewrite <-cmap_edual, !Hη. by apply Hts.
  Qed.
End cren.
