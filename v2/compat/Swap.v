(** * Transpositions of channel names on environments (stage S4)

    A transposition of two channel names a ↔ b renames every end of a
    term ([eswap a b], lang/ChannelSwap.v) and every end of an
    environment ([sswap a b] = kmap (oswap a b)). V and E are invariant
    under it, for every cost table ([Vrel_swap], [Erel_swap]). Both are
    instances of the renaming lemma of compat/Rename.v, which proves
    them. This file keeps the transposition on environments and
    readiness. *)

From GV Require Export compat.Blind lang.ChannelSwap.

Section swap.
  Context (a b : chan).

  Global Instance oswap_inj_inst : Inj eq eq (oswap a b).
  Proof. intros o o'. apply oswap_inj. Qed.

  Definition sswap (Θ : senv) : senv := kmap (oswap a b) Θ.

  Lemma sswap_lookup Θ o : sswap Θ !! oswap a b o = Θ !! o.
  Proof. apply lookup_kmap. all: try apply _. Qed.

  Lemma sswap_lookup' Θ o : sswap Θ !! o = Θ !! oswap a b o.
  Proof. by rewrite <-(oswap_involutive a b o) at 1; rewrite sswap_lookup. Qed.

  Lemma sswap_inv Θ : sswap (sswap Θ) = Θ.
  Proof. apply map_eq. intros o. by rewrite !sswap_lookup', oswap_involutive. Qed.

  Lemma sswap_empty : sswap ∅ = ∅.
  Proof. apply kmap_empty. all: try apply _. Qed.
  Lemma sswap_singleton o x : sswap {[o := x]} = {[oswap a b o := x]}.
  Proof. apply kmap_singleton. all: try apply _. Qed.
  Lemma sswap_insert Θ o x : sswap (<[o := x]> Θ) = <[oswap a b o := x]> (sswap Θ).
  Proof. apply kmap_insert. all: try apply _. Qed.
  Lemma sswap_delete Θ o : sswap (delete o Θ) = delete (oswap a b o) (sswap Θ).
  Proof. apply kmap_delete. all: try apply _. Qed.
  Lemma sswap_union Θ1 Θ2 : sswap (Θ1 ∪ Θ2) = sswap Θ1 ∪ sswap Θ2.
  Proof. apply kmap_union. all: try apply _. Qed.
  Lemma sswap_disjoint Θ1 Θ2 : sswap Θ1 ##ₘ sswap Θ2 ↔ Θ1 ##ₘ Θ2.
  Proof. apply map_disjoint_kmap. all: try apply _. Qed.
  Lemma set_map_oswap_inv (X : gset cend) : set_map (D:=gset cend) (oswap a b) (set_map (D:=gset cend) (oswap a b) X) = X.
  Proof.
    apply set_eq. intros o. split.
    - intros (o1 & -> & Ho1)%elem_of_map. apply elem_of_map in Ho1 as (o2 & -> & Ho2).
      by rewrite oswap_involutive.
    - intros H. apply elem_of_map. exists (oswap a b o). split; [by rewrite oswap_involutive|].
      apply elem_of_map. by exists o.
  Qed.

  Lemma sswap_dom Θ : dom (sswap Θ) = set_map (oswap a b) (dom Θ).
  Proof. apply dom_kmap_L. all: try apply _. Qed.
  Lemma sswap_heads Θ : senv_heads (sswap Θ) = senv_heads Θ.
  Proof.
    apply set_eq. intros y. rewrite !elem_of_senv_heads. setoid_rewrite sswap_lookup'.
    split; intros (o & S & x & H & ->); [|exists (oswap a b o); rewrite oswap_involutive];
      eauto.
  Qed.

  Lemma sswap_disjoint_l Θ1 Θ2 : sswap Θ1 ##ₘ Θ2 ↔ Θ1 ##ₘ sswap Θ2.
  Proof. by rewrite <-sswap_disjoint, sswap_inv. Qed.

  Lemma sswap_new_env c S x Θ :
    sswap (new_env c S x Θ) = new_env (cswap a b c) S x (sswap Θ).
  Proof. unfold new_env. by rewrite !sswap_insert. Qed.

  Lemma cfresh_swap c Θ : cfresh (cswap a b c) (sswap Θ) ↔ cfresh c Θ.
  Proof.
    unfold cfresh. rewrite !not_elem_of_dom.
    rewrite <-!(sswap_lookup Θ). simpl. done.
  Qed.

  Lemma gfresh_swap ℓ g Θ : gfresh ℓ g (sswap Θ) ↔ gfresh ℓ g Θ.
  Proof.
    unfold gfresh. setoid_rewrite sswap_lookup'. split; intros H o S x Hx.
    - apply (H (oswap a b o) S x). by rewrite oswap_involutive.
    - by apply (H (oswap a b o) S x).
  Qed.

  Lemma eswap_subst1 w e : eswap a b (subst1 w e) = subst1 (eswap a b w) (eswap a b e).
  Proof. apply emap_subst1. Qed.

  Lemma eswap_thunk e : eswap a b (thunk e) = thunk (eswap a b e).
  Proof. unfold thunk. simpl. by rewrite emap_rename, eswap_subst1. Qed.

  Lemma fends_eswap e : fends (eswap a b e) = set_map (oswap a b) (fends e).
  Proof. apply fends_emap. Qed.

  Lemma tstep_unswap e α e' :
    tstep (eswap a b e) α e' → tstep e (lren (cswap a b) α) (eswap a b e').
  Proof. intros H. apply (tstep_eswap a b) in H. by rewrite eswap_involutive in H. Qed.

  Lemma irred_swap e : irred e → irred (eswap a b e).
  Proof. intros Hi α e' Hs. by apply (Hi _ _ (tstep_unswap _ _ _ Hs)). Qed.

  Lemma sends_sren σ : sends (sren (cswap a b) σ) = set_map (oswap a b) (sends σ).
  Proof. destruct σ; simpl; set_solver. Qed.

  Lemma offered_swap Θ e o : offered_t (sswap Θ) (eswap a b e) o ↔ offered_t Θ e (oswap a b o).
  Proof.
    unfold offered_t. rewrite sswap_dom. split.
    - intros [Hd (σ & e' & Hs & Ho)]. split; [apply elem_of_map in Hd as (o' & -> & ?); by rewrite oswap_involutive|].
      apply tstep_unswap in Hs. exists (sren (cswap a b) σ), (eswap a b e'). split; [done|].
      rewrite sends_sren. by apply elem_of_map_2.
    - intros [Hd (σ & e' & Hs & Ho)]. split; [apply elem_of_map; exists (oswap a b o); by rewrite oswap_involutive|].
      apply (tstep_eswap a b) in Hs. exists (sren (cswap a b) σ), (eswap a b e'). split; [done|].
      rewrite sends_sren. apply elem_of_map. exists (oswap a b o). by rewrite oswap_involutive.
  Qed.

  Lemma ready_swap W Θ F e : ready _ W(Θ ∣ F, e) → ready _ W(sswap Θ ∣ F, eswap a b e).
  Proof.
    intros H Hs. assert (stable_t e) as Hs'.
    { intros α e' Hst. apply (tstep_eswap a b) in Hst. destruct (Hs _ _ Hst) as [σ Hσ].
      destruct α; simpl in Hσ; try discriminate; eauto. }
    destruct (H Hs') as [H1 H2]. split.
    - intros Hno. rewrite is_val_emap. apply H1.
      intros o Ho. apply (Hno (oswap a b o)), offered_swap.
      by rewrite oswap_involutive.
    - destruct H2 as [(os & e' & Hl)|Hb]; [left|right].
      + apply (tstep_eswap a b) in Hl. by eexists _, _.
      + intros o S x Ho Hx. rewrite sswap_lookup' in Hx. apply offered_swap in Ho.
        destruct (Hb _ _ _ Ho Hx) as [B1 B2]. split; [|done].
        intros o' S' x' Hx' Hno. rewrite sswap_lookup' in Hx'. apply (B1 _ _ _ Hx').
        intros Hoff. by apply Hno, offered_swap.
  Qed.
End swap.
