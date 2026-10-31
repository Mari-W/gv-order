(** * Renaming channels (§10)

    The paper's Renaming.v, with the world fixed. A transposition of
    two channel names a ↔ b, applied to terms and processes ([ChannelSwap.v])
    and to the keys of environments, maps the logical relation to
    itself ([rel_swap]). Worlds and types mention no channels, so they
    stay as they are. Consequence: a process can rename its restricted
    names away from any finite set of names
    ([Prel_swap_restricted]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export invariance.PointConversion lang.ChannelSwap.

(** ** Environments *)

Lemma gswap_intersection a b C1 C2 :
  gswap a b (C1 ∩ C2) = gswap a b C1 ∩ gswap a b C2.
Proof.
  apply set_eq; intros c.
  rewrite elem_of_intersection, !elem_of_gswap', elem_of_intersection. done.
Qed.

Global Instance cswap_inj_inst a b : Inj (=) (=) (cswap a b).
Proof. intros x y. apply cswap_inj. Qed.

(** Session types and points mention no channels, so a transposition
    moves only the keys of an environment. *)
Definition tenvswap (a b : chan) (Θ : tenv) : tenv := kmap (cswap a b) Θ.

Definition senvswap (a b : chan) (Σ : senv) : senv := kmap (cswap a b) Σ.

Definition kswap (a b : chan) (k : ekey) : ekey := (cswap a b k.1, k.2).

Section envs.
  Context (a b : chan).

  Lemma lookup_tenvswap Θ c :
    tenvswap a b Θ !! cswap a b c = Θ !! c.
  Proof. unfold tenvswap. by rewrite (lookup_kmap (cswap a b)). Qed.

  Lemma lookup_tenvswap' Θ c :
    tenvswap a b Θ !! c = Θ !! cswap a b c.
  Proof.
    rewrite <-(cswap_involutive a b c) at 1. by rewrite lookup_tenvswap.
  Qed.

  Lemma lookup_senvswap Σ c :
    senvswap a b Σ !! cswap a b c = Σ !! c.
  Proof. unfold senvswap. by rewrite (lookup_kmap (cswap a b)). Qed.

  Lemma lookup_senvswap' Σ c :
    senvswap a b Σ !! c = Σ !! cswap a b c.
  Proof.
    rewrite <-(cswap_involutive a b c) at 1. by rewrite lookup_senvswap.
  Qed.

  Lemma tenvswap_involutive Θ : tenvswap a b (tenvswap a b Θ) = Θ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_tenvswap', cswap_involutive.
    done.
  Qed.

  Lemma senvswap_involutive Σ : senvswap a b (senvswap a b Σ) = Σ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_senvswap', cswap_involutive.
    done.
  Qed.

  Lemma dom_tenvswap Θ : dom (tenvswap a b Θ) = gswap a b (dom Θ).
  Proof.
    apply set_eq. intros c. rewrite elem_of_gswap', !elem_of_dom.
    rewrite lookup_tenvswap'. by destruct (Θ !! _).
  Qed.

  Lemma dom_senvswap Σ : dom (senvswap a b Σ) = gswap a b (dom Σ).
  Proof.
    apply set_eq. intros c. rewrite elem_of_gswap', !elem_of_dom.
    rewrite lookup_senvswap'. by destruct (Σ !! _).
  Qed.

  Lemma tenvswap_empty : tenvswap a b ∅ = ∅.
  Proof. apply map_eq. intros c. by rewrite lookup_tenvswap', !lookup_empty. Qed.

  Lemma tenvswap_insert Θ c o :
    tenvswap a b (<[c := o]> Θ) = <[cswap a b c := o]> (tenvswap a b Θ).
  Proof.
    apply map_eq. intros d. rewrite lookup_tenvswap'.
    destruct (decide (d = cswap a b c)) as [->|Hd].
    - by rewrite cswap_involutive, !lookup_insert_eq.
    - rewrite !lookup_insert_ne; [by rewrite lookup_tenvswap'|done|].
      intros ->. apply Hd. by rewrite cswap_involutive.
  Qed.

  Lemma senvswap_insert Σ c e :
    senvswap a b (<[c := e]> Σ) = <[cswap a b c := e]> (senvswap a b Σ).
  Proof.
    apply map_eq. intros d. rewrite lookup_senvswap'.
    destruct (decide (d = cswap a b c)) as [->|Hd].
    - by rewrite cswap_involutive, !lookup_insert_eq.
    - rewrite !lookup_insert_ne; [by rewrite lookup_senvswap'|done|].
      intros ->. apply Hd. by rewrite cswap_involutive.
  Qed.

  Lemma tenvswap_singleton c o :
    tenvswap a b {[c := o]} = {[cswap a b c := o]}.
  Proof. by rewrite <-!insert_empty, tenvswap_insert, tenvswap_empty. Qed.

  Lemma senvswap_union Σ1 Σ2 :
    senvswap a b (Σ1 ∪ Σ2) = senvswap a b Σ1 ∪ senvswap a b Σ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_union, !lookup_senvswap', lookup_union.
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma tenvswap_union Θ1 Θ2 :
    tenvswap a b (Θ1 ∪ Θ2) = tenvswap a b Θ1 ∪ tenvswap a b Θ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_union, !lookup_tenvswap', lookup_union.
    by destruct (Θ1 !! _), (Θ2 !! _).
  Qed.

  Lemma senvswap_difference Σ1 Σ2 :
    senvswap a b (Σ1 ∖ Σ2) = senvswap a b Σ1 ∖ senvswap a b Σ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_difference, !lookup_senvswap',
      lookup_difference.
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma senvswap_disjoint Σ1 Σ2 :
    Σ1 ##ₘ Σ2 → senvswap a b Σ1 ##ₘ senvswap a b Σ2.
  Proof.
    intros Hd c. rewrite !lookup_senvswap'. specialize (Hd (cswap a b c)).
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma tenvswap_of Σ : tenvswap a b (tenv_of Σ) = tenv_of (senvswap a b Σ).
  Proof.
    apply map_eq. intros c. unfold tenv_of.
    rewrite lookup_tenvswap', !lookup_fmap, lookup_senvswap'.
    by destruct (Σ !! _).
  Qed.

  Lemma tenv_ones_swap Θ : tenv_ones (tenvswap a b Θ) = senvswap a b (tenv_ones Θ).
  Proof.
    apply map_eq. intros c. unfold tenv_ones.
    rewrite lookup_omap, lookup_tenvswap', lookup_senvswap', lookup_omap.
    by destruct (Θ !! _) as [[]|].
  Qed.

  Lemma tenv_entry_swap Θ k :
    tenv_entry (tenvswap a b Θ) (kswap a b k) = tenv_entry Θ k.
  Proof.
    destruct k as [c s]. unfold tenv_entry, kswap. simpl.
    rewrite lookup_tenvswap. by destruct (Θ !! c) as [[]|], s.
  Qed.

  Lemma tenv_entry_swap' Θ k :
    tenv_entry (tenvswap a b Θ) k = tenv_entry Θ (kswap a b k).
  Proof.
    destruct k as [c s]. rewrite <-(cswap_involutive a b c) at 1.
    apply (tenv_entry_swap Θ (cswap a b c, s)).
  Qed.

  Lemma kswap_involutive k : kswap a b (kswap a b k) = k.
  Proof. destruct k. unfold kswap. simpl. by rewrite cswap_involutive. Qed.

  Lemma entry_head_swap k e : entry_head (kswap a b k) e = entry_head k e.
  Proof. done. Qed.

  Lemma ends_heads_swap c o : ends_heads (cswap a b c) o = ends_heads c o.
  Proof. by destruct o. Qed.

  Lemma tenv_heads_swap Θ : tenv_heads (tenvswap a b Θ) = tenv_heads Θ.
  Proof.
    apply set_eq. intros x. rewrite !elem_of_tenv_heads. split.
    - intros (c & o & Hc & Hx). rewrite lookup_tenvswap' in Hc.
      exists (cswap a b c), o. split; [done|]. by rewrite ends_heads_swap.
    - intros (c & o & Hc & Hx). exists (cswap a b c), o.
      rewrite lookup_tenvswap, ends_heads_swap. done.
  Qed.

  Lemma tenv_roots_swap Θ : tenv_roots (tenvswap a b Θ) = tenv_roots Θ.
  Proof.
    apply set_eq. intros x. rewrite !elem_of_tenv_roots. split.
    - intros (c & o & Hc & Hx). rewrite lookup_tenvswap' in Hc. eauto.
    - intros (c & o & Hc & Hx). exists (cswap a b c), o.
      by rewrite lookup_tenvswap.
  Qed.

  Lemma senv_roots_swap Σ : senv_roots (senvswap a b Σ) = senv_roots Σ.
  Proof. unfold senv_roots. by rewrite <-tenvswap_of, tenv_roots_swap. Qed.

  (** The relations between environments. *)

  Lemma tenv_join_swap Θ Θ1 Θ2 :
    tenv_join Θ Θ1 Θ2 → tenv_join (tenvswap a b Θ) (tenvswap a b Θ1) (tenvswap a b Θ2).
  Proof.
    intros H c. rewrite !lookup_tenvswap'. specialize (H (cswap a b c)).
    inversion H; simpl; constructor.
  Qed.

  Lemma tenv_comp_swap peq Θ Θ1 Θ2 :
    tenv_comp peq Θ Θ1 Θ2 →
    tenv_comp peq (tenvswap a b Θ) (tenvswap a b Θ1) (tenvswap a b Θ2).
  Proof.
    intros [Hj Hd]. split; [by apply tenv_join_swap|].
    intros c e1 e2 H1 H2. rewrite lookup_tenvswap' in H1, H2.
    destruct (Θ1 !! _) as [[]|] eqn:E1; try done.
    destruct (Θ2 !! _) as [[]|] eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (Hd _ _ _ E1 E2) as [? ?]. simpl. split; [done|]. done.
  Qed.

  Lemma tenv_ext_swap Θ1 c e Θ :
    tenv_ext Θ1 c e Θ →
    tenv_ext (tenvswap a b Θ1) (cswap a b c) e (tenvswap a b Θ).
  Proof.
    intros [[H1 ->]|(e' & H1 & [->| ->])].
    - left. rewrite lookup_tenvswap, H1. split; [done|]. by rewrite tenvswap_insert.
    - right. exists e'. rewrite lookup_tenvswap, H1.
      split; [done|]. left. by rewrite tenvswap_insert.
    - right. exists e'. rewrite lookup_tenvswap, H1.
      split; [done|]. right. by rewrite tenvswap_insert.
  Qed.

  Lemma tenv_hd_swap Θ c u k Θ1 :
    tenv_hd Θ c u k Θ1 →
    tenv_hd (tenvswap a b Θ) (cswap a b c) u k (tenvswap a b Θ1).
  Proof.
    intros (s & Hext & Hu). exists s. split.
    - apply (tenv_ext_swap _ _ (s, k)). done.
    - done.
  Qed.

  Lemma tenv_dual_swap peq Θ : tenv_dual peq Θ → tenv_dual peq (tenvswap a b Θ).
  Proof.
    intros H c e1 e2 He. rewrite lookup_tenvswap' in He.
    destruct (Θ !! _) as [[]|] eqn:E; try done. injection He as <- <-.
    destruct (H _ _ _ E). simpl. split; [done|]. done.
  Qed.

  Lemma senv_hd_swap Σ c u k Σ1 :
    senv_hd Σ c u k Σ1 →
    senv_hd (senvswap a b Σ) (cswap a b c) u k (senvswap a b Σ1).
  Proof.
    intros (s & -> & Hu). exists s.
    rewrite senvswap_insert. split; [done|]. done.
  Qed.

  Lemma senv_dual_on_swap peq Σ1 Σ2 :
    senv_dual_on peq Σ1 Σ2 → senv_dual_on peq (senvswap a b Σ1) (senvswap a b Σ2).
  Proof.
    intros H c e1 e2 H1 H2. rewrite lookup_senvswap' in H1, H2.
    destruct (Σ1 !! _) eqn:E1, (Σ2 !! _) eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (H _ _ _ E1 E2). simpl. split; [done|]. done.
  Qed.

  Lemma recv_back_swap Σr Θ2 :
    recv_back (senvswap a b Σr) (tenvswap a b Θ2) = gswap a b (recv_back Σr Θ2).
  Proof.
    unfold recv_back. rewrite tenv_ones_swap, dom_tenvswap, !dom_senvswap.
    by rewrite gswap_union, gswap_intersection, gswap_difference.
  Qed.

  Lemma recv_env_swap Σr Θ2 :
    recv_env (senvswap a b Σr) (tenvswap a b Θ2) = senvswap a b (recv_env Σr Θ2).
  Proof.
    unfold recv_env. by rewrite tenv_ones_swap, senvswap_union, !senvswap_difference.
  Qed.

  Lemma recv_ok_swap W Σr Θ2 :
    recv_ok W Σr Θ2 → recv_ok W (senvswap a b Σr) (tenvswap a b Θ2).
  Proof.
    intros (Hd & Ht & Hb). split_and!.
    - rewrite tenv_ones_swap. by apply senv_dual_on_swap.
    - by apply tenv_dual_swap.
    - rewrite tenv_ones_swap, dom_tenvswap, !dom_senvswap, <-gswap_difference.
      by apply gswap_disjoint_iff.
  Qed.

  Lemma send_split_swap W Σe Θe :
    send_split W Σe Θe → send_split W (senvswap a b Σe) (tenvswap a b Θe).
  Proof.
    intros [Hsub H]. split.
    - rewrite dom_senvswap, dom_tenvswap. intros c. rewrite !elem_of_gswap'. auto.
    - intros r o Hr. rewrite lookup_tenvswap' in Hr.
      destruct (Θe !! _) as [o0|] eqn:E; [|done]. injection Hr as <-.
      specialize (H _ _ E). destruct o0 as [e'|e1 e2]; simpl.
      + destruct H as (e & He & ? & ?). exists e.
        rewrite lookup_senvswap', He. split_and!; [done|done|]. done.
      + destruct H as (He & ? & ?). rewrite lookup_senvswap', He.
        split_and!; [done|done|]. done.
  Qed.
End envs.

(** ** Readiness and frames *)

Section ready.
  Context (a b : chan).

  Lemma slswap_involutive σ : slswap a b (slswap a b σ) = σ.
  Proof.
    destruct σ; simpl; by rewrite ?cswap_involutive, ?eswap_involutive,
      ?gswap_involutive.
  Qed.

  Lemma tlswap_involutive α : tlswap a b (tlswap a b α) = α.
  Proof.
    destruct α; simpl; by rewrite ?slswap_involutive, ?cswap_involutive,
      ?eswap_involutive.
  Qed.

  Lemma selects_swap Θ σ k :
    selects Θ σ k → selects (tenvswap a b Θ) (slswap a b σ) (kswap a b k).
  Proof.
    destruct σ as [c v|c v|c|cd|c i|c i]; simpl.
    - intros (Hk & e & m & T & s & He & Hu). split; [by rewrite Hk|].
      exists e, m, T, s.
      rewrite tenv_entry_swap, He. split; [done|]. simpl.
      done.
    - intros (Hk & e & m & T & s & He & Hu). split; [by rewrite Hk|].
      exists e, m, T, s.
      rewrite tenv_entry_swap, He. split; [done|]. simpl.
      done.
    - intros (Hk & e & He & Hu & Ht). split; [by rewrite Hk|].
      exists e. rewrite tenv_entry_swap, He.
      split_and!; [done|done|].
      intros Hk2 e' He'. simpl in Hk2.
      pose proof (tenv_entry_swap a b Θ (c, false)) as Hs. unfold kswap in Hs.
      simpl in Hs. rewrite He' in Hs. apply (Ht Hk2 e'). by rewrite Hs.
    - intros (Hk & He). split.
      + by apply elem_of_gswap.
      + rewrite tenv_entry_swap. destruct He as [e He]. rewrite He. by eexists.
    - intros (Hk & e & s1 & s2 & He & Hu). split; [by rewrite Hk|].
      exists e, s1, s2. by rewrite tenv_entry_swap, He.
    - intros (Hk & e & s1 & s2 & He & Hu). split; [by rewrite Hk|].
      exists e, s1, s2. by rewrite tenv_entry_swap, He.
  Qed.

  Lemma offered_t_swap Θ t k :
    offered_t Θ t k → offered_t (tenvswap a b Θ) (eswap a b t) (kswap a b k).
  Proof.
    intros (σ & t' & Hst & Hs). exists (slswap a b σ), (eswap a b t').
    split; [exact (tstep_eswap a b _ _ _ Hst)|]. by apply selects_swap.
  Qed.

  Lemma offered_t_swap_iff Θ t k :
    offered_t (tenvswap a b Θ) (eswap a b t) k ↔ offered_t Θ t (kswap a b k).
  Proof.
    split.
    - intros H. apply offered_t_swap in H.
      by rewrite tenvswap_involutive, eswap_involutive in H.
    - intros H. apply offered_t_swap in H. by rewrite kswap_involutive in H.
  Qed.

  Lemma offered_p_swap Σ p k :
    offered_p Σ p k → offered_p (senvswap a b Σ) (pswap a b p) (kswap a b k).
  Proof.
    intros (σ & p' & Hst & Hs). exists (slswap a b σ), (pswap a b p').
    split; [exact (proc_step_pswap a b _ _ _ Hst)|].
    rewrite <-tenvswap_of. by apply selects_swap.
  Qed.

  Lemma offered_p_swap_iff Σ p k :
    offered_p (senvswap a b Σ) (pswap a b p) k ↔ offered_p Σ p (kswap a b k).
  Proof.
    split.
    - intros H. apply offered_p_swap in H.
      by rewrite senvswap_involutive, pswap_involutive in H.
    - intros H. apply offered_p_swap in H. by rewrite kswap_involutive in H.
  Qed.

  Lemma stable_t_swap t : stable_t t → stable_t (eswap a b t).
  Proof.
    intros H α t' Hst. apply (tstep_eswap a b) in Hst.
    rewrite eswap_involutive in Hst. specialize (H _ _ Hst).
    by destruct α.
  Qed.

  Lemma stable_p_swap p : stable_p p → stable_p (pswap a b p).
  Proof.
    intros H p' Hst. apply (proc_step_pswap a b) in Hst.
    rewrite pswap_involutive in Hst. exact (H _ Hst).
  Qed.

  Lemma irred_swap e : irred e → irred (eswap a b e).
  Proof.
    intros H α e' Hst. apply (tstep_eswap a b) in Hst.
    rewrite eswap_involutive in Hst. exact (H _ _ Hst).
  Qed.

  Lemma pirred_swap p : pirred p → pirred (pswap a b p).
  Proof.
    intros H π p' Hst. apply (proc_step_pswap a b) in Hst.
    rewrite pswap_involutive in Hst. exact (H _ _ Hst).
  Qed.

  Lemma above_offered_swap W Θ (off off' : ekey → Prop) :
    (∀ k, off' k ↔ off (kswap a b k)) →
    above_offered W Θ off →
    above_offered W (tenvswap a b Θ) off'.
  Proof.
    intros Hoff H k e He Hk. rewrite tenv_entry_swap' in He.
    destruct (tenv_entry Θ (kswap a b k)) as [e0|] eqn:E0; [|done].
    injection He as <-. rewrite Hoff in Hk.
    destruct (H _ _ E0 Hk) as (k' & e' & Ho & He' & Hlt).
    exists (kswap a b k'), e'. split_and!.
    - by rewrite Hoff, kswap_involutive.
    - by rewrite tenv_entry_swap, He'.
    - rewrite <-(kswap_involutive a b k). by rewrite !entry_head_swap.
  Qed.

  Lemma below_rest_swap W Θ (off off' : ekey → Prop) F :
    (∀ k, off' k ↔ off (kswap a b k)) →
    below_rest W Θ off F →
    below_rest W (tenvswap a b Θ) off' F.
  Proof.
    intros Hoff H k e Ho He. rewrite tenv_entry_swap' in He.
    destruct (tenv_entry Θ (kswap a b k)) as [e0|] eqn:E0; [|done].
    injection He as <-. rewrite Hoff in Ho.
    destruct (H _ _ Ho E0) as [H1 H2].
    rewrite <-(kswap_involutive a b k), entry_head_swap. split; [|done].
    intros k' e' He' Hn. rewrite tenv_entry_swap' in He'.
    destruct (tenv_entry Θ (kswap a b k')) as [e1|] eqn:E1; [|done].
    injection He' as <-. rewrite <-(kswap_involutive a b k'), entry_head_swap.
    apply (H1 _ _ E1). by rewrite <-Hoff.
  Qed.

  Lemma ready_t_swap W Θ F t :
    ready_t W Θ F t → ready_t W (tenvswap a b Θ) F (eswap a b t).
  Proof.
    intros H Hs. apply (stable_t_swap) in Hs. rewrite eswap_involutive in Hs.
    destruct (H Hs) as [Hv Ha]. split.
    - intros Hno. rewrite is_val_eswap. apply Hv. intros k Hk.
      apply (Hno (kswap a b k)). by rewrite offered_t_swap_iff, kswap_involutive.
    - destruct Ha as [(cd & t' & Hst)|Ha].
      { left. exists (gswap a b cd), (eswap a b t').
        exact (tstep_eswap a b _ _ _ Hst). }
      right. apply (below_rest_swap _ _ (offered_t Θ t)); [|done].
      intros k. apply offered_t_swap_iff.
  Qed.

  Lemma ready_p_swap W Σ p :
    ready_p W Σ p → ready_p W (senvswap a b Σ) (pswap a b p).
  Proof.
    intros H Hs. apply stable_p_swap in Hs. rewrite pswap_involutive in Hs.
    destruct (H Hs) as [(cd & p' & Hst)|[Hv Ha]].
    { left. exists (gswap a b cd), (pswap a b p').
      exact (proc_step_pswap a b _ _ _ Hst). }
    right. split.
    - intros Hno. apply terminated_pswap. apply Hv. intros k Hk.
      apply (Hno (kswap a b k)). by rewrite offered_p_swap_iff, kswap_involutive.
    - rewrite <-tenvswap_of.
      apply (above_offered_swap _ _ (offered_p Σ p)); [|done].
      intros k. apply offered_p_swap_iff.
  Qed.

End ready.

(** ** Small transport facts used by the main lemma *)

Section misc.
  Context (a b : chan).

  Lemma msswap_elem e E : e ∈ msswap a b E → ∃ e0, e = eswap a b e0 ∧ e0 ∈ E.
  Proof. apply elem_of_gmultiset_map. Qed.

  Lemma tstep_eswap_inv' e α e'' :
    tstep (eswap a b e) α e'' →
    tstep e (tlswap a b α) (eswap a b e'').
  Proof.
    intros H. apply (tstep_eswap a b) in H. by rewrite eswap_involutive in H.
  Qed.

  Lemma proc_step_pswap_inv' p π q :
    proc_step (pswap a b p) π q → proc_step p (plswap a b π) (pswap a b q).
  Proof.
    intros H. apply (proc_step_pswap a b) in H. by rewrite pswap_involutive in H.
  Qed.
End misc.

(** ** The relations are equivariant

    One induction on the step index carries all three relations. *)

Lemma ptau_link_pswap a b p q :
  ptau_link p q → ptau_link (pswap a b p) (pswap a b q).
Proof.
  intros (C & E & e & c & d & e' & -> & Hst & Hc & ->).
  exists (gswap a b C), (msswap a b E), (eswap a b e), (cswap a b c),
    (cswap a b d), (eswap a b e').
  unfold pswap; simpl. split_and!.
  - by rewrite msswap_disj_union, msswap_singleton.
  - apply (tstep_eswap a b) in Hst. simpl in Hst. by rewrite gswap_upair in Hst.
  - by rewrite elem_of_gswap.
  - by rewrite gswap_difference, gswap_singleton, echsubst_msswap,
      msswap_disj_union, msswap_singleton.
Qed.

Lemma rel_swap a b n :
  (∀ W Θ T v, Vrel n W Θ T v → Vrel n W (tenvswap a b Θ) T (eswap a b v)) ∧
  (∀ W Θ T F e, Erel n W Θ T F e → Erel n W (tenvswap a b Θ) T F (eswap a b e)) ∧
  (∀ W Σ T p, Prel n W Σ T p → Prel n W (senvswap a b Σ) T (pswap a b p)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ j, j < n → ∀ W Θ T v, Vrel j W Θ T v →
            Vrel j W (tenvswap a b Θ) T (eswap a b v)) as IHV
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W Θ T F e, Erel j W Θ T F e →
            Erel j W (tenvswap a b Θ) T F (eswap a b e)) as IHE
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W Σ T p, Prel j W Σ T p →
            Prel j W (senvswap a b Σ) T (pswap a b p)) as IHP
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ W Θ ub lb T1 U v, Vrel n W Θ (TLolli ub lb T1 U) v →
            Vrel n W (tenvswap a b Θ) (TLolli ub lb T1 U) (eswap a b v)) as Hfun.
  { intros W Θ ub lb T1 U v HVv.
      apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & Hlb & H)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists (eswap a b eb). split_and!.
        * done.
        * by rewrite fchans_eswap, dom_tenvswap, Hfc.
        * by rewrite tenv_heads_swap.
        * intros W' j Θ' Θ'' w F Hx Hj Hc HVw Hub.
          apply (tenv_comp_swap a b) in Hc. rewrite tenvswap_involutive in Hc.
          apply (IHV j Hj) in HVw.
          specialize (H _ _ _ _ _ _ Hx Hj Hc HVw Hub).
          apply (IHE j Hj) in H.
          by rewrite tenvswap_involutive, eswap_subst1, eswap_involutive in H.
      + apply Vrel_lolli_iff. right. exists k, T0. split_and!; [done| |done|done].
        by rewrite tenvswap_empty. }
  assert (∀ W Θ T eb, Vlam n W Θ T (Lam eb) →
            Vlam n W (tenvswap a b Θ) T (eswap a b (Lam eb))) as Hlam.
  { intros W Θ T eb HVv.
    apply Vlam_iff in HVv as [(? & ? & ? & ? & ->) HVv]. apply Vlam_iff.
    split; [eauto|by apply Hfun]. }
  assert (∀ W Θ T v, Vrel n W Θ T v → Vrel n W (tenvswap a b Θ) T (eswap a b v)) as HV.
  { intros W Θ T. revert Θ.
    induction T as [|ub lb T1 IHT1 U IHU|T1 IHT1 U IHU|T1 IHT1 U IHU|m kk C0 T1 IHT1|s x
                   |lb m C0 T1 IHT1] using ty_ind_ex;
      intros Θ v HVv; simpl.
    - apply Vrel_unit_iff in HVv as [-> ->].
      apply Vrel_unit_iff. by rewrite tenvswap_empty.
    - by apply Hfun.
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
      apply Vrel_prod_iff.
      exists (eswap a b v1), (eswap a b v2), (tenvswap a b Θ1), (tenvswap a b Θ2).
      split_and!; [done|by apply tenv_comp_swap|by apply IHT1|by apply IHU].
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + by apply IHT1.
      + by apply IHU.
    - apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & H).
      apply Vrel_box_iff. rewrite tenvswap_empty. split; [done|].
      exists (eswap a b eb). split_and!; [done|by rewrite fchans_eswap, Hfc, gswap_empty|].
      intros W' xs ss Hx Hxs Hss Hsc HC HK.
      specialize (H _ xs ss Hx Hxs Hss Hsc HC HK). apply Hlam in H.
      unfold thunk in H. simpl in H.
      by rewrite tenvswap_empty, eswap_rename, eswap_subst1 in H.
    - apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs & Hx).
      apply Vrel_sess_iff. exists (cswap a b c), s0, k.
      split_and!; [done|by rewrite tenvswap_singleton|done|done].
    - apply Vrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HC & H)].
      apply Vrel_ex_iff. split; [by rewrite tenv_heads_swap|].
      exists xs. split_and!; [done..|]. by apply (IHT1 (plist xs)). }
  split_and!; [exact HV| |].
  - (* term relation *)
    destruct n as [|n']; [intros; apply Erel_0|].
    intros W Θ T F e HE.
    induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
    apply Erel_S_iff. split_and!.
    { intros Hirr. apply HV. apply Hval.
      apply (irred_swap a b) in Hirr. by rewrite eswap_involutive in Hirr. }
    { intros Hirr. apply ready_t_swap, Hrdy.
      intros Hirr0. apply Hirr. by apply irred_swap. }
    intros α e'' Hst. apply tstep_eswap_inv' in Hst.
    specialize (Hstep _ _ Hst).
    rewrite <-(tlswap_involutive a b α), <-(eswap_involutive a b e'').
    destruct (tlswap a b α) as [|[c w|c w|c|cd|c i|c i]|c|w]; simpl in Hstep |- *.
    + by apply (IHE n' ltac:(lia)).
    + (* recv *)
      destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists (tenvswap a b Θ1), m, U, s, k.
      split; [by apply (tenv_hd_swap a b _ _ (SSeq (SRcv m U) s))|].
      intros W' j Θ2 Θ1c Θ' Hx Hj Hext Hc HVw.
      apply (tenv_comp_swap a b) in Hc.
      apply (tenv_ext_swap a b) in Hext. rewrite tenvswap_involutive, cswap_involutive in Hext.
      apply (IHV j ltac:(lia)) in HVw. rewrite eswap_involutive in HVw.
      pose proof (H _ _ _ _ _ Hx Hj Hext Hc HVw) as HE'.
      apply (IHE j ltac:(lia)) in HE'. by rewrite tenvswap_involutive in HE'.
    + (* send *)
      destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists (tenvswap a b Θr), (tenvswap a b Θ1), (tenvswap a b Θ2), m,
        U, s, k, (tenvswap a b Θ').
      split_and!.
      * by apply (tenv_hd_swap a b _ _ (SSeq (SSnd m U) s)).
      * by apply tenv_comp_swap.
      * by apply HV.
      * by apply (tenv_ext_swap a b _ _ (s, pt_shift 1 k)).
      * exact (proj2 HE').
    + (* close *)
      destruct Hstep as (Θ1 & k & Hhd & HE').
      exists (tenvswap a b Θ1), k. split.
      * by apply (tenv_hd_swap a b _ _ SEnd).
      * exact (proj2 HE').
    + (* link *)
      destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & H1 & H2 & Hdu & Hal & HE').
      exists (cswap a b c), (cswap a b d), (tenvswap a b Θ1), (tenvswap a b Θm),
        sc, sd, kc, kd.
      split_and!.
      * apply gswap_upair.
      * by apply (tenv_ext_swap a b _ _ (sd, kd)).
      * by apply (tenv_ext_swap a b _ _ (sc, kc)).
      * done.
      * done.
      * exact (proj2 HE').
    + (* select *)
      destruct Hstep as (Θr & s1 & s2 & k & Θ' & Hhd & Hext & HE').
      exists (tenvswap a b Θr), s1, s2, k, (tenvswap a b Θ'). split_and!.
      * by apply (tenv_hd_swap a b _ _ (SPlus s1 s2)).
      * by apply (tenv_ext_swap a b _ _ (sbranch i s1 s2, pt_shift 1 k)).
      * exact (proj2 HE').
    + (* branch *)
      destruct Hstep as (Θr & s1 & s2 & k & Θ' & Hhd & Hext & HE').
      exists (tenvswap a b Θr), s1, s2, k, (tenvswap a b Θ'). split_and!.
      * by apply (tenv_hd_swap a b _ _ (SWith s1 s2)).
      * by apply (tenv_ext_swap a b _ _ (sbranch i s1 s2, pt_shift 1 k)).
      * by apply (IHE n' ltac:(lia)).
    + (* new *)
      intros Hc.
      assert (c ∉ dom Θ) as Hc0.
      { rewrite dom_tenvswap, elem_of_gswap', cswap_involutive in Hc. done. }
      destruct (Hstep Hc0) as (a0 & s & s' & W1 & Ha & Hdu & Hfr & HE').
      exists a0, s, s', W1. split_and!.
      * by rewrite tenv_roots_swap.
      * done.
      * done.
      * apply (IHE n' ltac:(lia)) in HE'. by rewrite tenvswap_insert in HE'.
    + (* spawn *)
      destruct Hstep as (Θ1 & Θ2 & ub & lb & Hc & HVw & HE').
      exists (tenvswap a b Θ1), (tenvswap a b Θ2), ub, lb.
      split_and!.
      * by apply tenv_comp_swap.
      * apply (HV _ _ (TLolli ub lb TUnit TUnit)) in HVw. exact HVw.
      * by apply (IHE n' ltac:(lia)).
  - (* process relation *)
    destruct n as [|n']; [intros; apply Prel_0|].
    intros W Σ T p HP.
    induction HP as [W Σ T p Hirr Hrdy Hstep] using Prel_S_ind.
    apply Prel_S_iff. split_and!.
    { intros Hpirr.
      destruct Hirr as (v & E & -> & Hv & HVv & HE).
      { apply (pirred_swap a b) in Hpirr. by rewrite pswap_involutive in Hpirr. }
      unfold pswap; simpl.
      rewrite gswap_empty, msswap_disj_union, msswap_singleton.
      exists (eswap a b v), (msswap a b E). split_and!.
      + done.
      + by rewrite is_val_eswap.
      + apply HV in HVv. by rewrite tenvswap_of in HVv.
      + intros e He. apply msswap_elem in He as (e0 & -> & He0).
        by rewrite (HE e0 He0). }
    { intros Hpirr. apply ready_p_swap.
      apply Hrdy. intros Hp0. apply Hpirr. by apply pirred_swap. }
    intros π q' Hst. apply proc_step_pswap_inv' in Hst.
    specialize (Hstep _ _ Hst).
    rewrite <-(pswap_involutive a b q').
    set (q := pswap a b q') in *. clearbody q.
    assert (π = plswap a b (plswap a b π)) as ->.
    { destruct π; simpl; by rewrite ?slswap_involutive. }
    destruct (plswap a b π) as [|[c w|c w|c|cd|c i|c i]]; simpl in Hstep |- *.
    + (* τ *)
      destruct Hstep as [Htau Hlink].
      assert ((pswap a b q).1 ## dom (senvswap a b Σ) → q.1 ## dom Σ) as Hdd.
      { intros Hd. destruct q as [Cq Eq]; simpl in *.
        rewrite dom_senvswap in Hd. by apply gswap_disjoint_iff in Hd. }
      split.
      { intros Hd. destruct (Htau (Hdd Hd)) as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [by rewrite senv_roots_swap|done|].
        by apply (IHP n' ltac:(lia)). }
      intros Hl Hd. apply (ptau_link_pswap a b) in Hl.
      rewrite !pswap_involutive in Hl.
      exact (proj2 (Hlink Hl (Hdd Hd))).
    + (* recv *)
      destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists (senvswap a b Σ1), m, U, s, k.
      split_and!.
      * by apply (senv_hd_swap a b _ _ (SSeq (SRcv m U) s)).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * intros W' j Θ2 Hx Hj Hfr Hok HVw.
        assert (dom (tenvswap a b Θ2) ## p.1) as Hfr'.
        { rewrite dom_tenvswap. destruct p as [C E]; simpl in *.
          rewrite <-(gswap_involutive a b C). by apply gswap_disjoint_iff. }
        assert (recv_ok W' (<[c := (s, pt_shift 1 k)]> Σ1) (tenvswap a b Θ2)) as Hok'.
        { apply (recv_ok_swap a b) in Hok.
          by rewrite senvswap_insert, senvswap_involutive, cswap_involutive in Hok. }
        apply (IHV j ltac:(lia)) in HVw. rewrite eswap_involutive in HVw.
        specialize (H _ _ _ Hx Hj Hfr' Hok' HVw).
        apply (IHP j ltac:(lia)) in H.
        rewrite <-recv_env_swap, tenvswap_involutive, senvswap_insert in H.
        unfold pswap in H; simpl in H.
        rewrite gswap_union, <-recv_back_swap, tenvswap_involutive,
          senvswap_insert in H.
        exact H.
    + (* send *)
      destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         Hd0v & Hc0 & Hcv & Hdom & Hsplit & HdΣ & HVw & HP').
      exists (senvswap a b Σ0), (senvswap a b Σv), m, U,
        s, k, (senvswap a b Σe), (tenvswap a b Θe).
      split_and!.
      * rewrite <-senvswap_union. by apply (senv_hd_swap a b _ _ (SSeq (SSnd m U) s)).
      * by apply senvswap_disjoint.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * destruct p as [C E]; simpl in *.
        by rewrite dom_tenvswap, fchans_eswap, Hdom, gswap_intersection.
      * by apply send_split_swap.
      * rewrite dom_tenvswap, dom_senvswap. by apply gswap_disjoint_iff.
      * apply HV in HVw. by rewrite tenvswap_union, tenvswap_of in HVw.
      * pose proof (proj2 HP') as HP2.
        by rewrite senvswap_insert, senvswap_union in HP2.
    + (* close *)
      destruct Hstep as (Σ1 & k & Hhd & Hc & HP').
      exists (senvswap a b Σ1), k. split_and!.
      * by apply (senv_hd_swap a b _ _ SEnd).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * exact (proj2 HP').
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & Hne & -> & Hc1 & Hd1 & Hdu & Hal & HP').
      exists (cswap a b c), (cswap a b d), (senvswap a b Σ1), sc,
        sd, kc, kd.
      split_and!.
      * apply gswap_upair.
      * intros Heq. by apply cswap_inj in Heq.
      * by rewrite !senvswap_insert.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * done.
      * done.
      * exact (proj2 HP').
    + (* select *)
      destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc & HP').
      exists (senvswap a b Σ1), s1, s2, k. split_and!.
      * by apply (senv_hd_swap a b _ _ (SPlus s1 s2)).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * pose proof (proj2 HP') as HP2. by rewrite senvswap_insert in HP2.
    + (* branch *)
      destruct Hstep as (Σ1 & s1 & s2 & k & Hhd & Hc & HP').
      exists (senvswap a b Σ1), s1, s2, k. split_and!.
      * by apply (senv_hd_swap a b _ _ (SWith s1 s2)).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * apply (IHP n' ltac:(lia)) in HP'. by rewrite senvswap_insert in HP'.
Qed.

Lemma Vrel_swap a b n W Θ T v :
  Vrel n W Θ T v → Vrel n W (tenvswap a b Θ) T (eswap a b v).
Proof. apply (rel_swap a b n). Qed.

Lemma Erel_swap a b n W Θ T F e :
  Erel n W Θ T F e → Erel n W (tenvswap a b Θ) T F (eswap a b e).
Proof. apply (rel_swap a b n). Qed.

Lemma Prel_swap a b n W Σ T p :
  Prel n W Σ T p → Prel n W (senvswap a b Σ) T (pswap a b p).
Proof. apply (rel_swap a b n). Qed.

(** ** Renaming restricted names *)

Lemma senvswap_fix a b Σ : a ∉ dom Σ → b ∉ dom Σ → senvswap a b Σ = Σ.
Proof.
  intros Ha Hb. apply map_eq. intros c. rewrite lookup_senvswap'.
  destruct (decide (c = a)) as [->|?]; [|destruct (decide (c = b)) as [->|?]].
  - rewrite cswap_l. apply not_elem_of_dom in Ha, Hb. by rewrite Ha, Hb.
  - rewrite cswap_r. apply not_elem_of_dom in Ha, Hb. by rewrite Ha, Hb.
  - by rewrite cswap_ne.
Qed.

(** A process may rename names outside its interface: the world and
    the interface stay. *)
Lemma Prel_swap_restricted a b n W Σ T p :
  a ∉ dom Σ → b ∉ dom Σ → Prel n W Σ T p → Prel n W Σ T (pswap a b p).
Proof.
  intros Ha Hb HP. apply (Prel_swap a b) in HP. by rewrite senvswap_fix in HP.
Qed.
