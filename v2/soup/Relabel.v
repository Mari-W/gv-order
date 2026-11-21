(** * Relabelling the threads of a soup (stage S8)

    The lock-free judgment holds a soup at one lifting of the process,
    and lock freedom quantifies over runs from every lifting. Two
    liftings of one soup differ by a bijection of thread identifiers
    ([relabel_map]), and the soup moves along it ([soup_relabel]). *)

From stdpp Require Import relations.
From GV Require Export soup.Soup soup.OwnFacts.

Lemma relabel_map (M1 M2 : gmap nat expr) :
  soup M1 = soup M2 →
  ∃ f g : nat → nat,
    (∀ t e, M1 !! t = Some e → M2 !! f t = Some e ∧ g (f t) = t) ∧
    (∀ t' e, M2 !! t' = Some e → M1 !! g t' = Some e ∧ f (g t') = t').
Proof.
  revert M2. induction M1 as [|i e M1 Hi IH] using map_ind; intros M2 HM.
  - rewrite soup_empty in HM. exists id, id. split; [by intros ??; rewrite lookup_empty|].
    intros t' e He. exfalso. assert (e ∈ soup M2) as Hin by (apply elem_of_soup; by exists t').
    rewrite <-HM in Hin. multiset_solver.
  - rewrite soup_insert in HM by done. symmetry in HM.
    destruct (soup_extract M2 (soup M1) e HM) as (j & Hj & HMj).
    destruct (IH (delete j M2) (eq_sym HMj)) as (f & g & H1 & H2).
    exists (λ t, if decide (t = i) then j else f t), (λ t', if decide (t' = j) then i else g t'). split.
    + intros t e' Ht. destruct (decide (t = i)) as [->|Hti].
      * rewrite lookup_insert_eq in Ht. injection Ht as <-. split; [done|]. by rewrite decide_True.
      * rewrite lookup_insert_ne in Ht by done. destruct (H1 t e' Ht) as [H H'].
        apply lookup_delete_Some in H as [Hne H]. split; [done|]. by rewrite decide_False.
    + intros t' e' Ht'. destruct (decide (t' = j)) as [->|Htj].
      * rewrite Hj in Ht'. injection Ht' as <-. rewrite lookup_insert_eq. split; [done|]. by rewrite decide_True.
      * destruct (H2 t' e') as [H H']; [by rewrite lookup_delete_ne|].
        assert (g t' ≠ i) as Hgi by (intros Hx; rewrite Hx, Hi in H; done).
        rewrite lookup_insert_ne by done. split; [done|]. by rewrite decide_False.
Qed.

Definition krelabel (f : nat → nat) (K : own) : own := (λ h, Hold (f h.(h_th)) h.(h_pt) h.(h_ctr) h.(h_cap)) <$> K.

Lemma soup_relabel N n W Σ T C M1 M2 K A Π U (f g : nat → nat) :
  (∀ t e, M1 !! t = Some e → M2 !! f t = Some e ∧ g (f t) = t) →
  (∀ t' e, M2 !! t' = Some e → M1 !! g t' = Some e ∧ f (g t') = t') →
  soup_inv N n W Σ T (LFState (C, M1) K) A Π U →
  soup_inv N n W Σ T (LFState (C, M2) (krelabel f K)) A Π (U ∘ g).
Proof.
  intros H1 H2 Hs.
  assert (Hth : ∀ o h, K !! o = Some h → is_Some (M1 !! h.(h_th))) by apply (sp_owner _ _ _ _ _ _ _ _ _ Hs).
  assert (Hown : ∀ t' e, M2 !! t' = Some e → ∀ o,
    (∃ h, krelabel f K !! o = Some h ∧ h.(h_th) = t') ↔ (∃ h, K !! o = Some h ∧ h.(h_th) = g t')).
  { intros t' e He o. destruct (H2 t' e He) as [Hg Hfg]. unfold krelabel. rewrite lookup_fmap. split.
    - intros (h & Ho & Ht). destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Ho. injection Ho as <-.
      simpl in Ht. exists h0. split; [done|]. destruct (Hth o h0 E) as [e0 He0].
      destruct (H1 _ e0 He0) as [_ Hgf]. by rewrite <-Ht, Hgf.
    - intros (h & Ho & Ht). rewrite Ho. eexists. split; [done|]. simpl. by rewrite Ht, Hfg. }
  assert (Hkres : ∀ {Y} t' e (m : gmap cend Y), M2 !! t' = Some e → kres (krelabel f K) t' m = kres K (g t') m).
  { intros Y t' e m He. apply map_eq_some. intros o v. rewrite !lookup_kres, (Hown t' e He o). done. }
  assert (Hctrs : ∀ t' e, M2 !! t' = Some e → ctrs (krelabel f K) t' = ctrs K (g t')).
  { intros t' e He. apply map_eq_some. intros o c. rewrite !lookup_ctrs. split.
    - intros (h & Kh & Ht & Hc). unfold krelabel in Kh. rewrite lookup_fmap in Kh.
      destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Kh. injection Kh as <-. simpl in *.
      exists h0. split_and!; [done| |done]. destruct (Hth o h0 E) as [e0 He0].
      destruct (H1 _ e0 He0) as [_ Hgf]. by rewrite <-Ht, Hgf.
    - intros (h & Kh & Ht & Hc). exists (Hold (f h.(h_th)) h.(h_pt) h.(h_ctr) h.(h_cap)).
      unfold krelabel. rewrite lookup_fmap, Kh. simpl. split_and!; [done| |done].
      destruct (H2 t' e He) as [_ Hfg]. by rewrite Ht, Hfg. }
  unfold soup_inv in *. constructor; simpl in *.
  - exact (sp_tfree _ _ _ _ _ _ _ _ _ Hs).
  - intros t e He. rewrite (Hkres _ t e A He). destruct (H2 t e He) as [Hg _]. by apply (sp_rel _ _ _ _ _ _ _ _ _ Hs).
  - intros t e He. destruct (H2 t e He) as [Hg _]. by apply ((sp_ty _ _ _ _ _ _ _ _ _ Hs) (g t) e).
  - intros t e He. rewrite (Hkres _ t e Π He), (Hctrs t e He). destruct (H2 t e He) as [Hg _].
    by apply ((sp_fuel _ _ _ _ _ _ _ _ _ Hs) (g t) e).
  - unfold krelabel. rewrite <-map_fmap_compose. exact (sp_pts _ _ _ _ _ _ _ _ _ Hs).
  - unfold krelabel. rewrite dom_fmap_L. exact (sp_dom _ _ _ _ _ _ _ _ _ Hs).
  - intros o h Ho. unfold krelabel in Ho. rewrite lookup_fmap in Ho.
    destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Ho. injection Ho as <-. simpl.
    destruct ((sp_owner _ _ _ _ _ _ _ _ _ Hs) o h0 E) as [e0 He0]. destruct (H1 _ e0 He0) as [Hf _]. by eexists.
  - intros o. unfold krelabel. rewrite dom_fmap_L. apply (sp_closed _ _ _ _ _ _ _ _ _ Hs).
  - intros o. unfold krelabel. rewrite !dom_fmap_L. apply (sp_pair _ _ _ _ _ _ _ _ _ Hs).
  - exact (sp_sdual _ _ _ _ _ _ _ _ _ Hs).
  - exact (sp_pdual _ _ _ _ _ _ _ _ _ Hs).
  - exact (sp_sig _ _ _ _ _ _ _ _ _ Hs).
  - intros o h Ho. unfold krelabel in Ho. rewrite lookup_fmap in Ho.
    destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Ho. injection Ho as <-. simpl. by apply ((sp_fin _ _ _ _ _ _ _ _ _ Hs) o h0).
  - exact (sp_psig _ _ _ _ _ _ _ _ _ Hs).
  - intros o h Ho. unfold krelabel in Ho. rewrite lookup_fmap in Ho.
    destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Ho. injection Ho as <-. simpl. by apply ((sp_cap _ _ _ _ _ _ _ _ _ Hs) o h0).
  - intros o h h' Ho Ho' Hc. unfold krelabel in Ho, Ho'. rewrite lookup_fmap in Ho, Ho'.
    destruct (K !! o) as [h0|] eqn:E; [|done]. destruct (K !! edual o) as [h1|] eqn:E'; [|done].
    simpl in Ho, Ho'. injection Ho as <-. injection Ho' as <-. simpl. by apply ((sp_tsum _ _ _ _ _ _ _ _ _ Hs) o h0 h1).
  - intros o h HΣ Ho. unfold krelabel in Ho. rewrite lookup_fmap in Ho.
    destruct (K !! o) as [h0|] eqn:E; [|done]. simpl in Ho. injection Ho as <-. simpl. by apply ((sp_sigcap _ _ _ _ _ _ _ _ _ Hs) o h0).
Qed.
