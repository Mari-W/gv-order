(** * Facts about ownership maps (stage S8)

    Lookups of the parts of a soup state ([kth], [kres], [ctrs]) and of
    the operations of the index-free update. Every map equality of the
    soup step is proved pointwise from these. *)

From stdpp Require Import relations.
From GV Require Export soup.Soup.

Lemma map_eq_some {K' : Type} `{Countable K'} {Y : Type} (m1 m2 : gmap K' Y) :
  (∀ o v, m1 !! o = Some v ↔ m2 !! o = Some v) → m1 = m2.
Proof. intros Hm. apply map_eq. intros o. apply option_eq. apply Hm. Qed.

Section own.
  Implicit Types (K : own) (t : nat) (o : cend) (h : hold).

  Lemma lookup_kth K t o h : kth K t !! o = Some h ↔ K !! o = Some h ∧ h.(h_th) = t.
  Proof. unfold kth. by rewrite map_lookup_filter_Some. Qed.

  Lemma elem_of_dom_kth K t o : o ∈ dom (kth K t) ↔ ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof.
    rewrite elem_of_dom. split; [intros [h Hh]; apply lookup_kth in Hh; eauto|].
    intros (h & Hh & Ht). exists h. by apply lookup_kth.
  Qed.

  Lemma lookup_kres {Y : Type} K t (m : gmap cend Y) o v :
    kres K t m !! o = Some v ↔ m !! o = Some v ∧ ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. unfold kres. rewrite map_lookup_filter_Some, elem_of_dom_kth. done. Qed.

  Lemma lookup_kres_None {Y : Type} K t (m : gmap cend Y) o :
    kres K t m !! o = None ↔ m !! o = None ∨ ¬ ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof.
    destruct (kres K t m !! o) eqn:E.
    - apply lookup_kres in E as [E1 E2]. split; [done|]. intros [H|H]; [congruence|done].
    - split; [|done]. intros _. destruct (m !! o) eqn:Em; [right|by left].
      intros Hh. assert (kres K t m !! o = Some y) as E' by (by apply lookup_kres). congruence.
  Qed.

  Lemma lookup_ctrs K t o f : ctrs K t !! o = Some f ↔ ∃ h, K !! o = Some h ∧ h.(h_th) = t ∧ h.(h_ctr) = f.
  Proof.
    unfold ctrs. rewrite lookup_fmap_Some. split.
    - intros (h & <- & Hh). apply lookup_kth in Hh as [? ?]. eauto.
    - intros (h & Hh & Ht & <-). exists h. split; [done|]. by apply lookup_kth.
  Qed.

  Lemma dom_kres {Y : Type} K t (m : gmap cend Y) : dom (kres K t m) = dom m ∩ dom (kth K t).
  Proof.
    apply set_eq. intros o. rewrite elem_of_intersection, !elem_of_dom. split.
    - intros [v Hv]. apply lookup_kres in Hv as [Hv Hh]. split; [eauto|]. by apply elem_of_dom, elem_of_dom_kth.
    - intros [[v Hv] Hh]. exists v. apply lookup_kres. split; [done|]. by apply elem_of_dom_kth, elem_of_dom.
  Qed.

  Lemma dom_ctrs K t : dom (ctrs K t) = dom (kth K t).
  Proof. unfold ctrs. by rewrite dom_fmap_L. Qed.

  Lemma lookup_kmod f K o : kmod f K !! o = f o <$> K !! o.
  Proof. unfold kmod. rewrite map_lookup_imap. by destruct (K !! o). Qed.

  Lemma dom_kmod f K : dom (kmod f K) = dom K.
  Proof.
    apply set_eq. intros o. rewrite !elem_of_dom, lookup_kmod. by destruct (K !! o).
  Qed.

  (** Two states have the same part at t when the entries of t agree. *)
  Lemma kres_ext {Y : Type} K K' t (m m' : gmap cend Y) :
    (∀ o, (∃ h, K' !! o = Some h ∧ h.(h_th) = t) ↔ (∃ h, K !! o = Some h ∧ h.(h_th) = t)) →
    (∀ o h, K !! o = Some h → h.(h_th) = t → m' !! o = m !! o) →
    kres K' t m' = kres K t m.
  Proof.
    intros Ho Hm. apply map_eq_some. intros o v. rewrite !lookup_kres, Ho. split.
    - intros [Hv (h & Hh & Ht)]. rewrite (Hm o h Hh Ht) in Hv. eauto.
    - intros [Hv (h & Hh & Ht)]. rewrite (Hm o h Hh Ht). eauto.
  Qed.

  Lemma ctrs_ext K K' t :
    (∀ o f, (∃ h, K' !! o = Some h ∧ h.(h_th) = t ∧ h.(h_ctr) = f) ↔
            (∃ h, K !! o = Some h ∧ h.(h_th) = t ∧ h.(h_ctr) = f)) →
    ctrs K' t = ctrs K t.
  Proof. intros H. apply map_eq_some. intros o f. by rewrite !lookup_ctrs. Qed.
End own.

(** ** Renaming keys *)

Section kmapr.
  Context {Y : Type}.
  Implicit Types (g : cend → cend) (m : gmap cend Y).

  Lemma kmapr_lookup_inv g m o' v : kmapr g m !! o' = Some v → ∃ o, o' = g o ∧ m !! o = Some v.
  Proof.
    intros H. apply elem_of_list_to_map_2 in H.
    apply list_elem_of_fmap in H as ([o v'] & Heq & Hin). simpl in Heq. simplify_eq.
    apply elem_of_map_to_list in Hin. eauto.
  Qed.

  Lemma kmapr_lookup g m o v : kinj g m → m !! o = Some v → kmapr g m !! g o = Some v.
  Proof.
    intros Hk Ho. apply elem_of_list_to_map_1.
    - assert (((λ p : cend * Y, (g p.1, p.2)) <$> map_to_list m).*1 =
              g <$> (map_to_list m).*1) as ->.
      { rewrite <-!list_fmap_compose. by apply list_fmap_ext. }
      apply NoDup_fmap_2_strong; [|apply NoDup_fst_map_to_list].
      intros o1 o2 (p1 & -> & Hp1)%list_elem_of_fmap (p2 & -> & Hp2)%list_elem_of_fmap Heq.
      destruct p1 as [o1 v1], p2 as [o2 v2]. apply elem_of_map_to_list in Hp1, Hp2.
      exact (Hk o1 o2 v1 v2 Hp1 Hp2 Heq).
    - apply list_elem_of_fmap. exists (o, v). split; [done|]. by apply elem_of_map_to_list.
  Qed.

  Lemma kmapr_renk g m : kinj g m → renk g m (kmapr g m).
  Proof.
    intros Hk. split; [intros; by apply kmapr_lookup|]. intros o' v H. by apply kmapr_lookup_inv.
  Qed.

  Lemma kmapr_lookup_iff g m o' v : kinj g m →
    kmapr g m !! o' = Some v ↔ ∃ o, o' = g o ∧ m !! o = Some v.
  Proof.
    intros Hk. split; [apply kmapr_lookup_inv|]. intros (o & -> & Ho). by apply kmapr_lookup.
  Qed.

  Lemma dom_kmapr g m : kinj g m → dom (kmapr g m) = set_map g (dom m).
  Proof.
    intros Hk. apply set_eq. intros o'. rewrite elem_of_map, elem_of_dom. split.
    - intros [v Hv]. destruct (kmapr_lookup_inv _ _ _ _ Hv) as (o & -> & Ho).
      exists o. split; [done|]. by apply elem_of_dom_2 in Ho.
    - intros (o & -> & [v Hv]%elem_of_dom). exists v. by apply kmapr_lookup.
  Qed.
End kmapr.

Lemma kren_kmapr (h : cend → cend) (Θ : senv) : kren h Θ = kmapr h Θ.
Proof. done. Qed.

Lemma kinj_fmap {Y Z : Type} (g : cend → cend) (f : Y → Z) (m : gmap cend Y) :
  kinj g m → kinj g (f <$> m).
Proof.
  intros H o1 o2 v1 v2 H1 H2. apply lookup_fmap_Some in H1 as (w1 & _ & H1).
  apply lookup_fmap_Some in H2 as (w2 & _ & H2). exact (H o1 o2 w1 w2 H1 H2).
Qed.

Lemma kinj_dom_sub {Y Z : Type} (g : cend → cend) (m : gmap cend Y) (m' : gmap cend Z) :
  dom m' ⊆ dom m → kinj g m → kinj g m'.
Proof.
  intros Hd H o1 o2 v1 v2 H1 H2. apply elem_of_dom_2 in H1, H2.
  destruct (proj1 (elem_of_dom m o1) (Hd _ H1)) as [w1 Hw1].
  destruct (proj1 (elem_of_dom m o2) (Hd _ H2)) as [w2 Hw2].
  exact (H o1 o2 w1 w2 Hw1 Hw2).
Qed.
