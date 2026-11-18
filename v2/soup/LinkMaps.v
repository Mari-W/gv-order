(** * Ownership after a link (stage S8)

    A link of o1 and o2 removes both ends from the linker and renames
    every other end by [csub o1 o2]: the partner of o1 becomes o2. On the
    ends that remain, [csub o1 o2] is injective, so the parts of every
    thread are renamed copies of the old parts, and the two partners of
    the linked ends form one channel. *)

From stdpp Require Import relations.
From GV Require Export soup.OwnFacts.

(** ** The link substitution off the linked ends *)

Lemma csub_self o1 a : csub o1 (edual o1) a = a.
Proof. unfold csub. rewrite edual_edual. repeat case_decide; subst; done. Qed.

Lemma csub_inj_off o1 o2 a b :
  a ≠ o1 → a ≠ o2 → b ≠ o1 → b ≠ o2 → csub o1 o2 a = csub o1 o2 b → a = b.
Proof. unfold csub. intros. repeat case_decide; subst; done. Qed.

Lemma csub_eq_o2 o1 o2 a : a ≠ o1 → a ≠ o2 → csub o1 o2 a = o2 → a = edual o1.
Proof. unfold csub. intros. repeat case_decide; subst; done. Qed.

Lemma csub_eq_off o1 o2 a : a ≠ edual o1 → a ≠ o1 → csub o1 o2 a = a.
Proof. unfold csub. intros. repeat case_decide; subst; done. Qed.

Definition kdel2 {Y : Type} (o1 o2 : cend) (m : gmap cend Y) : gmap cend Y := delete o1 (delete o2 m).

Lemma lookup_kdel2 {Y : Type} o1 o2 (m : gmap cend Y) a v :
  kdel2 o1 o2 m !! a = Some v ↔ a ≠ o1 ∧ a ≠ o2 ∧ m !! a = Some v.
Proof. unfold kdel2. rewrite !lookup_delete_Some. naive_solver. Qed.

Lemma kinj_csub {Y : Type} o1 o2 (m : gmap cend Y) : kinj (csub o1 o2) (kdel2 o1 o2 m).
Proof.
  intros a b va vb Ha Hb Heq. apply lookup_kdel2 in Ha as (H1 & H2 & _). apply lookup_kdel2 in Hb as (H3 & H4 & _).
  exact (csub_inj_off o1 o2 a b H1 H2 H3 H4 Heq).
Qed.

(** ** Parts after renaming *)

Section kmapr.
  Context (g : cend → cend).

  Lemma kres_kmapr {Y : Type} (K : own) t (m : gmap cend Y) :
    kinj g K → dom m ⊆ dom K → kres (kmapr g K) t (kmapr g m) = kmapr g (kres K t m).
  Proof.
    intros Hk Hd. assert (kinj g m) as Hm by (by eapply kinj_dom_sub).
    assert (kinj g (kres K t m)) as Hm' by (eapply kinj_dom_sub; [|exact Hm]; rewrite dom_kres; set_solver).
    apply map_eq_some. intros o' v. rewrite lookup_kres, !kmapr_lookup_iff by done. split.
    - intros [(o & -> & Ho) (h & Hh & Ht)]. apply kmapr_lookup_inv in Hh as (o0 & Heq & Ho0).
      assert (o0 = o) as ->.
      { apply elem_of_dom_2 in Ho. apply Hd in Ho. apply elem_of_dom in Ho as [h' Hh'].
        exact (Hk o0 o h h' Ho0 Hh' (eq_sym Heq)). }
      exists o. split; [done|]. apply lookup_kres. eauto.
    - intros (o & -> & Ho). apply lookup_kres in Ho as [Ho (h & Hh & Ht)]. split; [eauto|].
      exists h. split; [by apply kmapr_lookup|done].
  Qed.

  Lemma ctrs_kmapr (K : own) t : kinj g K → ctrs (kmapr g K) t = kmapr g (ctrs K t).
  Proof.
    intros Hk. assert (kinj g (ctrs K t)) as Hc.
    { eapply kinj_dom_sub; [|exact Hk]. rewrite dom_ctrs. intros o Ho. apply elem_of_dom_kth in Ho as (h & Hh & _).
      by apply elem_of_dom_2 in Hh. }
    apply map_eq_some. intros o' f. rewrite lookup_ctrs, kmapr_lookup_iff by done. split.
    - intros (h & Hh & Ht & <-). apply kmapr_lookup_inv in Hh as (o & -> & Ho).
      exists o. split; [done|]. apply lookup_ctrs. eauto.
    - intros (o & -> & Ho). apply lookup_ctrs in Ho as (h & Hh & Ht & <-). exists h.
      split; [by apply kmapr_lookup|done].
  Qed.

  Lemma fmap_kmapr {Y Z : Type} (f : Y → Z) (m : gmap cend Y) :
    kinj g m → f <$> kmapr g m = kmapr g (f <$> m).
  Proof.
    intros Hk. assert (kinj g (f <$> m)) as Hk' by (by apply kinj_fmap).
    apply map_eq_some. intros o' v. rewrite lookup_fmap_Some, kmapr_lookup_iff by done. split.
    - intros (w & <- & Hw). apply kmapr_lookup_inv in Hw as (o & -> & Ho). exists o.
      split; [done|]. by rewrite lookup_fmap, Ho.
    - intros (o & -> & Ho). apply lookup_fmap_Some in Ho as (w & <- & Hw). exists w.
      split; [done|by apply kmapr_lookup].
  Qed.
End kmapr.

Lemma kres_kdel2 {Y : Type} (K : own) t (m : gmap cend Y) o1 o2 :
  kres (kdel2 o1 o2 K) t (kdel2 o1 o2 m) = kdel2 o1 o2 (kres K t m).
Proof.
  apply map_eq_some. intros o v. rewrite lookup_kres, !lookup_kdel2, lookup_kres.
  setoid_rewrite lookup_kdel2. naive_solver.
Qed.

Lemma ctrs_kdel2 (K : own) t o1 o2 : ctrs (kdel2 o1 o2 K) t = kdel2 o1 o2 (ctrs K t).
Proof.
  apply map_eq_some. intros o f. rewrite lookup_ctrs, lookup_kdel2, lookup_ctrs.
  setoid_rewrite lookup_kdel2. naive_solver.
Qed.

Lemma mrem_kdel2 {Y : Type} (m : gmap cend Y) o1 o2 : mrem ({[o1]} ∪ {[o2]}) m = kdel2 o1 o2 m.
Proof. apply map_eq_some. intros o v. rewrite lookup_mrem_Some, lookup_kdel2. set_solver. Qed.

Lemma kdel2_comm {Y : Type} (m : gmap cend Y) o1 o2 : kdel2 o1 o2 m = kdel2 o2 o1 m.
Proof. unfold kdel2. apply delete_delete. Qed.

(** ** The pairing after a link

    A symmetric relation R holds between the values of the two ends of
    every channel of m. After the link of o1 and o2 it holds of the
    renamed map, when it holds between the partners of o1 and o2. *)
Lemma link_pair {Y : Type} (R : Y → Y → Prop) (m : gmap cend Y) o1 o2 :
  o1 ≠ o2 → o2 ≠ edual o1 →
  (∀ v v', R v v' → R v' v) →
  (∀ a v v', m !! a = Some v → m !! edual a = Some v' → R v v') →
  (∀ r1 r2, m !! edual o1 = Some r1 → m !! edual o2 = Some r2 → R r1 r2) →
  ∀ o' v v', kmapr (csub o1 o2) (kdel2 o1 o2 m) !! o' = Some v →
    kmapr (csub o1 o2) (kdel2 o1 o2 m) !! edual o' = Some v' → R v v'.
Proof.
  intros H12 Hns Hsym Hold Hlink o' v v' H1 H2.
  apply kmapr_lookup_inv in H1 as (a & -> & Ha). apply kmapr_lookup_inv in H2 as (b & Hb & Hb').
  apply lookup_kdel2 in Ha as (Ha1 & Ha2 & Ha). apply lookup_kdel2 in Hb' as (Hb1 & Hb2 & Hb').
  assert (H21 : o2 ≠ edual o1) by done.
  destruct (decide (a = edual o1)) as [->|Ha3].
  { (* the partner of o1 now holds o2 *)
    assert (csub o1 o2 (edual o1) = o2) as Hc by (unfold csub; by rewrite decide_True).
    rewrite Hc in Hb.
    assert (b = edual o2) as ->.
    { destruct (decide (b = edual o1)) as [->|Hb3].
      - rewrite Hc in Hb. exfalso. by apply (edual_ne o2).
      - by rewrite (csub_eq_off o1 o2 b Hb3 Hb1) in Hb. }
    by apply Hlink. }
  destruct (decide (a = edual o2)) as [->|Ha4].
  { rewrite (csub_eq_off o1 o2 (edual o2) Ha3 Ha1) in Hb.
    rewrite edual_edual in Hb. symmetry in Hb.
    pose proof (csub_eq_o2 o1 o2 b Hb1 Hb2 Hb) as ->. apply Hsym. by apply Hlink. }
  rewrite (csub_eq_off o1 o2 a Ha3 Ha1) in Hb.
  assert (b = edual a) as ->.
  { destruct (decide (b = edual o1)) as [->|Hb3].
    - assert (csub o1 o2 (edual o1) = o2) as Hc by (unfold csub; by rewrite decide_True).
      rewrite Hc in Hb. exfalso. apply Ha4. by rewrite <-Hb, edual_edual.
    - rewrite (csub_eq_off o1 o2 b Hb3 Hb1) in Hb. done. }
  exact (Hold a v v' Ha Hb').
Qed.

Lemma kmapr_id_ext {Y : Type} (g : cend → cend) (m : gmap cend Y) : (∀ a, g a = a) → kmapr g m = m.
Proof.
  intros Hg. assert (kinj g m) as Hk by (intros a b ? ? _ _ Heq; by rewrite !Hg in Heq).
  apply map_eq_some. intros o v. rewrite kmapr_lookup_iff by done. split.
  - intros (a & -> & Ha). by rewrite Hg.
  - intros Ho. exists o. by rewrite Hg.
Qed.

Lemma elem_of_dom_kdel2 {Y : Type} (m : gmap cend Y) o1 o2 a :
  a ∈ dom (kdel2 o1 o2 m) ↔ a ≠ o1 ∧ a ≠ o2 ∧ a ∈ dom m.
Proof. unfold kdel2. rewrite !dom_delete_L, !elem_of_difference, !elem_of_singleton. naive_solver. Qed.

(** The channels after a link: the linked channel of o1 goes. *)
Lemma link_dom_closed {Y : Type} (m : gmap cend Y) (C : gset chan) o1 o2 :
  o1 ≠ o2 → o2 ∈ dom m → (∀ a, a ∈ dom m → ech a ∈ C) →
  ∀ o', o' ∈ dom (kmapr (csub o1 o2) (kdel2 o1 o2 m)) → ech o' ∈ C ∖ {[ech o1]}.
Proof.
  intros H12 Ho2 Hc o' Ho'. rewrite dom_kmapr in Ho' by apply kinj_csub.
  apply elem_of_map in Ho' as (a & -> & Ha). apply elem_of_dom_kdel2 in Ha as (Ha1 & Ha2 & Ha).
  apply elem_of_difference. rewrite elem_of_singleton.
  destruct (decide (a = edual o1)) as [->|Ha3].
  - assert (csub o1 o2 (edual o1) = o2) as -> by (unfold csub; by rewrite decide_True).
    split; [by apply Hc|]. intros He. destruct (ech_eq _ _ He) as [-> | ->]; [done|].
    by rewrite edual_edual in Ha2.
  - rewrite (csub_eq_off o1 o2 a Ha3 Ha1). split; [by apply Hc|].
    intros He. destruct (ech_eq _ _ He) as [-> | ->]; [by apply Ha1|apply Ha3; by rewrite edual_edual].
Qed.

(** The ends after a link are paired again. *)
Lemma link_dom_pair {Y : Type} (m : gmap cend Y) o1 o2 :
  o1 ≠ o2 → o2 ≠ edual o1 → (∀ a, a ∈ dom m → edual a ∈ dom m) → o1 ∈ dom m → o2 ∈ dom m →
  ∀ o', o' ∈ dom (kmapr (csub o1 o2) (kdel2 o1 o2 m)) →
    edual o' ∈ dom (kmapr (csub o1 o2) (kdel2 o1 o2 m)).
Proof.
  intros H12 Hns Hp Ho1 Ho2 o' Ho'. rewrite dom_kmapr in Ho' |- * by apply kinj_csub.
  apply elem_of_map in Ho' as (a & -> & Ha). apply elem_of_dom_kdel2 in Ha as (Ha1 & Ha2 & Ha).
  apply elem_of_map.
  assert (Hc1 : csub o1 o2 (edual o1) = o2) by (unfold csub; by rewrite decide_True).
  assert (Hd2 : edual o2 ≠ o1) by (intros Hx; apply Hns; by rewrite <-Hx, edual_edual).
  assert (Hd2' : edual o2 ≠ edual o1) by (intros Hx; apply H12; by apply edual_inj).
  assert (Hd1 : edual o1 ≠ o2) by (intros Hx; apply Hns; by rewrite <-Hx).
  destruct (decide (a = edual o1)) as [->|Ha3].
  { exists (edual o2). rewrite Hc1, (csub_eq_off o1 o2 (edual o2) Hd2' Hd2). split; [done|].
    apply elem_of_dom_kdel2. split_and!; [done|apply edual_ne|by apply Hp]. }
  rewrite (csub_eq_off o1 o2 a Ha3 Ha1).
  destruct (decide (a = edual o2)) as [->|Ha4].
  { exists (edual o1). rewrite Hc1, edual_edual. split; [done|].
    apply elem_of_dom_kdel2. split_and!; [apply edual_ne|done|by apply Hp]. }
  exists (edual a). rewrite csub_eq_off.
  - split; [done|]. apply elem_of_dom_kdel2. split_and!; [| |by apply Hp].
    + intros Hx. apply Ha3. by rewrite <-Hx, edual_edual.
    + intros Hx. apply Ha4. by rewrite <-Hx, edual_edual.
  - intros Hx. apply Ha1. by apply edual_inj.
  - intros Hx. apply Ha3. by rewrite <-Hx, edual_edual.
Qed.
