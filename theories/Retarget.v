(** * Channel renaming stability for the logical relation (§4.5)

    P-Act-Link substitutes one channel for another across the whole
    soup, so the composition lemmas need the relations to be stable
    under channel renaming. Two independent facts suffice (see
    docs/link-design.md):

    - equivariance: transposing two channel names everywhere — terms,
      labels, restricted sets, environment keys — preserves all three
      relations. Transpositions are bijective, so every clause
      transports exactly.
    - junk collapse: renaming a channel that is fresh for the
      *interface* (∉ dom Σ ∪ C) — but possibly present in the syntax —
      into any other name preserves the relations: an interface-fresh
      channel can never act, so its occurrences are inert.

    The one-sided substitution of P-Act-Link is their composite:
    echsubst x d E = chsubst x d (eswap x d E). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export LogRel.

(** eswap commutes with the de Bruijn operations (channels and
    variables live in different namespaces). *)
Lemma eswap_rename a b r e : eswap a b (rename r e) = rename r (eswap a b e).
Proof. revert r. induction e; intros r; simpl; f_equal; auto. Qed.

Lemma eswap_up a b σ x :
  eswap a b (up σ x) = up (λ y, eswap a b (σ y)) x.
Proof.
  destruct x; simpl; [done|]. unfold compose. apply eswap_rename.
Qed.

Lemma eswap_subst a b σ e :
  eswap a b (subst σ e) = subst (λ x, eswap a b (σ x)) (eswap a b e).
Proof.
  revert σ. induction e; intros σ; simpl; f_equal; auto.
  all: rewrite ?IHe, ?IHe0, ?IHe1, ?IHe2, ?IHe3.
  all: apply subst_ext; intros x;
    first [apply eswap_up
          |etrans; [apply eswap_up|]; apply up_ext; intros ?;
           apply eswap_up].
Qed.

Lemma eswap_subst1 a b v e :
  eswap a b (subst1 v e) = subst1 (eswap a b v) (eswap a b e).
Proof.
  unfold subst1. rewrite eswap_subst. apply subst_ext.
  by intros [|x].
Qed.

Lemma eswap_subst2 a b u v e :
  eswap a b (subst2 u v e) = subst2 (eswap a b u) (eswap a b v) (eswap a b e).
Proof.
  unfold subst2. rewrite eswap_subst. apply subst_ext.
  by intros [|[|x]].
Qed.

(** ** Equivariance of the operational semantics *)

Definition gswap (a b : chan) (C : gset chan) : gset chan :=
  set_map (cswap a b) C.

Definition slswap (a b : chan) (σ : slabel) : slabel :=
  match σ with
  | SRecv c v => SRecv (cswap a b c) (eswap a b v)
  | SSend c v => SSend (cswap a b c) (eswap a b v)
  | SClos c => SClos (cswap a b c)
  | SLink cd => SLink (gswap a b cd)
  end.

Definition tlswap (a b : chan) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LSess σ => LSess (slswap a b σ)
  | LFork c v => LFork (cswap a b c) (eswap a b v)
  end.

Lemma gswap_upair a b c d :
  gswap a b ({[c; d]} : gset chan) = {[cswap a b c; cswap a b d]}.
Proof.
  unfold gswap. by rewrite set_map_union_L, !set_map_singleton_L.
Qed.

Lemma head_step_eswap a b e α e' :
  head_step e α e' →
  head_step (eswap a b e) (tlswap a b α) (eswap a b e').
Proof.
  destruct 1; simpl.
  - rewrite eswap_subst1. constructor. by rewrite is_val_eswap.
  - constructor.
  - rewrite eswap_subst2. constructor; by rewrite is_val_eswap.
  - constructor. by rewrite is_val_eswap.
  - constructor. by rewrite is_val_eswap.
  - constructor. by rewrite is_val_eswap.
  - constructor.
  - rewrite eswap_subst1. constructor. by rewrite is_val_eswap.
  - rewrite eswap_subst1. constructor. by rewrite is_val_eswap.
  - rewrite eswap_subst1. constructor.
  - rewrite gswap_upair. constructor.
Qed.

Lemma tstep_eswap a b e α e' :
  tstep e α e' → tstep (eswap a b e) (tlswap a b α) (eswap a b e').
Proof.
  induction 1; simpl.
  - apply TStepHead. by apply head_step_eswap.
  - by apply TStepAppL.
  - apply TStepAppR; [by rewrite is_val_eswap|done].
  - by apply TStepPairL.
  - apply TStepPairR; [by rewrite is_val_eswap|done].
  - by apply TStepLetU.
  - by apply TStepLetP.
  - by apply TStepInj1.
  - by apply TStepInj2.
  - by apply TStepCase.
  - by apply TStepForce.
Qed.

Lemma gswap_involutive a b C : gswap a b (gswap a b C) = C.
Proof.
  apply set_eq. intros c. split.
  - intros Hc. unfold gswap in Hc.
    apply elem_of_map in Hc as (c1 & -> & Hc1).
    apply elem_of_map in Hc1 as (c2 & -> & Hc2).
    by rewrite cswap_involutive.
  - intros Hc. apply elem_of_map. exists (cswap a b c).
    split; [by rewrite cswap_involutive|].
    apply elem_of_map. by exists c.
Qed.

(** The inverse direction, by involutivity. *)
Lemma tstep_eswap_inv a b e α' E' :
  tstep (eswap a b e) α' E' →
  ∃ α e', tstep e α e' ∧ α' = tlswap a b α ∧ E' = eswap a b e'.
Proof.
  intros Hst.
  pose proof (tstep_eswap a b _ _ _ Hst) as Hst'.
  rewrite eswap_involutive in Hst'.
  eexists _, _. split_and!; [exact Hst'| |].
  - destruct α' as [|[c v|c v|c|cd]|c v]; simpl;
      rewrite ?cswap_involutive, ?eswap_involutive, ?gswap_involutive; done.
  - by rewrite eswap_involutive.
Qed.

(** ** Transposition on sets, multisets, environments, processes *)

Notation msswap := echswap.

Definition senvswap (a b : chan) (Σ : senv) : senv :=
  kmap (cswap a b) Σ.

Definition pswap (a b : chan) (p : proc) : proc :=
  (gswap a b p.1, msswap a b p.2).

Global Instance cswap_injective a b : Inj (=) (=) (cswap a b).
Proof. intros x y. apply cswap_inj. Qed.

Lemma elem_of_gswap a b c C : cswap a b c ∈ gswap a b C ↔ c ∈ C.
Proof.
  unfold gswap. rewrite elem_of_map. split.
  - intros (c' & Heq & Hc'). apply cswap_inj in Heq. by subst.
  - intros Hc. by exists c.
Qed.


Lemma msswap_involutive a b E : msswap a b (msswap a b E) = E.
Proof.
  unfold echswap. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite eswap_involutive.
Qed.

Lemma msswap_disj_union a b E1 E2 :
  msswap a b (E1 ⊎ E2) = msswap a b E1 ⊎ msswap a b E2.
Proof. apply gmultiset_map_disj_union. Qed.

Lemma msswap_singleton a b e :
  msswap a b ({[+ e +]} : gmultiset expr) = {[+ eswap a b e +]}.
Proof. apply gmultiset_map_singleton. Qed.

Lemma lookup_kswap a b Σ c :
  senvswap a b Σ !! cswap a b c = Σ !! c.
Proof. apply (lookup_kmap (cswap a b)). Qed.

Lemma senvswap_insert a b Σ c s :
  senvswap a b (<[c := s]> Σ) = <[cswap a b c := s]> (senvswap a b Σ).
Proof. apply (kmap_insert (cswap a b)). Qed.

Lemma senvswap_empty a b : senvswap a b (∅ : senv) = ∅.
Proof. apply (kmap_empty (cswap a b)). Qed.

Lemma dom_kswap a b Σ : dom (senvswap a b Σ) = gswap a b (dom Σ).
Proof. apply (dom_kmap_L (cswap a b)). Qed.

Lemma senvswap_involutive a b Σ : senvswap a b (senvswap a b Σ) = Σ.
Proof.
  apply map_eq. intros c.
  transitivity (senvswap a b (senvswap a b Σ) !! cswap a b (cswap a b c)).
  { by rewrite cswap_involutive. }
  by rewrite !lookup_kswap.
Qed.

Lemma senvswap_union a b Σ1 Σ2 :
  senvswap a b (Σ1 ∪ Σ2) = senvswap a b Σ1 ∪ senvswap a b Σ2.
Proof. apply (kmap_union (cswap a b)). Qed.

Lemma senvswap_disjoint a b Σ1 Σ2 :
  Σ1 ##ₘ Σ2 → senvswap a b Σ1 ##ₘ senvswap a b Σ2.
Proof.
  intros Hd. apply map_disjoint_dom. rewrite !dom_kswap.
  apply map_disjoint_dom in Hd.
  apply elem_of_disjoint. intros c H1 H2.
  apply elem_of_map in H1 as (c1 & -> & Hc1).
  apply elem_of_map in H2 as (c2 & Heq & Hc2).
  apply cswap_inj in Heq. subst. set_solver.
Qed.

(** Channel footprints transport along the swap. *)
Lemma fchans_eswap a b e : fchans (eswap a b e) = gswap a b (fchans e).
Proof.
  induction e; simpl; unfold gswap in *;
    rewrite ?IHe, ?IHe0, ?IHe1, ?IHe2, ?IHe3; set_solver.
Qed.

Lemma echans_msswap a b E : echans (msswap a b E) = gswap a b (echans E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echswap. rewrite gmultiset_map_empty, !echans_empty.
    unfold gswap. set_solver.
  - unfold echswap in *.
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
    rewrite !echans_disj_union, !echans_singleton, IH, fchans_eswap.
    unfold gswap. set_solver.
Qed.


Lemma elem_of_gswap' a b c C : c ∈ gswap a b C ↔ cswap a b c ∈ C.
Proof.
  split.
  - intros (c1 & -> & Hc1)%elem_of_map. by rewrite cswap_involutive.
  - intros Hc. rewrite <-(cswap_involutive a b c). by apply elem_of_gswap.
Qed.

Lemma gswap_union a b C1 C2 :
  gswap a b (C1 ∪ C2) = gswap a b C1 ∪ gswap a b C2.
Proof.
  unfold gswap.
  first [apply set_map_union_L|apply leibniz_equiv, set_map_union].
Qed.

Lemma gswap_difference a b C1 C2 :
  gswap a b (C1 ∖ C2) = gswap a b C1 ∖ gswap a b C2.
Proof.
  apply set_eq; intros c. split.
  - intros Hc. unfold gswap in Hc.
    apply elem_of_map in Hc as (c1 & -> & Hc1).
    apply elem_of_difference in Hc1 as [H1 H2].
    rewrite elem_of_difference, !elem_of_gswap. auto.
  - intros [H1 H2]%elem_of_difference.
    unfold gswap in H1. apply elem_of_map in H1 as (c1 & -> & Hc1).
    rewrite elem_of_gswap. apply elem_of_difference. split; [done|].
    intros H. apply H2. by rewrite elem_of_gswap.
Qed.

Lemma gswap_singleton a b c : gswap a b ({[c]} : gset chan) = {[cswap a b c]}.
Proof.
  unfold gswap.
  first [apply set_map_singleton_L|apply leibniz_equiv, set_map_singleton].
Qed.

Lemma gswap_empty a b : gswap a b (∅ : gset chan) = ∅.
Proof. unfold gswap. apply set_eq; intros c. set_solver. Qed.

(** [chsubst] is equivariant. *)
Lemma eswap_chsubst a b c d e :
  eswap a b (chsubst c d e)
  = chsubst (cswap a b c) (cswap a b d) (eswap a b e).
Proof.
  induction e; simpl; f_equal; auto.
  repeat case_decide; simplify_eq; try done;
    exfalso; eauto using cswap_inj.
Qed.

Lemma echsubst_msswap a b c d E :
  msswap a b (echsubst c d E)
  = echsubst (cswap a b c) (cswap a b d) (msswap a b E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echswap, echsubst. by rewrite !gmultiset_map_empty.
  - unfold echswap, echsubst in *.
    rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton.
    by rewrite IH, eswap_chsubst.
Qed.

(** ** Equivariance of the process LTS *)

(** Conjugation: a transposition maps a transposition to the
    transposition of the swapped names. *)
Lemma cswap_conj a b c d z :
  cswap a b (cswap c d z)
  = cswap (cswap a b c) (cswap a b d) (cswap a b z).
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma eswap_conj a b c d e :
  eswap a b (eswap c d e)
  = eswap (cswap a b c) (cswap a b d) (eswap a b e).
Proof. induction e; simpl; f_equal; auto using cswap_conj. Qed.

Lemma echswap_conj a b c d E :
  msswap a b (echswap c d E)
  = echswap (cswap a b c) (cswap a b d) (msswap a b E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echswap. by rewrite !gmultiset_map_empty.
  - unfold echswap in *.
    rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton.
    by rewrite IH, eswap_conj.
Qed.

(** The composed form the Out-variant forwarding rules produce. *)
Lemma echswap_conj' a b c d E e' :
  msswap a b (echswap c d (E ⊎ ({[+ e' +]} : gmultiset expr)))
  = echswap (cswap a b c) (cswap a b d)
      (msswap a b E ⊎ {[+ eswap a b e' +]}).
Proof.
  rewrite echswap_conj. f_equal.
  by rewrite msswap_disj_union, msswap_singleton.
Qed.

Lemma gswap_disjoint_iff a b C1 C2 :
  gswap a b C1 ## gswap a b C2 ↔ C1 ## C2.
Proof.
  split; intros Hd; apply elem_of_disjoint; intros c H1 H2.
  - assert (cswap a b c ∈ gswap a b C1) by (by apply elem_of_gswap).
    assert (cswap a b c ∈ gswap a b C2) by (by apply elem_of_gswap).
    set_solver.
  - apply elem_of_gswap' in H1. apply elem_of_gswap' in H2. set_solver.
Qed.

Definition plswap (a b : chan) (π : plabel) : plabel :=
  match π with
  | PTau => PTau
  | PSess σ => PSess (slswap a b σ)
  end.

Lemma subjs_sswap a b σ : subjs (slswap a b σ) = gswap a b (subjs σ).
Proof.
  destruct σ; simpl; try (by rewrite gswap_singleton). done.
Qed.

Lemma sentc_sswap a b σ : sentc (slswap a b σ) = gswap a b (sentc σ).
Proof.
  destruct σ; simpl; rewrite ?fchans_eswap, ?gswap_empty; done.
Qed.

Lemma proc_step_pswap a b p π p' :
  proc_step p π p' →
  proc_step (pswap a b p) (plswap a b π) (pswap a b p').
Proof.
  destruct 1; unfold pswap; simpl.
  - (* session *)
    rewrite !msswap_disj_union, !msswap_singleton, gswap_difference.
    rewrite <-sentc_sswap.
    apply PStepSession.
    + by apply (tstep_eswap a b) in H.
    + rewrite subjs_sswap. by apply gswap_disjoint_iff.
  - (* β *)
    rewrite !msswap_disj_union, !msswap_singleton.
    apply PStepBeta. by apply (tstep_eswap a b) in H.
  - (* fork *)
    rewrite !msswap_disj_union, !msswap_singleton, gswap_union,
      gswap_singleton. simpl.
    apply PStepFork.
    + by apply (tstep_eswap a b) in H.
    + by rewrite elem_of_gswap.
    + rewrite echans_msswap. by rewrite elem_of_gswap.
    + rewrite fchans_eswap. by rewrite elem_of_gswap.
  - (* msg *)
    rewrite !msswap_disj_union, !msswap_singleton.
    eapply PStepMsg.
    + by apply (tstep_eswap a b) in H.
    + by apply (tstep_eswap a b) in H0.
    + by rewrite elem_of_gswap.
  - (* close *)
    rewrite !msswap_disj_union, !msswap_singleton, gswap_difference,
      gswap_singleton.
    eapply PStepClose.
    + by apply (tstep_eswap a b) in H.
    + by apply (tstep_eswap a b) in H0.
    + by rewrite elem_of_gswap.
  - (* link *)
    rewrite (msswap_disj_union a b E), msswap_singleton, gswap_difference,
      gswap_singleton, echsubst_msswap, msswap_disj_union, msswap_singleton.
    apply PStepLink.
    + apply (tstep_eswap a b) in H. simpl in H.
      by rewrite gswap_upair in H.
    + by rewrite elem_of_gswap.
Qed.

Lemma pswap_involutive a b p : pswap a b (pswap a b p) = p.
Proof.
  destruct p as [C E]. unfold pswap; simpl.
  by rewrite gswap_involutive, msswap_involutive.
Qed.

Lemma proc_step_pswap_inv a b p π' q' :
  proc_step (pswap a b p) π' q' →
  ∃ π q, proc_step p π q ∧ π' = plswap a b π ∧ q' = pswap a b q.
Proof.
  intros Hst.
  pose proof (proc_step_pswap a b _ _ _ Hst) as Hst'.
  rewrite pswap_involutive in Hst'.
  eexists _, _. split_and!; [exact Hst'| |].
  - destruct π' as [|[c v|c v|c|cd]]; simpl;
      rewrite ?cswap_involutive, ?eswap_involutive, ?gswap_involutive; done.
  - by rewrite pswap_involutive.
Qed.

(** Remaining transport helpers. *)


Lemma gswap_intersection a b C1 C2 :
  gswap a b (C1 ∩ C2) = gswap a b C1 ∩ gswap a b C2.
Proof.
  apply set_eq; intros c. split.
  - intros Hc. unfold gswap in Hc.
    apply elem_of_map in Hc as (c1 & -> & Hc1).
    apply elem_of_intersection in Hc1 as [H1 H2].
    apply elem_of_intersection. split; by apply elem_of_gswap.
  - intros [H1 H2]%elem_of_intersection.
    apply elem_of_gswap' in H1.
    rewrite elem_of_gswap'. apply elem_of_intersection. split; [done|].
    by apply elem_of_gswap' in H2.
Qed.

Lemma msswap_empty a b : msswap a b (∅ : gmultiset expr) = ∅.
Proof. unfold echswap. apply gmultiset_map_empty. Qed.

Lemma senvswap_fmap a b (f : sty → sty) Σ :
  senvswap a b (f <$> Σ) = f <$> senvswap a b Σ.
Proof.
  apply map_eq. intros c.
  transitivity (senvswap a b (f <$> Σ) !! cswap a b (cswap a b c)).
  { by rewrite cswap_involutive. }
  rewrite lookup_kswap, !lookup_fmap.
  transitivity (f <$> (senvswap a b Σ !! cswap a b (cswap a b c)));
    [|by rewrite cswap_involutive].
  by rewrite lookup_kswap.
Qed.

Lemma senvswap_singleton a b c s :
  senvswap a b ({[c := s]} : senv) = {[cswap a b c := s]}.
Proof.
  rewrite <-!insert_empty. by rewrite senvswap_insert, senvswap_empty.
Qed.

Lemma elem_of_msswap a b e E :
  e ∈ msswap a b E ↔ ∃ e0, e = eswap a b e0 ∧ e0 ∈ E.
Proof. apply elem_of_gmultiset_map. Qed.

Lemma pswap_pair a b C E : pswap a b (C, E) = (gswap a b C, msswap a b E).
Proof. done. Qed.

(** Owner families transport along the swap. *)
Lemma Owners_pswap a b (P Q : senv → ty → proc → Prop) σ Σ T p :
  (∀ Σ' T' p', P Σ' T' p' → Q (senvswap a b Σ') T' (pswap a b p')) →
  Owners P σ Σ T p →
  Owners Q (senvswap a b σ) (senvswap a b Σ) T (pswap a b p).
Proof.
  intros HPQ Hpow.
  induction Hpow as [|σ0 d s Σd Σr Td Tr Tt Cd Ed Cr Er Hlk Hd1 Hd2 Hd3
                      Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 HP1 Hrec IH Hty].
  - rewrite senvswap_empty, pswap_pair, gswap_empty, msswap_empty.
    apply Owners_nil.
  - rewrite senvswap_insert, senvswap_union, pswap_pair, gswap_union,
      msswap_disj_union.
    eapply Owners_cons.
    + by rewrite lookup_kswap.
    + rewrite dom_kswap. by rewrite elem_of_gswap.
    + rewrite dom_kswap. by rewrite elem_of_gswap.
    + by rewrite elem_of_gswap.
    + by rewrite elem_of_gswap.
    + rewrite !dom_kswap. by apply gswap_disjoint_iff.
    + rewrite dom_kswap. by apply gswap_disjoint_iff.
    + by apply senvswap_disjoint.
    + by apply gswap_disjoint_iff.
    + rewrite dom_kswap. by apply gswap_disjoint_iff.
    + rewrite dom_kswap. by apply gswap_disjoint_iff.
    + rewrite <-senvswap_insert. exact (HPQ _ _ _ HP1).
    + exact IH.
    + exact Hty.
Qed.

(** ** Equivariance of the logical relation

    Every clause transports by applying the original clause at swapped
    inputs and swapping the output; involutivity cancels the round
    trip. *)
Lemma rel_eswap a b n :
  (∀ T Σ v, Vrel n Σ T v → Vrel n (senvswap a b Σ) T (eswap a b v)) ∧
  (∀ T Σ e, Erel n Σ T e → Erel n (senvswap a b Σ) T (eswap a b e)) ∧
  (∀ T Σ p, Prel n Σ T p → Prel n (senvswap a b Σ) T (pswap a b p)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ j, j < n → ∀ T Σ v, Vrel j Σ T v →
            Vrel j (senvswap a b Σ) T (eswap a b v)) as IHV
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ T Σ e, Erel j Σ T e →
            Erel j (senvswap a b Σ) T (eswap a b e)) as IHE
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ T Σ p, Prel j Σ T p →
            Prel j (senvswap a b Σ) T (pswap a b p)) as IHP
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ T Σ v, Vrel n Σ T v → Vrel n (senvswap a b Σ) T (eswap a b v))
    as HV.
  { induction T as [|T1 IH1 U1 IH2|T1 IH1 U1 IH2|T1 IH1 U1 IH2|T1 IH1|s];
      intros Σ v HVv.
    - apply Vrel_unit_iff in HVv as [-> ->].
      apply Vrel_unit_iff. by rewrite senvswap_empty.
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & H)|(k & -> & -> & Hk)].
      + apply Vrel_lolli_iff. left. exists (eswap a b eb).
        split_and!; [done|by rewrite fchans_eswap, dom_kswap, Hfc|].
        intros j Σ' w Hj Hd HVw.
        apply (senvswap_disjoint a b) in Hd.
        rewrite senvswap_involutive in Hd.
        specialize (H j (senvswap a b Σ') (eswap a b w) Hj Hd
                      (IHV j Hj _ _ _ HVw)).
        apply IHE in H; [|done].
        rewrite senvswap_union, senvswap_involutive in H.
        rewrite eswap_subst1, eswap_involutive in H.
        exact H.
      + apply Vrel_lolli_iff. right. exists k.
        split_and!; [done|by rewrite senvswap_empty|done].
    - apply Vrel_prod_iff in HVv
        as (v1 & v2 & Σ1 & Σ2 & -> & [-> Hd] & H1 & H2).
      apply Vrel_prod_iff.
      exists (eswap a b v1), (eswap a b v2), (senvswap a b Σ1), (senvswap a b Σ2).
      split_and!; [done| |by apply IH1|by apply IH2].
      split; [apply senvswap_union|by apply senvswap_disjoint].
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + by apply IH1.
      + by apply IH2.
    - apply Vrel_bang_iff in HVv as (-> & eb & -> & Hfc & H).
      apply Vrel_bang_iff. rewrite senvswap_empty.
      split; [done|]. exists (eswap a b eb).
      split_and!; [done|by rewrite fchans_eswap, Hfc, gswap_empty|].
      intros j Hj. specialize (H j Hj).
      apply IHE in H; [|done].
      rewrite senvswap_empty, eswap_subst1 in H.
      exact H.
    - apply Vrel_sess_iff in HVv as (c & s0 & -> & -> & Hu).
      apply Vrel_sess_iff. exists (cswap a b c), s0.
      split_and!; [done|apply senvswap_singleton|done]. }
  split_and!; [exact HV| |].
  - (* term relation *)
    intros T Σ e HE.
    destruct n as [|n']; [apply Erel_0|].
    apply Erel_S_iff in HE as (Hval & Hstep).
    apply Erel_S_iff. split_and!.
    { intros Hirr.
      apply HV, Hval. intros α e' Hst.
      exact (Hirr _ _ (tstep_eswap a b _ _ _ Hst)). }
    intros α' e'' Hst'.
    apply tstep_eswap_inv in Hst' as (α & e0' & Hst & -> & ->).
    specialize (Hstep α e0' Hst).
    destruct α as [|[c w|c w|c|cd]|c w]; simpl in Hstep |- *.
    + apply IHE; [lia|done].
    + (* recv *)
      destruct Hstep as (Σ1 & U & s & (s0 & -> & Hu) & Hc & H).
      exists (senvswap a b Σ1), U, s. split_and!.
      { exists s0. split; [apply senvswap_insert|done]. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      intros j Σ2 Hj Hd Hcd HVw.
      apply (senvswap_disjoint a b) in Hd. rewrite senvswap_involutive in Hd.
      assert (c ∉ dom (senvswap a b Σ2)) as Hcd'.
      { rewrite dom_kswap, elem_of_gswap'. exact Hcd. }
      apply IHV in HVw; [|lia]. rewrite eswap_involutive in HVw.
      specialize (H j (senvswap a b Σ2) Hj Hd Hcd' HVw).
      apply IHE in H; [|lia].
      rewrite senvswap_insert, senvswap_union, senvswap_involutive in H.
      exact H.
    + (* send *)
      destruct Hstep as (Σ1 & Σ2 & U & s & (s0 & -> & Hu) & Hd12 & Hc1
                         & Hc2 & HVw & HE').
      exists (senvswap a b Σ1), (senvswap a b Σ2), U, s. split_and!.
      { exists s0. split; [|done].
        by rewrite senvswap_insert, senvswap_union. }
      { by apply senvswap_disjoint. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { by apply HV. }
      apply IHE in HE'; [|lia]. rewrite senvswap_insert in HE'. exact HE'.
    + (* close *)
      destruct Hstep as (Σ1 & (s0 & -> & Hu) & Hc & HE').
      exists (senvswap a b Σ1). split_and!.
      { exists s0. split; [apply senvswap_insert|done]. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      apply IHE in HE'; [|lia]. exact HE'.
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & -> & Hcd & -> & Hc1 & Hd1
                         & Hdu & HE').
      exists (cswap a b c), (cswap a b d), (senvswap a b Σ1), sc, sd.
      split_and!.
      { apply gswap_upair. }
      { intros Heq. apply cswap_inj in Heq. done. }
      { by rewrite !senvswap_insert. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { done. }
      apply IHE in HE'; [|lia]. exact HE'.
    + (* fork *)
      intros Hcd.
      assert (c ∉ dom Σ) as Hcd0.
      { rewrite dom_kswap in Hcd. by rewrite elem_of_gswap in Hcd. }
      destruct (Hstep Hcd0) as (Σ1 & Σ2 & s & [-> Hd] & HVw & HE').
      exists (senvswap a b Σ1), (senvswap a b Σ2), s. split_and!.
      { split; [apply senvswap_union|by apply senvswap_disjoint]. }
      { by apply HV. }
      apply IHE in HE'; [|lia]. rewrite senvswap_insert in HE'. exact HE'.
  - (* process relation *)
    intros T Σ p HP.
    destruct n as [|n']; [apply Prel_0|].
    apply Prel_S_iff in HP as (Hirr & Hstep).
    apply Prel_S_iff. split_and!.
    { intros Hpirr.
      destruct Hirr as (v & E & -> & Hv & HVv & HE).
      { intros π q Hst.
        exact (Hpirr _ _ (proc_step_pswap a b _ _ _ Hst)). }
      rewrite pswap_pair, gswap_empty, msswap_disj_union, msswap_singleton.
      exists (eswap a b v), (msswap a b E). split_and!.
      + done.
      + by rewrite is_val_eswap.
      + by apply HV.
      + intros e He. apply elem_of_msswap in He as (e0 & -> & He0).
        by rewrite (HE e0 He0). }
    intros π' q' Hst'.
    apply proc_step_pswap_inv in Hst' as (π & q & Hst & -> & ->).
    specialize (Hstep π q Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* τ *)
      intros Hg. apply IHP; [lia|]. apply Hstep.
      destruct q as [Cq Eq]; simpl in *.
      rewrite dom_kswap in Hg. by apply gswap_disjoint_iff in Hg.
    + (* recv *)
      destruct Hstep as (Σ1 & U & s & (s0 & -> & Hu) & Hc & H).
      exists (senvswap a b Σ1), U, s. split_and!.
      { exists s0. split; [apply senvswap_insert|done]. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      intros j Σ2 Hj Hd Hcd Hfr HVw.
      apply (senvswap_disjoint a b) in Hd. rewrite senvswap_involutive in Hd.
      assert (c ∉ dom (senvswap a b Σ2)) as Hcd'.
      { rewrite dom_kswap, elem_of_gswap'. exact Hcd. }
      assert (dom (senvswap a b Σ2) ## p.1) as Hfr'.
      { destruct p as [Cp Ep]; simpl in *.
        rewrite dom_kswap. apply elem_of_disjoint; intros x H1 H2.
        apply elem_of_gswap' in H1.
        assert (cswap a b x ∈ gswap a b Cp) by (by apply elem_of_gswap).
        set_solver. }
      apply IHV in HVw; [|lia]. rewrite eswap_involutive in HVw.
      specialize (H j (senvswap a b Σ2) Hj Hd Hcd' Hfr' HVw).
      apply IHP in H; [|lia].
      rewrite senvswap_insert, senvswap_union, senvswap_involutive in H.
      exact H.
    + (* send *)
      destruct Hstep as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew
                         & T0 & Tw & (s0 & -> & Hu) & Hd0v & Hd0w & Hdvw
                         & Hc0 & Hcv & Hcw & Hdome & Hσed & Hcσe & HpC
                         & HC0w & HpE & HVw & HP0 & HPw & Hty).
      exists (senvswap a b Σ0), (senvswap a b Σv), U, s, (senvswap a b σe),
        (senvswap a b Σw), (gswap a b C0), (msswap a b E0), (gswap a b Cw),
        (msswap a b Ew), T0, Tw.
      split_and!.
      { exists s0. split; [|done].
        by rewrite senvswap_insert, !senvswap_union. }
      { by apply senvswap_disjoint. }
      { by apply senvswap_disjoint. }
      { by apply senvswap_disjoint. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { destruct p as [Cp Ep]; simpl in *.
        rewrite dom_kswap, fchans_eswap, Hdome.
        apply gswap_intersection. }
      { rewrite !dom_kswap. by apply gswap_disjoint_iff. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { destruct q as [Cq Eq]; simpl in *.
        rewrite HpC. apply gswap_union. }
      { by apply gswap_disjoint_iff. }
      { destruct q as [Cq Eq]; simpl in *.
        rewrite HpE. apply msswap_disj_union. }
      { apply HV in HVw.
        rewrite senvswap_union, senvswap_fmap in HVw. exact HVw. }
      { apply IHP in HP0; [|lia]. rewrite senvswap_insert in HP0.
        exact HP0. }
      { rewrite <-(pswap_pair a b Cw Ew).
        eapply Owners_pswap; [|exact HPw].
        intros Σ' T' p0 HP'. apply IHP; [lia|]. exact HP'. }
      { exact Hty. }
    + (* close *)
      destruct Hstep as (Σ1 & (s0 & -> & Hu) & Hc & HP').
      exists (senvswap a b Σ1). split_and!.
      { exists s0. split; [apply senvswap_insert|done]. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      apply IHP in HP'; [|lia]. exact HP'.
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & -> & Hcd & -> & Hc1 & Hd1
                         & Hdu & HP').
      exists (cswap a b c), (cswap a b d), (senvswap a b Σ1), sc, sd.
      split_and!.
      { apply gswap_upair. }
      { intros Heq. apply cswap_inj in Heq. done. }
      { by rewrite !senvswap_insert. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { rewrite dom_kswap. by rewrite elem_of_gswap. }
      { done. }
      apply IHP in HP'; [|lia]. exact HP'.
Qed.

(** The corollaries used downstream. *)
Lemma Vrel_eswap a b n Σ T v :
  Vrel n Σ T v → Vrel n (senvswap a b Σ) T (eswap a b v).
Proof. apply rel_eswap. Qed.

Lemma Erel_eswap a b n Σ T e :
  Erel n Σ T e → Erel n (senvswap a b Σ) T (eswap a b e).
Proof. apply rel_eswap. Qed.

Lemma Prel_eswap a b n Σ T p :
  Prel n Σ T p → Prel n (senvswap a b Σ) T (pswap a b p).
Proof. apply rel_eswap. Qed.

(** ** Identity and paper-equivalence facts for the forwarding step *)

(** A transposition of names foreign to a set or map is the identity. *)
Lemma gswap_id a b C : a ∉ C → b ∉ C → gswap a b C = C.
Proof.
  intros Ha Hb. apply set_eq; intros c. split.
  - intros Hc. unfold gswap in Hc.
    apply elem_of_map in Hc as (c1 & -> & Hc1).
    rewrite cswap_ne; [done|intros ->; done|intros ->; done].
  - intros Hc.
    assert (c ≠ a) by (intros ->; done).
    assert (c ≠ b) by (intros ->; done).
    rewrite <-(cswap_ne a b c); [|done|done]. by apply elem_of_gswap.
Qed.

Lemma senvswap_id a b Σ : a ∉ dom Σ → b ∉ dom Σ → senvswap a b Σ = Σ.
Proof.
  intros Ha Hb. apply not_elem_of_dom in Ha. apply not_elem_of_dom in Hb.
  apply map_eq; intros c.
  destruct (decide (c = a)) as [->|Hca].
  - assert (senvswap a b Σ !! a = Σ !! b) as ->.
    { rewrite <-(lookup_kswap a b Σ b). f_equal. symmetry. apply cswap_r. }
    congruence.
  - destruct (decide (c = b)) as [->|Hcb].
    + assert (senvswap a b Σ !! b = Σ !! a) as ->.
      { rewrite <-(lookup_kswap a b Σ a). f_equal. symmetry.
        apply cswap_l. }
      congruence.
    + assert (senvswap a b Σ !! c = Σ !! c) as -> ; [|done].
      rewrite <-(lookup_kswap a b Σ c). f_equal. symmetry.
      by apply cswap_ne.
Qed.

(** On soups where the surviving end does not occur, the transposition
    of the forwarding step IS the paper's one-sided substitution —
    typed configurations are channel-tight, so this covers them all. *)
Lemma chsubst_eswap c d e : d ∉ fchans e → eswap c d e = chsubst c d e.
Proof.
  induction e; simpl; intros Hd; f_equal; auto.
  all: try (first [apply IHe|apply IHe0|apply IHe1|apply IHe2|apply IHe3];
            set_solver).
  all: unfold cswap; repeat case_decide; simplify_eq; try done; set_solver.
Qed.

Lemma echswap_echsubst c d E :
  d ∉ echans E → echswap c d E = echsubst c d E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; intros Hd.
  - unfold echswap, echsubst. by rewrite !gmultiset_map_empty.
  - rewrite echans_disj_union, echans_singleton in Hd.
    unfold echswap, echsubst in *.
    rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton.
    rewrite chsubst_eswap by set_solver.
    rewrite IH by set_solver. done.
Qed.

(** ** Environments up to unfolding

    The relations read stored session types only through [unfoldS]
    (via [senv_hd] and the up-to-unfold channel clause of [Vdef]), so
    replacing every entry by one with the same unfolding is invisible.
    CONNECT's forwarding case uses this to trade the retargeted peer's
    [dual s] entry for the [sd] entry recorded by the link clause. *)

Definition senv_conv (Σ Σ' : senv) : Prop :=
  dom Σ = dom Σ' ∧
  ∀ c s s', Σ !! c = Some s → Σ' !! c = Some s' → unfoldS s = unfoldS s'.

Lemma senv_conv_refl Σ : senv_conv Σ Σ.
Proof. split; [done|]. intros c s s' H1 H2. by simplify_eq. Qed.

Lemma senv_conv_empty_inv Σ : senv_conv ∅ Σ → Σ = ∅.
Proof.
  intros [Hd _]. apply dom_empty_iff_L. by rewrite <-Hd, dom_empty_L.
Qed.

Lemma senv_conv_insert Σ Σ' c s s' :
  senv_conv Σ Σ' → unfoldS s = unfoldS s' →
  senv_conv (<[c := s]> Σ) (<[c := s']> Σ').
Proof.
  intros [Hd Hp] Hu. split.
  - by rewrite !dom_insert_L, Hd.
  - intros c0 t t'. destruct (decide (c0 = c)) as [->|Hne].
    + rewrite !lookup_insert_eq. intros. by simplify_eq.
    + rewrite !lookup_insert_ne by done. by apply Hp.
Qed.

Lemma senv_conv_union Σ1 Σ1' Σ2 Σ2' :
  senv_conv Σ1 Σ1' → senv_conv Σ2 Σ2' →
  senv_conv (Σ1 ∪ Σ2) (Σ1' ∪ Σ2').
Proof.
  intros [Hd1 Hp1] [Hd2 Hp2]. split.
  - by rewrite !dom_union_L, Hd1, Hd2.
  - intros c t t' Ht Ht'.
    apply lookup_union_Some_raw in Ht as [Ht|[H1N Ht]].
    + apply lookup_union_Some_raw in Ht' as [Ht'|[H1N' Ht']]; [eauto|].
      exfalso. apply (not_elem_of_dom Σ1' c) in H1N'.
      apply H1N'. rewrite <-Hd1. apply elem_of_dom. eauto.
    + apply lookup_union_Some_raw in Ht' as [Ht'|[H1N' Ht']]; [|eauto].
      exfalso. apply (not_elem_of_dom Σ1 c) in H1N.
      apply H1N. rewrite Hd1. apply elem_of_dom. eauto.
Qed.

(** Same-domain environments are interchangeable in disjointness. *)
Lemma senv_conv_disj Σ Σ' Θ :
  senv_conv Σ Σ' → Θ ##ₘ Σ ↔ Θ ##ₘ Σ'.
Proof.
  intros [Hd _]. rewrite !map_disjoint_dom, Hd. done.
Qed.

Lemma senv_conv_split Σ Σ' Σ1 Σ2 :
  senv_conv Σ Σ' → senv_split Σ Σ1 Σ2 →
  ∃ Σ1' Σ2', senv_split Σ' Σ1' Σ2' ∧ senv_conv Σ1 Σ1' ∧ senv_conv Σ2 Σ2'.
Proof.
  intros [Hd Hp] [-> Hdisj].
  exists (filter (λ kv, kv.1 ∈ dom Σ1) Σ'),
    (filter (λ kv, kv.1 ∉ dom Σ1) Σ').
  assert (∀ c, c ∈ dom Σ' ↔ c ∈ dom Σ1 ∨ c ∈ dom Σ2) as Hd'.
  { intros c. rewrite <-Hd, dom_union_L. set_solver. }
  assert (∀ c, c ∈ dom Σ1 → c ∉ dom Σ2) as H12.
  { apply map_disjoint_dom in Hdisj. set_solver. }
  split_and!.
  - split; [symmetry; apply map_filter_union_complement|].
    apply map_disjoint_filter_complement.
  - split.
    + apply set_eq. intros c. rewrite !elem_of_dom. split.
      * intros [t Ht].
        assert (is_Some (Σ' !! c)) as [t' Ht'].
        { apply elem_of_dom, Hd'. left. apply elem_of_dom. eauto. }
        exists t'. apply map_lookup_filter_Some. split; [done|]. simpl.
        apply elem_of_dom. eauto.
      * intros [t' Ht'].
        apply map_lookup_filter_Some in Ht' as [Ht' Hin]. simpl in Hin.
        by apply elem_of_dom in Hin.
    + intros c t t' Ht Ht'.
      apply map_lookup_filter_Some in Ht' as [Ht' _].
      eapply Hp; [|exact Ht']. by apply lookup_union_Some_l.
  - split.
    + apply set_eq. intros c. rewrite !elem_of_dom. split.
      * intros [t Ht].
        assert (is_Some (Σ' !! c)) as [t' Ht'].
        { apply elem_of_dom, Hd'. right. apply elem_of_dom. eauto. }
        exists t'. apply map_lookup_filter_Some. split; [done|]. simpl.
        intros Hc1. eapply H12; [exact Hc1|]. apply elem_of_dom. eauto.
      * intros [t' Ht'].
        apply map_lookup_filter_Some in Ht' as [Ht' Hnin]. simpl in Hnin.
        assert (c ∈ dom Σ2) as Hc2.
        { destruct (proj1 (Hd' c)) as [Hc1|Hc2];
            [apply elem_of_dom; eauto|done|done]. }
        by apply elem_of_dom in Hc2.
    + intros c t t' Ht Ht'.
      apply map_lookup_filter_Some in Ht' as [Ht' Hnin]. simpl in Hnin.
      eapply Hp; [|exact Ht'].
      rewrite lookup_union_r; [done|].
      by apply not_elem_of_dom.
Qed.

Lemma senv_conv_hd Σ Σ' c u Σ1 :
  c ∉ dom Σ1 → senv_conv Σ Σ' → senv_hd Σ c u Σ1 →
  ∃ Σ1', senv_hd Σ' c u Σ1' ∧ c ∉ dom Σ1' ∧ senv_conv Σ1 Σ1'.
Proof.
  intros Hc [Hd Hp] (s0 & -> & Hu).
  assert (is_Some (Σ' !! c)) as [s0' Hs0'].
  { apply elem_of_dom. rewrite <-Hd, dom_insert_L. set_solver. }
  exists (delete c Σ'). split_and!.
  - exists s0'. split; [by rewrite insert_delete_id|].
    rewrite <-Hu. symmetry. eapply Hp; [|exact Hs0'].
    apply lookup_insert_eq.
  - rewrite dom_delete_L. set_solver.
  - split.
    + rewrite dom_delete_L, <-Hd, dom_insert_L. set_solver.
    + intros c0 t t' Ht Ht'.
      apply lookup_delete_Some in Ht' as [Hne Ht'].
      eapply Hp; [|exact Ht'].
      rewrite lookup_insert_ne; [done|].
      intros ->. apply Hc. by apply elem_of_dom.
Qed.

Lemma senv_conv_ins2 Σ' c sc d sd Σ1 :
  c ≠ d → c ∉ dom Σ1 → d ∉ dom Σ1 →
  senv_conv (<[c := sc]> (<[d := sd]> Σ1)) Σ' →
  ∃ sc' sd' Σ1',
    Σ' = <[c := sc']> (<[d := sd']> Σ1') ∧
    unfoldS sc' = unfoldS sc ∧ unfoldS sd' = unfoldS sd ∧
    c ∉ dom Σ1' ∧ d ∉ dom Σ1' ∧ senv_conv Σ1 Σ1'.
Proof.
  intros Hcd Hc1 Hd1 Hconv.
  pose proof Hconv as [Hd Hp].
  assert (is_Some (Σ' !! c)) as [sc' Hsc'].
  { apply elem_of_dom. rewrite <-Hd, !dom_insert_L. set_solver. }
  assert (is_Some (Σ' !! d)) as [sd' Hsd'].
  { apply elem_of_dom. rewrite <-Hd, !dom_insert_L. set_solver. }
  exists sc', sd', (delete d (delete c Σ')). split_and!.
  - apply map_eq; intros c0.
    destruct (decide (c0 = c)) as [->|Hne1].
    + rewrite lookup_insert_eq. done.
    + rewrite lookup_insert_ne by done.
      destruct (decide (c0 = d)) as [->|Hne2].
      * rewrite lookup_insert_eq. done.
      * rewrite lookup_insert_ne by done.
        rewrite !lookup_delete_ne by done. done.
  - symmetry. eapply Hp; [|exact Hsc']. apply lookup_insert_eq.
  - symmetry. eapply Hp; [|exact Hsd'].
    rewrite lookup_insert_ne by done. apply lookup_insert_eq.
  - rewrite !dom_delete_L. set_solver.
  - rewrite !dom_delete_L. set_solver.
  - split.
    + rewrite !dom_delete_L, <-Hd, !dom_insert_L. set_solver.
    + intros c0 t t' Ht Ht'.
      apply lookup_delete_Some in Ht' as [Hne2 Ht'].
      apply lookup_delete_Some in Ht' as [Hne1 Ht'].
      eapply Hp; [|exact Ht'].
      rewrite !lookup_insert_ne; [done| |]; intros ->.
      * apply Hd1. by apply elem_of_dom.
      * apply Hc1. by apply elem_of_dom.
Qed.

Lemma Owners_conv (P Q : senv → ty → proc → Prop) σ Σ Σ' T p :
  (∀ Σ1 Σ1' T' p', senv_conv Σ1 Σ1' → P Σ1 T' p' → Q Σ1' T' p') →
  senv_conv Σ Σ' → Owners P σ Σ T p → Owners Q σ Σ' T p.
Proof.
  intros HPQ Hconv Hpow. revert Σ' Hconv.
  induction Hpow as [|σ0 d s Σd Σr Td Tr Tt Cd Ed Cr Er Hlk Hd1 Hd2 Hd3
                      Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 HP1 Hrec IH Hty];
    intros Σ' Hconv.
  - rewrite (senv_conv_empty_inv _ Hconv). apply Owners_nil.
  - destruct (senv_conv_split _ _ _ _ Hconv (conj eq_refl Hd7))
      as (Σd' & Σr' & [-> Hdisj'] & Hcd & Hcr).
    eapply Owners_cons;
      rewrite <-?(proj1 Hcd), <-?(proj1 Hcr); try done.
    + eapply HPQ; [|exact HP1].
      apply senv_conv_insert; [done|done].
    + by apply IH.
Qed.

(** ** The relations read Σ up to unfolding

    Same induction shape as [rel_eswap]; the term/process is unchanged
    and every clause's Σ facts transport along [senv_conv]. *)
Lemma rel_conv n :
  (∀ T Σ Σ' v, senv_conv Σ Σ' → Vrel n Σ T v → Vrel n Σ' T v) ∧
  (∀ T Σ Σ' e, senv_conv Σ Σ' → Erel n Σ T e → Erel n Σ' T e) ∧
  (∀ T Σ Σ' p, senv_conv Σ Σ' → Prel n Σ T p → Prel n Σ' T p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ j, j < n → ∀ T Σ Σ' v, senv_conv Σ Σ' → Vrel j Σ T v →
            Vrel j Σ' T v) as IHV by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ T Σ Σ' e, senv_conv Σ Σ' → Erel j Σ T e →
            Erel j Σ' T e) as IHE by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ T Σ Σ' p, senv_conv Σ Σ' → Prel j Σ T p →
            Prel j Σ' T p) as IHP by (intros j Hj; apply (IHn j Hj)).
  assert (∀ T Σ Σ' v, senv_conv Σ Σ' → Vrel n Σ T v → Vrel n Σ' T v)
    as HV.
  { induction T as [|T1 IH1 U1 IH2|T1 IH1 U1 IH2|T1 IH1 U1 IH2|T1 IH1|s];
      intros Σ Σ' v Hconv HVv.
    - apply Vrel_unit_iff in HVv as [-> ->].
      apply Vrel_unit_iff. by rewrite (senv_conv_empty_inv _ Hconv).
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & H)|(k & -> & -> & Hk)].
      + apply Vrel_lolli_iff. left. exists eb.
        split_and!; [done|by rewrite Hfc, (proj1 Hconv)|].
        intros j Σ2 w Hj Hd HVw.
        eapply IHE;
          [lia|apply senv_conv_union; [exact Hconv|apply senv_conv_refl]|].
        apply H; [lia| |exact HVw].
        by rewrite (senv_conv_disj _ _ Σ2 Hconv).
      + apply Vrel_lolli_iff. right. exists k.
        split_and!; [done|by rewrite (senv_conv_empty_inv _ Hconv)|done].
    - apply Vrel_prod_iff in HVv
        as (v1 & v2 & Σ1 & Σ2 & -> & Hsp & H1 & H2).
      destruct (senv_conv_split _ _ _ _ Hconv Hsp)
        as (Σ1' & Σ2' & Hsp' & Hc1 & Hc2).
      apply Vrel_prod_iff. exists v1, v2, Σ1', Σ2'.
      split_and!; eauto.
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]); eauto.
    - apply Vrel_bang_iff in HVv as (-> & eb & -> & Hfc & H).
      apply Vrel_bang_iff.
      rewrite (senv_conv_empty_inv _ Hconv). eauto 10.
    - apply Vrel_sess_iff in HVv as (c & s0 & -> & -> & Hu).
      assert (senv_hd ({[c := s0]} : senv) c (unfoldS s0) ∅) as Hhd.
      { by exists s0. }
      assert (c ∉ dom (∅ : senv)) as Hce by set_solver.
      destruct (senv_conv_hd _ _ _ _ _ Hce Hconv Hhd)
        as (Σ1' & (s0' & -> & Hu') & _ & Hc1).
      rewrite (senv_conv_empty_inv _ Hc1).
      apply Vrel_sess_iff. exists c, s0'.
      split_and!; [done|apply insert_empty|congruence]. }
  split_and!; [exact HV| |].
  - (* term relation *)
    intros T Σ Σ' e Hconv HE.
    destruct n as [|n']; [apply Erel_0|].
    apply Erel_S_iff in HE as (Hval & Hstep).
    apply Erel_S_iff. split_and!.
    { intros Hirr. eapply HV; [done|]. by apply Hval. }
    intros α e' Hst. specialize (Hstep α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c w]; simpl in Hstep |- *.
    + eapply IHE; [lia|done|done].
    + (* recv *)
      destruct Hstep as (Σ1 & U & s & Hhd & Hc & H).
      destruct (senv_conv_hd _ _ _ _ _ Hc Hconv Hhd)
        as (Σ1' & Hhd' & Hc' & Hc1).
      exists Σ1', U, s. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd HVw.
      eapply IHE;
        [lia|apply senv_conv_insert;
          [apply senv_conv_union; [exact Hc1|apply senv_conv_refl]|done]|].
      apply H; auto.
      by rewrite (senv_conv_disj _ _ Σ2 Hc1).
    + (* send *)
      destruct Hstep as (Σ1 & Σ2 & U & s & Hhd & Hd12 & Hc1 & Hc2
                         & HVw & HE').
      assert (c ∉ dom (Σ1 ∪ Σ2)) as Hcr.
      { rewrite dom_union_L. set_solver. }
      destruct (senv_conv_hd _ _ _ _ _ Hcr Hconv Hhd)
        as (ΣR' & Hhd' & HcR' & HcR).
      destruct (senv_conv_split _ _ _ _ HcR (conj eq_refl Hd12))
        as (Σ1' & Σ2' & [-> Hd'] & Hs1 & Hs2).
      exists Σ1', Σ2', U, s. split_and!.
      { done. }
      { done. }
      { by rewrite <-(proj1 Hs1). }
      { by rewrite <-(proj1 Hs2). }
      { eapply HV; [exact Hs2|done]. }
      eapply IHE; [lia|apply senv_conv_insert; [exact Hs1|done]|done].
    + (* close *)
      destruct Hstep as (Σ1 & Hhd & Hc & HE').
      destruct (senv_conv_hd _ _ _ _ _ Hc Hconv Hhd)
        as (Σ1' & Hhd' & Hc' & Hc1).
      exists Σ1'. split_and!; [done|done|].
      eapply IHE; [lia|exact Hc1|done].
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & -> & Hcd & -> & Hcx & Hdx
                         & Hdu & HE').
      destruct (senv_conv_ins2 _ _ _ _ _ _ Hcd Hcx Hdx Hconv)
        as (sc' & sd' & Σ1' & -> & Huc & Hud & Hcx' & Hdx' & Hc1).
      exists c, d, Σ1', sc', sd'.
      split_and!; [done|done|done|done|done| |].
      { rewrite Hud, Hdu, <-!dual_unfoldS, Huc. done. }
      eapply IHE; [lia|exact Hc1|done].
    + (* fork *)
      intros Hcd.
      assert (c ∉ dom Σ) as Hcd0 by (by rewrite (proj1 Hconv)).
      destruct (Hstep Hcd0) as (Σ1 & Σ2 & sf & Hsp & HVw & HE').
      destruct (senv_conv_split _ _ _ _ Hconv Hsp)
        as (Σ1' & Σ2' & Hsp' & Hs1 & Hs2).
      exists Σ1', Σ2', sf. split_and!.
      { done. }
      { eapply HV; [exact Hs1|done]. }
      eapply IHE; [lia|apply senv_conv_insert; [exact Hs2|done]|done].
  - (* process relation *)
    intros T Σ Σ' p Hconv HP.
    destruct n as [|n']; [apply Prel_0|].
    apply Prel_S_iff in HP as (Hirr & Hstep).
    apply Prel_S_iff. split_and!.
    { intros Hpirr.
      destruct (Hirr Hpirr) as (v & E & -> & Hv & HVv & HE).
      exists v, E. split_and!; [done|done| |done].
      eapply HV; [exact Hconv|done]. }
    intros π p' Hst. specialize (Hstep π p' Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* τ *)
      intros Hg. eapply IHP; [lia|exact Hconv|].
      apply Hstep. by rewrite (proj1 Hconv).
    + (* recv *)
      destruct Hstep as (Σ1 & U & s & Hhd & Hc & H).
      destruct (senv_conv_hd _ _ _ _ _ Hc Hconv Hhd)
        as (Σ1' & Hhd' & Hc' & Hc1).
      exists Σ1', U, s. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd Hfr HVw.
      eapply IHP;
        [lia|apply senv_conv_insert;
          [apply senv_conv_union; [exact Hc1|apply senv_conv_refl]|done]|].
      apply H; auto.
      by rewrite (senv_conv_disj _ _ Σ2 Hc1).
    + (* send *)
      destruct Hstep as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew
                         & T0 & Tw & Hhd & Hd0v & Hd0w & Hdvw & Hc0 & Hcv
                         & Hcw & Hdome & Hσed & Hcσe & HpC & HC0w & HpE
                         & HVw & HP0 & HPw & Hty).
      assert (c ∉ dom (Σ0 ∪ Σv ∪ Σw)) as Hcr.
      { rewrite !dom_union_L. set_solver. }
      destruct (senv_conv_hd _ _ _ _ _ Hcr Hconv Hhd)
        as (ΣR' & Hhd' & HcR' & HcR).
      assert (Σ0 ∪ Σv ##ₘ Σw) as Hd0vw.
      { by apply map_disjoint_union_l. }
      destruct (senv_conv_split _ _ (Σ0 ∪ Σv) Σw HcR (conj eq_refl Hd0vw))
        as (Σ0v' & Σw' & [-> HdA] & Hs0v & Hsw).
      destruct (senv_conv_split _ _ Σ0 Σv Hs0v (conj eq_refl Hd0v))
        as (Σ0' & Σv' & [-> HdB] & Hs0 & Hsv).
      exists Σ0', Σv', U, s, σe, Σw', C0, E0, Cw, Ew, T0, Tw.
      split_and!.
      { done. }
      { done. }
      { apply map_disjoint_union_l in HdA as [? ?]. done. }
      { apply map_disjoint_union_l in HdA as [? ?]. done. }
      { by rewrite <-(proj1 Hs0). }
      { by rewrite <-(proj1 Hsv). }
      { by rewrite <-(proj1 Hsw). }
      { done. }
      { rewrite <-(proj1 Hconv). done. }
      { done. }
      { done. }
      { done. }
      { done. }
      { eapply HV; [|exact HVw].
        apply senv_conv_union; [exact Hsv|apply senv_conv_refl]. }
      { eapply IHP; [lia|apply senv_conv_insert; [exact Hs0|done]|done]. }
      { eapply Owners_conv; [|exact Hsw|exact HPw].
        intros ΣA ΣA' TA pA HcA HPA. eapply IHP; [lia|exact HcA|done]. }
      { done. }
    + (* close *)
      destruct Hstep as (Σ1 & Hhd & Hc & HP').
      destruct (senv_conv_hd _ _ _ _ _ Hc Hconv Hhd)
        as (Σ1' & Hhd' & Hc' & Hc1).
      exists Σ1'. split_and!; [done|done|].
      eapply IHP; [lia|exact Hc1|done].
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & -> & Hcd & -> & Hcx & Hdx
                         & Hdu & HP').
      destruct (senv_conv_ins2 _ _ _ _ _ _ Hcd Hcx Hdx Hconv)
        as (sc' & sd' & Σ1' & -> & Huc & Hud & Hcx' & Hdx' & Hc1).
      exists c, d, Σ1', sc', sd'.
      split_and!; [done|done|done|done|done| |].
      { rewrite Hud, Hdu, <-!dual_unfoldS, Huc. done. }
      eapply IHP; [lia|exact Hc1|done].
Qed.

Lemma Prel_conv n Σ Σ' T p :
  senv_conv Σ Σ' → Prel n Σ T p → Prel n Σ' T p.
Proof. apply rel_conv. Qed.

(** The single-entry instance used by CONNECT's forwarding case. *)
Lemma Prel_entry_conv n Σ c t t' T p :
  unfoldS t = unfoldS t' →
  Prel n (<[c := t]> Σ) T p → Prel n (<[c := t']> Σ) T p.
Proof.
  intros Hu. apply Prel_conv.
  apply senv_conv_insert; [apply senv_conv_refl|done].
Qed.

(** ** The two orientations of a forwarding between restricted ends

    P-Act-Link reads its label as an unordered pair, so when BOTH ends
    are restricted the rule fires in two ways: retire [c] and retarget
    everything to [d], or retire [d] and retarget to [c].  The two
    outcomes are not equal as configurations, but they are the same
    configuration up to the transposition [c ↔ d], and the relation is
    invariant under transpositions ([Prel_eswap]).  So one orientation
    being related gives the other for free, and a proof may always pick
    the convenient one. *)

Lemma gswap_diff_swap (C : gset chan) c d :
  c ≠ d → c ∈ C → d ∈ C → gswap c d (C ∖ {[d]}) = C ∖ {[c]}.
Proof.
  intros Hne Hc Hd. apply set_eq. intros x.
  rewrite elem_of_gswap'.
  destruct (decide (x = c)) as [->|Hxc].
  { rewrite cswap_l. clear -Hne Hd. set_solver. }
  destruct (decide (x = d)) as [->|Hxd].
  { rewrite cswap_r. clear -Hne Hc Hd. set_solver. }
  rewrite cswap_ne by done. clear -Hxc Hxd. set_solver.
Qed.

Lemma Prel_link_orient n Σ T C E c d :
  c ≠ d → c ∈ C → d ∈ C → c ∉ dom Σ → d ∉ dom Σ →
  Prel n Σ T (C ∖ {[d]}, echsubst d c E) →
  Prel n Σ T (C ∖ {[c]}, echsubst c d E).
Proof.
  intros Hne Hc Hd HcΣ HdΣ HP.
  pose proof (Prel_eswap c d _ _ _ _ HP) as HP'.
  rewrite senvswap_id in HP' by done.
  rewrite pswap_pair, gswap_diff_swap, echswap_echsubst_flip in HP' by done.
  exact HP'.
Qed.
