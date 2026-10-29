(** * LTS renaming: transpositions of channel names (§10)

    A transposition of two channel names, applied to terms, labels,
    restricted sets and soups, maps transitions to transitions and
    preserves safety. Adequacy uses it for runs whose [new] steps pick
    names the world already knows: such a run is, step by step, a
    renaming of a run whose fresh names avoid any given finite set
    ([frun_rename]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Safety.

(** ** Transposition commutes with the de Bruijn operations *)

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

(** A transposition of two names a term does not mention is the
    identity. *)
Lemma eswap_fresh a b e : a ∉ fchans e → b ∉ fchans e → eswap a b e = e.
Proof.
  induction e; simpl; intros Ha Hb; f_equal;
    try (apply IHe || apply IHe1 || apply IHe2 || apply IHe3); try set_solver.
  apply cswap_ne; set_solver.
Qed.

(** ** Sets *)

Definition gswap (a b : chan) (C : gset chan) : gset chan :=
  set_map (cswap a b) C.

Lemma elem_of_gswap a b c C : cswap a b c ∈ gswap a b C ↔ c ∈ C.
Proof.
  unfold gswap. rewrite elem_of_map. split.
  - intros (c' & Heq & Hc'). apply cswap_inj in Heq. by subst.
  - intros Hc. by exists c.
Qed.

Lemma elem_of_gswap' a b c C : c ∈ gswap a b C ↔ cswap a b c ∈ C.
Proof.
  split.
  - intros (c1 & -> & Hc1)%elem_of_map. by rewrite cswap_involutive.
  - intros Hc. rewrite <-(cswap_involutive a b c). by apply elem_of_gswap.
Qed.

Lemma gswap_involutive a b C : gswap a b (gswap a b C) = C.
Proof.
  apply set_eq. intros c. rewrite !elem_of_gswap', cswap_involutive. done.
Qed.

Lemma gswap_upair a b c d :
  gswap a b ({[c; d]} : gset chan) = {[cswap a b c; cswap a b d]}.
Proof.
  unfold gswap. by rewrite set_map_union_L, !set_map_singleton_L.
Qed.

Lemma gswap_union a b C1 C2 :
  gswap a b (C1 ∪ C2) = gswap a b C1 ∪ gswap a b C2.
Proof. unfold gswap. apply set_map_union_L. Qed.

Lemma gswap_singleton a b c : gswap a b ({[c]} : gset chan) = {[cswap a b c]}.
Proof. unfold gswap. apply set_map_singleton_L. Qed.

Lemma gswap_empty a b : gswap a b (∅ : gset chan) = ∅.
Proof. unfold gswap. apply set_eq; intros c. set_solver. Qed.

Lemma gswap_difference a b C1 C2 :
  gswap a b (C1 ∖ C2) = gswap a b C1 ∖ gswap a b C2.
Proof.
  apply set_eq; intros c.
  rewrite elem_of_difference, !elem_of_gswap', elem_of_difference. done.
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

Lemma gswap_fresh a b C : a ∉ C → b ∉ C → gswap a b C = C.
Proof.
  intros Ha Hb. apply set_eq; intros c. rewrite elem_of_gswap'.
  destruct (decide (c = a)) as [->|?]; [rewrite cswap_l; set_solver|].
  destruct (decide (c = b)) as [->|?]; [rewrite cswap_r; set_solver|].
  by rewrite cswap_ne.
Qed.

Lemma fchans_eswap a b e : fchans (eswap a b e) = gswap a b (fchans e).
Proof.
  induction e; simpl; unfold gswap in *;
    rewrite ?IHe, ?IHe0, ?IHe1, ?IHe2, ?IHe3; set_solver.
Qed.

(** ** Labels *)

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
  | LNew c => LNew (cswap a b c)
  | LSpawn v => LSpawn (eswap a b v)
  end.

Definition plswap (a b : chan) (π : plabel) : plabel :=
  match π with
  | PTau => PTau
  | PSess σ => PSess (slswap a b σ)
  end.

Lemma subjs_sswap a b σ : subjs (slswap a b σ) = gswap a b (subjs σ).
Proof. destruct σ; simpl; try (by rewrite gswap_singleton). done. Qed.

Lemma sentc_sswap a b σ : sentc (slswap a b σ) = gswap a b (sentc σ).
Proof. destruct σ; simpl; rewrite ?fchans_eswap, ?gswap_empty; done. Qed.

(** ** The term LTS is equivariant *)

Lemma head_step_eswap a b e α e' :
  head_step e α e' →
  head_step (eswap a b e) (tlswap a b α) (eswap a b e').
Proof.
  destruct 1; simpl; rewrite ?eswap_subst1, ?eswap_subst2, ?gswap_upair;
    constructor; rewrite ?is_val_eswap; done.
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
Qed.

(** ** Soups and processes *)

Notation msswap := echswap.

Definition pswap (a b : chan) (p : proc) : proc :=
  (gswap a b p.1, msswap a b p.2).

Lemma msswap_disj_union a b E1 E2 :
  msswap a b (E1 ⊎ E2) = msswap a b E1 ⊎ msswap a b E2.
Proof. apply gmultiset_map_disj_union. Qed.

Lemma msswap_singleton a b e :
  msswap a b ({[+ e +]} : gmultiset expr) = {[+ eswap a b e +]}.
Proof. apply gmultiset_map_singleton. Qed.

Lemma msswap_empty a b : msswap a b (∅ : gmultiset expr) = ∅.
Proof. apply gmultiset_map_empty. Qed.

Lemma msswap_involutive a b E : msswap a b (msswap a b E) = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !msswap_empty.
  - rewrite !msswap_disj_union, !msswap_singleton, IH.
    by rewrite eswap_involutive.
Qed.

Lemma msswap_fresh a b E : a ∉ echans E → b ∉ echans E → msswap a b E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [by rewrite msswap_empty|].
  rewrite echans_disj_union, echans_singleton. intros Ha Hb.
  rewrite msswap_disj_union, msswap_singleton, IH by set_solver.
  rewrite eswap_fresh by set_solver. done.
Qed.

Lemma echans_msswap a b E : echans (msswap a b E) = gswap a b (echans E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - rewrite msswap_empty, !echans_empty. by rewrite gswap_empty.
  - rewrite msswap_disj_union, msswap_singleton.
    rewrite !echans_disj_union, !echans_singleton, IH, fchans_eswap.
    by rewrite gswap_union.
Qed.

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

Lemma pswap_involutive a b p : pswap a b (pswap a b p) = p.
Proof.
  destruct p as [C E]. unfold pswap; simpl.
  by rewrite gswap_involutive, msswap_involutive.
Qed.

Lemma pswap_fresh a b (p : proc) :
  a ∉ p.1 → b ∉ p.1 → a ∉ echans p.2 → b ∉ echans p.2 → pswap a b p = p.
Proof.
  destruct p as [C E]. unfold pswap; simpl. intros.
  by rewrite gswap_fresh, msswap_fresh.
Qed.

(** ** The process LTS is equivariant *)

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
  - (* new *)
    rewrite !msswap_disj_union, !msswap_singleton, gswap_union,
      gswap_singleton.
    apply PStepNew.
    + by apply (tstep_eswap a b) in H.
    + by rewrite elem_of_gswap.
    + rewrite echans_msswap. by rewrite elem_of_gswap.
    + rewrite fchans_eswap. by rewrite elem_of_gswap.
  - (* spawn *)
    rewrite !msswap_disj_union, !msswap_singleton. simpl.
    apply PStepSpawn. by apply (tstep_eswap a b) in H.
  - (* msg *)
    rewrite !msswap_disj_union, !msswap_singleton.
    eapply PStepMsg.
    + by apply (tstep_eswap a b) in H.
    + by apply (tstep_eswap a b) in H0.
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

Lemma preduction_pswap a b p q :
  preduction p q → preduction (pswap a b p) (pswap a b q).
Proof. intros H. exact (proc_step_pswap a b _ _ _ H). Qed.

Lemma nsteps_pswap a b m p q :
  nsteps preduction m p q → nsteps preduction m (pswap a b p) (pswap a b q).
Proof.
  induction 1; [constructor|]. econstructor; [|done].
  by apply preduction_pswap.
Qed.

(** ** Safety is equivariant *)

Lemma terminated_pswap a b p : terminated p → terminated (pswap a b p).
Proof.
  intros (v & E & -> & Hv & HE). unfold pswap; simpl.
  assert (msswap a b E = E) as HEq.
  { apply msswap_fresh; intros (e & He & Hc)%elem_of_echans;
      rewrite (HE e He) in Hc; set_solver. }
  exists (eswap a b v), E. split_and!; [|by rewrite is_val_eswap|done].
  by rewrite gswap_empty, msswap_disj_union, msswap_singleton, HEq.
Qed.

Lemma safe_pswap a b p : safe p → safe (pswap a b p).
Proof.
  intros [Ht|[q Hq]]; [left; by apply terminated_pswap|right].
  exists (pswap a b q). by apply preduction_pswap.
Qed.

Lemma safe_pswap_iff a b p : safe (pswap a b p) ↔ safe p.
Proof.
  split; [|apply safe_pswap].
  intros H. rewrite <-(pswap_involutive a b p). by apply safe_pswap.
Qed.

(** ** Runs with fresh names

    [frun N m p q]: an m-step run from p to q in which every [new]
    picks a name outside N, and N grows by the names created. *)

Inductive frun : gset chan → nat → proc → proc → Prop :=
  | frun_0 N p : frun N 0 p p
  | frun_S N m p q r :
      preduction p q →
      q.1 ∖ p.1 ## N →
      frun (N ∪ (q.1 ∖ p.1)) m q r →
      frun N (S m) p r.

(** Every run is a renaming of a run with fresh names, up to safety
    of its last state. *)
Lemma frun_rename m : ∀ N p r,
  nsteps preduction m p r → ∃ r', frun N m p r' ∧ (safe r' → safe r).
Proof.
  induction m as [|m IH]; intros N p r Hr.
  { inversion Hr; subst. exists r. split; [constructor|done]. }
  inversion Hr as [|? ? q ? Hpq Hqr]; subst.
  inversion Hpq as [| | C E e c e' Hst HcC HcE Hce| | | |]; subst.
  1,3,4,5,6:
    (* no name is created: q.1 ⊆ p.1 *)
    (match type of Hpq with preduction ?P ?Q =>
       destruct (IH (N ∪ (Q.1 ∖ P.1)) Q r Hqr) as (r' & Hrun & Hsafe) end;
     exists r'; split; [|done];
     econstructor; [exact Hpq| |exact Hrun]; simpl; set_solver).
  (* new: rename c to a name z outside N, then continue *)
  destruct (exist_fresh (N ∪ C ∪ echans E ∪ fchans e ∪ {[c]})) as [z Hz].
  assert (z ∉ N ∧ z ∉ C ∧ z ∉ echans E ∧ z ∉ fchans e ∧ z ≠ c)
    as (HzN & HzC & HzE & Hze & Hzc) by (clear -Hz; set_solver).
  clear Hz.
  assert (pswap c z (C, E ⊎ {[+ e +]}) = (C, E ⊎ {[+ e +]})) as Hp.
  { apply pswap_fresh; simpl; rewrite ?echans_disj_union, ?echans_singleton;
      [done|done|clear -HcE Hce; set_solver|clear -HzE Hze; set_solver]. }
  assert (preduction (C, E ⊎ {[+ e +]})
            (pswap c z (C ∪ {[c]}, E ⊎ {[+ e' +]}))) as Hpq'.
  { rewrite <-Hp at 1. by apply preduction_pswap. }
  assert ((pswap c z (C ∪ {[c]}, E ⊎ {[+ e' +]})).1 = C ∪ {[z]}) as Hq1.
  { unfold pswap; simpl. rewrite gswap_union, gswap_singleton, cswap_l.
    by rewrite gswap_fresh. }
  destruct (IH (N ∪ ((C ∪ {[z]}) ∖ C))
              (pswap c z (C ∪ {[c]}, E ⊎ {[+ e' +]})) (pswap c z r))
    as (r' & Hrun & Hsafe).
  { by apply nsteps_pswap. }
  exists r'. split.
  - econstructor; [exact Hpq'| |rewrite Hq1; exact Hrun].
    rewrite Hq1. simpl. clear -HzN. set_solver.
  - intros Hs. apply (safe_pswap_iff c z). by apply Hsafe.
Qed.

(** A τ step creates at most one channel. *)
Lemma preduction_chans p q :
  preduction p q → q.1 ⊆ p.1 ∨ ∃ c, c ∉ p.1 ∧ q.1 = p.1 ∪ {[c]}.
Proof.
  inversion 1; subst; simpl; [left; set_solver|right; eauto|left; set_solver..].
Qed.

(** ** α-variants

    [alpha p q]: q arises from p by renaming restricted names of p to
    names p does not mention, one at a time. Every other name is
    fixed. *)

Inductive alpha : proc → proc → Prop :=
  | alpha_refl p : alpha p p
  | alpha_step p q a b :
      a ∈ p.1 → b ∉ p.1 → b ∉ echans p.2 →
      alpha (pswap a b p) q → alpha p q.

Lemma cswap_conj a b c d z :
  cswap a b (cswap c d z) = cswap (cswap a b c) (cswap a b d) (cswap a b z).
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma eswap_conj a b c d e :
  eswap a b (eswap c d e) = eswap (cswap a b c) (cswap a b d) (eswap a b e).
Proof. induction e; simpl; f_equal; auto using cswap_conj. Qed.

Lemma gswap_conj a b c d C :
  gswap a b (gswap c d C) = gswap (cswap a b c) (cswap a b d) (gswap a b C).
Proof.
  apply set_eq. intros z. rewrite !elem_of_gswap'.
  rewrite <-(cswap_involutive a b z) at 2.
  rewrite <-cswap_conj, cswap_involutive. done.
Qed.

Lemma msswap_conj a b c d E :
  msswap a b (msswap c d E) = msswap (cswap a b c) (cswap a b d) (msswap a b E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !msswap_empty.
  - rewrite !msswap_disj_union, !msswap_singleton, IH. by rewrite eswap_conj.
Qed.

Lemma pswap_conj a b c d p :
  pswap a b (pswap c d p) = pswap (cswap a b c) (cswap a b d) (pswap a b p).
Proof. unfold pswap. simpl. by rewrite gswap_conj, msswap_conj. Qed.

Lemma alpha_pswap a b p q : alpha p q → alpha (pswap a b p) (pswap a b q).
Proof.
  induction 1 as [p|p q c d Hc Hd HdE _ IH]; [constructor|].
  apply (alpha_step _ _ (cswap a b c) (cswap a b d)).
  - destruct p; simpl in *. by apply elem_of_gswap.
  - destruct p; simpl in *. by rewrite elem_of_gswap.
  - destruct p; simpl in *. rewrite echans_msswap. by rewrite elem_of_gswap.
  - by rewrite <-pswap_conj.
Qed.

Lemma alpha_trans p q r : alpha p q → alpha q r → alpha p r.
Proof.
  induction 1; [done|]. intros Hr. econstructor; eauto.
Qed.
