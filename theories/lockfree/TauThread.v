(** * No τ-divergence, thread by thread

    [no_tau_divergence] (LiveAdequacy.v) speaks about the whole process.
    Lock freedom needs it for one thread: a thread that never takes a
    channel step takes finitely many administrative steps, whatever the
    other threads do meanwhile. The measure is the accessibility of the
    thread's term with every channel name erased ([cerase]). Erasing
    the names makes the measure blind to the renaming of a link
    ([cerase_emap]) and to the choice of fresh names at [new]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Instr liveness.LiveAdequacy.

(** ** Renaming commutes with substitution and with steps *)

Lemma emap_ext g h e : (∀ c, g c = h c) → emap g e = emap h e.
Proof. intros H. induction e; simpl; f_equal; auto. Qed.

Lemma emap_rename g r e : emap g (rename r e) = rename r (emap g e).
Proof. revert r. induction e; intros r; simpl; f_equal; auto. Qed.

Lemma emap_up g σ x : emap g (up σ x) = up (λ y, emap g (σ y)) x.
Proof. destruct x; simpl; [done|]. unfold compose. apply emap_rename. Qed.

Lemma emap_subst g σ e : emap g (subst σ e) = subst (λ x, emap g (σ x)) (emap g e).
Proof.
  revert σ. induction e; intros σ; simpl; f_equal; auto.
  all: rewrite ?IHe, ?IHe0, ?IHe1, ?IHe2, ?IHe3.
  all: apply subst_ext; intros x;
    first [apply emap_up
          |etrans; [apply emap_up|]; apply up_ext; intros ?; apply emap_up].
Qed.

Lemma emap_subst1 g v e : emap g (subst1 v e) = subst1 (emap g v) (emap g e).
Proof. unfold subst1. rewrite emap_subst. apply subst_ext. by intros [|x]. Qed.

Lemma emap_subst2 g u v e : emap g (subst2 u v e) = subst2 (emap g u) (emap g v) (emap g e).
Proof. unfold subst2. rewrite emap_subst. apply subst_ext. by intros [|[|x]]. Qed.

Definition smap (g : chan → chan) (σ : slabel) : slabel :=
  match σ with
  | SRecv c v => SRecv (g c) (emap g v)
  | SSend c v => SSend (g c) (emap g v)
  | SClos c => SClos (g c)
  | SLink cd => SLink (set_map g cd)
  | SSel c b => SSel (g c) b
  | SBra c b => SBra (g c) b
  end.

Definition lmap (g : chan → chan) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LSess σ => LSess (smap g σ)
  | LNew c => LNew (g c)
  | LSpawn v => LSpawn (emap g v)
  end.

Lemma head_step_emap g e α e' : head_step e α e' → head_step (emap g e) (lmap g α) (emap g e').
Proof.
  destruct 1; simpl; rewrite ?emap_subst1, ?emap_subst2.
  all: try (constructor; by rewrite ?is_val_emap).
  - by destruct b; constructor.
  - replace (set_map g {[c; d]} : gset chan) with ({[g c; g d]} : gset chan) by set_solver.
    constructor.
Qed.

Lemma tstep_emap g e α e' : tstep e α e' → tstep (emap g e) (lmap g α) (emap g e').
Proof.
  induction 1; simpl.
  - constructor. by apply head_step_emap.
  - by apply TStepAppL.
  - apply TStepAppR; [by rewrite is_val_emap|done].
  - by apply TStepPairL.
  - apply TStepPairR; [by rewrite is_val_emap|done].
  - by apply TStepLetU.
  - by apply TStepLetP.
  - by apply TStepInj1.
  - by apply TStepInj2.
  - by apply TStepCase.
Qed.

(** ** Erasing every channel name *)

Definition cerase : expr → expr := emap (λ _, "").

Lemma cerase_emap g e : cerase (emap g e) = cerase e.
Proof. unfold cerase. rewrite emap_emap. by apply emap_ext. Qed.

Lemma cerase_idem e : cerase (cerase e) = cerase e.
Proof. apply cerase_emap. Qed.

(** A head redex only steps at its head. *)
Lemma head_tstep e α e' α2 e2 : head_step e α e' → tstep e α2 e2 → head_step e α2 e2.
Proof.
  intros H1 H2. inversion H1; subst; inversion H2; subst; try done.
  all: exfalso; (eapply val_no_tstep; [eassumption|]); simpl;
    repeat (apply andb_True; split); done.
Qed.

(** Steps are deterministic up to the names of channels. *)
Lemma tstep_det_cerase e α1 e1 α2 e2 :
  tstep e α1 e1 → tstep e α2 e2 → lmap (λ _, "") α1 = lmap (λ _, "") α2 →
  cerase e1 = cerase e2.
Proof.
  intros H1. revert α2 e2. induction H1 as [e α e' Hh|e1 α e1' e2 Hs IH|v e2 α e2' Hv Hs IH
    |e1 α e1' e2 Hs IH|v e2 α e2' Hv Hs IH|e1 α e1' e2 Hs IH|e1 α e1' e2 Hs IH
    |e α e' Hs IH|e α e' Hs IH|e α e' e1 e2 Hs IH]; intros α2 g2 H2 Hl.
  - pose proof (head_tstep _ _ _ _ _ Hh H2) as Hh2.
    inversion Hh; subst; inversion Hh2; subst; simpl in *; simplify_eq; try done.
    all: unfold cerase in *; simpl; rewrite ?Hl; try done.
  - apply tstep_app_inv in H2 as [(g1 & Hg & ->)|[(Hval & _)|(Hval & _)]].
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eauto using val_no_tstep.
    + exfalso. eauto using val_no_tstep.
  - apply tstep_app_inv in H2 as [(g1 & Hg & ->)|[(_ & g1 & Hg & ->)|(_ & Hval & _)]].
    + exfalso. eauto using val_no_tstep.
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eauto using val_no_tstep.
  - apply tstep_pair_inv in H2 as [(g1 & Hg & ->)|(Hval & _)].
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eauto using val_no_tstep.
  - apply tstep_pair_inv in H2 as [(g1 & Hg & ->)|(_ & g1 & Hg & ->)].
    + exfalso. eauto using val_no_tstep.
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
  - apply tstep_letu_inv in H2 as [(g1 & Hg & ->)|(-> & _)].
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eapply val_no_tstep; [eassumption|done].
  - apply tstep_letp_inv in H2 as [(g1 & Hg & ->)|(u & w & -> & Hu & Hw & _)].
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eapply val_no_tstep; [eassumption|]. simpl. by apply andb_True.
  - apply tstep_inj1_inv in H2 as (g1 & Hg & ->).
    unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
  - apply tstep_inj2_inv in H2 as (g1 & Hg & ->).
    unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
  - apply tstep_case_inv in H2 as [(g1 & Hg & ->)|[(w & -> & Hw & _)|(w & -> & Hw & _)]].
    + unfold cerase in *; simpl. f_equal. exact (IH _ _ Hg Hl).
    + exfalso. eapply val_no_tstep; [eassumption|done].
    + exfalso. eapply val_no_tstep; [eassumption|done].
Qed.

(** ** The measure *)

(** One administrative step of an erased term, erased again. *)
Definition tR (y x : expr) : Prop :=
  ∃ α x', admin_lbl α ∧ tstep x α x' ∧ y = cerase x'.

Lemma tR_step e α e' : admin_lbl α → tstep e α e' → tR (cerase e') (cerase e).
Proof.
  intros Hα Hs. exists (lmap (λ _, "") α), (cerase e'). split_and!.
  - by destruct α.
  - by apply tstep_emap.
  - by rewrite cerase_idem.
Qed.

(** An admin-accessible process has admin-accessible threads. *)
Lemma padmin_acc_thread q :
  Acc (λ y x, padmin x y) q → ∀ E e, q.2 = E ⊎ {[+ e +]} → Acc tR (cerase e).
Proof.
  induction 1 as [[C E0] _ IH]. intros E e HE. simpl in HE. subst E0.
  constructor. intros y (α & x' & Hα & Hst & ->).
  destruct (act_step _ _ _ Hst) as (a' & Ha' & Ho). unfold cerase in Ha'.
  rewrite act_emap in Ha'. destruct (act e) as [a|] eqn:Ha; [|done]. simpl in Ha'.
  simplify_eq. destruct a; simpl in Ho; destruct α as [|σ|c1|w];
    try (exfalso; exact Ho); try (exfalso; exact Hα).
  - (* β *)
    destruct (act_offer e ABeta LBeta Ha I) as [e' He'].
    assert (cerase x' = cerase e') as ->.
    { rewrite <-(cerase_idem e'). eapply tstep_det_cerase; [exact Hst|by apply tstep_emap|done]. }
    apply (IH (C, E ⊎ {[+ e' +]}) (PABeta C E e e' He') E e' eq_refl).
  - (* new, at a globally fresh name *)
    set (c0 := fresh (C ∪ echans E ∪ fchans e)).
    assert (c0 ∉ C ∪ echans E ∪ fchans e) as Hc0 by apply is_fresh.
    destruct (act_offer e ANew (LNew c0) Ha I) as [e' He'].
    assert (cerase x' = cerase e') as ->.
    { rewrite <-(cerase_idem e'). eapply tstep_det_cerase; [exact Hst|by apply tstep_emap|done]. }
    assert (c0 ∉ C) by (clear -Hc0; set_solver).
    assert (c0 ∉ echans E) by (clear -Hc0; set_solver).
    assert (c0 ∉ fchans e) by (clear -Hc0; set_solver).
    apply (IH (C ∪ {[c0]}, E ⊎ {[+ e' +]}) (PANew C E e c0 e' He' H H0 H1) E e' eq_refl).
  - (* spawn *)
    subst w. destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e' He'].
    assert (cerase x' = cerase e') as ->.
    { rewrite <-(cerase_idem e'). eapply tstep_det_cerase; [exact Hst|by apply tstep_emap|].
      simpl. unfold cerase. by rewrite emap_emap. }
    apply (IH (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}) (PASpawn C E e v e' He')
      (E ⊎ {[+ App v EUnit +]}) e').
    simpl. multiset_solver.
Qed.

(** Every thread of every reachable configuration is admin-accessible. *)
Theorem thread_acc p q s e :
  no_tau_divergence p → pred_star p (erase q) → q.2 !! s = Some e → Acc tR (cerase e).
Proof.
  intros Hnd Hr He. apply (padmin_acc_thread (erase q) (Hnd _ Hr) (soup (delete s q.2))).
  simpl. by apply soup_delete.
Qed.
