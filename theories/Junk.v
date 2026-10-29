(** * Junk renaming (§10)

    The paper's Junk.v, with the world fixed. Renaming a channel that a
    related process does not own (a "junk" name, absent from the
    interface and the restricted set, though possibly present in the
    syntax) into an arbitrary other name preserves the process
    relation. An interface-fresh channel can never act (every clause
    that would observe it demands an interface entry), so its
    occurrences are inert. Worlds mention no channels, so the world
    stays as it is.

    This file holds the syntax and the step correspondence of a
    channel substitution; the transport of the relation follows. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Chain Renaming.

(** ** Substitution on channels, labels, and label sets *)

Definition csub (x b c : chan) : chan := if decide (c = x) then b else c.

Definition gsub (x b : chan) (C : gset chan) : gset chan :=
  set_map (csub x b) C.

Definition ssub (x b : chan) (σ : slabel) : slabel :=
  match σ with
  | SRecv c v => SRecv (csub x b c) (chsubst x b v)
  | SSend c v => SSend (csub x b c) (chsubst x b v)
  | SClos c => SClos (csub x b c)
  | SLink cd => SLink (gsub x b cd)
  end.

Definition lsub (x b : chan) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LSess σ => LSess (ssub x b σ)
  | LNew c => LNew (csub x b c)
  | LSpawn v => LSpawn (chsubst x b v)
  end.

Lemma csub_hit x b : csub x b x = b.
Proof. unfold csub. by case_decide. Qed.

Lemma csub_ne x b c : c ≠ x → csub x b c = c.
Proof. intros. unfold csub. by case_decide. Qed.

Lemma chsubst_chan x b c : chsubst x b (Chan c) = Chan (csub x b c).
Proof. done. Qed.

Lemma gsub_upair x b c d :
  gsub x b ({[c; d]} : gset chan) = {[csub x b c; csub x b d]}.
Proof.
  unfold gsub. by rewrite set_map_union_L, !set_map_singleton_L.
Qed.

(** ** Pure syntax facts *)

Lemma chsubst_refl c e : chsubst c c e = e.
Proof.
  induction e; simpl; f_equal; auto. by case_decide; subst.
Qed.

Lemma fchans_chsubst_notin x b e : x ≠ b → x ∉ fchans (chsubst x b e).
Proof.
  intros Hne Hin. apply fchans_chsubst in Hin. set_solver.
Qed.

Lemma fchans_chsubst_sup x b e : fchans e ⊆ fchans (chsubst x b e) ∪ {[x]}.
Proof.
  induction e; simpl; try set_solver. case_decide; set_solver.
Qed.

Lemma fchans_chsubst_hit x b e :
  x ∈ fchans e → b ∈ fchans (chsubst x b e).
Proof.
  induction e; simpl; try set_solver. case_decide; set_solver.
Qed.

Lemma echans_echsubst_hit x b E :
  x ∈ echans E → b ∈ echans (echsubst x b E).
Proof.
  intros (e & He & Hx)%elem_of_echans. apply elem_of_echans.
  exists (chsubst x b e). split; [|by apply fchans_chsubst_hit].
  unfold echsubst. apply elem_of_gmultiset_map. by exists e.
Qed.

Lemma eswap_id a b e : a ∉ fchans e → b ∉ fchans e → eswap a b e = e.
Proof. apply eswap_fresh. Qed.

(** chsubst commutes with the de Bruijn operations. *)
Lemma chsubst_rename x b r e :
  chsubst x b (rename r e) = rename r (chsubst x b e).
Proof. revert r. induction e; intros r; simpl; f_equal; auto. Qed.

Lemma chsubst_up x b σ y :
  chsubst x b (up σ y) = up (λ z, chsubst x b (σ z)) y.
Proof.
  destruct y; simpl; [done|]. unfold compose. apply chsubst_rename.
Qed.

Lemma chsubst_subst x b σ e :
  chsubst x b (subst σ e) = subst (λ y, chsubst x b (σ y)) (chsubst x b e).
Proof.
  revert σ. induction e; intros σ; simpl; f_equal; auto.
  all: rewrite ?IHe, ?IHe0, ?IHe1, ?IHe2, ?IHe3.
  all: apply subst_ext; intros y;
    first [apply chsubst_up
          |etrans; [apply chsubst_up|]; apply up_ext; intros ?;
           apply chsubst_up].
Qed.

Lemma chsubst_subst1 x b v e :
  chsubst x b (subst1 v e) = subst1 (chsubst x b v) (chsubst x b e).
Proof.
  unfold subst1. rewrite chsubst_subst. apply subst_ext.
  by intros [|y].
Qed.

Lemma chsubst_subst2 x b u v e :
  chsubst x b (subst2 u v e)
  = subst2 (chsubst x b u) (chsubst x b v) (chsubst x b e).
Proof.
  unfold subst2. rewrite chsubst_subst. apply subst_ext.
  by intros [|[|y]].
Qed.

(** Commutation of two channel substitutions with distinct sources,
    the second one's source untouched by the first (covers both a
    disjoint pair and a shared target). *)
Lemma chsubst_comm x b c d e :
  c ≠ x → d ≠ x → b ≠ c →
  chsubst x b (chsubst c d e) = chsubst c d (chsubst x b e).
Proof.
  intros. induction e; simpl; f_equal; auto.
  unfold csub in *. repeat case_decide; congruence.
Qed.

(** Chaining through the junk name: first retargeting c to x, then
    renaming x to b, is renaming both c and x to b. *)
Lemma chsubst_chain x b c e :
  c ≠ x → b ≠ x → b ≠ c →
  chsubst x b (chsubst c x e) = chsubst c b (chsubst x b e).
Proof.
  intros. induction e; simpl; f_equal; auto.
  unfold csub in *. repeat case_decide; congruence.
Qed.

(** Multiset liftings. *)
Lemma echsubst_comm x b c d E :
  c ≠ x → d ≠ x → b ≠ c →
  echsubst x b (echsubst c d E) = echsubst c d (echsubst x b E).
Proof.
  intros. unfold echsubst.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite chsubst_comm.
Qed.

Lemma echsubst_chain x b c E :
  c ≠ x → b ≠ x → b ≠ c →
  echsubst x b (echsubst c x E) = echsubst c b (echsubst x b E).
Proof.
  intros. unfold echsubst.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite chsubst_chain.
Qed.

(** Collapse: retargeting b to x and then renaming x to b restores
    b's occurrences and takes x's along — the same as renaming x to b
    outright. *)
Lemma chsubst_collapse x b e :
  chsubst x b (chsubst b x e) = chsubst x b e.
Proof.
  induction e; simpl; f_equal; auto.
  unfold csub. repeat case_decide; congruence.
Qed.

Lemma echsubst_collapse x b E :
  echsubst x b (echsubst b x E) = echsubst x b E.
Proof.
  unfold echsubst.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite chsubst_collapse.
Qed.

Lemma echsubst_refl c E : echsubst c c E = E.
Proof.
  unfold echsubst.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite gmultiset_map_empty.
  - rewrite gmultiset_map_disj_union, gmultiset_map_singleton, IH.
    by rewrite chsubst_refl.
Qed.

Lemma echans_echsubst_notin x b E : x ≠ b → x ∉ echans (echsubst x b E).
Proof.
  intros Hne Hin. apply elem_of_echans in Hin as (e' & He' & Hx).
  unfold echsubst in He'.
  apply elem_of_gmultiset_map in He' as (e & -> & _).
  by eapply fchans_chsubst_notin.
Qed.

Lemma echans_echsubst_sup x b E :
  echans E ⊆ echans (echsubst x b E) ∪ {[x]}.
Proof.
  intros y Hy. apply elem_of_echans in Hy as (e & He & Hy).
  destruct (decide (y = x)); [set_solver|].
  apply elem_of_union; left. apply elem_of_echans.
  exists (chsubst x b e). split.
  - unfold echsubst. apply elem_of_gmultiset_map. by exists e.
  - pose proof (fchans_chsubst_sup x b e). set_solver.
Qed.

(** Splitting a substituted soup: every decomposition of the image is
    the image of a decomposition. *)
Lemma echsubst_decomp x b E F' f' :
  echsubst x b E = F' ⊎ {[+ f' +]} →
  ∃ F f, E = F ⊎ {[+ f +]} ∧ F' = echsubst x b F ∧ f' = chsubst x b f.
Proof.
  intros Heq.
  assert (f' ∈ echsubst x b E) as Hin by (rewrite Heq; multiset_solver).
  unfold echsubst in Hin.
  apply elem_of_gmultiset_map in Hin as (f & -> & Hf).
  exists (E ∖ {[+ f +]}), f.
  assert (E = E ∖ {[+ f +]} ⊎ {[+ f +]}) as HE by multiset_solver.
  split_and!; [done| |done].
  rewrite HE in Heq.
  rewrite echsubst_disj_union, echsubst_singleton in Heq.
  multiset_solver.
Qed.

(** ** Forward step correspondence

    Substituted terms simulate the original's steps, except that a
    forwarding pair {x, b} would collapse into a singleton (that case
    is excluded by a side condition; against a related process it
    contradicts the forwarding clause). *)

Lemma head_step_chsubst x b e α e' :
  head_step e α e' →
  head_step (chsubst x b e) (lsub x b α) (chsubst x b e').
Proof.
  intros Hst. destruct Hst; simpl;
    rewrite ?chsubst_subst1, ?chsubst_subst2, ?gsub_upair;
    constructor; rewrite ?is_val_chsubst; done.
Qed.

Lemma tstep_chsubst x b e α e' :
  tstep e α e' →
  tstep (chsubst x b e) (lsub x b α) (chsubst x b e').
Proof.
  intros Hst. induction Hst; simpl.
  - apply TStepHead. by apply head_step_chsubst.
  - apply TStepAppL. by apply IHHst.
  - apply TStepAppR; [by rewrite is_val_chsubst|by apply IHHst].
  - apply TStepPairL. by apply IHHst.
  - apply TStepPairR; [by rewrite is_val_chsubst|by apply IHHst].
  - apply TStepLetU. by apply IHHst.
  - apply TStepLetP. by apply IHHst.
  - apply TStepInj1. by apply IHHst.
  - apply TStepInj2. by apply IHHst.
  - apply TStepCase. by apply IHHst.
Qed.

(** ** Backward step correspondence

    Every step of the substituted term is the image of a step of the
    original. For deterministic labels (β, send, close, forwarding) the
    label and continuation are exact images. The receptive labels
    (receive, fork) quantify over incoming values respectively fresh
    names, which need not be images; those get tailored statements. *)

Definition det_label (α : tlabel) : Prop :=
  match α with
  | LBeta | LSpawn _ | LSess (SSend _ _) | LSess (SClos _) | LSess (SLink _) => True
  | _ => False
  end.

Lemma tstep_chsubst_det_inv x b e α' f' :
  tstep (chsubst x b e) α' f' → det_label α' →
  ∃ α f, tstep e α f ∧ α' = lsub x b α ∧ f' = chsubst x b f.
Proof.
  intros Hst Hdet.
  remember (chsubst x b e) as g eqn:Hg.
  revert e Hg. induction Hst; intros e0 Hg.
  - (* head step *)
    destruct H; destruct e0; simplify_eq/=.
    + (* β *)
      destruct e0_1; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
      { done. }
      by rewrite chsubst_subst1.
    + (* let unit *)
      destruct e0_1; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor. }
      { done. }
      done.
    + (* let pair *)
      destruct e0_1; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor; by rewrite is_val_chsubst in *. }
      { done. }
      by rewrite chsubst_subst2.
    + (* new: not a deterministic label *)
      done.
    + (* spawn *)
      destruct e0_1; simplify_eq/=.
      eexists (LSpawn e0_2), EUnit. split_and!.
      { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
      { done. }
      done.
    + (* recv: not a deterministic label *)
      done.
    + (* send *)
      destruct e0_1; simplify_eq/=.
      destruct e0_2; simplify_eq/=.
      destruct e0_2_2; simplify_eq/=.
      eexists (LSess (SSend c0 e0_2_1)), _. split_and!.
      { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
      { done. }
      done.
    + (* close *)
      destruct e0_1; simplify_eq/=.
      destruct e0_2; simplify_eq/=.
      eexists (LSess (SClos c0)), EUnit. split_and!.
      { apply TStepHead. constructor. }
      { done. }
      done.
    + (* case inj1 *)
      destruct e0_1; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
      { done. }
      by rewrite chsubst_subst1.
    + (* case inj2 *)
      destruct e0_1; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
      { done. }
      by rewrite chsubst_subst1.
    + (* force *)
      destruct e0_1; simplify_eq/=.
      destruct e0_2; simplify_eq/=.
      eexists LBeta, _. split_and!.
      { apply TStepHead. constructor. }
      { done. }
      by rewrite chsubst_subst1.
    + (* link *)
      destruct e0_1; simplify_eq/=.
      destruct e0_2; simplify_eq/=.
      destruct e0_2_1; simplify_eq/=. destruct e0_2_2; simplify_eq/=.
      eexists (LSess (SLink {[c0; c]})), EUnit. split_and!.
      { apply TStepHead. constructor. }
      { simpl. by rewrite gsub_upair. }
      done.
  - (* congruence: App left *)
    destruct e0; simplify_eq/=.
    + destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
      eexists _, (App f e0_2). split_and!; [|done|done].
      by apply TStepAppL.
  - (* App right *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (App e0_1 f). split_and!; [|done|done].
    apply TStepAppR; [by rewrite is_val_chsubst in H|done].
  - (* Pair left *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Pair f e0_2). split_and!; [|done|done].
    by apply TStepPairL.
  - (* Pair right *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Pair e0_1 f). split_and!; [|done|done].
    apply TStepPairR; [by rewrite is_val_chsubst in H|done].
  - (* LetU *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (LetU f e0_2). split_and!; [|done|done].
    by apply TStepLetU.
  - (* LetP *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (LetP f e0_2). split_and!; [|done|done].
    by apply TStepLetP.
  - (* Inj1 *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Inj1 f). split_and!; [|done|done]. by apply TStepInj1.
  - (* Inj2 *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Inj2 f). split_and!; [|done|done]. by apply TStepInj2.
  - (* Case *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Case f e0_2 e0_3). split_and!; [|done|done].
    by apply TStepCase.
Qed.

(** ** Backward correspondence for the receptive labels

    A receive accepts every value and a fork every name, so a step of
    the substituted term at value w (name c) need not be the image of a
    step at the same value (name). Instead: the original steps at any
    value (name) the caller chooses, and the two continuations differ
    by exactly the substitution plus the chosen value (name). *)

Lemma fchans_chsubst_other x b c e :
  c ∉ fchans e → c ≠ b → c ∉ fchans (chsubst x b e).
Proof.
  intros Hc Hb Hin. apply fchans_chsubst in Hin. set_solver.
Qed.

(** Internal form: the received value is itself an image (a message
    from a substituted sibling). *)
Lemma tstep_chsubst_recv_inv_subst x b e c w f' :
  tstep (chsubst x b e) (LSess (SRecv c (chsubst x b w))) f' →
  ∃ c0 f, csub x b c0 = c ∧
    tstep e (LSess (SRecv c0 w)) f ∧ f' = chsubst x b f.
Proof.
  intros Hst.
  remember (chsubst x b e) as g eqn:Hg.
  remember (LSess (SRecv c (chsubst x b w))) as lab eqn:Hlab.
  revert e Hg. induction Hst; intros e0 Hg.
  - (* head step *)
    destruct H; simplify_eq/=.
    destruct e0; simplify_eq/=.
    destruct e0_1; simplify_eq/=.
    destruct e0_2; simplify_eq/=.
    exists c0, (Pair w (Chan c0)). split_and!; [done| |done].
    apply TStepHead. constructor. by rewrite is_val_chsubst in H.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (App f e0_2). split_and!; [done| |done].
    by apply TStepAppL.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (App e0_1 f). split_and!; [done| |done].
    apply TStepAppR; [by rewrite is_val_chsubst in H|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Pair f e0_2). split_and!; [done| |done].
    by apply TStepPairL.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Pair e0_1 f). split_and!; [done| |done].
    apply TStepPairR; [by rewrite is_val_chsubst in H|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (LetU f e0_2). split_and!; [done| |done].
    by apply TStepLetU.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (LetP f e0_2). split_and!; [done| |done].
    by apply TStepLetP.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Inj1 f). split_and!; [done| |done]. by apply TStepInj1.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Inj2 f). split_and!; [done| |done]. by apply TStepInj2.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Case f e0_2 e0_3). split_and!; [done| |done].
    by apply TStepCase.
Qed.

(** External form: the received value is arbitrary and may mention the
    junk name x; the original instead receives its α-variant with x
    transposed to a globally fresh z, and the continuations differ by
    the substitution followed by that transposition. *)
Lemma tstep_chsubst_recv_inv_swap x b z e c w' f' :
  x ≠ b → z ≠ x → z ≠ b → z ∉ fchans w' →
  tstep (chsubst x b e) (LSess (SRecv c w')) f' →
  z ∉ fchans e →
  ∃ c0 f, csub x b c0 = c ∧
    tstep e (LSess (SRecv c0 (eswap x z w'))) f ∧
    f' = eswap x z (chsubst x b f).
Proof.
  intros Hxb Hzx Hzb Hzw Hst.
  remember (chsubst x b e) as g eqn:Hg.
  remember (LSess (SRecv c w')) as lab eqn:Hlab.
  revert e Hg. induction Hst; intros e0 Hg Hze.
  - (* head step *)
    destruct H; simplify_eq/=.
    destruct e0; simplify_eq/=.
    destruct e0_1; simplify_eq/=.
    destruct e0_2; simplify_eq/=.
    exists c0, (Pair (eswap x z w') (Chan c0)). split_and!; [done| |].
    { apply TStepHead. constructor.
      by rewrite is_val_eswap. }
    simpl.
    rewrite (chsubst_id x b (eswap x z w')); last first.
    { rewrite fchans_eswap. rewrite elem_of_gswap'.
      rewrite cswap_l. done. }
    rewrite eswap_involutive.
    f_equal. f_equal. unfold cswap, csub in *.
    repeat case_decide; simplify_eq; try done; set_solver.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (App f e0_2). split_and!; [done|by apply TStepAppL|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (App e0_1 f).
    split_and!;
      [done|apply TStepAppR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Pair f e0_2). split_and!; [done|by apply TStepPairL|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Pair e0_1 f).
    split_and!;
      [done|apply TStepPairR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (LetU f e0_2). split_and!; [done|by apply TStepLetU|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (LetP f e0_2). split_and!; [done|by apply TStepLetP|].
    simpl. f_equal.
    rewrite eswap_id; [done|by apply fchans_chsubst_notin|].
    apply fchans_chsubst_other; [set_solver|done].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Inj1 f). split_and!; [done|by apply TStepInj1|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Inj2 f). split_and!; [done|by apply TStepInj2|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Case f e0_2 e0_3).
    split_and!; [done|by apply TStepCase|].
    simpl. f_equal.
    all: rewrite eswap_id;
      [done|by apply fchans_chsubst_notin|
       apply fchans_chsubst_other; [set_solver|done]].
Qed.

(** New: the substituted term creates c; the original creates any
    sufficiently fresh name c0 the caller chooses, and the
    continuations differ by the substitution followed by retargeting
    c0 to c. *)
Lemma tstep_chsubst_new_inv x b e c f' :
  tstep (chsubst x b e) (LNew c) f' →
  ∀ c0, c0 ∉ fchans e → c0 ≠ x → c0 ≠ b →
    ∃ f, tstep e (LNew c0) f ∧ f' = chsubst c0 c (chsubst x b f).
Proof.
  intros Hst.
  remember (chsubst x b e) as g eqn:Hg.
  remember (LNew c) as lab eqn:Hlab.
  revert e Hg. induction Hst; intros e0 Hg c0 Hc0e Hc0x Hc0b.
  - (* head step *)
    destruct H; simplify_eq/=.
    destruct e0; simplify_eq/=.
    destruct e0_1; simplify_eq/=. destruct e0_2; simplify_eq/=.
    exists (Pair (Chan c0) (Chan c0)). split.
    { apply TStepHead. constructor. }
    simpl. unfold csub. repeat case_decide; congruence.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (App f e0_2). split; [by apply TStepAppL|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (App e0_1 f).
    split; [apply TStepAppR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (Pair f e0_2). split; [by apply TStepPairL|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (Pair e0_1 f).
    split; [apply TStepPairR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (LetU f e0_2). split; [by apply TStepLetU|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (LetP f e0_2). split; [by apply TStepLetP|].
    simpl. f_equal. rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [done|done|done|].
    eexists (Inj1 f). split; [by apply TStepInj1|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [done|done|done|].
    eexists (Inj2 f). split; [by apply TStepInj2|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl c0) as (f & Hf & ->); [set_solver|done|done|].
    eexists (Case f e0_2 e0_3). split; [by apply TStepCase|].
    simpl. f_equal.
    all: rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
Qed.

(** ** Auxiliary facts for the transport *)

Lemma echsubst_empty x b : echsubst x b (∅ : gmultiset expr) = ∅.
Proof. apply gmultiset_map_empty. Qed.

Lemma subjs_ssub x b σ : subjs (ssub x b σ) = gsub x b (subjs σ).
Proof.
  destruct σ; simpl; try done.
  all: unfold gsub; by rewrite set_map_singleton_L.
Qed.

Lemma gsub_id x b cd : x ∉ cd → gsub x b cd = cd.
Proof.
  intros Hx. apply set_eq. intros y. unfold gsub. rewrite elem_of_map.
  split.
  - intros (y0 & -> & Hy0). rewrite csub_ne; [done|]. set_solver.
  - intros Hy. exists y. split; [|done].
    rewrite csub_ne; [done|]. set_solver.
Qed.

Lemma Vrel_chsubst_id n W Θ U w x b :
  x ∉ dom Θ → Vrel n W Θ U w → chsubst x b w = w.
Proof.
  intros Hx HV. apply chsubst_id.
  rewrite (Vrel_fchans _ _ _ _ _ HV). exact Hx.
Qed.

(** τ-step inversion into the six underlying rules. *)
Lemma ptau_inv C E p' :
  proc_step (C, E) PTau p' →
  (∃ F e e', E = F ⊎ {[+ e +]} ∧ tstep e LBeta e' ∧
     p' = (C, F ⊎ {[+ e' +]}))
  ∨ (∃ F e c e', E = F ⊎ {[+ e +]} ∧ tstep e (LNew c) e' ∧
       c ∉ C ∧ c ∉ echans F ∧ c ∉ fchans e ∧
       p' = (C ∪ {[c]}, F ⊎ {[+ e' +]}))
  ∨ (∃ F e v e', E = F ⊎ {[+ e +]} ∧ tstep e (LSpawn v) e' ∧
       p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}))
  ∨ (∃ F c v e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SSend c v)) e' ∧ tstep f (LSess (SRecv c v)) f' ∧
       p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F c e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SClos c)) e' ∧ tstep f (LSess (SClos c)) f' ∧
       c ∈ C ∧ p' = (C ∖ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F e c d e', E = F ⊎ {[+ e +]} ∧ tstep e (LSess (SLink {[c; d]})) e' ∧
       c ∈ C ∧ p' = (C ∖ {[c]}, echsubst c d (F ⊎ {[+ e' +]}))).
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 10.
  - right; left. eauto 12.
  - right; right; left. eauto 12.
  - right; right; right; left. eauto 14.
  - right; right; right; right; left. eauto 14.
  - right; right; right; right; right. eauto 14.
Qed.

(** ** Moving the ends of a channel to another key

    [tenv_move W c d Θ Θ′]: Θ′ is Θ with the ends of c moved to d.
    If Θ holds no end of c this is the identity on Θ (junk); if Θ
    holds no end of d it renames c to d; if Θ holds one end of each,
    they become the two ends of d (fusion), which must then be dual and
    aliased. *)

Definition tenv_move (W : world) (c d : chan) (Θ Θ' : tenv) : Prop :=
  Θ' !! c = None ∧ (∀ k, k ≠ c → k ≠ d → Θ' !! k = Θ !! k) ∧
  ends_join (Θ !! c) (Θ !! d) (Θ' !! d) ∧
  (∀ e1 e2, Θ !! c = Some (One e1) → Θ !! d = Some (One e2) →
     w_eq W e1.2 e2.2 ∧ sdual e1.1 e2.1).

Section move.
  Context (W : world) (c d : chan) (Hcd : c ≠ d).

  Lemma move_lookup_ne Θ Θ' k :
    tenv_move W c d Θ Θ' → k ≠ c → k ≠ d → Θ' !! k = Θ !! k.
  Proof. intros (_ & H & _). apply H. Qed.

  Lemma move_dom Θ Θ' k :
    tenv_move W c d Θ Θ' →
    k ∈ dom Θ' ↔ k ≠ c ∧ (k ∈ dom Θ ∨ (k = d ∧ c ∈ dom Θ)).
  Proof.
    intros (Hc & Ho & Hj & _). rewrite !elem_of_dom.
    destruct (decide (k = c)) as [->|Hkc].
    { rewrite Hc. split; [by intros []|naive_solver]. }
    destruct (decide (k = d)) as [->|Hkd].
    - destruct (ends_join_cases _ _ _ Hj) as
        [(E1 & E2 & E3)|[(o & E1 & E2 & E3)|[(o & E1 & E2 & E3)|(e1 & e2 & E1 & E2 & [E3|E3])]]];
        rewrite ?E1, ?E2, ?E3; naive_solver.
    - rewrite Ho by done. naive_solver.
  Qed.

  Lemma move_empty Θ' : tenv_move W c d ∅ Θ' → Θ' = ∅.
  Proof.
    intros (Hc & Ho & Hj & _). apply map_empty. intros k.
    rewrite !lookup_empty in Hj.
    destruct (ends_join_cases _ _ _ Hj) as
      [(_ & _ & E3)|[(? & ? & _)|[(? & _ & ? & _)|(? & ? & ? & _)]]]; try done.
    destruct (decide (k = c)) as [->|?]; [done|].
    destruct (decide (k = d)) as [->|?]; [done|]. rewrite Ho by done. apply lookup_empty.
  Qed.

  Lemma move_mono W' Θ Θ' :
    (∀ x y, w_eq W x y → w_eq W' x y) → tenv_move W c d Θ Θ' → tenv_move W' c d Θ Θ'.
  Proof.
    intros Hm (Hc & Ho & Hj & Hd). split_and!; [done..|].
    intros e1 e2 H1 H2. destruct (Hd e1 e2 H1 H2). auto.
  Qed.

  Lemma move_id Θ : c ∉ dom Θ → tenv_move W c d Θ Θ.
  Proof.
    intros Hc. apply not_elem_of_dom in Hc. split_and!; [done|done| |].
    - rewrite Hc. destruct (Θ !! d); constructor.
    - intros e1 e2 H. congruence.
  Qed.

  Lemma move_insert Θ Θ' k o :
    k ≠ c → k ≠ d → tenv_move W c d Θ Θ' →
    tenv_move W c d (<[k := o]> Θ) (<[k := o]> Θ').
  Proof.
    intros Hkc Hkd (Hc & Ho & Hj & Hdd). split_and!.
    - by rewrite lookup_insert_ne.
    - intros k' Hk'c Hk'd. destruct (decide (k' = k)) as [->|Hne].
      + by rewrite !lookup_insert_eq.
      + rewrite !lookup_insert_ne by done. by apply Ho.
    - rewrite !lookup_insert_ne by done. done.
    - intros e1 e2. rewrite !lookup_insert_ne by done. apply Hdd.
  Qed.

  (** The ends move with their keys. *)
  Lemma move_keys Θ Θ' :
    tenv_move W c d Θ Θ' →
    ∃ κ : ekey → ekey, (∀ k, (κ k).1 = csub c d k.1) ∧
      (∀ k, k.1 ≠ c → k.1 ≠ d → κ k = k) ∧
      (∀ k e, tenv_entry Θ k = Some e → tenv_entry Θ' (κ k) = Some e) ∧
      (∀ k' e', tenv_entry Θ' k' = Some e' → ∃ k, κ k = k' ∧ tenv_entry Θ k = Some e').
  Proof.
    intros (Hc & Ho & Hj & _).
    assert (∀ k, k.1 ≠ c → k.1 ≠ d → tenv_entry Θ' k = tenv_entry Θ k) as Hent.
    { intros [k b] H1 H2. unfold tenv_entry. simpl in *. by rewrite Ho. }
    destruct (ends_join_cases _ _ _ Hj) as
      [(E1 & E2 & E3)|[(o & E1 & E2 & E3)|[(o & E1 & E2 & E3)|(e1 & e2 & E1 & E2 & [E3|E3])]]].
    4: exists (λ k, if decide (k.1 = c) then (d, false)
                    else if decide (k.1 = d) then (d, true) else k).
    5: exists (λ k, if decide (k.1 = c) then (d, true)
                    else if decide (k.1 = d) then (d, false) else k).
    1-3: exists (λ k, (csub c d k.1, k.2)).
    all: split_and!.
    all: try (intros [k b]; simpl; unfold csub; repeat case_decide; simpl; congruence).
    all: try (intros [k b] Hk1 Hk2; simpl in *; unfold csub;
              repeat case_decide; simpl; congruence).
    all: try (intros [k b] e He; simpl in *; unfold csub;
              destruct (decide (k = c)) as [->|Hkc];
              [unfold tenv_entry in *; simpl in *; rewrite ?E1, ?E2, ?E3 in *;
               destruct b; simplify_eq; done|];
              destruct (decide (k = d)) as [->|Hkd];
              [unfold tenv_entry in *; simpl in *; rewrite ?E1, ?E2, ?E3 in *;
               destruct b; simplify_eq; done|];
              rewrite Hent; done).
    all: intros [k b] e He; destruct (decide (k = c)) as [->|Hkc];
      [unfold tenv_entry in He; simpl in He; by rewrite Hc in He|].
    all: destruct (decide (k = d)) as [->|Hkd];
      [|exists (k, b); simpl; unfold csub; repeat case_decide; try congruence;
        split; [done|]; by rewrite <-Hent].
    all: unfold tenv_entry in *; simpl in *; rewrite ?E1, ?E2, ?E3 in *.
    all: try (exists (c, b); simpl; unfold csub;
              repeat case_decide; try congruence; simpl;
              rewrite ?E1; destruct o; destruct b; simplify_eq; done).
    all: try (exists (d, b); simpl; unfold csub;
              repeat case_decide; try congruence; simpl;
              rewrite ?E2; destruct o; destruct b; simplify_eq; done).
    all: destruct b; simplify_eq.
    all: first [exists (c, false); simpl; repeat case_decide; try congruence;
                simpl; rewrite E1; done
               |exists (d, false); simpl; repeat case_decide; try congruence;
                simpl; rewrite E2; done].
  Qed.
End move.

Lemma elem_of_tenv_heads_entry Θ x :
  x ∈ tenv_heads Θ ↔ ∃ k e, tenv_entry Θ k = Some e ∧ x = e.2.
Proof.
  rewrite elem_of_tenv_heads. split.
  - intros (c & o & Hc & Hx). destruct o as [e|e1 e2]; simpl in Hx.
    + apply elem_of_singleton in Hx as ->. exists (c, false), e.
      unfold tenv_entry. simpl. by rewrite Hc.
    + apply elem_of_union in Hx as [->%elem_of_singleton| ->%elem_of_singleton].
      * exists (c, false), e1. unfold tenv_entry. simpl. by rewrite Hc.
      * exists (c, true), e2. unfold tenv_entry. simpl. by rewrite Hc.
  - intros ([c b] & e & He & ->). unfold tenv_entry in He. simpl in He.
    destruct (Θ !! c) as [[f|f1 f2]|] eqn:Hc, b; simplify_eq; exists c; eexists;
      (split; [done|]); simpl; set_solver.
Qed.

Lemma elem_of_tenv_roots_entry Θ x :
  x ∈ tenv_roots Θ ↔ ∃ k e, tenv_entry Θ k = Some e ∧ x ∈ entry_roots e.
Proof.
  rewrite elem_of_tenv_roots. split.
  - intros (c & o & Hc & Hx). destruct o as [e|e1 e2]; simpl in Hx.
    + exists (c, false), e. unfold tenv_entry. simpl. by rewrite Hc.
    + apply elem_of_union in Hx as [Hx|Hx].
      * exists (c, false), e1. unfold tenv_entry. simpl. by rewrite Hc.
      * exists (c, true), e2. unfold tenv_entry. simpl. by rewrite Hc.
  - intros ([c b] & e & He & Hx). unfold tenv_entry in He. simpl in He.
    destruct (Θ !! c) as [[f|f1 f2]|] eqn:Hc, b; simplify_eq; exists c; eexists;
      (split; [done|]); simpl; set_solver.
Qed.

Lemma join_one_res a b e :
  ends_join a b (Some (One e)) → (a = Some (One e) ∧ b = None) ∨ (a = None ∧ b = Some (One e)).
Proof. intros H. inversion H; subst; [left|right]; done. Qed.

Lemma join_l_none a r : ends_join a None r → r = a.
Proof. intros H. by inversion H. Qed.

Section move2.
  Context (W : world) (HW : world_wf W) (c d : chan) (Hcd : c ≠ d).

  Lemma move_heads Θ Θ' : tenv_move W c d Θ Θ' → tenv_heads Θ' = tenv_heads Θ.
  Proof.
    intros H. destruct (move_keys W c d Hcd Θ Θ' H) as (κ & _ & _ & Hf & Hb).
    apply set_eq. intros x. rewrite !elem_of_tenv_heads_entry. split.
    - intros (k' & e & He & ->). destruct (Hb _ _ He) as (k & _ & Hk). eauto.
    - intros (k & e & He & ->). eauto.
  Qed.

  Lemma move_roots Θ Θ' : tenv_move W c d Θ Θ' → tenv_roots Θ' = tenv_roots Θ.
  Proof.
    intros H. destruct (move_keys W c d Hcd Θ Θ' H) as (κ & _ & _ & Hf & Hb).
    apply set_eq. intros x. rewrite !elem_of_tenv_roots_entry. split.
    - intros (k' & e & He & Hx). destruct (Hb _ _ He) as (k & _ & Hk). eauto.
    - intros (k & e & He & Hx). eauto.
  Qed.

  (** Splitting a composition along a move. *)
  Lemma move_comp_split Θ Θ' Θ1 Θ2 :
    tenv_move W c d Θ Θ' → tenv_comp (w_eq W) Θ Θ1 Θ2 →
    ∃ Θ1' Θ2', tenv_move W c d Θ1 Θ1' ∧ tenv_move W c d Θ2 Θ2' ∧
      tenv_comp (w_eq W) Θ' Θ1' Θ2'.
  Proof.
    intros (Hc & Ho & Hj & Hdd) [Hjn Hdu].
    destruct (map_choice2 (λ k o1 o2,
        (k ≠ c → k ≠ d → o1 = Θ1 !! k ∧ o2 = Θ2 !! k) ∧
        (k = c → o1 = None ∧ o2 = None) ∧
        (k = d → ends_join (Θ1 !! c) (Θ1 !! d) o1 ∧
                 ends_join (Θ2 !! c) (Θ2 !! d) o2 ∧ ends_join o1 o2 (Θ' !! d)))
        (dom Θ1 ∪ dom Θ2 ∪ {[d]})) as (Θ1' & Θ2' & HP).
    { intros k. destruct (decide (k = c)) as [->|Hkc].
      { exists None, None. split_and!; [done|done|congruence]. }
      destruct (decide (k = d)) as [->|Hkd].
      2: { exists (Θ1 !! k), (Θ2 !! k). split_and!; [done|congruence|congruence]. }
      exists (match Θ1 !! c, Θ1 !! d with
              | None, x => x | x, None => x | Some _, Some _ => Θ' !! d end),
             (match Θ2 !! c, Θ2 !! d with
              | None, x => x | x, None => x | Some _, Some _ => Θ' !! d end).
      split_and!; [done|congruence|intros _].
      pose proof (Hjn c) as Jc. pose proof (Hjn d) as Jd.
      destruct (Θ1 !! c) as [a1|], (Θ2 !! c) as [a2|], (Θ1 !! d) as [b1|],
        (Θ2 !! d) as [b2|];
        inversion Jc as [Ec|? Ec|? Ec|? ? Ec|? ? Ec]; inversion Jd as [Ed|? Ed|? Ed|? ? Ed|? ? Ed];
        inversion Hj; simplify_eq; try congruence;
        repeat match goal with H : Some _ = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        repeat match goal with H : None = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        repeat match goal with H : _ = Θ' !! _ |- _ => rewrite <-H in *; clear H end;
        simplify_eq; split_and!; try constructor; try done; try congruence.
    }
    { intros k Hk. split_and!.
      - intros Hkc Hkd. split; symmetry; apply not_elem_of_dom; set_solver.
      - done.
      - intros ->. set_solver. }
    exists Θ1', Θ2'.
    assert (∀ k, k ≠ c → k ≠ d → Θ1' !! k = Θ1 !! k ∧ Θ2' !! k = Θ2 !! k) as Hne
      by (intros k ? ?; by apply HP).
    destruct (proj1 (proj2 (HP c)) eq_refl) as [Hc1 Hc2].
    destruct (proj2 (proj2 (HP d)) eq_refl) as (Hd1 & Hd2 & Hd12).
    pose proof (Hjn c) as Jc. pose proof (Hjn d) as Jd.
    (* the ends of c and d in Θ, read off the parts *)
    assert (∀ e1 e2, Θ1 !! c = Some (One e1) → Θ1 !! d = Some (One e2) →
              Θ !! c = Some (One e1) ∧ Θ !! d = Some (One e2)) as Hpart1.
    { intros e1 e2 H1 H2. rewrite H1 in Jc. rewrite H2 in Jd.
      inversion Jc; inversion Jd; simplify_eq;
        repeat match goal with H : Some _ = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        repeat match goal with H : None = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        try (by split); inversion Hj. }
    assert (∀ e1 e2, Θ2 !! c = Some (One e1) → Θ2 !! d = Some (One e2) →
              Θ !! c = Some (One e1) ∧ Θ !! d = Some (One e2)) as Hpart2.
    { intros e1 e2 H1 H2. rewrite H1 in Jc. rewrite H2 in Jd.
      inversion Jc; inversion Jd; simplify_eq;
        repeat match goal with H : Some _ = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        repeat match goal with H : None = Θ !! _ |- _ => rewrite <-H in *; clear H end;
        try (by split); inversion Hj. }
    split_and!.
    - split_and!; [done|intros; by apply Hne|done|].
      intros e1 e2 H1 H2. destruct (Hpart1 e1 e2 H1 H2). by apply Hdd.
    - split_and!; [done|intros; by apply Hne|done|].
      intros e1 e2 H1 H2. destruct (Hpart2 e1 e2 H1 H2). by apply Hdd.
    - split.
      + intros k. destruct (decide (k = c)) as [->|Hkc].
        { rewrite Hc, Hc1, Hc2. constructor. }
        destruct (decide (k = d)) as [->|Hkd]; [done|].
        destruct (Hne k Hkc Hkd) as [-> ->]. rewrite Ho by done. apply Hjn.
      + intros k e1 e2 H1 H2. destruct (decide (k = c)) as [->|Hkc]; [congruence|].
        destruct (decide (k = d)) as [->|Hkd].
        2: { destruct (Hne k Hkc Hkd) as [E1 E2]. rewrite E1 in H1. rewrite E2 in H2.
             by apply (Hdu k). }
        rewrite H1 in Hd1. rewrite H2 in Hd2.
        destruct (join_one_res _ _ _ Hd1) as [[A1 B1]|[A1 B1]];
          destruct (join_one_res _ _ _ Hd2) as [[A2 B2]|[A2 B2]].
        * by apply (Hdu c).
        * rewrite A1, A2 in Jc. rewrite B1, B2 in Jd. inversion Jc. inversion Jd.
          by apply Hdd.
        * rewrite A1, A2 in Jc. rewrite B1, B2 in Jd. inversion Jc. inversion Jd.
          destruct (Hdd e2 e1) as [Hx Hs]; [done|done|]. split.
          -- by apply (wf_eq_sym _ HW).
          -- by apply sdual_sym.
        * by apply (Hdu d).
  Qed.

  Lemma move_none Θ Θ' : tenv_move W c d Θ Θ' → Θ !! c = None → Θ' = Θ.
  Proof.
    intros (Hc & Ho & Hj & _) HΘc. apply map_eq. intros k.
    destruct (decide (k = c)) as [->|Hkc]; [by rewrite Hc, HΘc|].
    destruct (decide (k = d)) as [->|Hkd]; [|by apply Ho].
    rewrite HΘc in Hj. inversion Hj; congruence.
  Qed.

  Lemma move_hd Θ Θ' c0 u k Θr :
    tenv_move W c d Θ Θ' → tenv_hd Θ c0 u k Θr →
    (c0 ≠ c ∧ c0 ≠ d) ∨ (c0 = c ∧ Θ !! d = None) ∨ (c0 = d ∧ Θ !! c = None) →
    ∃ Θr', tenv_hd Θ' (csub c d c0) u k Θr' ∧ tenv_move W c d Θr Θr'.
  Proof.
    intros Hm (s & Hext & Hu) Hcase. pose proof Hm as Hm0.
    destruct Hm as (Hc & Ho & Hj & Hdd).
    destruct Hcase as [[H1 H2]|[[-> Hd]|[-> HΘc]]].
    - rewrite csub_ne by done.
      assert (Θ' !! c0 = Θ !! c0) as E0 by (by apply Ho).
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])].
      + exists (delete c0 Θ'). split.
        * exists s. split; [|done]. left. split; [apply lookup_delete_eq|].
          rewrite insert_delete_id; [done|]. rewrite E0. by rewrite lookup_insert_eq.
        * split_and!.
          -- rewrite lookup_delete_ne by done. done.
          -- intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
             ++ rewrite lookup_delete_eq. done.
             ++ rewrite lookup_delete_ne by done. rewrite Ho by done.
                by rewrite lookup_insert_ne.
          -- rewrite lookup_delete_ne by done. by rewrite !lookup_insert_ne in Hj.
          -- intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
      + exists (<[c0 := One f]> Θ'). split.
        * exists s. split; [|done]. right. exists f. split; [apply lookup_insert_eq|].
          left. rewrite insert_over; [done|]. rewrite E0. by rewrite lookup_insert_eq.
        * split_and!.
          -- by rewrite lookup_insert_ne.
          -- intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
             ++ by rewrite !lookup_insert_eq.
             ++ rewrite !lookup_insert_ne by done. rewrite Ho by done.
                by rewrite lookup_insert_ne.
          -- rewrite !lookup_insert_ne by done. by rewrite !lookup_insert_ne in Hj.
          -- intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
      + exists (<[c0 := One f]> Θ'). split.
        * exists s. split; [|done]. right. exists f. split; [apply lookup_insert_eq|].
          right. rewrite insert_over; [done|]. rewrite E0. by rewrite lookup_insert_eq.
        * split_and!.
          -- by rewrite lookup_insert_ne.
          -- intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
             ++ by rewrite !lookup_insert_eq.
             ++ rewrite !lookup_insert_ne by done. rewrite Ho by done.
                by rewrite lookup_insert_ne.
          -- rewrite !lookup_insert_ne by done. by rewrite !lookup_insert_ne in Hj.
          -- intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
    - rewrite csub_hit.
      assert (Θr !! d = None) as Hrd.
      { destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])]; by rewrite lookup_insert_ne in Hd. }
      rewrite Hd in Hj.
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])]; rewrite lookup_insert_eq in Hj;
        apply join_l_none in Hj.
      + exists (delete d Θ'). split.
        * exists s. split; [|done]. left. split; [apply lookup_delete_eq|].
          rewrite insert_delete_id; [done|]. done.
        * split_and!.
          -- by rewrite lookup_delete_ne.
          -- intros k' ? ?. rewrite lookup_delete_ne by done. rewrite Ho by done.
             by rewrite lookup_insert_ne.
          -- rewrite Hr, Hrd, lookup_delete_eq. constructor.
          -- intros e1 e2 A B. congruence.
      + exists (<[d := One f]> Θ'). split.
        * exists s. split; [|done]. right. exists f. split; [apply lookup_insert_eq|].
          left. rewrite insert_over; done.
        * split_and!.
          -- by rewrite lookup_insert_ne.
          -- intros k' ? ?. rewrite lookup_insert_ne by done. rewrite Ho by done.
             by rewrite lookup_insert_ne.
          -- rewrite Hr, Hrd, lookup_insert_eq. constructor.
          -- intros e1 e2 A B. congruence.
      + exists (<[d := One f]> Θ'). split.
        * exists s. split; [|done]. right. exists f. split; [apply lookup_insert_eq|].
          right. rewrite insert_over; done.
        * split_and!.
          -- by rewrite lookup_insert_ne.
          -- intros k' ? ?. rewrite lookup_insert_ne by done. rewrite Ho by done.
             by rewrite lookup_insert_ne.
          -- rewrite Hr, Hrd, lookup_insert_eq. constructor.
          -- intros e1 e2 A B. congruence.
    - rewrite csub_ne by done.
      assert (Θ' = Θ) as ->.
      { apply (move_none Θ Θ'); [done|done]. }
      exists Θr. split; [by exists s|]. apply move_id. apply not_elem_of_dom.
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])]; by rewrite lookup_insert_ne in HΘc.
  Qed.

  Lemma move_ext Θ1 Θ1' c0 e Θ'' :
    tenv_move W c d Θ1 Θ1' → tenv_ext Θ1 c0 e Θ'' →
    (c0 ≠ c ∧ c0 ≠ d) ∨ (c0 = c ∧ Θ1 !! d = None) ∨ (c0 = d ∧ Θ1 !! c = None) →
    ∃ Θ3, tenv_ext Θ1' (csub c d c0) e Θ3 ∧ tenv_move W c d Θ'' Θ3.
  Proof.
    intros Hm Hext Hcase. pose proof Hm as Hm0.
    destruct Hm as (Hc & Ho & Hj & Hdd).
    destruct Hcase as [[H1 H2]|[[-> Hd]|[-> HΘc]]].
    - rewrite csub_ne by done.
      assert (Θ1' !! c0 = Θ1 !! c0) as E0 by (by apply Ho).
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])].
      + exists (<[c0 := One e]> Θ1'). split; [left; by rewrite E0|].
        by apply move_insert.
      + exists (<[c0 := Both e f]> Θ1'). split; [right; exists f; rewrite E0; by split; [|left]|].
        by apply move_insert.
      + exists (<[c0 := Both f e]> Θ1'). split; [right; exists f; rewrite E0; by split; [|right]|].
        by apply move_insert.
    - rewrite csub_hit. rewrite Hd in Hj. apply join_l_none in Hj.
      assert (∀ o, tenv_move W c d (<[c := o]> Θ1) (<[d := o]> Θ1')) as Hmv.
      { intros o. split_and!.
        - by rewrite lookup_insert_ne.
        - intros k' ? ?. by rewrite !lookup_insert_ne, Ho.
        - rewrite lookup_insert_eq, lookup_insert_ne, Hd, lookup_insert_eq by done. constructor.
        - intros e1 e2 A' B'. rewrite lookup_insert_ne in B' by done. congruence. }
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])].
      + exists (<[d := One e]> Θ1'). split; [left; by rewrite Hj|]. apply Hmv.
      + exists (<[d := Both e f]> Θ1'). split; [|apply Hmv].
        right; exists f; rewrite Hj; by split; [|left].
      + exists (<[d := Both f e]> Θ1'). split; [|apply Hmv].
        right; exists f; rewrite Hj; by split; [|right].
    - rewrite csub_ne by done.
      assert (Θ1' = Θ1) as -> by (by apply (move_none Θ1 Θ1')).
      exists Θ''. split; [done|]. apply move_id. apply not_elem_of_dom.
      destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])]; by rewrite lookup_insert_ne.
  Qed.
End move2.
