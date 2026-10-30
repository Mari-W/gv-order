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

  (** Joining with a part that holds no end of c. *)
  Lemma move_comp_join Θ Θ' Θa Θ'' :
    tenv_move W c d Θ Θ' → tenv_comp (w_eq W) Θ'' Θ' Θa → Θa !! c = None →
    ∃ Θ0, tenv_comp (w_eq W) Θ0 Θ Θa ∧ tenv_move W c d Θ0 Θ''.
  Proof.
    intros (Hc & Ho & Hj & Hdd) [Hjn Hdu] Hac.
    set (od := match Θ !! c with
               | None => Θ'' !! d
               | Some _ => match Θ !! d with None => Θa !! d | Some _ => Θ !! d end
               end).
    destruct (map_choice2 (B := unit) (λ k o _,
        (k ≠ c → k ≠ d → o = Θ'' !! k) ∧ (k = c → o = Θ !! c) ∧ (k = d → o = od))
        (dom Θ'' ∪ dom Θ)) as (Θ0 & _ & HP).
    { intros k. destruct (decide (k = c)) as [->|Hkc].
      { exists (Θ !! c), None. split_and!; [done|done|congruence]. }
      destruct (decide (k = d)) as [->|Hkd].
      - exists od, None. split_and!; [done|congruence|done].
      - exists (Θ'' !! k), None. split_and!; [done|congruence|congruence]. }
    { intros k Hk. split_and!.
      - intros. symmetry. apply not_elem_of_dom. set_solver.
      - intros ->. symmetry. apply not_elem_of_dom. set_solver.
      - intros ->. assert (Θ'' !! d = None) as E1 by (apply not_elem_of_dom; set_solver).
        assert (Θ !! d = None) as E2 by (apply not_elem_of_dom; set_solver).
        unfold od. destruct (Θ !! c); [|done]. rewrite E2. pose proof (Hjn d) as J.
        rewrite E1 in J. inversion J; done. }
    assert (∀ k, k ≠ c → k ≠ d → Θ0 !! k = Θ'' !! k) as H0ne by (intros; by apply HP).
    assert (Θ0 !! c = Θ !! c) as H0c by (by apply HP).
    assert (Θ0 !! d = od) as H0d by (by apply HP).
    pose proof (Hjn d) as Jd. pose proof (Hjn c) as Jc.
    rewrite Hc, Hac in Jc. apply join_l_none in Jc.
    destruct (Θ !! c) as [oc|] eqn:Ec; [destruct (Θ !! d) as [od0|] eqn:Ed|];
      unfold od in H0d; rewrite ?Ec, ?Ed in H0d, Hj.
    - (* both c and d in Θ: fused, the part holds neither *)
      assert (Θa !! d = None ∧ Θ'' !! d = Θ' !! d) as [Had Hdd'].
      { destruct (ends_join_cases _ _ _ Hj) as
          [(? & ? & ?)|[(? & ? & ? & ?)|[(? & ? & ? & ?)|(e1 & e2 & E1 & E2 & [E3|E3])]]];
          try discriminate; rewrite E3 in Jd; inversion Jd; split; congruence. }
      exists Θ0. split_and!.
      + split.
        * intros k. destruct (decide (k = c)) as [->|Hkc].
          { rewrite H0c, Hac, ?Ec. constructor. }
          destruct (decide (k = d)) as [->|Hkd].
          { rewrite H0d, Ed, Had. constructor. }
          rewrite H0ne by done. rewrite <-(Ho k) by done. apply Hjn.
        * intros k f1 f2 F1 F2. destruct (decide (k = c)) as [->|Hkc]; [congruence|].
          destruct (decide (k = d)) as [->|Hkd]; [congruence|].
          apply (Hdu k); [by rewrite Ho|done].
      + split_and!.
        * exact Jc.
        * intros k ? ?. by rewrite H0ne.
        * rewrite H0c, H0d, Hdd'. exact Hj.
        * intros f1 f2 F1 F2. rewrite H0c in F1. rewrite H0d in F2. by apply Hdd.
    - (* only c in Θ: renaming, d comes from the part *)
      apply join_l_none in Hj. exists Θ0. split_and!.
      + split.
        * intros k. destruct (decide (k = c)) as [->|Hkc].
          { rewrite H0c, Hac, ?Ec. constructor. }
          destruct (decide (k = d)) as [->|Hkd].
          { rewrite H0d, ?Ed. destruct (Θa !! d); constructor. }
          rewrite H0ne by done. rewrite <-(Ho k) by done. apply Hjn.
        * intros k f1 f2 F1 F2. destruct (decide (k = c)) as [->|Hkc]; [congruence|].
          destruct (decide (k = d)) as [->|Hkd]; [congruence|].
          apply (Hdu k); [by rewrite Ho|done].
      + split_and!.
        * exact Jc.
        * intros k ? ?. by rewrite H0ne.
        * rewrite H0c, H0d, ?Ec, <-Hj. done.
        * intros f1 f2 F1 F2. rewrite H0c, ?Ec in F1. rewrite H0d in F2.
          apply (Hdu d); [by rewrite Hj, ?Ec|done].
    - (* no c in Θ: the move is the identity *)
      assert (Θ' = Θ) as ->.
      { apply map_eq. intros k. destruct (decide (k = c)) as [->|Hkc]; [by rewrite Hc, Ec|].
        destruct (decide (k = d)) as [->|Hkd]; [|by apply Ho].
        inversion Hj; congruence. }
      exists Θ''. split_and!.
      + by split.
      + assert (Θ0 = Θ'') as <-.
        { apply map_eq. intros k. destruct (decide (k = c)) as [->|Hkc].
          - by rewrite H0c, Jc.
          - destruct (decide (k = d)) as [->|Hkd]; [done|]. by apply H0ne. }
        apply move_id. apply not_elem_of_dom. by rewrite H0c.
  Qed.
End move2.


Lemma recv_back_not_env W Σr Θ2 c :
  recv_ok W Σr Θ2 → c ∈ recv_back Σr Θ2 → c ∉ dom (recv_env Σr Θ2).
Proof.
  intros (_ & _ & Hb) Hc. unfold recv_back, recv_env in *.
  rewrite dom_union_L, elem_of_union, !elem_of_dom.
  intros [[e He]|[e He]].
  - apply lookup_difference_Some in He as [HΣ Hn].
    apply elem_of_union in Hc as [Hc|Hc].
    + apply elem_of_intersection in Hc as [Hc1 Hc2].
      apply elem_of_dom in Hc1 as [o Ho].
      destruct o as [e1|e1 e2].
      * unfold tenv_ones in Hn. rewrite lookup_omap, Ho in Hn. done.
      * apply (proj1 (elem_of_disjoint _ _) Hb c); [|by apply elem_of_dom_2 in HΣ].
        apply elem_of_difference. split; [by apply elem_of_dom_2 in Ho|].
        unfold tenv_ones. rewrite elem_of_dom, lookup_omap, Ho. by intros [? ?].
    + apply (proj1 (elem_of_disjoint _ _) Hb c); [done|by apply elem_of_dom_2 in HΣ].
  - apply lookup_difference_Some in He as [Ho Hn].
    apply elem_of_union in Hc as [Hc|Hc].
    + apply elem_of_intersection in Hc as [_ Hc2]. apply elem_of_dom in Hc2 as [? ?].
      congruence.
    + apply elem_of_difference in Hc as [_ Hc]. apply Hc. by apply elem_of_dom_2 in Ho.
Qed.

(** Every session step of a substituted term comes from one of the
    original, on the preimage of its subjects. *)
Definition ssub_rel (x b : chan) (σ σ' : slabel) : Prop :=
  match σ, σ' with
  | SRecv c0 _, SRecv c' _ => csub x b c0 = c'
  | SSend c0 w, SSend c' w' => csub x b c0 = c' ∧ w' = chsubst x b w
  | SClos c0, SClos c' => csub x b c0 = c'
  | SLink cd0, SLink cd' => gsub x b cd0 = cd'
  | _, _ => False
  end.

Lemma ssub_rel_subjs x b σ σ' : ssub_rel x b σ σ' → subjs σ' = gsub x b (subjs σ).
Proof.
  destruct σ, σ'; simpl; try done; unfold gsub; rewrite ?set_map_singleton_L;
    naive_solver.
Qed.

Lemma tstep_chsubst_back x b e σ' f' :
  tstep (chsubst x b e) (LSess σ') f' → ∃ σ f, tstep e (LSess σ) f ∧ ssub_rel x b σ σ'.
Proof.
  intros Hst. destruct σ' as [c w'|c w'|c|cd].
  - destruct (recv_retarget _ _ _ _ EUnit Hst) as [f'' Hf''] ; [done|].
    destruct (tstep_chsubst_recv_inv_subst x b e c EUnit f'') as (c0 & f & Hc0 & Hf & _);
      [done|]. exists (SRecv c0 EUnit), f. by split.
  - destruct (tstep_chsubst_det_inv x b e _ f' Hst I) as (α & f & Hf & Hα & _).
    destruct α as [|[c0 w|c0 w|c0|cd0]| |]; simpl in Hα; try discriminate.
    injection Hα as H1 H2. subst. exists (SSend c0 w), f. by split.
  - destruct (tstep_chsubst_det_inv x b e _ f' Hst I) as (α & f & Hf & Hα & _).
    destruct α as [|[c0 w|c0 w|c0|cd0]| |]; simpl in Hα; try discriminate.
    injection Hα as H1. subst. exists (SClos c0), f. by split.
  - destruct (tstep_chsubst_det_inv x b e _ f' Hst I) as (α & f & Hf & Hα & _).
    destruct α as [|[c0 w|c0 w|c0|cd0]| |]; simpl in Hα; try discriminate.
    injection Hα as H1. subst. exists (SLink cd0), f. by split.
Qed.

Lemma ssub_rel_select x b Σ σ σ' k :
  ssub_rel x b σ σ' → subjs σ' = subjs σ →
  selects (tenv_of Σ) σ k ↔ selects (tenv_of Σ) σ' k.
Proof.
  intros Hr Hs. destruct σ as [c0 w|c0 w|c0|cd0], σ' as [c w'|c w'|c|cd]; simpl in *;
    try done; unfold gsub in *; rewrite ?set_map_singleton_L in Hs.
  all: try (apply (inj singleton) in Hs as ->; done).
  by rewrite Hs.
Qed.
(** ** The junk-renaming transport for processes *)

(** Every external offer of a related process is on interface channels. *)
Lemma Prel_offer_dom n W Σ T C E0 e σ e' :
  Prel (S n) W Σ T (C, E0 ⊎ {[+ e +]}) → tstep e (LSess σ) e' → subjs σ ## C →
  subjs σ ⊆ dom Σ.
Proof.
  intros HP Hst Hd.
  pose proof (Prel_S_step _ _ _ _ _ _ _ HP (PStepSession C E0 e σ e' Hst Hd)) as Hc.
  destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
  - destruct Hc as (Σ1 & m & U & s & k & Hhd & _). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (?&?&?&?&?&?&?&?&Hhd&_). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (Σ1 & k & Hhd & _). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (c & d & Σ1 & sc & sd & kc & kd & -> & _ & -> & _).
    rewrite !dom_insert_L. set_solver.
Qed.

Lemma echsubst_disj_union2 x b F e f :
  echsubst x b (F ⊎ {[+ e +]} ⊎ {[+ f +]}) =
  echsubst x b F ⊎ {[+ chsubst x b e +]} ⊎ {[+ chsubst x b f +]}.
Proof. by rewrite !echsubst_disj_union, !echsubst_singleton. Qed.

Lemma echsubst_disj_union1 x b F e :
  echsubst x b (F ⊎ {[+ e +]}) = echsubst x b F ⊎ {[+ chsubst x b e +]}.
Proof. by rewrite echsubst_disj_union, echsubst_singleton. Qed.

Lemma msswap_echsubst_fresh a z x b E :
  a ∉ echans (echsubst x b E) → z ∉ echans (echsubst x b E) →
  msswap a z (echsubst x b E) = echsubst x b E.
Proof. intros Ha Hz. by apply msswap_fresh. Qed.

Lemma terminated_pirred p : terminated p → pirred p.
Proof.
  intros (v & E & -> & Hv & HE) π q Hq.
  assert (Hval : ∀ e, e ∈ ({[+ v +]} ⊎ E : gmultiset expr) → is_val e).
  { intros e He. apply gmultiset_elem_of_disj_union in He as [He|He].
    - by apply gmultiset_elem_of_singleton in He as ->.
    - by rewrite (HE e He). }
  inversion Hq; subst;
    match goal with
    | H : tstep ?e _ _, Heq : _ = {[+ v +]} ⊎ E |- _ =>
        eapply val_no_tstep; [exact H|apply Hval; rewrite <-Heq; multiset_solver]
    | H : tstep ?e _ _, Heq : {[+ v +]} ⊎ E = _ |- _ =>
        eapply val_no_tstep; [exact H|apply Hval; rewrite Heq; multiset_solver]
    end.
Qed.

Lemma msswap_echsubst_flip a b E : msswap a b (echsubst b a E) = echsubst a b E.
Proof.
  unfold echsubst, msswap. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite eswap_chsubst_flip.
Qed.

Lemma chsubst_retarget x c d e :
  x ≠ c → chsubst c d (chsubst x c e) = chsubst x d (chsubst c d e).
Proof.
  intros. induction e; simpl; f_equal; auto.
  unfold csub in *. repeat case_decide; congruence.
Qed.

Lemma echsubst_retarget x c d E :
  x ≠ c → echsubst c d (echsubst x c E) = echsubst x d (echsubst c d E).
Proof.
  intros. unfold echsubst. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite chsubst_retarget.
Qed.

Lemma lsub_beta x b α : lsub x b α = LBeta → α = LBeta.
Proof. by destruct α. Qed.

(** [set_solver] after dropping the large hypotheses of the transport. *)
Local Ltac sset :=
  repeat match goal with
    | H : ?P |- _ =>
        lazymatch P with
        | context [Prel] => clear H
        | context [Pcase_gen] => clear H
        | context [proc_step] => clear H
        | context [offered_p] => clear H
        | context [Vrel] => clear H
        | context [tstep] => clear H
        end
    end; set_solver.

Lemma imp4 (A B C D R G : Prop) : (A → B → C → D → R) → (R → G) → A → B → C → D → G.
Proof. tauto. Qed.

Lemma Prel_junk n : ∀ W Σ T C E x b,
  x ∉ dom Σ → x ∉ C → (b ∈ C → b ∉ dom Σ) → b ≠ x →
  Prel n W Σ T (C, E) → Prel n W Σ T (C, echsubst x b E).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros W Σ T C E x b HxΣ HxC HbC Hbx HP.
  destruct n as [|n']; [apply Prel_0|].
  remember (C, E) as p eqn:Hp. revert C E Hp b HxΣ HxC HbC Hbx.
  induction HP as [W Σ T p Hirr Hrdy Hstep] using Prel_S_ind.
  intros C E -> b HxΣ HxC HbC Hbx.
  assert (HP : Prel (S n') W Σ T (C, E)).
  { apply Prel_S_iff. split_and!; [done|done|]. intros π q Hq.
    eapply Pcase_gen_mono; [|exact (Hstep π q Hq)]. by intros ? ? ? ? [? _]. }
  assert (Hstep_tau : ∀ q, proc_step (C, E) PTau q → Ptau_case (Prel n') W Σ T q)
    by (intros q Hq; exact (proj1 (Hstep PTau q Hq))).
  assert (IH : ∀ W0 Σ0 C0 E0 b0, x ∉ dom Σ0 → x ∉ C0 → (b0 ∈ C0 → b0 ∉ dom Σ0) →
             b0 ≠ x → Prel n' W0 Σ0 T (C0, E0) → Prel n' W0 Σ0 T (C0, echsubst x b0 E0)).
  { intros. apply IHn; [lia|done..]. }
  assert (Hoff : ∀ E0 e σ e', E = E0 ⊎ {[+ e +]} → tstep e (LSess σ) e' →
                   subjs σ ## C → x ∉ subjs σ).
  { intros E0 e σ e' -> Hst Hd Hx. apply HxΣ.
    by apply (Prel_offer_dom _ _ _ _ _ _ _ _ _ HP Hst Hd). }
  (* a step whose preimage subjects avoid C but contain x is impossible *)
  assert (Hpre : ∀ E0 e σ e', E = E0 ⊎ {[+ e +]} → tstep e (LSess σ) e' →
                   gsub x b (subjs σ) ## C → x ∉ subjs σ).
  { intros E0 e σ e' HE Hst Hd Hx. apply (Hoff E0 e σ e' HE Hst); [|done].
    apply elem_of_disjoint. intros y Hy HyC.
    destruct (decide (y = x)) as [->|Hyx]; [done|].
    apply (elem_of_disjoint _ _) in Hd. apply (Hd y); [|done].
    unfold gsub. apply elem_of_map. exists y. by rewrite csub_ne. }
  (* forward: a τ step of the original gives one of the image *)
  assert (Hfwd_tau : ∀ q, proc_step (C, E) PTau q →
            ∃ q', proc_step (C, echsubst x b E) PTau q').
  { intros q Hq.
    apply ptau_inv in Hq as
      [ (F & e & e' & -> & Hts & _)
      | [ (F & e & c & e' & -> & Hts & _)
      | [ (F & e & v & e' & -> & Hts & _)
      | [ (F & c & v & e & e' & f & f' & -> & Hts & Htr & _)
      | [ (F & c & e & e' & f & f' & -> & Hts & Htr & HcC & _)
      | (F & e & c & d & e' & -> & Hts & HcC & _) ]]]]].
    - apply (tstep_chsubst x b) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepBeta.
    - apply (tstep_chsubst x b) in Hts. simpl in Hts.
      destruct (exist_fresh (C ∪ echans (echsubst x b F) ∪ fchans (chsubst x b e))) as [z Hz].
      destruct (new_retarget _ _ _ z Hts) as [e'' He''].
      eexists. rewrite echsubst_disj_union1. apply PStepNew; [done|set_solver..].
    - apply (tstep_chsubst x b) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepSpawn.
    - apply (tstep_chsubst x b) in Hts, Htr. eexists.
      rewrite echsubst_disj_union2. by eapply PStepMsg.
    - assert (c ≠ x) by set_solver.
      apply (tstep_chsubst x b) in Hts, Htr. simpl in Hts, Htr.
      rewrite csub_ne in Hts, Htr by done. eexists.
      rewrite echsubst_disj_union2. by eapply PStepClose.
    - assert (c ≠ x) by set_solver.
      apply (tstep_chsubst x b) in Hts. simpl in Hts. rewrite gsub_upair, csub_ne in Hts by done.
      eexists. rewrite echsubst_disj_union1. by eapply PStepLink. }
  assert (Hfwd_sess : ∀ σ q, proc_step (C, E) (PSess σ) q →
            ∃ q', proc_step (C, echsubst x b E) (PSess (ssub x b σ)) q').
  { intros σ q Hq. apply proc_step_sess_inv in Hq as (F & e & e' & HE & Hst & Hd & _).
    pose proof (Hoff _ _ _ _ HE Hst Hd) as Hx.
    apply (tstep_chsubst x b) in Hst. simpl in Hst. eexists.
    rewrite HE, echsubst_disj_union1. apply PStepSession; [done|].
    by rewrite subjs_ssub, gsub_id. }
  assert (Hoffers : ∀ k, offered_p Σ (C, E) k ↔ offered_p Σ (C, echsubst x b E) k).
  { intros k. split.
    - intros (σ & q & Hq & Hsel). pose proof Hq as Hq'.
      apply proc_step_sess_inv in Hq' as (F & e & e' & HE & Hst & Hd & _).
      pose proof (Hoff _ _ _ _ HE Hst Hd) as Hx.
      destruct (Hfwd_sess σ q Hq) as [q' Hq''].
      exists (ssub x b σ), q'. split; [done|].
      assert (ssub_rel x b σ (ssub x b σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select x b Σ σ (ssub x b σ) k Hr); [|done].
      by rewrite subjs_ssub, gsub_id.
    - intros (σ' & q & Hq & Hsel).
      apply proc_step_sess_inv in Hq as (F' & e1 & e1' & HE & Hst & Hd & _).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      destruct (tstep_chsubst_back x b e σ' e1' Hst) as (σ & f & Hf & Hr).
      pose proof (ssub_rel_subjs _ _ _ _ Hr) as Hs.
      assert (x ∉ subjs σ) as Hx.
      { apply (Hpre F e σ f eq_refl Hf). by rewrite <-Hs. }
      rewrite gsub_id in Hs by done.
      exists σ, (C ∖ sentc σ, F ⊎ {[+ f +]}). split.
      + apply PStepSession; [done|]. by rewrite <-Hs.
      + by apply (ssub_rel_select x b Σ σ σ' k Hr). }
  apply Prel_S_iff. split_and!.
  - (* P-Stop *)
    intros Hpirr.
    assert (pirred (C, E)) as Hp0.
    { intros π q Hq. destruct π as [|σ].
      - destruct (Hfwd_tau q Hq) as [q' Hq']. by apply (Hpirr PTau q').
      - destruct (Hfwd_sess σ q Hq) as [q' Hq']. by apply (Hpirr (PSess (ssub x b σ)) q'). }
    destruct (Hirr Hp0) as (v & E1 & Heq & Hv & HVv & HE1).
    injection Heq as -> ->.
    exists v, (echsubst x b E1). split_and!.
    + rewrite echsubst_disj_union, echsubst_singleton.
      assert (x ∉ dom (tenv_of Σ)) as HxΣ' by (unfold tenv_of; by rewrite dom_fmap_L).
      by rewrite (Vrel_chsubst_id _ _ _ _ _ x b HxΣ' HVv).
    + done.
    + done.
    + intros e0 He0. unfold echsubst in He0.
      apply elem_of_gmultiset_map in He0 as (f0 & -> & Hf0). by rewrite (HE1 _ Hf0).
  - (* readiness *)
    intros Hnirr Hs.
    assert (stable_p (C, E)) as Hs0.
    { intros q Hq. destruct (Hfwd_tau q Hq) as [q' Hq']. exact (Hs q' Hq'). }
    assert (∀ E1 v, (C, E) = (∅, {[+ v +]} ⊎ E1) → is_val v → (∀ e, e ∈ E1 → e = EUnit) →
              terminated (C, echsubst x b E)) as Hterm.
    { intros E1 v Heq Hv HE1. injection Heq as -> ->.
      exists (chsubst x b v), (echsubst x b E1). split_and!.
      - by rewrite echsubst_disj_union, echsubst_singleton.
      - by rewrite is_val_chsubst.
      - intros e0 He0. unfold echsubst in He0.
        apply elem_of_gmultiset_map in He0 as (f0 & -> & Hf0). by rewrite (HE1 _ Hf0). }
    assert (¬ pirred (C, E)) as Hni.
    { intros Hp0. apply Hnirr. destruct (Hirr Hp0) as (v & E1 & Heq & Hv & _ & HE1).
      apply terminated_pirred. by apply (Hterm E1 v). }
    destruct (Hrdy Hni Hs0) as [Hv Ha]. split.
    + intros Hno. destruct (Hv (λ k Ho, Hno k (proj1 (Hoffers k) Ho)))
        as (v & E1 & Heq & Hvv & HE1).
      by apply (Hterm E1 v).
    + intros k e He Hk. destruct (Ha k e He) as (k' & e' & Ho & He' & Hlt).
      { intros Ho. apply Hk. by apply Hoffers. }
      exists k', e'. split_and!; [by apply Hoffers|done|done].
  - (* steps of the image *)
    intros π q Hst. destruct π as [|σ'].
    + (* τ *)
      simpl. split.
      2: { (* the giving clause of an internal link *)
        intros (C0 & F' & e' & c & d & e'' & HeqP & Hts & HcC & Hq) Hd.
        injection HeqP as <- HeqE. subst q.
          apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
          apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
          destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
          injection Hα as Hcd.
          destruct (tstep_link_shape _ _ _ Hf0) as (c0 & d0 & ->).
          assert (c ≠ x) as Hcx by set_solver.
          rewrite <-echsubst_disj_union1.
          assert (∀ C', C' ⊆ C ∖ {[c]} ∪ {[b]} → b ∈ C → C' ## dom Σ) as Hguard.
          { intros C' HC' HbC'. apply elem_of_disjoint. intros y Hy1 Hy2.
            apply HC' in Hy1. apply elem_of_union in Hy1 as [Hy1| ->%elem_of_singleton].
            - by apply (elem_of_disjoint _ _) in Hd; apply (Hd y).
            - by apply (HbC HbC'). }
          destruct (decide (x = c0 ∨ x = d0)) as [Hx|Hx].
          { (* the original links the junk x with a restricted d1 *)
            assert (∃ d1, {[c0; d0]} = ({[x; d1]} : gset chan)) as [d1 Hxd1].
            { destruct Hx as [<-|<-]; [by exists d0|exists c0; by rewrite upair_comm]. }
            rewrite Hxd1 in Hf0, Hcd. rewrite gsub_upair, csub_hit in Hcd.
            assert (d1 ≠ x) as Hd1x.
            { intros ->. apply (Hoff F f (SLink {[x; x]}) f0); [done|done| |simpl; set_solver].
              simpl. set_solver. }
            rewrite csub_ne in Hcd by done.
            assert (d1 ∈ C) as Hd1C.
            { destruct (decide (d1 ∈ C)) as [|Hn]; [done|]. exfalso.
              apply (Hoff F f (SLink {[x; d1]}) f0); [done|done| |simpl; set_solver].
              simpl. set_solver. }
            rewrite upair_comm in Hf0.
            symmetry in Hcd.
            assert (c ∈ ({[b; d1]} : gset chan)) as Hc'.
            { rewrite Hcd. apply elem_of_union; left. by apply elem_of_singleton. }
            assert (b ≠ d1 → (c = b ∧ d = d1) ∨ (c = d1 ∧ d = b)) as Hcases.
            { intros Hbd. apply upair_eq_inv in Hcd; [|done]. naive_solver. }
            assert ((C ∖ {[d1]}) ## dom Σ) as Hd'.
            { destruct (decide (b = d1)) as [->|Hbd].
              - assert (c = d1) as ->.
                { apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton]; done. }
                done.
              - destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
                apply Hguard; [|done]. intros y Hy. apply elem_of_difference in Hy as [Hy _].
                destruct (decide (y = b)) as [->|Hyb].
                + apply elem_of_union; right. by apply elem_of_singleton.
                + apply elem_of_union; left. apply elem_of_difference.
                  split; [done|]. by intros ->%elem_of_singleton. }
            pose proof (proj2 (Hstep _ _ (PStepLink C F f d1 x f0 Hf0 Hd1C))
              ltac:(exists C, F, f, d1, x, f0; split_and!; done) Hd') as HP0.
            refine (imp4 _ _ _ _ _ _ (proj2 HP0 _ _ eq_refl b) (λ HP', _) _ _ _ _);
              [|done|set_solver| |done].
            2: { intros Hb. apply HbC. set_solver. }
            destruct (decide (b = d1)) as [->|Hbd].
            - assert (c = d1 ∧ d = d1) as [-> ->].
              { assert (d ∈ ({[d1; d1]} : gset chan)) as Hd1.
                { rewrite Hcd. apply elem_of_union; right. by apply elem_of_singleton. }
                apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton];
                apply elem_of_union in Hd1 as [?%elem_of_singleton|?%elem_of_singleton]; done. }
              rewrite echsubst_refl. by rewrite echsubst_collapse in HP'.
            - rewrite echsubst_chain in HP' by done.
              destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
              apply (Prel_swap_restricted b d1) in HP'; [|by apply HbC|].
              2: { intros Hin. apply (elem_of_disjoint _ _) in Hd. apply (Hd d1); [set_solver|done]. }
              unfold pswap in HP'. simpl in HP'.
              assert (gswap b d1 (C ∖ {[d1]}) = C ∖ {[b]}) as Hg.
              { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
                repeat case_decide; subst; set_solver. }
              rewrite Hg, msswap_echsubst_flip in HP'. done. }
          assert (x ∉ ({[c0; d0]} : gset chan)) as Hx'.
          { intros Hin. apply elem_of_union in Hin as [?%elem_of_singleton|?%elem_of_singleton];
              apply Hx; auto. }
          rewrite gsub_id in Hcd by done. rewrite <-Hcd in Hf0.
          assert (d ≠ x) as Hdx.
          { intros ->. apply Hx'. rewrite <-Hcd. apply elem_of_union; right.
            by apply elem_of_singleton. }
          pose proof (proj2 (Hstep _ _ (PStepLink C F f c d f0 Hf0 HcC))
            ltac:(exists C, F, f, c, d, f0; split_and!; done) Hd) as HP0.
          assert (x ∉ C ∖ {[c]}) as HxC'.
          { intros Hin. apply elem_of_difference in Hin as [? _]. done. }
          destruct (decide (b = c)) as [->|Hbc].
          { refine (imp4 _ _ _ _ _ _ (proj2 HP0 _ _ eq_refl d) (λ HP', _) _ _ _ _);
              [|done|done| |done].
            2: { intros Hdin HdΣ. apply (elem_of_disjoint _ _) in Hd. by apply (Hd d). }
            by rewrite echsubst_retarget. }
          refine (imp4 _ _ _ _ _ _ (proj2 HP0 _ _ eq_refl b) (λ HP', _) _ _ _ _);
            [|done|done| |done].
          2: { intros Hb. apply HbC. by apply elem_of_difference in Hb as [? _]. }
          by rewrite echsubst_comm in HP'. }
      intros Hd.
      apply ptau_inv in Hst as
        [ (F' & e' & e'' & HeqE & Hts & ->)
        | [ (F' & e' & c & e'' & HeqE & Hts & HcC & HcF & Hce & ->)
        | [ (F' & e' & v' & e'' & HeqE & Hts & ->)
        | [ (F' & c & v' & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->)
        | [ (F' & c & e' & e'' & g' & g'' & HeqE & Hts & Htr & HcC & ->)
        | (F' & e' & c & d & e'' & HeqE & Hts & HcC & ->) ]]]]].
      * (* β *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        apply eq_sym, lsub_beta in Hα as ->.
        destruct (Hstep_tau _ (PStepBeta _ _ _ _ Hf0) Hd) as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        rewrite <-echsubst_disj_union1. by apply IH.
      * (* new *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        destruct (decide (c = b)) as [->|Hcb].
        { (* new at b: the substitution was trivial *)
          assert (x ∉ fchans f) as Hxf by (intros Hx; by apply Hce, fchans_chsubst_hit).
          assert (x ∉ echans F) as HxF by (intros Hx; by apply HcF, echans_echsubst_hit).
          rewrite (chsubst_id x b f) in Hts, Hce by done.
          rewrite (echsubst_id x b F) in HcF |- * by done.
          exact (Hstep_tau _ (PStepNew C F f b e'' Hts HcC HcF Hce) Hd). }
        destruct (decide (c = x)) as [->|Hcx].
        { (* new at x: freshen through z, then transpose back *)
          destruct (exist_fresh (C ∪ dom Σ ∪ echans F ∪ fchans f ∪ {[x; b]})) as [z Hz].
          destruct (tstep_chsubst_new_inv x b f x e'' Hts z) as (f0 & Hf0 & ->);
            [set_solver..|].
          assert (proc_step (C, F ⊎ {[+ f +]}) PTau (C ∪ {[z]}, F ⊎ {[+ f0 +]})) as Horig.
          { apply PStepNew; [done|set_solver..]. }
          destruct (Hstep_tau _ Horig ltac:(simpl; set_solver)) as (N & W1 & HN & Hfr & HP').
          exists N, W1. split_and!; [done|done|].
          apply (IH _ _ _ _ b) in HP'; [|done|set_solver| |done].
          2: { intros Hb. apply HbC. set_solver. }
          apply (Prel_swap_restricted x z) in HP'; [|done|set_solver].
          unfold pswap in HP'. simpl in HP'.
          rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP'.
          rewrite (msswap_fresh x z (echsubst x b F)) in HP';
            [|apply echans_echsubst_notin; congruence|].
          2: { pose proof (echans_echsubst_sub x b F) as Hsub. set_solver. }
          assert (gswap x z (C ∪ {[z]}) = C ∪ {[x]}) as Hg.
          { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
            repeat case_decide; subst; set_solver. }
          rewrite Hg in HP'.
          assert (eswap x z (chsubst x b f0) = chsubst z x (chsubst x b f0)) as He.
          { rewrite eswap_comm. rewrite <-(chsubst_id x z (chsubst x b f0)) at 1;
              [apply eswap_chsubst_flip|]. apply fchans_chsubst_notin. congruence. }
          by rewrite <-He. }
        assert (c ∉ fchans f) as Hcf.
        { pose proof (fchans_chsubst_sup x b f). set_solver. }
        destruct (tstep_chsubst_new_inv x b f c e'' Hts c Hcf Hcx Hcb) as (f0 & Hf0 & ->).
        rewrite chsubst_refl.
        assert (c ∉ echans F) as HcF0.
        { pose proof (echans_echsubst_sup x b F). set_solver. }
        destruct (Hstep_tau _ (PStepNew C F f c f0 Hf0 HcC HcF0 Hcf) Hd)
          as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        rewrite <-echsubst_disj_union1. apply IH; [done|set_solver| |done|done].
        intros Hb. apply HbC. set_solver.
      * (* spawn *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
        destruct (Hstep_tau _ (PStepSpawn _ _ _ _ _ Hf0) Hd) as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        apply (IH _ _ _ _ b) in HP'; [|done..].
        by rewrite !echsubst_disj_union, !echsubst_singleton in HP'.
      * (* internal message *)
        apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0 Hw0. subst v'.
        apply tstep_chsubst_recv_inv_subst in Htr as (c1 & g0 & Hc1 & Hg0 & ->).
        assert (c0 ≠ x) as Hc0x.
        { intros ->. apply (Hoff (F2 ⊎ {[+ g +]}) h (SSend x w0) h0); [multiset_solver|done| |];
            simpl; set_solver. }
        assert (c1 ≠ x) as Hc1x.
        { intros ->. apply (Hoff (F2 ⊎ {[+ h +]}) g (SRecv x w0) g0); [multiset_solver|done| |];
            simpl; set_solver. }
        rewrite csub_ne in Hc0, Hc1 by done. subst c0 c1.
        destruct (Hstep_tau _ (PStepMsg C F2 c w0 h h0 g g0 Hh0 Hg0) Hd)
          as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        apply (IH _ _ _ _ b) in HP'; [|done..]. by rewrite echsubst_disj_union2 in HP'.
      * (* internal close *)
        apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0.
        apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα2 & ->); [|done].
        destruct α as [|[c1 w1|c1 w1|c1|cd1]| |]; simpl in Hα2; try discriminate.
        injection Hα2 as Hc1.
        assert (c0 ≠ x) as Hc0x.
        { intros ->. apply (Hoff (F2 ⊎ {[+ g +]}) h (SClos x) h0); [multiset_solver|done| |];
            simpl; set_solver. }
        assert (c1 ≠ x) as Hc1x.
        { intros ->. apply (Hoff (F2 ⊎ {[+ h +]}) g (SClos x) g0); [multiset_solver|done| |];
            simpl; set_solver. }
        rewrite csub_ne in Hc0, Hc1 by done. subst c0 c1.
        destruct (Hstep_tau _ (PStepClose C F2 c h h0 g g0 Hh0 Hg0 HcC) Hd)
          as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        apply (IH _ _ _ _ b) in HP'; [|set_solver|set_solver| |done].
        2: { intros Hb. apply HbC. set_solver. }
        by rewrite echsubst_disj_union2 in HP'.
      * (* internal link *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hcd.
        destruct (tstep_link_shape _ _ _ Hf0) as (c0 & d0 & ->).
        assert (c ≠ x) as Hcx by set_solver.
        rewrite <-echsubst_disj_union1.
        assert (∀ C', C' ⊆ C ∖ {[c]} ∪ {[b]} → b ∈ C → C' ## dom Σ) as Hguard.
        { intros C' HC' HbC'. apply elem_of_disjoint. intros y Hy1 Hy2.
          apply HC' in Hy1. apply elem_of_union in Hy1 as [Hy1| ->%elem_of_singleton].
          - by apply (elem_of_disjoint _ _) in Hd; apply (Hd y).
          - by apply (HbC HbC'). }
        destruct (decide (x = c0 ∨ x = d0)) as [Hx|Hx].
        { (* the original links the junk x with a restricted d1 *)
          assert (∃ d1, {[c0; d0]} = ({[x; d1]} : gset chan)) as [d1 Hxd1].
          { destruct Hx as [<-|<-]; [by exists d0|exists c0; by rewrite upair_comm]. }
          rewrite Hxd1 in Hf0, Hcd. rewrite gsub_upair, csub_hit in Hcd.
          assert (d1 ≠ x) as Hd1x.
          { intros ->. apply (Hoff F f (SLink {[x; x]}) f0); [done|done| |simpl; set_solver].
            simpl. set_solver. }
          rewrite csub_ne in Hcd by done.
          assert (d1 ∈ C) as Hd1C.
          { destruct (decide (d1 ∈ C)) as [|Hn]; [done|]. exfalso.
            apply (Hoff F f (SLink {[x; d1]}) f0); [done|done| |simpl; set_solver].
            simpl. set_solver. }
          rewrite upair_comm in Hf0.
          symmetry in Hcd.
          assert (c ∈ ({[b; d1]} : gset chan)) as Hc'.
          { rewrite Hcd. apply elem_of_union; left. by apply elem_of_singleton. }
          assert (b ≠ d1 → (c = b ∧ d = d1) ∨ (c = d1 ∧ d = b)) as Hcases.
          { intros Hbd. apply upair_eq_inv in Hcd; [|done]. naive_solver. }
          assert ((C ∖ {[d1]}) ## dom Σ) as Hd'.
          { destruct (decide (b = d1)) as [->|Hbd].
            - assert (c = d1) as ->.
              { apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton]; done. }
              done.
            - destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
              apply Hguard; [|done]. intros y Hy. apply elem_of_difference in Hy as [Hy _].
              destruct (decide (y = b)) as [->|Hyb].
              + apply elem_of_union; right. by apply elem_of_singleton.
              + apply elem_of_union; left. apply elem_of_difference.
                split; [done|]. by intros ->%elem_of_singleton. }
          destruct (Hstep_tau _ (PStepLink C F f d1 x f0 Hf0 Hd1C) Hd')
            as (N & W1 & HN & Hfr & HP').
          exists N, W1. split_and!; [done|done|].
          apply (IH _ _ _ _ b) in HP'; [|done|set_solver| |done].
          2: { intros Hb. apply HbC. set_solver. }
          destruct (decide (b = d1)) as [->|Hbd].
          - assert (c = d1 ∧ d = d1) as [-> ->].
            { assert (d ∈ ({[d1; d1]} : gset chan)) as Hd1.
              { rewrite Hcd. apply elem_of_union; right. by apply elem_of_singleton. }
              apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton];
              apply elem_of_union in Hd1 as [?%elem_of_singleton|?%elem_of_singleton]; done. }
            rewrite echsubst_refl. by rewrite echsubst_collapse in HP'.
          - rewrite echsubst_chain in HP' by done.
            destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
            apply (Prel_swap_restricted b d1) in HP'; [|by apply HbC|].
            2: { intros Hin. apply (elem_of_disjoint _ _) in Hd. apply (Hd d1); [set_solver|done]. }
            unfold pswap in HP'. simpl in HP'.
            assert (gswap b d1 (C ∖ {[d1]}) = C ∖ {[b]}) as Hg.
            { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
              repeat case_decide; subst; set_solver. }
            rewrite Hg, msswap_echsubst_flip in HP'. done. }
        assert (x ∉ ({[c0; d0]} : gset chan)) as Hx'.
        { intros Hin. apply elem_of_union in Hin as [?%elem_of_singleton|?%elem_of_singleton];
            apply Hx; auto. }
        rewrite gsub_id in Hcd by done. rewrite <-Hcd in Hf0.
        assert (d ≠ x) as Hdx.
        { intros ->. apply Hx'. rewrite <-Hcd. apply elem_of_union; right.
          by apply elem_of_singleton. }
        destruct (Hstep_tau _ (PStepLink C F f c d f0 Hf0 HcC) Hd)
          as (N & W1 & HN & Hfr & HP').
        exists N, W1. split_and!; [done|done|].
        assert (x ∉ C ∖ {[c]}) as HxC'.
        { intros Hin. apply elem_of_difference in Hin as [? _]. done. }
        destruct (decide (b = c)) as [->|Hbc].
        { apply (IH _ _ _ _ d) in HP'; [|done|done| |done].
          2: { intros Hdin HdΣ. apply (elem_of_disjoint _ _) in Hd. by apply (Hd d). }
          by rewrite echsubst_retarget. }
        apply (IH _ _ _ _ b) in HP'; [|done|done| |done].
        2: { intros Hb. apply HbC. by apply elem_of_difference in Hb as [? _]. }
        by rewrite echsubst_comm in HP'.
    + (* external steps of the image *)
      apply proc_step_sess_inv in Hst as (F' & e1 & e1' & HE & Hts & Hd & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      destruct σ' as [c w'|c w'|c|cd]; simpl.
      * (* receive: the value may mention x; freshen through z *)
        destruct (exist_fresh (fchans w' ∪ fchans e ∪ echans F ∪ C ∪ dom Σ ∪ {[x; b]}))
          as [z Hz].
        destruct (tstep_chsubst_recv_inv_swap x b z e c w' e1')
          as (c0 & f & Hc0 & Hf & ->); [done|sset|sset|sset|done|sset|].
        assert (c0 ≠ x) as Hc0x.
        { intros ->. apply (Hoff F e (SRecv x (eswap x z w')) f); [done|done| |];
            simpl; sset. }
        rewrite csub_ne in Hc0 by done. subst c0.
        destruct (Hstep _ _ (PStepSession C F e (SRecv c (eswap x z w')) f Hf Hd))
          as (Σ1 & m & U & s & k & Hhd & Hc1 & H).
        exists Σ1, m, U, s, k. split_and!; [done|done|].
        intros W' j Θ2' HW' Hj Hfr Hok HVw.
        assert (x ∉ dom (<[c := (s, pt_shift 1 k)]> Σ1)) as HxΣr.
        { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
        assert (z ∉ dom (<[c := (s, pt_shift 1 k)]> Σ1)) as HzΣr.
        { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
        assert (z ∉ dom Θ2') as HzΘ by (rewrite <-(Vrel_fchans _ _ _ _ _ HVw); sset).
        set (Σr := <[c := (s, pt_shift 1 k)]> Σ1) in *.
        set (Θ2 := tenvswap x z Θ2').
        assert (dom Θ2 ## C) as Hfr2.
        { unfold Θ2. rewrite dom_tenvswap. apply elem_of_disjoint. intros y Hy HyC.
          apply elem_of_gswap' in Hy. unfold cswap in Hy.
          repeat case_decide; subst; [sset|sset|].
          by apply (elem_of_disjoint _ _) in Hfr; apply (Hfr y). }
        assert (recv_ok W' Σr Θ2) as Hok2.
        { apply (recv_ok_swap x z) in Hok. rewrite senvswap_fix in Hok by done. done. }
        assert (Vrel j W' Θ2 (payload_at m U k) (eswap x z w')) as HVw2 by (by apply Vrel_swap).
        pose proof (H W' j Θ2 HW' Hj Hfr2 Hok2 HVw2) as HP1.
        cbn [sentc fst snd] in HP1. rewrite ?difference_empty_L in HP1.
        assert (x ∉ dom Θ2) as HxΘ2.
        { unfold Θ2. rewrite dom_tenvswap, elem_of_gswap', cswap_l. done. }
        apply (IHn j ltac:(lia) _ _ _ _ _ x b) in HP1.
        2: { unfold recv_env. rewrite dom_union_L, !dom_difference_L. intros Hx.
             apply elem_of_union in Hx as [Hx|Hx]; apply elem_of_difference in Hx as [Hx _];
               [done|]. revert Hx. apply not_elem_of_dom. unfold tenv_ones.
             rewrite lookup_omap. by apply not_elem_of_dom in HxΘ2 as ->. }
        2: { intros Hx. apply elem_of_union in Hx as [Hx|Hx]; [done|].
             unfold recv_back in Hx. sset. }
        2: { intros Hb. apply elem_of_union in Hb as [Hb|Hb].
             - unfold recv_env. rewrite dom_union_L, !dom_difference_L. intros Hb'.
               apply elem_of_union in Hb' as [Hb'|Hb']; apply elem_of_difference in Hb' as [Hb' _].
               + apply (HbC Hb). apply senv_hd_dom in Hhd. unfold Σr in Hb'.
                 rewrite dom_insert_L in Hb'. apply elem_of_union in Hb' as [Hb'|Hb'];
                   sset.
               + apply (elem_of_disjoint _ _) in Hfr2. apply (Hfr2 b); [|done].
                 revert Hb'. unfold tenv_ones. rewrite !elem_of_dom, lookup_omap.
                 intros [o Ho]. destruct (Θ2 !! b) eqn:E; [by eexists|done].
             - by apply (recv_back_not_env W' _ _ _ Hok2). }
        2: done.
        apply (Prel_swap x z) in HP1. unfold pswap in HP1. simpl in HP1. unfold Θ2 in HP1.
        rewrite <-recv_env_swap, senvswap_fix, tenvswap_involutive in HP1 by done.
        rewrite gswap_union, <-recv_back_swap, senvswap_fix, tenvswap_involutive in HP1
          by done.
        rewrite gswap_fresh in HP1 by sset.
        rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP1.
        rewrite (msswap_fresh x z (echsubst x b F)) in HP1;
          [|apply echans_echsubst_notin; congruence|].
        2: { pose proof (echans_echsubst_sub x b F) as Hsub. sset. }
        cbn [sentc fst snd]. rewrite ?difference_empty_L. exact HP1.
      * (* send: the value carries no x *)
        apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0 Hw0. subst w'.
        assert (c0 ≠ x) as Hc0x.
        { intros ->. apply (Hoff F e (SSend x w0) f); [done|done| |]; simpl; sset. }
        rewrite csub_ne in Hc0 by done. subst c0.
        destruct (Hstep _ _ (PStepSession C F e (SSend c w0) f Hf Hd))
          as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd & Hd0v & Hc0' & Hcv & Hdom & Hsplit &
              HdΣ & HVw & HP').
        assert (x ∉ fchans w0) as Hxw.
        { rewrite (Vrel_fchans _ _ _ _ _ HVw), dom_union_L.
          unfold tenv_of. rewrite dom_fmap_L. apply senv_hd_dom in Hhd.
          rewrite dom_union_L in Hhd. sset. }
        rewrite (chsubst_id x b w0) by done.
        exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done.
        refine (imp4 _ _ _ _ _ _ (proj2 HP' _ _ eq_refl b) (λ HP', _) _ _ _ _).
        { by rewrite echsubst_disj_union1 in HP'. }
        { rewrite dom_insert_L, dom_union_L. apply senv_hd_dom in Hhd.
          rewrite dom_union_L in Hhd. destruct Hsplit as [Hsub _].
          intros Hx. apply elem_of_union in Hx as [Hx|Hx]; [sset|].
          apply elem_of_union in Hx as [Hx|Hx]; [sset|].
          apply Hsub in Hx. rewrite Hdom in Hx. sset. }
        { sset. }
        { intros Hb. rewrite dom_insert_L, dom_union_L. destruct Hsplit as [Hsub _].
          apply elem_of_difference in Hb as [HbC' Hbs]. simpl in Hbs.
          apply senv_hd_dom in Hhd. rewrite dom_union_L in Hhd.
          pose proof (HbC HbC') as HbΣ.
          intros Hb'. apply elem_of_union in Hb' as [Hb'|Hb']; [sset|].
          apply elem_of_union in Hb' as [Hb'|Hb']; [sset|].
          apply Hsub in Hb'. rewrite Hdom in Hb'. sset. }
        { done. }
      * (* close *)
        apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0.
        assert (c0 ≠ x) as Hc0x.
        { intros ->. apply (Hoff F e (SClos x) f); [done|done| |]; simpl; sset. }
        rewrite csub_ne in Hc0 by done. subst c0.
        destruct (Hstep _ _ (PStepSession C F e (SClos c) f Hf Hd))
          as (Σ1 & k & Hhd & Hc1 & HP').
        exists Σ1, k. split_and!; [done|done|].
        refine (imp4 _ _ _ _ _ _ (proj2 HP' _ _ eq_refl b) (λ HP', _) _ _ _ _).
        { by rewrite echsubst_disj_union1 in HP'. }
        { apply senv_hd_dom in Hhd. sset. }
        { sset. }
        { intros Hb. apply senv_hd_dom in Hhd. pose proof (HbC ltac:(sset)). sset. }
        { done. }
      * (* link *)
        apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hcd.
        assert (x ∉ cd0) as Hx.
        { apply (Hpre F e (SLink cd0) f eq_refl Hf). simpl. by rewrite <-Hcd. }
        rewrite gsub_id in Hcd by done. subst cd.
        destruct (Hstep _ _ (PStepSession C F e (SLink cd0) f Hf Hd))
          as (c1 & d1 & Σ1 & sc & sd & kc & kd & -> & Hne & HΣ & Hc1 & Hd1 & Hdu & Hal & HP').
        exists c1, d1, Σ1, sc, sd, kc, kd. split_and!; try done.
        refine (imp4 _ _ _ _ _ _ (proj2 HP' _ _ eq_refl b) (λ HP', _) _ _ _ _).
        { by rewrite echsubst_disj_union1 in HP'. }
        { rewrite HΣ in HxΣ. rewrite !dom_insert_L in HxΣ. sset. }
        { sset. }
        { intros Hb. rewrite HΣ in HbC. rewrite !dom_insert_L in HbC.
          pose proof (HbC ltac:(sset)). sset. }
        { done. }
Qed.

(** ** Substituting a channel inside a related term (E-level) *)

Section sub_helpers.
  Context (W : world) (c d : chan) (Hcd : c ≠ d).

  Lemma fchans_move Θ Θ' e :
    tenv_move W c d Θ Θ' → fchans e = dom Θ → fchans (chsubst c d e) = dom Θ'.
  Proof.
    intros Hm He. destruct (decide (c ∈ dom Θ)) as [Hc|Hc].
    - apply set_eq. intros y. rewrite (move_dom W c d Θ Θ' y Hm). split.
      + intros Hy. apply fchans_chsubst in Hy. rewrite <-He.
        apply elem_of_union in Hy as [Hy| ->%elem_of_singleton];
          [apply elem_of_difference in Hy as [? ?]; split; [set_solver|by left]|].
        split; [congruence|right; split; [done|by rewrite He]].
      + intros [Hyc [Hy|[-> _]]].
        * rewrite <-He in Hy. apply (fchans_chsubst_sup c d e) in Hy.
          apply elem_of_union in Hy as [?|?%elem_of_singleton]; [done|congruence].
        * apply fchans_chsubst_hit. by rewrite He.
    - rewrite chsubst_id by (by rewrite He).
      rewrite (move_none W c d Θ Θ' Hm) by (by apply not_elem_of_dom). done.
  Qed.

  Lemma move_singleton c0 o Θ' :
    tenv_move W c d {[c0 := o]} Θ' →
    (c0 = c ∧ Θ' = {[d := o]}) ∨ (c0 ≠ c ∧ Θ' = {[c0 := o]}).
  Proof.
    intros Hm. destruct (decide (c0 = c)) as [->|Hne].
    - left. split; [done|]. destruct Hm as (Hc & Ho & Hj & _).
      rewrite lookup_singleton_eq, lookup_singleton_ne in Hj by done.
      apply join_l_none in Hj.
      apply map_eq. intros k. destruct (decide (k = c)) as [->|Hkc].
      { rewrite Hc, lookup_singleton_ne by done. done. }
      destruct (decide (k = d)) as [->|Hkd]; [by rewrite lookup_singleton_eq|].
      rewrite Ho, !lookup_singleton_ne by done. done.
    - right. split; [done|]. apply (move_none W c d); [done|].
      by rewrite lookup_singleton_ne.
  Qed.
End sub_helpers.

(** A session step of a related term acts on channels its environment holds. *)
Lemma Erel_subjs n W Θ T F e σ e' :
  Erel (S n) W Θ T F e → tstep e (LSess σ) e' → subjs σ ⊆ dom Θ.
Proof.
  intros HE Hst. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc.
  destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
  - destruct Hc as (Θ1 & m & U & s & k & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (Θ1 & k & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & _).
    destruct H2 as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L;
    destruct H1 as [[_ ->]|(g & _ & [-> | ->])]; rewrite ?dom_insert_L; set_solver.
Qed.

(** A stable, ready term holding one end each of two aliased channels
    acts on neither, unless by a link. *)
Lemma fusion_exclusion n W Θ T F e c d e1 e2 σ e' :
  strict W → Erel (S n) W Θ T F e → Θ !! c = Some (One e1) → Θ !! d = Some (One e2) →
  w_eq W e1.2 e2.2 → c ≠ d → tstep e (LSess σ) e' →
  (c ∈ subjs σ ∨ d ∈ subjs σ) → ∃ cd, σ = SLink cd.
Proof.
  intros [HWf Hirr] HE Hc Hd Hx Hcd Hst Hsub.
  destruct σ as [c0 w|c0 w|c0|cd]; [exfalso..|by eexists].
  all: assert (stable_t e) as Hs by (intros α f Hf;
         destruct (tstep_same_act _ _ _ _ _ Hst Hf) as (a & Ha & Ha');
         destruct a, α; simpl in *; done).
  all: assert (¬ irred e) as Hni by (intros Hi; by apply (Hi _ _ Hst)).
  all: pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep; simpl in Hstep.
  all: apply Erel_S_iff in HE as (_ & Hrdy & _).
  all: destruct (Hrdy Hni) as [Hr _]; destruct (Hr Hs) as [_ Ha].
  all: assert (∀ k, offered_t Θ e k → k.1 = c0) as Hsame
         by (intros k (σ' & f & Hf & Hsel); apply selects_subj in Hsel;
             destruct (tstep_same_act _ _ _ _ _ Hst Hf) as (a & Ha1 & Ha2);
             destruct a, σ'; simpl in *; try done; set_solver).
  all: simpl in Hsub; assert (c0 = c ∨ c0 = d) as [->| ->] by set_solver.
  (* the other channel's end is not offered, and lies above no offer *)
  all: match goal with
       | |- _ => idtac
       end.
  all: first
    [ (destruct (Ha (d, false) e2) as (k' & f & Ho & Hf & Hlt);
       [unfold tenv_entry; simpl; by rewrite Hd
       |intros Ho; apply Hsame in Ho; simpl in Ho; congruence|];
       pose proof (Hsame _ Ho) as Hk'; destruct k' as [k1 [|]]; simpl in Hk'; subst k1;
       unfold tenv_entry in Hf; simpl in Hf; rewrite Hc in Hf; [done|];
       injection Hf as <-; unfold entry_head in Hlt; simpl in Hlt;
       apply (Hirr e2.2); eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|apply HWf])
    | (destruct (Ha (c, false) e1) as (k' & f & Ho & Hf & Hlt);
       [unfold tenv_entry; simpl; by rewrite Hc
       |intros Ho; apply Hsame in Ho; simpl in Ho; congruence|];
       pose proof (Hsame _ Ho) as Hk'; destruct k' as [k1 [|]]; simpl in Hk'; subst k1;
       unfold tenv_entry in Hf; simpl in Hf; rewrite Hd in Hf; [done|];
       injection Hf as <-; unfold entry_head in Hlt; simpl in Hlt;
       apply (Hirr e1.2); eapply (wf_lt_eq _ HWf); [exact Hx|exact Hlt|apply HWf]) ].
Qed.

(** ** Junk collapse for terms *)

Lemma tenvswap_fix a b Θ : a ∉ dom Θ → b ∉ dom Θ → tenvswap a b Θ = Θ.
Proof.
  intros Ha Hb. apply map_eq. intros c. rewrite lookup_tenvswap'.
  destruct (decide (c = a)) as [->|?]; [|destruct (decide (c = b)) as [->|?]].
  - rewrite cswap_l. apply not_elem_of_dom in Ha, Hb. by rewrite Ha, Hb.
  - rewrite cswap_r. apply not_elem_of_dom in Ha, Hb. by rewrite Ha, Hb.
  - by rewrite cswap_ne.
Qed.

Lemma ssub_rel_select_t x b Θ σ σ' k :
  ssub_rel x b σ σ' → subjs σ' = subjs σ → selects Θ σ k ↔ selects Θ σ' k.
Proof.
  intros Hr Hs. destruct σ as [c0 w|c0 w|c0|cd0], σ' as [c w'|c w'|c|cd]; simpl in *;
    try done; unfold gsub in *; rewrite ?set_map_singleton_L in Hs.
  all: try (apply (inj singleton) in Hs as ->; done).
  by rewrite Hs.
Qed.

Lemma irred_chsubst x b e : irred (chsubst x b e) → irred e.
Proof. intros H α e' Hst. apply (tstep_chsubst x b) in Hst. by apply (H _ _ Hst). Qed.

Lemma stable_chsubst x b e : stable_t (chsubst x b e) → stable_t e.
Proof.
  intros H α e' Hst. apply (tstep_chsubst x b) in Hst. specialize (H _ _ Hst).
  by destruct α.
Qed.


Lemma irred_chsubst_back x b e : irred e → irred (chsubst x b e).
Proof.
  intros Hi α f' Hf'. destruct α as [|σ'|c'|w'].
  - apply tstep_chsubst_det_inv in Hf' as (α & f & Hf & _); [|done]. by apply (Hi _ _ Hf).
  - destruct (tstep_chsubst_back x b e σ' f' Hf') as (σ & f & Hf & _). by apply (Hi _ _ Hf).
  - destruct (exist_fresh (fchans e ∪ {[x; b]})) as [c0 Hc0].
    destruct (tstep_chsubst_new_inv x b e c' f' Hf' c0) as (f & Hf & _); [set_solver..|].
    by apply (Hi _ _ Hf).
  - apply tstep_chsubst_det_inv in Hf' as (α & f & Hf & _); [|done]. by apply (Hi _ _ Hf).
Qed.

Lemma chsubst_eswap_same a b e : chsubst a b (eswap a b e) = chsubst a b e.
Proof.
  induction e; simpl; f_equal; auto. unfold csub, cswap. repeat case_decide; congruence.
Qed.
Lemma Erel_junk n : ∀ W Θ T F e x b,
  strict W → x ∉ dom Θ → x ≠ b → Erel n W Θ T F e → Erel n W Θ T F (chsubst x b e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros W Θ T F e x b HW HxΘ Hxb HE.
  destruct n as [|n']; [apply Erel_0|].
  revert HW HxΘ.
  induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
  intros HW HxΘ.
  assert (HE0 : Erel (S n') W Θ T F e).
  { apply Erel_S_iff. split_and!; [done|done|]. intros α e' Hst.
    eapply Ecase_gen_mono; [|exact (Hstep α e' Hst)]. by intros ? ? ? ? ? [? _]. }
  (* the term never acts on x *)
  assert (Hnx : ∀ σ e', tstep e (LSess σ) e' → x ∉ subjs σ).
  { intros σ e' Hst Hx. apply HxΘ. by apply (Erel_subjs _ _ _ _ _ _ _ _ HE0 Hst). }
  assert (Hoff : ∀ k, offered_t Θ e k ↔ offered_t Θ (chsubst x b e) k).
  { intros k. split.
    - intros (σ & f & Hf & Hsel). pose proof (Hnx _ _ Hf) as Hx.
      exists (ssub x b σ), (chsubst x b f). split; [by apply (tstep_chsubst x b) in Hf|].
      assert (ssub_rel x b σ (ssub x b σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select_t x b Θ σ (ssub x b σ) k Hr); [|done].
      by rewrite subjs_ssub, gsub_id.
    - intros (σ' & f' & Hf' & Hsel).
      destruct (tstep_chsubst_back x b e σ' f' Hf') as (σ & f & Hf & Hr).
      pose proof (Hnx _ _ Hf) as Hx. pose proof (ssub_rel_subjs _ _ _ _ Hr) as Hs.
      rewrite gsub_id in Hs by done.
      exists σ, f. split; [done|]. by apply (ssub_rel_select_t x b Θ σ σ' k Hr). }
  apply Erel_S_iff. split_and!.
  - intros Hirr. apply irred_chsubst in Hirr as Hirr0. pose proof (Hval Hirr0) as HV.
    rewrite chsubst_id; [done|]. by rewrite (Vrel_fchans _ _ _ _ _ HV).
  - intros Hni. assert (¬ irred e) as Hni0.
    { intros Hi. apply Hni. by apply irred_chsubst_back. }
    destruct (Hrdy Hni0) as [Hr Hf]. split.
    + intros Hs. apply stable_chsubst in Hs as Hs0. destruct (Hr Hs0) as [Hv Ha]. split.
      * intros Hno. rewrite is_val_chsubst. apply Hv. intros k Hk. apply (Hno k).
        by apply Hoff.
      * intros k e1 He1 Hk. destruct (Ha k e1 He1) as (k' & e' & Ho & He' & Hlt).
        { intros Ho. apply Hk. by apply Hoff. }
        exists k', e'. split_and!; [by apply Hoff|done|done].
    + intros Hs k e1 Ho He1. apply stable_chsubst in Hs as Hs0.
      apply (Hf Hs0 k e1); [by apply Hoff|done].
  - intros α f' Hst. destruct α as [|[c' w'|c' w'|c'|cd']|c'|w'].
    + (* β *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      apply eq_sym, lsub_beta in Hα as ->.
      apply IHn; [lia|done..|]. exact (Hstep _ _ Hf).
    + (* receive: freshen the payload's x through z *)
      destruct (exist_fresh (fchans w' ∪ fchans e ∪ dom Θ ∪ {[x; b]})) as [z Hz].
      destruct (tstep_chsubst_recv_inv_swap x b z e c' w' f')
        as (c0 & f & Hc0 & Hf & ->); [done|set_solver|set_solver|set_solver|done|set_solver|].
      pose proof (Hnx _ _ Hf) as Hx. simpl in Hx.
      rewrite csub_ne in Hc0 by set_solver. subst c0.
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct Hc as (Θ1 & m & U & s & k & Hhd & H).
      exists Θ1, m, U, s, k. split; [done|].
      intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hcomp HVw.
      assert (strict W') as HW'' by (by destruct HW' as (_ & _ & _ & ?)).
      assert (Hdom1 : dom Θ1c ⊆ dom Θ).
      { destruct Hhd as (s0 & Hext0 & _). intros y Hy.
        destruct Hext as [[_ ->]|(g & Hg & [-> | ->])]; rewrite ?dom_insert_L in Hy;
          destruct Hext0 as [[_ ->]|(g' & _ & [-> | ->])]; rewrite dom_insert_L;
          apply elem_of_union in Hy as [Hy|Hy]; set_solver. }
      assert (z ∉ dom Θ2) as HzΘ2 by (rewrite <-(Vrel_fchans _ _ _ _ _ HVw); set_solver).
      apply (tenv_comp_swap x z) in Hcomp.
      rewrite (tenvswap_fix x z Θ1c) in Hcomp by set_solver.
      pose proof (H W' j (tenvswap x z Θ2) Θ1c (tenvswap x z Θ') HW' Hj Hext Hcomp
                    (Vrel_swap x z _ _ _ _ _ HVw)) as HE1.
      assert (x ∉ dom (tenvswap x z Θ')) as Hx'.
      { destruct Hcomp as [Hj' _]. rewrite (tenv_join_dom _ _ _ Hj').
        rewrite dom_tenvswap, !elem_of_union, elem_of_gswap', cswap_l.
        intros [Hx1|Hx1]; [set_solver|done]. }
      pose proof (IHn j ltac:(lia) W' _ T F f x b HW'' Hx' Hxb HE1) as HE2.
      apply (Erel_swap x z) in HE2. rewrite tenvswap_involutive in HE2. exact HE2.
    + (* send: the value carries no x *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hw0. pose proof (Hnx _ _ Hf) as Hx. simpl in Hx.
      rewrite csub_ne in Hc0 by set_solver. subst c0 w'.
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct Hc as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & Hhd & Hsp & HVw & Hext & HE').
      assert (x ∉ fchans w0) as Hxw.
      { rewrite (Vrel_fchans _ _ _ _ _ HVw). destruct Hsp as [Hj' _].
        intros Hx2. apply HxΘ. destruct Hhd as (s0 & Hext0 & _).
        assert (x ∈ dom Θr) by (rewrite (tenv_join_dom _ _ _ Hj'); set_solver).
        destruct Hext0 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver. }
      rewrite (chsubst_id x b w0) by done.
      exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; [done..|].
      apply (proj2 HE'); [done|].
      intros Hx2. apply HxΘ. destruct Hhd as (s0 & Hext0 & _). destruct Hsp as [Hj' _].
      destruct (decide (x = c')) as [->|Hxc]; [set_solver|].
      assert (x ∈ dom Θ1) as Hx3.
      { destruct Hext as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L in Hx2; set_solver. }
      assert (x ∈ dom Θr) by (rewrite (tenv_join_dom _ _ _ Hj'); set_solver).
      destruct Hext0 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
    + (* close *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0. pose proof (Hnx _ _ Hf) as Hx. simpl in Hx.
      rewrite csub_ne in Hc0 by set_solver. subst c0.
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct Hc as (Θ1 & k & Hhd & HE').
      exists Θ1, k. split; [done|].
      apply (proj2 HE'); [done|].
      intros Hx2. apply HxΘ. destruct Hhd as (s0 & Hext0 & _).
      destruct Hext0 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
    + (* link *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hcd. pose proof (Hnx _ _ Hf) as Hx. simpl in Hx.
      rewrite gsub_id in Hcd by done. subst cd'.
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct Hc as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & Hdu & Hal & HE').
      exists c1, d1, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|].
      apply (proj2 HE'); [done|].
      intros Hx2. apply HxΘ.
      destruct H2 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L;
      destruct H1 as [[_ ->]|(g' & _ & [-> | ->])]; rewrite ?dom_insert_L; set_solver.
    + (* new: through a fresh c0, then rename c0 to the image's name *)
      intros Hc'.
      destruct (exist_fresh (fchans e ∪ dom Θ ∪ {[x; b; c']})) as [c0 Hc0].
      destruct (tstep_chsubst_new_inv x b e c' f' Hst c0) as (f & Hf & ->); [set_solver..|].
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct (Hc ltac:(set_solver)) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
      exists a, s, s', W1. split_and!; [done|done|done|].
      assert (strict W1) as HW1 by (by destruct Hfr as ((_ & _ & _ & ?) & _)).
      apply (IHn n' ltac:(lia) _ _ _ _ _ x b) in HE'; [|done| |done].
      2: { rewrite dom_insert_L. set_solver. }
      apply (Erel_swap c0 c') in HE'.
      rewrite tenvswap_insert, tenvswap_fix, cswap_l in HE' by set_solver.
      apply (IHn n' ltac:(lia) _ _ _ _ _ c0 c') in HE'; [|done| |set_solver].
      2: { rewrite dom_insert_L. set_solver. }
      by rewrite chsubst_eswap_same in HE'.
    + (* spawn *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
      pose proof (Hstep _ _ Hf) as Hc. simpl in Hc.
      destruct Hc as (Θ1 & Θ2 & ub & lb & Hsp & HVw & HE').
      assert (x ∉ dom Θ1 ∧ x ∉ dom Θ2) as [Hx1 Hx2].
      { destruct Hsp as [Hj' _]. rewrite (tenv_join_dom _ _ _ Hj') in HxΘ. set_solver. }
      exists Θ1, Θ2, ub, lb. split_and!; [done| |].
      * rewrite chsubst_id; [done|]. by rewrite (Vrel_fchans _ _ _ _ _ HVw).
      * by apply IHn; [lia|..].
Qed.

Lemma eswap_chsubst_absent a b e : b ∉ fchans e → eswap a b e = chsubst a b e.
Proof.
  induction e; simpl; intros Hb; f_equal; try (apply IHe || apply IHe1 || apply IHe2 ||
    apply IHe3); try set_solver.
  unfold cswap, csub. repeat case_decide; set_solver.
Qed.

(** Renaming c to a channel d the environment does not hold. *)
Lemma Erel_rename n W Θ T F e c d :
  strict W → d ∉ dom Θ → c ≠ d → Erel n W Θ T F e →
  Erel n W (tenvswap c d Θ) T F (chsubst c d e).
Proof.
  intros HW Hd Hcd HE. apply (Erel_swap c d) in HE.
  rewrite <-(chsubst_eswap_same c d e). apply Erel_junk; [done| |done|done].
  rewrite dom_tenvswap, elem_of_gswap', cswap_l. done.
Qed.

Lemma Vrel_rename n W Θ T v c d :
  d ∉ dom Θ → Vrel n W Θ T v → Vrel n W (tenvswap c d Θ) T (chsubst c d v).
Proof.
  intros Hd HV. rewrite <-eswap_chsubst_absent.
  - by apply Vrel_swap.
  - by rewrite (Vrel_fchans _ _ _ _ _ HV).
Qed.

(** ** Helpers for fusion *)

Section fuse_helpers.
  Context (W : world) (c d : chan) (Hcd : c ≠ d).

  Lemma move_rename_eq Θ Θ' : tenv_move W c d Θ Θ' → Θ !! d = None → Θ' = tenvswap c d Θ.
  Proof.
    intros (Hc & Ho & Hj & _) Hd. rewrite Hd in Hj. apply join_l_none in Hj.
    apply map_eq. intros k. rewrite lookup_tenvswap'.
    destruct (decide (k = c)) as [->|Hkc]; [by rewrite cswap_l, Hc, Hd|].
    destruct (decide (k = d)) as [->|Hkd]; [by rewrite cswap_r, Hj|].
    rewrite cswap_ne by done. by apply Ho.
  Qed.

  Lemma move_ext_given Θ1 Θ1' c0 e Θ1c' :
    tenv_move W c d Θ1 Θ1' → c0 ≠ c → c0 ≠ d → tenv_ext Θ1' c0 e Θ1c' →
    ∃ Θ1c, tenv_ext Θ1 c0 e Θ1c ∧ tenv_move W c d Θ1c Θ1c'.
  Proof.
    intros Hm H1 H2 Hext.
    assert (Θ1' !! c0 = Θ1 !! c0) as E0 by (by apply (move_lookup_ne W c d Θ1 Θ1')).
    destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])].
    - exists (<[c0 := One e]> Θ1). split; [left; by rewrite <-E0|]. by apply move_insert.
    - exists (<[c0 := Both e f]> Θ1). split; [right; exists f; rewrite <-E0; by split; [|left]|].
      by apply move_insert.
    - exists (<[c0 := Both f e]> Θ1). split; [right; exists f; rewrite <-E0; by split; [|right]|].
      by apply move_insert.
  Qed.

  Lemma move_unext Θ Θ' c0 e Θm :
    tenv_move W c d Θ Θ' → tenv_ext Θm c0 e Θ → c0 ≠ c → c0 ≠ d →
    ∃ Θm', tenv_ext Θm' c0 e Θ' ∧ tenv_move W c d Θm Θm'.
  Proof.
    intros Hm Hext H1 H2. pose proof Hm as (Hc & Ho & Hj & Hdd).
    assert (Θ' !! c0 = Θ !! c0) as E0 by (by apply Ho).
    destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])].
    - exists (delete c0 Θ'). split.
      + left. split; [apply lookup_delete_eq|].
        rewrite insert_delete_id; [done|]. rewrite E0. by rewrite lookup_insert_eq.
      + split_and!.
        * by rewrite lookup_delete_ne.
        * intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
          -- by rewrite lookup_delete_eq.
          -- rewrite lookup_delete_ne by done. rewrite Ho by done. by rewrite lookup_insert_ne.
        * rewrite lookup_delete_ne by done. by rewrite !lookup_insert_ne in Hj.
        * intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
    - exists (<[c0 := One f]> Θ'). split.
      + right. exists f. split; [apply lookup_insert_eq|].
        left. rewrite insert_over; [done|]. rewrite E0. by rewrite lookup_insert_eq.
      + split_and!.
        * by rewrite lookup_insert_ne.
        * intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
          -- by rewrite !lookup_insert_eq.
          -- rewrite !lookup_insert_ne by done. rewrite Ho by done. by rewrite lookup_insert_ne.
        * rewrite !lookup_insert_ne by done. by rewrite !lookup_insert_ne in Hj.
        * intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
    - exists (<[c0 := One f]> Θ'). split.
      + right. exists f. split; [apply lookup_insert_eq|].
        right. rewrite insert_over; [done|]. rewrite E0. by rewrite lookup_insert_eq.
      + split_and!.
        * by rewrite lookup_insert_ne.
        * intros k' ? ?. destruct (decide (k' = c0)) as [->|?].
          -- by rewrite !lookup_insert_eq.
          -- rewrite !lookup_insert_ne by done. rewrite Ho by done. by rewrite lookup_insert_ne.
        * rewrite !lookup_insert_ne by done. by rewrite !lookup_insert_ne in Hj.
        * intros e1 e2 A B. apply Hdd; by rewrite lookup_insert_ne.
  Qed.
End fuse_helpers.

Section fuse_helpers2.
  Context (W : world) (c d : chan) (Hcd : c ≠ d).

  (** Taking an end off, in every case of a move. *)
  Lemma move_unext_gen Θ Θ' c0 e Θm :
    tenv_move W c d Θ Θ' → tenv_ext Θm c0 e Θ →
    (c0 ≠ c ∧ c0 ≠ d) ∨ (c0 = c ∧ Θ !! d = None) ∨ (c0 = d ∧ Θ !! c = None) →
    ∃ Θm', tenv_ext Θm' (csub c d c0) e Θ' ∧ tenv_move W c d Θm Θm'.
  Proof.
    intros Hm Hext Hcase.
    destruct Hcase as [[H1 H2]|[[-> Hd]|[-> HΘc]]].
    - rewrite csub_ne by done. by apply (move_unext W c d Θ Θ').
    - rewrite csub_hit. rewrite (move_rename_eq W c d Θ Θ' Hm Hd).
      exists (tenvswap c d Θm). split.
      + apply (tenv_ext_swap c d) in Hext. by rewrite cswap_l in Hext.
      + assert (Θm !! d = None) as Hmd.
        { destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; by rewrite lookup_insert_ne in Hd. }
        split_and!.
        * rewrite lookup_tenvswap', cswap_l. done.
        * intros k ? ?. rewrite lookup_tenvswap', cswap_ne; done.
        * rewrite lookup_tenvswap', cswap_r, Hmd. destruct (Θm !! c); constructor.
        * intros e1 e2 A B. congruence.
    - rewrite csub_ne by done.
      assert (Θ' = Θ) as -> by (by apply (move_none W c d Θ Θ')).
      exists Θm. split; [done|]. apply move_id. apply not_elem_of_dom.
      destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; by rewrite lookup_insert_ne in HΘc.
  Qed.

  (** In a fusion, taking off c's end leaves the rest as it is. *)
  Lemma move_unext_fused_c Θ Θ' e1 e2 e Θm :
    tenv_move W c d Θ Θ' → Θ !! c = Some (One e1) → Θ !! d = Some (One e2) →
    tenv_ext Θm c e Θ → tenv_ext Θm d e Θ' ∧ tenv_move W c d Θm Θm.
  Proof.
    intros Hm Hc Hd Hext.
    destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])];
      [|by rewrite lookup_insert_eq in Hc..].
    rewrite lookup_insert_eq in Hc. injection Hc as <-.
    rewrite lookup_insert_ne in Hd by done.
    split; [|apply move_id; by apply not_elem_of_dom].
    destruct Hm as (Hc' & Ho & Hj & _).
    rewrite lookup_insert_eq, lookup_insert_ne, Hd in Hj by done.
    right. exists e2. split; [done|].
    assert (∀ o, Θ' !! d = Some o → Θ' = <[d := o]> Θm) as Heq.
    { intros o Ho'. apply map_eq. intros k. destruct (decide (k = d)) as [->|Hkd].
      - by rewrite lookup_insert_eq.
      - rewrite lookup_insert_ne by done. destruct (decide (k = c)) as [->|Hkc].
        + by rewrite Hc', Hr.
        + rewrite Ho by done. by rewrite lookup_insert_ne. }
    inversion Hj as [| | |? ? A B E|? ? A B E]; [left|right]; by apply Heq.
  Qed.

  (** In a fusion, taking off d's end renames c to d in the rest. *)
  Lemma move_unext_fused_d Θ Θ' e1 e2 e Θm :
    tenv_move W c d Θ Θ' → Θ !! c = Some (One e1) → Θ !! d = Some (One e2) →
    tenv_ext Θm d e Θ → tenv_ext (tenvswap c d Θm) d e Θ' ∧ tenv_move W c d Θm (tenvswap c d Θm).
  Proof.
    intros Hm Hc Hd Hext.
    destruct Hext as [[Hr ->]|(f & Hr & [-> | ->])];
      [|by rewrite lookup_insert_eq in Hd..].
    rewrite lookup_insert_eq in Hd. injection Hd as <-.
    rewrite lookup_insert_ne in Hc by done.
    assert (Θm !! c = Some (One e1)) as Hmc by done.
    split.
    - destruct Hm as (Hc' & Ho & Hj & _).
      rewrite lookup_insert_eq, lookup_insert_ne, Hmc in Hj by done.
      right. exists e1. split; [by rewrite lookup_tenvswap', cswap_r|].
      assert (∀ o, Θ' !! d = Some o → Θ' = <[d := o]> (tenvswap c d Θm)) as Heq.
      { intros o Ho'. apply map_eq. intros k. destruct (decide (k = d)) as [->|Hkd].
        - by rewrite lookup_insert_eq.
        - rewrite lookup_insert_ne, lookup_tenvswap' by done.
          destruct (decide (k = c)) as [->|Hkc].
          + by rewrite cswap_l, Hc', Hr.
          + rewrite cswap_ne, Ho by done. by rewrite lookup_insert_ne. }
      inversion Hj as [| | |? ? A B E|? ? A B E]; [right|left]; by apply Heq.
    - split_and!.
      + rewrite lookup_tenvswap', cswap_l. done.
      + intros k ? ?. rewrite lookup_tenvswap', cswap_ne; done.
      + rewrite lookup_tenvswap', cswap_r, Hr, Hmc. constructor.
      + intros f1 f2 A B. congruence.
  Qed.
End fuse_helpers2.

(** ** Fusion: two dual, aliased ends of distinct channels become the
    two ends of one channel *)

Definition fused (c d : chan) (Θ : tenv) : Prop :=
  ∃ e1 e2, Θ !! c = Some (One e1) ∧ Θ !! d = Some (One e2).

Global Instance fused_dec c d Θ : Decision (fused c d Θ).
Proof.
  unfold fused. destruct (Θ !! c) as [[]|], (Θ !! d) as [[]|];
    first [left; by eexists _, _ | right; intros (? & ? & ? & ?); congruence].
Defined.

(** A move is junk, a renaming, or a fusion. *)
Lemma move_cases W c d Θ Θ' :
  tenv_move W c d Θ Θ' →
  (Θ !! c = None ∧ Θ' = Θ) ∨ (Θ !! d = None ∧ Θ' = tenvswap c d Θ) ∨ fused c d Θ.
Proof.
  intros Hm. destruct (Θ !! c) as [oc|] eqn:Ec.
  - destruct (Θ !! d) as [od|] eqn:Ed.
    + right; right. pose proof Hm as (_ & _ & Hj & _). rewrite Ec, Ed in Hj.
      inversion Hj; subst; by eexists _, _.
    + right; left. split; [done|]. by apply (move_rename_eq W c d).
  - left. split; [done|]. by apply (move_none W c d).
Qed.

Lemma Vrel_move_easy n W Θ Θ' T v c d :
  c ≠ d → tenv_move W c d Θ Θ' → ¬ fused c d Θ →
  Vrel n W Θ T v → Vrel n W Θ' T (chsubst c d v).
Proof.
  intros Hcd Hm Hf HV. destruct (move_cases W c d Θ Θ' Hm) as [[Hc ->]|[[Hd ->]|?]]; [| |done].
  - rewrite chsubst_id; [done|]. rewrite (Vrel_fchans _ _ _ _ _ HV). by apply not_elem_of_dom.
  - apply Vrel_rename; [by apply not_elem_of_dom|done].
Qed.

Lemma Erel_move_easy n W Θ Θ' T F e c d :
  strict W → c ≠ d → tenv_move W c d Θ Θ' → ¬ fused c d Θ →
  Erel n W Θ T F e → Erel n W Θ' T F (chsubst c d e).
Proof.
  intros HW Hcd Hm Hf HE. destruct (move_cases W c d Θ Θ' Hm) as [[Hc ->]|[[Hd ->]|?]]; [| |done].
  - apply Erel_junk; [done|by apply not_elem_of_dom|done|done].
  - apply Erel_rename; [done|by apply not_elem_of_dom|done|done].
Qed.

Lemma selects_agree Θ Θ' σ k :
  (∀ y, y ∈ subjs σ → Θ' !! y = Θ !! y) → selects Θ σ k → selects Θ' σ k.
Proof.
  intros Hag Hs. destruct σ as [c0 w|c0 w|c0|cd]; simpl in *; unfold tenv_entry in *.
  - destruct Hs as [Hk Hr]. split; [done|]. rewrite Hag; [done|]. rewrite Hk. set_solver.
  - destruct Hs as [Hk Hr]. split; [done|]. rewrite Hag; [done|]. rewrite Hk. set_solver.
  - destruct Hs as [Hk (e0 & He & Hu & Hn)]. split; [done|]. exists e0.
    rewrite Hag by (rewrite Hk; set_solver). split_and!; [done|done|].
    intros H2 e' He'. simpl in He'. rewrite Hag in He' by set_solver. by apply (Hn H2 e').
  - destruct Hs as [Hk Hr]. split; [done|]. rewrite Hag; done.
Qed.

(** Taking an end off, in every case of a move. *)
Lemma move_unext_any W c d Θ Θ' c0 e Θm :
  c ≠ d → tenv_move W c d Θ Θ' → tenv_ext Θm c0 e Θ →
  ∃ Θm', tenv_ext Θm' (csub c d c0) e Θ' ∧ tenv_move W c d Θm Θm'.
Proof.
  intros Hcd Hm Hx.
  assert (is_Some (Θ !! c0)) as [o Ho].
  { destruct Hx as [[_ ->]|(e' & _ & [-> | ->])]; rewrite lookup_insert_eq; by eexists. }
  destruct (decide (c0 = c)) as [->|Hc0]; [|destruct (decide (c0 = d)) as [->|Hd0]].
  - destruct (Θ !! d) as [od|] eqn:Ed.
    + pose proof Hm as (_ & _ & Hj & _). rewrite Ho, Ed in Hj.
      inversion Hj as [| | |e1 e2 E1 E2 E3|e1 e2 E1 E2 E3]; subst.
      all: destruct (move_unext_fused_c W c d Hcd Θ Θ' e1 e2 e Θm Hm Ho Ed Hx) as [H1 H2].
      all: exists Θm; unfold csub; rewrite decide_True by done; done.
    + apply (move_unext_gen W c d Hcd Θ Θ' c e Θm Hm Hx). right; left. done.
  - destruct (Θ !! c) as [oc|] eqn:Ec.
    + pose proof Hm as (_ & _ & Hj & _). rewrite Ec, Ho in Hj.
      inversion Hj as [| | |e1 e2 E1 E2 E3|e1 e2 E1 E2 E3]; subst.
      all: destruct (move_unext_fused_d W c d Hcd Θ Θ' e1 e2 e Θm Hm Ec Ho Hx) as [H1 H2].
      all: exists (tenvswap c d Θm); unfold csub; rewrite decide_False by done; done.
    + apply (move_unext_gen W c d Hcd Θ Θ' d e Θm Hm Hx). right; right. done.
  - apply (move_unext_gen W c d Hcd Θ Θ' c0 e Θm Hm Hx). left. done.
Qed.

Section fused_offers.
  Context (W : world) (c d : chan) (Hcd : c ≠ d) (Θ Θ' : tenv) (e : expr)
    (Hm : tenv_move W c d Θ Θ') (κ : ekey → ekey)
    (Hκ1 : ∀ k, (κ k).1 = csub c d k.1)
    (Hκ2 : ∀ k, k.1 ≠ c → k.1 ≠ d → κ k = k)
    (Hκ3 : ∀ k e, tenv_entry Θ k = Some e → tenv_entry Θ' (κ k) = Some e)
    (Hκ4 : ∀ k' e', tenv_entry Θ' k' = Some e' → ∃ k, κ k = k' ∧ tenv_entry Θ k = Some e')
    (Hexcl : ∀ σ f, tstep e (LSess σ) f → (c ∈ subjs σ ∨ d ∈ subjs σ) → ∃ cd, σ = SLink cd).

  Lemma fused_offer_fwd k : offered_t Θ e k → offered_t Θ' (chsubst c d e) (κ k).
  Proof.
    intros (σ & f & Hf & Hsel). exists (ssub c d σ), (chsubst c d f).
    split; [by apply (tstep_chsubst c d) in Hf|].
    destruct (decide (c ∈ subjs σ ∨ d ∈ subjs σ)) as [Ht|Ht].
    - destruct (Hexcl _ _ Hf Ht) as [cd ->]. simpl in *.
      destruct Hsel as [Hk [e0 He0]]. split.
      + rewrite Hκ1. unfold gsub. by apply elem_of_map_2.
      + eexists. apply Hκ3. exact He0.
    - pose proof (selects_subj _ _ _ Hsel) as Hk.
      rewrite Hκ2 by set_solver.
      assert (ssub_rel c d σ (ssub c d σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select_t c d Θ' σ (ssub c d σ) k Hr).
      { rewrite subjs_ssub, gsub_id; [done|]. set_solver. }
      apply (selects_agree Θ); [|done].
      intros y Hy. apply (move_lookup_ne W c d); [done|set_solver|set_solver].
  Qed.

  Lemma fused_offer_back e1 e2 k' e' :
    world_wf W → Θ !! c = Some (One e1) → Θ !! d = Some (One e2) → w_eq W e1.2 e2.2 →
    offered_t Θ' (chsubst c d e) k' → tenv_entry Θ' k' = Some e' →
    ∃ k e0, offered_t Θ e k ∧ tenv_entry Θ k = Some e0 ∧ w_eq W e0.2 e'.2.
  Proof.
    intros HWf Hc Hd Hx (σ' & f' & Hf' & Hsel) He'.
    destruct (tstep_chsubst_back c d e σ' f' Hf') as (σ & f & Hf & Hr).
    destruct (Hκ4 k' e' He') as (k & <- & He).
    destruct (decide (c ∈ subjs σ ∨ d ∈ subjs σ)) as [Ht|Ht].
    - destruct (Hexcl _ _ Hf Ht) as [cd ->]. simpl in Ht.
      destruct σ' as [| | |cd']; simpl in Hr; try done. subst cd'.
      simpl in Hsel. destruct Hsel as [Hk _]. rewrite Hκ1 in Hk.
      unfold gsub in Hk. apply elem_of_map in Hk as (z & Hz & Hzin).
      destruct (decide (k.1 ∈ cd)) as [Hin|Hnin].
      + exists k, e'. split_and!; [|done|apply HWf].
        exists (SLink cd), f. split; [done|]. split; [done|by eexists].
      + destruct k as [k1 b]; simpl in *.
        unfold tenv_entry in He; simpl in He.
        destruct (decide (k1 = c)) as [->|Hk1].
        * assert (d ∈ cd) as Hdin.
          { unfold csub in Hz. rewrite decide_True in Hz by done.
            destruct (decide (z = c)) as [->|Hzc]; [done|]. by subst z. }
          rewrite Hc in He. destruct b; [done|]. injection He as <-.
          exists (d, false), e2. split_and!.
          -- exists (SLink cd), f. split; [done|]. split; [done|].
             unfold tenv_entry; simpl. rewrite Hd. by eexists.
          -- unfold tenv_entry; simpl. by rewrite Hd.
          -- by apply (wf_eq_sym _ HWf).
        * assert (k1 = d ∧ c ∈ cd) as [-> Hcin].
          { unfold csub in Hz. rewrite decide_False in Hz by done.
            destruct (decide (z = c)) as [->|Hzc]; [done|]. by subst z. }
          rewrite Hd in He. destruct b; [done|]. injection He as <-.
          exists (c, false), e1. split_and!.
          -- exists (SLink cd), f. split; [done|]. split; [done|].
             unfold tenv_entry; simpl. rewrite Hc. by eexists.
          -- unfold tenv_entry; simpl. by rewrite Hc.
          -- done.
    - pose proof (ssub_rel_subjs _ _ _ _ Hr) as Hs. rewrite gsub_id in Hs by set_solver.
      pose proof (selects_subj _ _ _ Hsel) as Hk. rewrite Hκ1, Hs in Hk.
      assert (k.1 ≠ c ∧ k.1 ≠ d) as [Hk1 Hk2].
      { unfold csub in Hk. case_decide; set_solver. }
      rewrite Hκ2 in Hsel by done.
      exists k, e'. split_and!; [|done|apply HWf].
      exists σ, f. split; [done|].
      apply (ssub_rel_select_t c d Θ' σ σ' k Hr) in Hsel; [|done].
      apply (selects_agree Θ'); [|done].
      intros y Hy. symmetry. apply (move_lookup_ne W c d); [done|set_solver|set_solver].
  Qed.
End fused_offers.

Lemma rel_fuse n :
  (∀ W Θ Θ' T v c d, strict W → c ≠ d → tenv_move W c d Θ Θ' →
     Vrel n W Θ T v → Vrel n W Θ' T (chsubst c d v)) ∧
  (∀ W Θ Θ' T F e c d, strict W → c ≠ d → tenv_move W c d Θ Θ' →
     Erel n W Θ T F e → Erel n W Θ' T F (chsubst c d e)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ Θ' T v c d, strict W → c ≠ d → tenv_move W c d Θ Θ' →
            Vrel n W Θ T v → Vrel n W Θ' T (chsubst c d v)) as HV.
  { intros W Θ Θ' T. revert Θ Θ'.
    induction T as [|ub lb T1 IHT1 U IHU|T1 IHT1 U IHU|T1 IHT1 U IHU|m T1 IHT1|s x];
      intros Θ Θ' v c d HW Hcd Hm HVv.
    all: destruct (decide (fused c d Θ)) as [Hfu|Hfu];
      [|by apply (Vrel_move_easy n W Θ Θ' _ v c d)].
    all: destruct Hfu as (e1 & e2 & Hc & Hd).
    - apply Vrel_unit_iff in HVv as [-> _]. by rewrite lookup_empty in Hc.
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & Hlb & HL)|(k & T0 & -> & -> & _)];
        [|by rewrite lookup_empty in Hc].
      apply Vrel_lolli_iff. left. exists (chsubst c d eb). split_and!.
      + done.
      + exact (fchans_move W c d Hcd Θ Θ' eb Hm Hfc).
      + by rewrite (move_heads W c d Hcd Θ Θ' Hm).
      + intros W' j Θa Θ'' w F Hx Hj Hcomp HVw Hub.
        assert (strict W') as HW' by (by destruct Hx as (_ & _ & _ & ?)).
        destruct (exist_fresh (dom Θ ∪ dom Θa ∪ fchans eb ∪ fchans w ∪ {[c; d]})) as [z Hz].
        assert (c ∉ dom Θ') as Hc' by (pose proof Hm as (Hc0 & _); by apply not_elem_of_dom).
        assert (z ∉ dom Θ') as Hz'.
        { rewrite (move_dom W c d Θ Θ' z Hm). set_solver. }
        apply (tenv_comp_swap c z) in Hcomp.
        rewrite (tenvswap_fix c z Θ') in Hcomp by done.
        assert (tenv_move W' c d Θ Θ') as HmW'.
        { eapply (move_mono W c d W'); [|exact Hm]. intros ? ? ?. by apply (proj1 (proj2 Hx)). }
        destruct (move_comp_join W' (proj1 HW') c d Hcd Θ Θ' (tenvswap c z Θa)
                    (tenvswap c z Θ'') HmW' Hcomp) as (Θ0 & Hc0 & Hm0).
        { rewrite lookup_tenvswap', cswap_l. apply not_elem_of_dom. set_solver. }
        pose proof (HL W' j (tenvswap c z Θa) Θ0 (eswap c z w) F Hx Hj Hc0
                      (Vrel_swap c z _ _ _ _ _ HVw) Hub) as HE1.
        apply (proj2 (IHn j Hj) W' _ _ _ _ _ c d HW' Hcd Hm0) in HE1.
        rewrite chsubst_subst1 in HE1.
        rewrite (chsubst_id c d (eswap c z w)) in HE1.
        2: { rewrite fchans_eswap, elem_of_gswap', cswap_l. set_solver. }
        apply (Erel_swap c z) in HE1. rewrite tenvswap_involutive, eswap_subst1,
          eswap_involutive in HE1.
        rewrite (eswap_fresh c z (chsubst c d eb)) in HE1; [done| |].
        * by apply fchans_chsubst_notin.
        * intros Hz2. apply fchans_chsubst in Hz2. set_solver.
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      destruct (move_comp_split W (proj1 HW) c d Hcd Θ Θ' Θ1 Θ2 Hm Hsp)
        as (Θ1' & Θ2' & Hm1 & Hm2 & Hsp').
      apply Vrel_prod_iff. exists (chsubst c d v1), (chsubst c d v2), Θ1', Θ2'.
      split_and!; [done|done|exact (IHT1 Θ1 Θ1' v1 c d HW Hcd Hm1 H1)|exact (IHU Θ2 Θ2' v2 c d HW Hcd Hm2 H2)].
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + exact (IHT1 Θ Θ' v' c d HW Hcd Hm H).
      + exact (IHU Θ Θ' v' c d HW Hcd Hm H).
    - apply Vrel_box_iff in HVv as (-> & _). by rewrite lookup_empty in Hc.
    - apply Vrel_sess_iff in HVv as (c0 & s0 & k & -> & -> & _).
      rewrite lookup_singleton_Some in Hc, Hd. destruct Hc as [<- _], Hd as [-> _]. done. }
  split; [exact HV|].
  intros W Θ Θ' T F e c d HW Hcd Hm HE.
  destruct n as [|n']; [apply Erel_0|].
  revert Θ' HW Hm.
  induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
  intros Θ' HW Hm.
  assert (HE0 : Erel (S n') W Θ T F e).
  { apply Erel_S_iff. split_and!; [done|done|]. intros α e' Hst.
    eapply Ecase_gen_mono; [|exact (Hstep α e' Hst)]. by intros ? ? ? ? ? [? _]. }
  destruct (decide (fused c d Θ)) as [Hfu|Hfu];
    [|by apply (Erel_move_easy (S n') W Θ Θ' T F e c d)].
  destruct Hfu as (e1 & e2 & Hc & Hd).
  assert (w_eq W e1.2 e2.2) as Hx by (pose proof Hm as (_ & _ & _ & H); by apply H).
  pose proof (proj1 HW) as HWf.
  assert (Hexcl : ∀ σ f, tstep e (LSess σ) f → (c ∈ subjs σ ∨ d ∈ subjs σ) →
                    ∃ cd, σ = SLink cd).
  { intros σ f Hf Ht. exact (fusion_exclusion n' W Θ T F e c d e1 e2 σ f HW HE0 Hc Hd Hx Hcd Hf Ht). }
  destruct (move_keys W c d Hcd Θ Θ' Hm) as (κ & Hκ1 & Hκ2 & Hκ3 & Hκ4).
  pose proof (fused_offer_fwd W c d Hcd Θ Θ' e Hm κ Hκ1 Hκ2 Hκ3 Hκ4 Hexcl) as Hfwd.
  pose proof (fused_offer_back W c d Hcd Θ Θ' e Hm κ Hκ1 Hκ2 Hκ3 Hκ4 Hexcl e1 e2) as Hback.
  assert (∀ j, j < S n' → ∀ W Θ Θ' T F e, strict W → tenv_move W c d Θ Θ' →
            Erel j W Θ T F e → Erel j W Θ' T F (chsubst c d e)) as IHE.
  { intros j Hj W1 Θ1 Θ1' T1 F1 e0 HW1 Hm1 HE1.
    exact (proj2 (IHn j Hj) W1 Θ1 Θ1' T1 F1 e0 c d HW1 Hcd Hm1 HE1). }
  apply Erel_S_iff. split_and!.
  - intros Hirr. apply irred_chsubst in Hirr as Hirr0.
    exact (HV W Θ Θ' T e c d HW Hcd Hm (Hval Hirr0)).
  - intros Hni. assert (¬ irred e) as Hni0.
    { intros Hi. apply Hni. by apply irred_chsubst_back. }
    destruct (Hrdy Hni0) as [Hr Hfr]. split.
    + intros Hs. apply stable_chsubst in Hs as Hs0. destruct (Hr Hs0) as [Hv Ha]. split.
      * intros Hno. rewrite is_val_chsubst. apply Hv. intros k Hk. apply (Hno (κ k)).
        by apply Hfwd.
      * intros k' e' He' Hk'. destruct (Hκ4 k' e' He') as (k & <- & He).
        destruct (Ha k e' He) as (k0 & e0 & Ho & He0 & Hlt).
        { intros Ho. apply Hk'. by apply Hfwd. }
        exists (κ k0), e0. split_and!; [by apply Hfwd|by apply Hκ3|].
        unfold entry_head in *. done.
    + intros Hs k' e' Ho He' y Hy. apply stable_chsubst in Hs as Hs0.
      destruct (Hback k' e' HWf Hc Hd Hx Ho He') as (k & e0 & Ho0 & He0 & Heq).
      pose proof (Hfr Hs0 k e0 Ho0 He0 y Hy) as Hlt. unfold entry_head in *.
      eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|apply HWf].
  - intros α f' Hst. destruct α as [|[c' w'|c' w'|c'|cd']|c'|w'].
    + (* β *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      apply eq_sym, lsub_beta in Hα as ->.
      eapply (IHE n'); [lia|done|exact Hm|exact (Hstep _ _ Hf)].
    + (* receive: freshen the payload's c through z *)
      destruct (exist_fresh (fchans w' ∪ fchans e ∪ dom Θ ∪ dom Θ' ∪ {[c; d]})) as [z Hz].
      destruct (tstep_chsubst_recv_inv_swap c d z e c' w' f')
        as (c0 & f & Hc0 & Hf & ->); [done|set_solver|set_solver|set_solver|done|set_solver|].
      assert (c0 ≠ c ∧ c0 ≠ d) as [Hc0c Hc0d].
      { split; intros ->; destruct (Hexcl _ _ Hf) as [? ?]; simpl; set_solver || done. }
      rewrite csub_ne in Hc0 by done. subst c0.
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct Hc1 as (Θ1 & m & U & s & k & Hhd & H).
      destruct (move_hd W c d Hcd Θ Θ' c' _ k Θ1 Hm Hhd (or_introl (conj Hc0c Hc0d)))
        as (Θ1' & Hhd' & Hm1). rewrite csub_ne in Hhd' by done.
      exists Θ1', m, U, s, k. split; [done|].
      intros W' j Θ2 Θ1c' Θ'' HW' Hj Hext Hcomp HVw.
      assert (strict W') as HW'' by (by destruct HW' as (_ & _ & _ & ?)).
      destruct (move_ext_given W c d Θ1 Θ1' c' _ Θ1c' Hm1 Hc0c Hc0d Hext)
        as (Θ1c & Hext1 & Hm1c).
      assert (z ∉ dom Θ2) as HzΘ2 by (rewrite <-(Vrel_fchans _ _ _ _ _ HVw); set_solver).
      assert (c ∉ dom Θ1c' ∧ z ∉ dom Θ1c') as [HcΘ1 HzΘ1].
      { assert (dom Θ1' ⊆ dom Θ' ∧ c' ∈ dom Θ') as [Hs1 Hs2].
        { destruct Hhd' as (s0 & Hx0 & _).
          destruct Hx0 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver. }
        assert (c ∉ dom Θ') as Hc'' by (pose proof Hm as (Hc0' & _); by apply not_elem_of_dom).
        assert (dom Θ1c' ⊆ dom Θ1' ∪ {[c']}) as Hs3.
        { destruct Hext as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver. }
        split; set_solver. }
      apply (tenv_comp_swap c z) in Hcomp.
      rewrite (tenvswap_fix c z Θ1c') in Hcomp by done.
      assert (tenv_move W' c d Θ1c Θ1c') as Hm1c'.
      { eapply (move_mono W c d W'); [|exact Hm1c]. intros ? ? ?. by apply (proj1 (proj2 HW')). }
      destruct (move_comp_join W' (proj1 HW'') c d Hcd Θ1c Θ1c' (tenvswap c z Θ2)
                  (tenvswap c z Θ'') Hm1c' Hcomp) as (Θ0 & Hc0 & Hm0).
      { rewrite lookup_tenvswap', cswap_l. by apply not_elem_of_dom. }
      pose proof (H W' j (tenvswap c z Θ2) Θ1c Θ0 HW' Hj Hext1 Hc0
                    (Vrel_swap c z _ _ _ _ _ HVw)) as HE1.
      apply (IHE j ltac:(lia) W' _ _ T F f HW'' Hm0) in HE1.
      apply (Erel_swap c z) in HE1. rewrite tenvswap_involutive in HE1. exact HE1.
    + (* send *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hw0.
      assert (c0 ≠ c ∧ c0 ≠ d) as [Hc0c Hc0d].
      { split; intros ->; destruct (Hexcl _ _ Hf) as [? ?]; simpl; set_solver || done. }
      rewrite csub_ne in Hc0 by done. subst c0 w'.
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct Hc1 as (Θr & Θ1 & Θ2 & m & U & s & k & Θ'' & Hhd & Hsp & HVw & Hext & HE').
      destruct (move_hd W c d Hcd Θ Θ' c' _ k Θr Hm Hhd (or_introl (conj Hc0c Hc0d)))
        as (Θr' & Hhd' & Hmr). rewrite csub_ne in Hhd' by done.
      destruct (move_comp_split W HWf c d Hcd Θr Θr' Θ1 Θ2 Hmr Hsp)
        as (Θ1' & Θ2' & Hm1 & Hm2 & Hsp').
      destruct (move_ext W c d Hcd Θ1 Θ1' c' _ Θ'' Hm1 Hext (or_introl (conj Hc0c Hc0d)))
        as (Θ3 & Hext' & Hm3). rewrite csub_ne in Hext' by done.
      exists Θr', Θ1', Θ2', m, U, s, k, Θ3. split_and!; [done|done| |done|].
      * exact (HV W Θ2 Θ2' _ w0 c d HW Hcd Hm2 HVw).
      * exact (proj2 HE' Θ3 HW Hm3).
    + (* close *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0.
      assert (c0 ≠ c ∧ c0 ≠ d) as [Hc0c Hc0d].
      { split; intros ->; destruct (Hexcl _ _ Hf) as [? ?]; simpl; set_solver || done. }
      rewrite csub_ne in Hc0 by done. subst c0.
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct Hc1 as (Θ1 & k & Hhd & HE').
      destruct (move_hd W c d Hcd Θ Θ' c' _ k Θ1 Hm Hhd (or_introl (conj Hc0c Hc0d)))
        as (Θ1' & Hhd' & Hm1). rewrite csub_ne in Hhd' by done.
      exists Θ1', k. split; [done|]. exact (proj2 HE' Θ1' HW Hm1).
    + (* link *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hcd'. subst cd'.
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct Hc1 as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & Hdu & Hal & HE').
      destruct (move_unext_any W c d Θ Θ' c1 _ Θm Hcd Hm H2) as (Θm' & H2' & Hmm).
      destruct (move_unext_any W c d Θm Θm' d1 _ Θ1 Hcd Hmm H1) as (Θ1' & H1' & Hm1).
      exists (csub c d c1), (csub c d d1), Θ1', Θm', sc, sd, kc, kd. split_and!; [|done..|].
      * unfold gsub. by rewrite set_map_union_L, !set_map_singleton_L.
      * exact (proj2 HE' Θ1' HW Hm1).
    + (* new: through a fresh c0, then rename c0 to the image's name *)
      intros Hc'.
      destruct (exist_fresh (fchans e ∪ dom Θ ∪ dom Θ' ∪ {[c; d; c']})) as [c0 Hc0].
      destruct (tstep_chsubst_new_inv c d e c' f' Hst c0) as (f & Hf & ->); [set_solver..|].
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct (Hc1 ltac:(set_solver)) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
      exists a, s, s', W1. split_and!; [|done|done|].
      { by rewrite (move_roots W c d Hcd Θ Θ' Hm). }
      assert (strict W1) as HW1 by (by destruct Hfr as ((_ & _ & _ & ?) & _)).
      assert (tenv_move W1 c d Θ Θ') as HmW1.
      { eapply (move_mono W c d W1); [|exact Hm]. intros ? ? ?.
        by apply (proj1 (proj2 (proj1 Hfr))). }
      apply (IHE n' ltac:(lia) W1 _ (<[c0 := Both (s, pconst a) (s', pconst a)]> Θ') T F f HW1)
        in HE'; [|apply move_insert; [set_solver|set_solver|done]].
      apply (Erel_rename _ _ _ _ _ _ c0 c') in HE'; [|done| |set_solver].
      2: { rewrite dom_insert_L. set_solver. }
      by rewrite tenvswap_insert, tenvswap_fix, cswap_l in HE' by set_solver.
    + (* spawn *)
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
      pose proof (Hstep _ _ Hf) as Hc1. simpl in Hc1.
      destruct Hc1 as (Θ1 & Θ2 & ub & lb & Hsp & HVw & HE').
      destruct (move_comp_split W HWf c d Hcd Θ Θ' Θ1 Θ2 Hm Hsp)
        as (Θ1' & Θ2' & Hm1 & Hm2 & Hsp').
      exists Θ1', Θ2', ub, lb. split_and!; [done| |].
      * exact (HV W Θ1 Θ1' _ v c d HW Hcd Hm1 HVw).
      * eapply (IHE n'); [lia|done|eassumption|eassumption].
Qed.
