(** * Junk-renaming transport (§4.5)

    Renaming a channel that a related process does not own — a "junk"
    name, absent from the interface and the restricted set, though
    possibly present in the syntax — into an arbitrary other name
    preserves the process relation. An interface-fresh channel can
    never act (every clause that would observe it demands an interface
    entry), so its occurrences are inert; and the renaming is uniform,
    so name coincidences (a stuck self-forward ⟨x,x⟩ staying stuck) are
    preserved.

    This is the lemma that lets P-Act-Link's whole-configuration
    substitution E[d/c] be pushed through the CONNECT induction with
    the relations kept exactly as in the paper — no channel-occurrence
    side conditions in Edef/Pdef.

    The input and fork clauses quantify over values (respectively fresh
    names) that may mention the renamed-away name x again; those cases
    are closed by instantiating the original's clause at an α-variant
    (x transposed to a globally fresh z) and repairing with the proven
    bijective transposition transport [Prel_eswap]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Renaming.

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
  | LFork c v => LFork (csub x b c) (chsubst x b v)
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
Proof.
  intros Ha Hb. rewrite chsubst_eswap by done. by apply chsubst_id.
Qed.

Lemma echswap_id a b E : a ∉ echans E → b ∉ echans E → echswap a b E = E.
Proof.
  intros Ha Hb. rewrite echswap_echsubst by done. by apply echsubst_id.
Qed.

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
  intros Hst. destruct Hst; simpl.
  - rewrite chsubst_subst1. constructor. by rewrite is_val_chsubst.
  - constructor.
  - rewrite chsubst_subst2. constructor; by rewrite is_val_chsubst.
  - constructor. by rewrite is_val_chsubst.
  - constructor. by rewrite is_val_chsubst.
  - constructor. by rewrite is_val_chsubst.
  - constructor.
  - rewrite chsubst_subst1. constructor. by rewrite is_val_chsubst.
  - rewrite chsubst_subst1. constructor. by rewrite is_val_chsubst.
  - rewrite chsubst_subst1. constructor.
  - rewrite gsub_upair. constructor.
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
  - apply TStepForce. by apply IHHst.
Qed.

(** ** Backward step correspondence

    Every step of the substituted term is the image of a step of the
    original. For deterministic labels (β, send, close, forwarding) the
    label and continuation are exact images. The receptive labels
    (receive, fork) quantify over incoming values respectively fresh
    names, which need not be images; those get tailored statements. *)

Definition det_label (α : tlabel) : Prop :=
  match α with
  | LBeta | LSess (SSend _ _) | LSess (SClos _) | LSess (SLink _) => True
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
    + (* fork: not a deterministic label *)
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
      destruct e0; simplify_eq/=.
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
  - (* Force *)
    destruct e0; simplify_eq/=.
    destruct (IHHst Hdet _ eq_refl) as (α0 & f & Hf & -> & ->).
    eexists _, (Force f). split_and!; [|done|done]. by apply TStepForce.
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
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->).
    eexists c0, (Force f). split_and!; [done| |done]. by apply TStepForce.
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
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (c0 & f & Hc0 & Hf & ->);
      [set_solver|].
    eexists c0, (Force f). split_and!; [done|by apply TStepForce|]. done.
Qed.

(** Fork: the substituted term forks at c; the original forks at any
    sufficiently fresh name c0 the caller chooses, and the
    continuations differ by the substitution followed by retargeting
    c0 to c. *)
Lemma tstep_chsubst_fork_inv x b e c v' f' :
  x ≠ b →
  tstep (chsubst x b e) (LFork c v') f' →
  ∃ v, v' = chsubst x b v ∧
    ∀ c0, c0 ∉ fchans e → c0 ≠ x → c0 ≠ b →
      ∃ f, tstep e (LFork c0 v) f ∧ f' = chsubst c0 c (chsubst x b f).
Proof.
  intros Hxb Hst.
  remember (chsubst x b e) as g eqn:Hg.
  remember (LFork c v') as lab eqn:Hlab.
  revert e Hg. induction Hst; intros e0 Hg.
  - (* head step *)
    destruct H; simplify_eq/=.
    destruct e0; simplify_eq/=.
    destruct e0_1; simplify_eq/=.
    exists e0_2. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    exists (Chan c0). split.
    { apply TStepHead. constructor. by rewrite is_val_chsubst in H. }
    rewrite chsubst_chan, csub_ne by done. rewrite chsubst_chan.
    unfold csub. by rewrite decide_True.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (App f e0_2). split; [by apply TStepAppL|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (App e0_1 f).
    split; [apply TStepAppR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (Pair f e0_2). split; [by apply TStepPairL|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (Pair e0_1 f).
    split; [apply TStepPairR; [by rewrite is_val_chsubst in H|done]|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (LetU f e0_2). split; [by apply TStepLetU|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (LetP f e0_2). split; [by apply TStepLetP|].
    simpl. f_equal.
    rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 Hc0e Hc0x Hc0b) as (f & Hf & ->).
    eexists (Inj1 f). split; [by apply TStepInj1|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 Hc0e Hc0x Hc0b) as (f & Hf & ->).
    eexists (Inj2 f). split; [by apply TStepInj2|]. done.
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 ltac:(set_solver) Hc0x Hc0b) as (f & Hf & ->).
    eexists (Case f e0_2 e0_3). split; [by apply TStepCase|].
    simpl. f_equal.
    all: rewrite (chsubst_id c0);
      [done|apply fchans_chsubst_other; [set_solver|done]].
  - destruct e0; simplify_eq/=.
    destruct (IHHst eq_refl _ eq_refl) as (v & -> & Hfam).
    exists v. split; [done|]. intros c0 Hc0e Hc0x Hc0b.
    destruct (Hfam c0 Hc0e Hc0x Hc0b) as (f & Hf & ->).
    eexists (Force f). split; [by apply TStepForce|]. done.
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

Lemma Vrel_chsubst_id n Σ U w x b :
  x ∉ dom Σ → Vrel n Σ U w → chsubst x b w = w.
Proof.
  intros Hx HV. apply chsubst_id.
  rewrite (Vrel_fchans _ _ _ _ HV). exact Hx.
Qed.

Lemma gswap_disjoint_out a b (S C : gset chan) :
  a ∉ C → b ∉ C → S ## C → gswap a b S ## C.
Proof.
  intros Ha Hb Hd. apply elem_of_disjoint. intros y Hy1 Hy2.
  rewrite elem_of_gswap' in Hy1.
  assert (y ≠ a) by set_solver. assert (y ≠ b) by set_solver.
  rewrite cswap_ne in Hy1 by done. set_solver.
Qed.

Lemma senvswap_disjoint_out a b Σn Σ1 :
  a ∉ dom Σ1 → b ∉ dom Σ1 → Σn ##ₘ Σ1 → senvswap a b Σn ##ₘ Σ1.
Proof.
  intros Ha Hb Hd. apply map_disjoint_dom. rewrite dom_kswap.
  apply map_disjoint_dom in Hd. by apply gswap_disjoint_out.
Qed.

(** Junk transport through the owner family.  The target b may be
    restricted somewhere in the family, provided it owns no interface
    entry: each piece receives the conditional fact for its own
    environment. *)
Lemma topo_split_junk (P : senv → ty → proc → Prop) x b σ Σ T C E :
  (∀ Σ' T' C' E',
     x ∉ dom Σ' → x ∉ C' → (b ∈ C' → b ∉ dom Σ') →
     P Σ' T' (C', E') → P Σ' T' (C', echsubst x b E')) →
  x ∉ dom σ → x ∉ dom Σ → x ∉ C →
  (b ∈ C → b ∉ dom Σ ∧ b ∉ dom σ) →
  topo_split P σ Σ T (C, E) →
  topo_split P σ Σ T (C, echsubst x b E).
Proof.
  intros HPQ Hσ HΣ HC HbC HP.
  remember (C, E) as p eqn:Hp.
  revert C E Hp Hσ HΣ HC HbC.
  induction HP; intros C0 E0 Hp Hσ HΣ HC HbC; simplify_eq.
  - rewrite echsubst_empty. constructor.
  - rewrite echsubst_disj_union.
    rewrite dom_insert_L in Hσ. rewrite dom_union_L in HΣ.
    rewrite dom_insert_L, dom_union_L in HbC.
    econstructor; try done.
    + apply HPQ; [ |set_solver| |done].
      * rewrite dom_insert_L. set_solver.
      * rewrite dom_insert_L. intros Hb.
        destruct HbC as [HbΣ Hbσ]; [clear -Hb; set_solver|].
        clear -HbΣ Hbσ. set_solver.
    + apply IHHP; [done|set_solver|set_solver|set_solver|].
      intros Hb.
      destruct HbC as [HbΣ Hbσ]; [clear -Hb; set_solver|].
      clear -HbΣ Hbσ. set_solver.
Qed.

(** τ-step inversion into the five underlying rules. *)
Lemma ptau_inv C E p' :
  proc_step (C, E) PTau p' →
  (∃ F e e', E = F ⊎ {[+ e +]} ∧ tstep e LBeta e' ∧
     p' = (C, F ⊎ {[+ e' +]}))
  ∨ (∃ F e c v e', E = F ⊎ {[+ e +]} ∧ tstep e (LFork c v) e' ∧
       c ∉ C ∧ c ∉ echans F ∧ c ∉ fchans e ∧
       p' = (C ∪ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}))
  ∨ (∃ F c v e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SSend c v)) e' ∧ tstep f (LSess (SRecv c v)) f' ∧
       c ∈ C ∧ p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F c e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SClos c)) e' ∧ tstep f (LSess (SClos c)) f' ∧
       c ∈ C ∧ p' = (C ∖ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F e c d e', E = F ⊎ {[+ e +]} ∧ tstep e (LSess (SLink {[c; d]})) e' ∧
       c ∈ C ∧ p' = (C ∖ {[c]}, echsubst c d (F ⊎ {[+ e' +]}))).
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 10.
  - right; left. eauto 12.
  - right; right; left. eauto 14.
  - right; right; right; left. eauto 14.
  - right; right; right; right. eauto 10.
Qed.

(** ** The junk-renaming transport

    Renaming an interface-fresh channel x — uniformly, everywhere — to
    an arbitrary name b preserves the process relation.  The target b
    may even be restricted, provided it too is interface-fresh.  The
    delicate case is a forwarding whose source names both x and b: the
    image retires b, while the original — x being unrestricted — can
    only retire the other end.  The two post-states are reconciled by
    first renaming the junk in the original's post-state (the
    induction hypothesis, at a smaller index) and then flipping the
    orientation of the forwarding ([Prel_link_orient]).  Before
    T-Act-Link admitted degenerate pairs this lemma required b ∉ C:
    renaming could collapse a live pair ⟨x,b⟩ into the then-stuck
    ⟨b,b⟩; now ⟨b,b⟩ fires and dissolves, and the same argument covers
    it. *)

Lemma Prel_junk_subst n Σ T C E x b :
  x ∉ dom Σ → x ∉ C → (b ∈ C → b ∉ dom Σ) → b ≠ x →
  Prel n Σ T (C, E) → Prel n Σ T (C, echsubst x b E).
Proof.
  revert Σ T C E x b.
  induction n as [n IHn] using lt_wf_ind;
    intros Σ T C E x b HxΣ HxC HbC Hbx HP.
  destruct n as [|n']; [apply Prel_0|].
  (* the original never offers a forwarding pair containing x, nor a
     session action whose subject is x: both would put x in dom Σ *)
  assert (∀ cd p1, proc_step (C, E) (PSess (SLink cd)) p1 → x ∉ cd) as Hnolinkx.
  { intros cd p1 Hst1 Hxcd.
    pose proof (Prel_S_step _ _ _ _ _ _ HP Hst1) as Hc. simpl in Hc.
    destruct Hc as (c1 & d1 & Σ1 & sc & sd & -> & Hne & HΣeq & _).
    apply HxΣ. rewrite HΣeq, !dom_insert_L. set_solver. }
  assert (∀ σ0 p1, proc_step (C, E) (PSess σ0) p1 → x ∉ subjs σ0)
    as Hnosessx.
  { intros σ0 p1 Hst1 Hsx.
    pose proof (Prel_S_step _ _ _ _ _ _ HP Hst1) as Hc.
    destruct σ0 as [c1 w1|c1 w1|c1|cd1]; simpl in Hsx, Hc; try subst c1.
    - destruct Hc as (Σ1 & U & s & Hhd & _).
      apply senv_hd_dom in Hhd. set_solver.
    - destruct Hc as (?&?&?&?&?&?&?&?&?&?&?&?&Hhd&_).
      apply senv_hd_dom in Hhd. set_solver.
    - destruct Hc as (Σ1 & Hhd & _).
      apply senv_hd_dom in Hhd. set_solver.
    - exact (Hnolinkx _ _ Hst1 Hsx). }
  apply Prel_S_intro.
  - (* termination clause: pirredness transfers back to the original *)
    intros Hpirr.
    assert (pirred (C, E)) as Hpo.
    { intros π p1 Hst1. destruct π as [|σ0].
      - apply ptau_inv in Hst1 as
          [ (F & e & e' & -> & Hts & _)
          | [ (F & e & c & v & e' & -> & Hts & HcC & HcF & Hce & _)
          | [ (F & c & v & e & e' & f & f' & -> & Hts & Htr & HcC & _)
          | [ (F & c & e & e' & f & f' & -> & Hts & Htr & HcC & _)
          | (F & e & c & d & e' & -> & Hts & HcC & _) ]]]].
        + (* β *)
          apply (tstep_chsubst x b) in Hts.
          eapply (Hpirr PTau).
          rewrite echsubst_disj_union, echsubst_singleton.
          by eapply PStepBeta.
        + (* fork: the image forks at a globally fresh name *)
          pose proof (tstep_fork_val_fchans _ _ _ _ Hts) as Hvf.
          set (pool := C ∪ echans F ∪ fchans e ∪ {[x]} ∪ {[b]}).
          assert (fresh pool ∉ pool) as Hfz by apply is_fresh.
          set (z := fresh pool) in *.
          apply (tstep_chsubst c z) in Hts.
          rewrite (chsubst_id c z e) in Hts by set_solver.
          simpl in Hts. rewrite csub_hit in Hts.
          rewrite (chsubst_id c z v) in Hts by set_solver.
          apply (tstep_chsubst x b) in Hts.
          simpl in Hts. rewrite (csub_ne x b z) in Hts by set_solver.
          eapply (Hpirr PTau).
          rewrite echsubst_disj_union, echsubst_singleton.
          eapply PStepFork; [exact Hts|set_solver| |].
          * pose proof (echans_echsubst_sub x b F). set_solver.
          * pose proof (fchans_chsubst x b e). set_solver.
        + (* internal message *)
          assert (c ≠ x) as Hcx by set_solver.
          apply (tstep_chsubst x b) in Hts.
          apply (tstep_chsubst x b) in Htr.
          simpl in Hts, Htr. rewrite (csub_ne x b c) in Hts, Htr by done.
          eapply (Hpirr PTau).
          rewrite !echsubst_disj_union, !echsubst_singleton.
          by eapply PStepMsg.
        + (* internal close *)
          assert (c ≠ x) as Hcx by set_solver.
          apply (tstep_chsubst x b) in Hts.
          apply (tstep_chsubst x b) in Htr.
          simpl in Hts, Htr. rewrite (csub_ne x b c) in Hts, Htr by done.
          eapply (Hpirr PTau).
          rewrite !echsubst_disj_union, !echsubst_singleton.
          by eapply PStepClose.
        + (* internal forwarding *)
          apply (tstep_chsubst x b) in Hts.
          simpl in Hts. rewrite gsub_upair in Hts.
          rewrite (csub_ne x b c) in Hts by set_solver.
          eapply (Hpirr PTau).
          rewrite echsubst_disj_union, echsubst_singleton.
          by eapply PStepLink.
      - (* any offer, forwarding included: the renaming touches
           neither the subjects nor the redex's own channels *)
        pose proof (Hnosessx _ _ Hst1) as Hsx.
        apply proc_step_sess_inv in Hst1
          as (F & e & e' & -> & Hts & HsC & ->).
        apply (tstep_chsubst x b) in Hts.
        eapply (Hpirr (PSess (ssub x b σ0))).
        rewrite echsubst_disj_union, echsubst_singleton.
        eapply PStepSession; [exact Hts|].
        rewrite subjs_ssub, gsub_id; done.
    }
    destruct (Prel_S_irred _ _ _ _ HP Hpo) as (v & E1 & Heq & Hv & HV & Hun).
    inversion Heq; subst C E.
    exists v, (echsubst x b E1).
    rewrite echsubst_disj_union, echsubst_singleton.
    rewrite (Vrel_chsubst_id _ _ _ _ _ _ HxΣ HV).
    split_and!; [done|done|done|].
    intros e0 He0. unfold echsubst in He0.
    apply elem_of_gmultiset_map in He0 as (f0 & -> & Hf0).
    rewrite (Hun _ Hf0). done.
  - (* step clause *)
    intros π q Hst. destruct π as [|σ'].
    + (* τ steps of the image *)
      apply ptau_inv in Hst as
        [ (F' & e' & e'' & HeqE & Hts & ->)
        | [ (F' & e' & c & v' & e'' & HeqE & Hts & HcC & HcF & Hce & ->)
        | [ (F' & c & v' & e' & e'' & f' & f'' & HeqE & Hts & Htr & HcC & ->)
        | [ (F' & c & e' & e'' & f' & f'' & HeqE & Hts & Htr & HcC & ->)
        | (F' & e' & c & d & e'' & HeqE & Hts & HcC & ->) ]]]].
      * (* β *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->);
          [|done].
        destruct α as [|σ0|c0 v0]; simpl in Hα; try discriminate.
        simpl. intros Hguard.
        rewrite <-echsubst_singleton, <-echsubst_disj_union.
        apply (IHn n' ltac:(lia) Σ T C _ x b HxΣ HxC HbC Hbx).
        pose proof (Prel_S_step _ _ _ _ _ _ HP
                      (PStepBeta _ _ _ _ Hf0)) as Hc.
        simpl in Hc. apply Hc. exact Hguard.
      * (* fork *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        simpl. intros Hguard.
        destruct (decide (c = b)) as [->|Hcb].
        { (* fork at b: the substitution must have been trivial *)
          assert (x ∉ fchans f) as Hxf.
          { intros Hx. apply Hce. by apply fchans_chsubst_hit. }
          assert (x ∉ echans F) as HxF.
          { intros Hx. apply HcF. by apply echans_echsubst_hit. }
          rewrite (chsubst_id x b f) in Hts by done.
          rewrite (echsubst_id x b F) in HcF |- * by done.
          rewrite (chsubst_id x b f) in Hce by done.
          pose proof (Prel_S_step _ _ _ _ _ _ HP
            (PStepFork C F f b v' e'' Hts HcC HcF Hce)) as Hc.
          simpl in Hc. apply Hc. exact Hguard. }
        apply tstep_chsubst_fork_inv in Hts as (v & -> & Hfam); [|done].
        destruct (decide (c = x)) as [->|Hcx].
        { (* fork at x: freshen through z, then transpose back *)
          set (pool := C ∪ dom Σ ∪ echans F ∪ fchans f ∪ {[x]} ∪ {[b]}).
          assert (fresh pool ∉ pool) as Hfz by apply is_fresh.
          set (z := fresh pool) in *.
          unfold pool in Hfz. clearbody z. clear pool.
          destruct (Hfam z) as (f0 & Hf0 & ->);
            [set_solver|set_solver|set_solver|].
          pose proof (tstep_fork_val_fchans _ _ _ _ Hf0) as Hvf.
          assert (proc_step (C, F ⊎ {[+ f +]}) PTau
                    (C ∪ {[z]}, F ⊎ {[+ f0 +]} ⊎ {[+ App v (Chan z) +]}))
            as Horig.
          { eapply PStepFork; [exact Hf0|set_solver|set_solver|set_solver]. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc. simpl in Hc.
          specialize (Hc ltac:(set_solver)).
          pose proof (IHn n' ltac:(lia) Σ T (C ∪ {[z]}) _ x b
                        HxΣ ltac:(set_solver)
                        ltac:(intros Hb; apply HbC; clear -Hb Hfz; set_solver)
                        Hbx Hc)
            as HQ.
          apply (Prel_eswap x z) in HQ.
          rewrite senvswap_id in HQ; [|done|set_solver].
          unfold pswap in HQ. simpl in HQ.
          assert (gswap x z (C ∪ {[z]}) = C ∪ {[x]}) as Hgs.
          { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
            repeat case_decide; subst; set_solver. }
          rewrite Hgs in HQ.
          rewrite !echsubst_disj_union, !echsubst_singleton in HQ.
          rewrite !msswap_disj_union, !msswap_singleton in HQ.
          rewrite (echswap_id x z (echsubst x b F)) in HQ;
            [ |apply echans_echsubst_notin; congruence
             |pose proof (echans_echsubst_sub x b F) as Hsub;
              clear -Hsub Hfz; set_solver].
          rewrite (eswap_comm x z (chsubst x b f0)) in HQ.
          rewrite (chsubst_eswap z x) in HQ;
            [|apply fchans_chsubst_notin; congruence].
          cbn [chsubst eswap] in HQ.
          rewrite decide_False in HQ by (clear -Hfz; set_solver).
          rewrite cswap_r in HQ.
          rewrite (eswap_id x z (chsubst x b v)) in HQ;
            [ |apply fchans_chsubst_notin; congruence
             |pose proof (fchans_chsubst x b v) as Hsub;
              clear -Hsub Hfz Hvf; set_solver].
          exact HQ. }
        (* fork at a name other than x and b: direct *)
        assert (c ∉ fchans f) as Hcf.
        { pose proof (fchans_chsubst_sup x b f). set_solver. }
        destruct (Hfam c Hcf Hcx Hcb) as (f0 & Hf0 & ->).
        rewrite chsubst_refl.
        assert (c ∉ echans F) as HcF0.
        { pose proof (echans_echsubst_sup x b F). set_solver. }
        pose proof (tstep_fork_val_fchans _ _ _ _ Hf0) as Hvf.
        assert (proc_step (C, F ⊎ {[+ f +]}) PTau
                  (C ∪ {[c]}, F ⊎ {[+ f0 +]} ⊎ {[+ App v (Chan c) +]}))
          as Horig by (eapply PStepFork; done).
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        specialize (Hc' Hguard).
        pose proof (IHn n' ltac:(lia) Σ T (C ∪ {[c]}) _ x b
                      HxΣ ltac:(set_solver)
                      ltac:(intros Hb; apply HbC; clear -Hb Hcb; set_solver)
                      Hbx Hc')
          as HQ.
        rewrite !echsubst_disj_union, !echsubst_singleton in HQ.
        simpl in HQ. rewrite decide_False in HQ by done.
        exact HQ.
      * (* internal message *)
        apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
        symmetry in HeqE1.
        apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        simpl. intros Hguard.
        assert (c ≠ x) as Hcx by set_solver.
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hc0 Hw0.
        (* a source subject equal to x would let the source offer on x *)
        assert (c0 = c) as ->.
        { destruct (decide (c0 = x)) as [->|Hne].
          - exfalso.
            assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]})
                      (PSess (SSend x w0))
                      (C ∖ sentc (SSend x w0), (F2 ⊎ {[+ g +]}) ⊎ {[+ h0 +]}))
              as Horig.
            { assert (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}
                      = (F2 ⊎ {[+ g +]}) ⊎ {[+ h +]}) as ->
                by multiset_solver.
              eapply PStepSession; [exact Hh0|]. simpl.
              clear -HxC. set_solver. }
            pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
            clear -Hsx0. set_solver.
          - rewrite csub_ne in Hc0; congruence. }
        subst v'.
        apply tstep_chsubst_recv_inv_subst in Htr
          as (c1 & g0 & Hc1 & Hg0 & ->).
        assert (c1 = c) as ->.
        { destruct (decide (c1 = x)) as [->|Hne].
          - exfalso.
            assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]})
                      (PSess (SRecv x w0))
                      (C ∖ sentc (SRecv x w0), (F2 ⊎ {[+ h +]}) ⊎ {[+ g0 +]}))
              as Horig.
            { eapply PStepSession; [exact Hg0|]. simpl.
              clear -HxC. set_solver. }
            pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
            clear -Hsx0. set_solver.
          - rewrite csub_ne in Hc1; congruence. }
        assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) PTau
                  (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Horig
          by (eapply PStepMsg; done).
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        specialize (Hc' Hguard).
        rewrite <-!echsubst_singleton, <-!echsubst_disj_union.
        by apply (IHn n' ltac:(lia) Σ T C _ x b HxΣ HxC HbC Hbx).
      * (* internal close *)
        apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
        symmetry in HeqE1.
        apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        simpl. intros Hguard.
        assert (c ≠ x) as Hcx by set_solver.
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hc0.
        assert (c0 = c) as ->.
        { destruct (decide (c0 = x)) as [->|Hne].
          - exfalso.
            assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]})
                      (PSess (SClos x))
                      (C ∖ sentc (SClos x), (F2 ⊎ {[+ g +]}) ⊎ {[+ h0 +]}))
              as Horig.
            { assert (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}
                      = (F2 ⊎ {[+ g +]}) ⊎ {[+ h +]}) as ->
                by multiset_solver.
              eapply PStepSession; [exact Hh0|]. simpl.
              clear -HxC. set_solver. }
            pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
            clear -Hsx0. set_solver.
          - rewrite csub_ne in Hc0; congruence. }
        apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα2 & ->);
          [|done].
        destruct α as [|[c1 w1|c1 w1|c1|cd1]|c1 v1]; simpl in Hα2;
          try discriminate.
        injection Hα2 as Hc1.
        assert (c1 = c) as ->.
        { destruct (decide (c1 = x)) as [->|Hne].
          - exfalso.
            assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]})
                      (PSess (SClos x))
                      (C ∖ sentc (SClos x), (F2 ⊎ {[+ h +]}) ⊎ {[+ g0 +]}))
              as Horig.
            { eapply PStepSession; [exact Hg0|]. simpl.
              clear -HxC. set_solver. }
            pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
            clear -Hsx0. set_solver.
          - rewrite csub_ne in Hc1; congruence. }
        assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) PTau
                  (C ∖ {[c]}, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Horig
          by (eapply PStepClose; done).
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        specialize (Hc' Hguard).
        rewrite <-!echsubst_singleton, <-!echsubst_disj_union.
        by apply (IHn n' ltac:(lia) Σ T (C ∖ {[c]}) _ x b
                    HxΣ ltac:(set_solver)
                    ltac:(intros Hb; apply HbC; clear -Hb; set_solver) Hbx).
      * (* internal forwarding *)
        apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
        simpl. intros Hguard.
        assert (c ≠ x) as Hcx by set_solver.
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hcd.
        pose proof (tstep_link_shape _ _ _ Hf0) as (c1 & d1 & ->).
        rewrite gsub_upair in Hcd.
        (* the pair may be degenerate on either side, so read the two
           ends off by membership rather than by [upair_eq_inv] *)
        assert (∃ ca da, ({[ca; da]} : gset chan) = {[c1; d1]} ∧
                  csub x b ca = c ∧ csub x b da = d)
          as (ca & da & Hpair2 & Hca & Hda).
        { assert (c ∈ ({[csub x b c1; csub x b d1]} : gset chan)) as Hcin
            by (rewrite <-Hcd; clear; set_solver).
          assert (csub x b c1 ∈ ({[c; d]} : gset chan)) as Hc1in
            by (rewrite Hcd; clear; set_solver).
          assert (csub x b d1 ∈ ({[c; d]} : gset chan)) as Hd1in
            by (rewrite Hcd; clear; set_solver).
          destruct (decide (csub x b c1 = c)) as [Hc1c|Hc1c].
          - exists c1, d1. split_and!; [done|done|].
            apply elem_of_union in Hd1in as [Hd1in|Hd1in];
              apply elem_of_singleton in Hd1in; [|done].
            (* both ends map to c, so the image pair is degenerate too *)
            assert (d ∈ ({[c; d]} : gset chan)) as Hdin by (clear; set_solver).
            rewrite Hcd, Hc1c, Hd1in in Hdin.
            assert (d = c) as -> by (clear -Hdin; set_solver). done.
          - exists d1, c1. split_and!;
              [apply upair_comm
              |clear -Hcin Hc1c; set_solver
              |clear -Hc1in Hc1c; set_solver]. }
        assert (tstep f (LSess (SLink {[ca; da]})) f0) as Hf1
          by (rewrite Hpair2; exact Hf0).
        clear Hf0.
        destruct (decide (ca = x)) as [->|Hcax].
        { (* the image retires the renamed junk itself: c = b *)
          rewrite csub_hit in Hca. subst c.
          destruct (decide (da = x)) as [->|Hdax].
          { (* both source ends are x: the source would offer a
               forwarding naming x, which the relation refutes *)
            exfalso.
            assert (proc_step (C, F ⊎ {[+ f +]}) (PSess (SLink {[x; x]}))
                      (C ∖ sentc (SLink {[x; x]}), F ⊎ {[+ f0 +]}))
              as Horig.
            { eapply PStepSession; [exact Hf1|]. simpl.
              clear -HxC. set_solver. }
            pose proof (Hnolinkx _ _ Horig) as Hxcd.
            clear -Hxcd. set_solver. }
          destruct (decide (da ∈ C)) as [HdaC|HdaC]; last first.
          { (* the other source end is free too: same refutation *)
            exfalso.
            assert (proc_step (C, F ⊎ {[+ f +]}) (PSess (SLink {[x; da]}))
                      (C ∖ sentc (SLink {[x; da]}), F ⊎ {[+ f0 +]}))
              as Horig.
            { eapply PStepSession; [exact Hf1|]. simpl.
              clear -HxC HdaC. set_solver. }
            pose proof (Hnolinkx _ _ Horig) as Hxcd.
            clear -Hxcd. set_solver. }
          rewrite csub_ne in Hda by done. subst d.
          assert (b ∉ dom Σ) as HbΣ by (apply HbC; exact HcC).
          assert (tstep f (LSess (SLink {[da; x]})) f0) as Hf2
            by (rewrite upair_comm; exact Hf1).
          destruct (decide (da = b)) as [->|Hdab].
          { (* degenerate image {[b]}: the self-forwarding dissolves *)
            assert (proc_step (C, F ⊎ {[+ f +]}) PTau
                      (C ∖ {[b]}, echsubst b x (F ⊎ {[+ f0 +]}))) as Horig
              by (eapply PStepLink; [exact Hf2|done]).
            pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'.
            simpl in Hc'. specialize (Hc' Hguard).
            pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[b]}) _ x b HxΣ
                          ltac:(clear -HxC; set_solver)
                          ltac:(intros Hb; clear -Hb; set_solver)
                          Hbx Hc') as HQ.
            rewrite echsubst_collapse in HQ.
            rewrite echsubst_refl.
            rewrite echsubst_disj_union, echsubst_singleton in HQ.
            exact HQ. }
          (* the source can only retire the other end da: rename the
             junk onto b in its post-state — the induction carries the
             restricted target — then flip the orientation *)
          assert (proc_step (C, F ⊎ {[+ f +]}) PTau
                    (C ∖ {[da]}, echsubst da x (F ⊎ {[+ f0 +]}))) as Horig
            by (eapply PStepLink; [exact Hf2|done]).
          pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'.
          simpl in Hc'.
          specialize (Hc' ltac:(clear -Hguard HbΣ; set_solver)).
          pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[da]}) _ x b HxΣ
                        ltac:(clear -HxC; set_solver)
                        ltac:(intros _; exact HbΣ) Hbx Hc') as HQ.
          rewrite echsubst_chain in HQ; [|done|done|congruence].
          rewrite <-echsubst_singleton, <-echsubst_disj_union.
          apply (Prel_link_orient n' Σ T C _ b da);
            [congruence|exact HcC|exact HdaC|exact HbΣ
            |clear -Hguard HdaC Hdab; set_solver|exact HQ]. }
        (* the source retires the same end c *)
        rewrite csub_ne in Hca by done. subst ca.
        assert (proc_step (C, F ⊎ {[+ f +]}) PTau
                  (C ∖ {[c]}, echsubst c da (F ⊎ {[+ f0 +]}))) as Horig
          by (eapply PStepLink; [exact Hf1|done]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        specialize (Hc' Hguard).
        destruct (decide (da = x)) as [->|Hdax].
        { (* the surviving end is the junk: its occurrences follow x
             to b *)
          rewrite csub_hit in Hda. subst d.
          pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[c]}) _ x b HxΣ
                        ltac:(clear -HxC; set_solver)
                        ltac:(intros Hb; apply HbC; clear -Hb; set_solver)
                        Hbx Hc') as HQ.
          destruct (decide (c = b)) as [->|Hcb].
          - rewrite echsubst_collapse in HQ.
            rewrite echsubst_refl.
            rewrite echsubst_disj_union, echsubst_singleton in HQ.
            exact HQ.
          - rewrite echsubst_chain in HQ; [|done|congruence|done].
            rewrite echsubst_disj_union, echsubst_singleton in HQ.
            exact HQ. }
        rewrite csub_ne in Hda by done. subst d.
        destruct (decide (c = b)) as [->|Hcb]; last first.
        { pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[c]}) _ x b HxΣ
                        ltac:(clear -HxC; set_solver)
                        ltac:(intros Hb; apply HbC; clear -Hb; set_solver)
                        Hbx Hc') as HQ.
          rewrite echsubst_comm in HQ; [|done|done|done].
          rewrite echsubst_disj_union, echsubst_singleton in HQ.
          exact HQ. }
        destruct (decide (da = b)) as [->|Hdab].
        { (* both ends are b: the retargeting is the identity *)
          rewrite echsubst_refl in Hc'.
          pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[b]}) _ x b HxΣ
                        ltac:(clear -HxC; set_solver)
                        ltac:(intros Hb; clear -Hb; set_solver)
                        Hbx Hc') as HQ.
          rewrite echsubst_refl.
          rewrite echsubst_disj_union, echsubst_singleton in HQ.
          exact HQ. }
        (* c = b, da ∉ {x, b}: rename the junk straight onto the
           survivor *)
        pose proof (IHn n' ltac:(lia) Σ T (C ∖ {[b]}) _ x da HxΣ
                      ltac:(clear -HxC; set_solver)
                      ltac:(intros Hb; clear -Hguard Hb; set_solver)
                      Hdax Hc') as HQ.
        rewrite <-(echsubst_chain b da x) in HQ;
          [|congruence|done|done].
        rewrite echsubst_disj_union, echsubst_singleton in HQ.
        exact HQ.
    + (* session offers *)
      apply proc_step_sess_inv in Hst
        as (E0' & e' & e'' & HeqE & Hts & HsC & ->).
      apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
      destruct σ' as [c w|c w|c|cd']; simpl in HsC.
      * (* input offer *)
        simpl.
        set (pool := C ∪ dom Σ ∪ echans (F ⊎ {[+ f +]}) ∪ fchans w
                       ∪ {[x]} ∪ {[b]} ∪ {[c]}).
        assert (fresh pool ∉ pool) as Hfz by apply is_fresh.
        set (z := fresh pool) in *.
        unfold pool in Hfz. clearbody z. clear pool.
        pose proof (echans_disj_union F {[+ f +]}) as Hedu.
        assert (z ∉ fchans f) as Hzf.
        { intros Hz. apply Hfz.
          assert (z ∈ echans (F ⊎ {[+ f +]}));
            [apply elem_of_echans; exists f; split;
              [multiset_solver|done]|set_solver]. }
        destruct (tstep_chsubst_recv_inv_swap x b z f c w e''
                    ltac:(congruence) ltac:(set_solver) ltac:(set_solver)
                    ltac:(set_solver) Hts Hzf)
          as (c0 & f0 & Hc0 & Hf0 & ->).
        assert (proc_step (C, F ⊎ {[+ f +]})
                  (PSess (SRecv c0 (eswap x z w)))
                  (C ∖ sentc (SRecv c0 (eswap x z w)), F ⊎ {[+ f0 +]}))
          as Horig.
        { eapply PStepSession; [exact Hf0|]. simpl.
          destruct (decide (c0 = x)) as [->|Hne]; [clear -HxC; set_solver|].
          rewrite csub_ne in Hc0 by done. by subst c0. }
        pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
        assert (c0 = c) as ->.
        { assert (c0 ≠ x) by (clear -Hsx0; set_solver).
          rewrite csub_ne in Hc0; congruence. }
        simpl in Horig.
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        destruct Hc' as (Σ1 & U & s & Hhd & Hc1 & Hcont).
        exists Σ1, U, s.
        pose proof (senv_hd_dom _ _ _ _ Hhd) as Hdom1.
        split_and!; [done|done|].
        intros j Σn Hj Hdn Hcdn Hfrn HVw.
        pose proof (Vrel_fchans _ _ _ _ HVw) as Hdomn.
        pose proof (Vrel_eswap x z _ _ _ _ HVw) as HVw'.
        assert (x ∉ dom Σ1) as HxΣ1 by set_solver.
        assert (z ∉ dom Σ1) as HzΣ1 by set_solver.
        assert (z ∉ dom Σn) as HzΣn by set_solver.
        simpl in Hfrn.
        specialize (Hcont j (senvswap x z Σn) Hj
                      (senvswap_disjoint_out _ _ _ _ HxΣ1 HzΣ1 Hdn)).
        assert (c ∉ dom (senvswap x z Σn)) as Hckn.
        { rewrite dom_kswap. intros Hcin.
          rewrite elem_of_gswap' in Hcin.
          rewrite cswap_ne in Hcin; [done|clear -Hsx0; set_solver|set_solver]. }
        specialize (Hcont Hckn).
        assert (dom (senvswap x z Σn) ## (C, F ⊎ {[+ f +]}).1) as Hfr'.
        { simpl. rewrite dom_kswap.
          apply gswap_disjoint_out; [done|set_solver|done]. }
        specialize (Hcont Hfr' HVw').
        assert (x ∉ gswap x z (dom Σn)) as Hxg.
        { rewrite elem_of_gswap', cswap_l. exact HzΣn. }
        assert (b ∈ C ∖ ∅ → b ∉ dom (<[c := s]> (Σ1 ∪ senvswap x z Σn)))
          as HbC'.
        { intros Hb. specialize (HbC ltac:(clear -Hb; set_solver)).
          rewrite dom_insert_L, dom_union_L, dom_kswap.
          assert (b ∉ gswap x z (dom Σn)) as Hbg.
          { rewrite elem_of_gswap', cswap_ne;
              [|done|clear -Hfz; set_solver].
            clear -Hfrn Hb. set_solver. }
          clear -HbC Hbg Hdom1 Hb. set_solver. }
        pose proof (IHn j ltac:(lia)
                      (<[c := s]> (Σ1 ∪ senvswap x z Σn)) T (C ∖ ∅) _ x b
                      ltac:(rewrite dom_insert_L, dom_union_L, dom_kswap;
                            set_solver)
                      ltac:(set_solver) HbC' Hbx Hcont)
          as HQ.
        apply (Prel_eswap x z) in HQ.
        unfold pswap in HQ. simpl in HQ.
        rewrite senvswap_insert in HQ.
        rewrite (cswap_ne x z c) in HQ; [|clear -Hsx0; set_solver|set_solver].
        rewrite senvswap_union in HQ.
        rewrite (senvswap_id x z Σ1) in HQ; [|done|done].
        rewrite senvswap_involutive in HQ.
        rewrite (gswap_id x z (C ∖ ∅)) in HQ; [|set_solver|set_solver].
        rewrite echsubst_disj_union, echsubst_singleton in HQ.
        rewrite msswap_disj_union, msswap_singleton in HQ.
        rewrite (echswap_id x z (echsubst x b F)) in HQ;
          [ |apply echans_echsubst_notin; congruence
           |pose proof (echans_echsubst_sub x b F) as Hsub;
            clear -Hsub Hfz Hedu; set_solver].
        exact HQ.
      * (* output offer *)
        simpl.
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hc0 Hw0.
        assert (proc_step (C, F ⊎ {[+ f +]})
                  (PSess (SSend c0 w0))
                  (C ∖ sentc (SSend c0 w0), F ⊎ {[+ f0 +]})) as Horig.
        { eapply PStepSession; [exact Hf0|]. simpl.
          destruct (decide (c0 = x)) as [->|Hne]; [clear -HxC; set_solver|].
          rewrite csub_ne in Hc0 by done. by subst c0. }
        pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
        assert (c0 = c) as ->.
        { assert (c0 ≠ x) by (clear -Hsx0; set_solver).
          rewrite csub_ne in Hc0; congruence. }
        simpl in Horig.
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'.
        simpl in Hc'.
        destruct Hc' as (Σ0 & Σv & U & s & σe & Σw & C0 & E0c & Cw & Ew
                          & T0 & Tw & Hhd & Hd01 & Hd02 & Hd03 & Hn0
                          & Hn1 & Hn2 & Hσe & Hσd & Hcσ & HC' & HCd
                          & HE' & HVw & HP0 & HPw & Hty).
        pose proof (senv_hd_dom _ _ _ _ Hhd) as Hdom1.
        assert (chsubst x b w0 = w0) as Hwid.
        { eapply Vrel_chsubst_id; [|exact HVw].
          rewrite dom_union_L, dom_fmap_L.
          simpl in Hσe. rewrite !dom_union_L in Hdom1. set_solver. }
        rewrite Hwid in Hw0. subst w.
        simpl in HC', HE', Hσe |- *.
        exists Σ0, Σv, U, s, σe, Σw, C0, (echsubst x b E0c), Cw,
          (echsubst x b Ew), T0, Tw.
        split_and!; try done.
        { rewrite <-echsubst_singleton, <-echsubst_disj_union.
          rewrite HE'. by rewrite echsubst_disj_union. }
        { apply (IHn n' ltac:(lia) (<[c := s]> Σ0) T0 C0 _ x b);
            [ |clear -HC' HxC; set_solver
             |intros Hb; specialize (HbC ltac:(clear -HC' Hb; set_solver));
              rewrite dom_insert_L; rewrite !dom_union_L in Hdom1;
              clear -HbC Hdom1; set_solver
             |done|done].
          rewrite dom_insert_L. rewrite !dom_union_L in Hdom1.
          rewrite Hdom1 in HxΣ. clear -HxΣ Hsx0. set_solver. }
        { apply (topo_split_junk _ x b); [ | | | | |exact HPw].
          - intros Σ' T' C' E' Hx' HxC' HbC' HPp.
            by apply (IHn n' ltac:(lia) Σ' T' C' E' x b
                        Hx' HxC' HbC' Hbx).
          - clear -Hσe HxC. set_solver.
          - rewrite !dom_union_L in Hdom1. rewrite Hdom1 in HxΣ.
            clear -HxΣ. set_solver.
          - clear -HC' HxC. set_solver.
          - intros Hb. specialize (HbC ltac:(clear -HC' Hb; set_solver)).
            rewrite !dom_union_L in Hdom1. split.
            + clear -HbC Hdom1. set_solver.
            + rewrite Hσe. clear -HC' Hb. set_solver. }
      * (* close offer *)
        simpl.
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hc0.
        assert (proc_step (C, F ⊎ {[+ f +]})
                  (PSess (SClos c0))
                  (C ∖ sentc (SClos c0), F ⊎ {[+ f0 +]})) as Horig.
        { eapply PStepSession; [exact Hf0|]. simpl.
          destruct (decide (c0 = x)) as [->|Hne]; [clear -HxC; set_solver|].
          rewrite csub_ne in Hc0 by done. by subst c0. }
        pose proof (Hnosessx _ _ Horig) as Hsx0. simpl in Hsx0.
        assert (c0 = c) as ->.
        { assert (c0 ≠ x) by (clear -Hsx0; set_solver).
          rewrite csub_ne in Hc0; congruence. }
        simpl in Horig.
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        destruct Hc' as (Σ1 & Hhd & Hc1 & Hcont).
        pose proof (senv_hd_dom _ _ _ _ Hhd) as Hdom1.
        exists Σ1. split_and!; [done|done|].
        rewrite <-echsubst_singleton, <-echsubst_disj_union.
        apply (IHn n' ltac:(lia) Σ1 T (C ∖ ∅) _ x b);
          [rewrite Hdom1 in HxΣ; clear -HxΣ; set_solver
          |clear -HxC; set_solver
          |intros Hb; specialize (HbC ltac:(clear -Hb; set_solver));
           rewrite Hdom1 in HbC; clear -HbC; set_solver
          |done|done].
      * (* forwarding offer *)
        simpl.
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->);
          [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0]|c0 v0]; simpl in Hα;
          try discriminate.
        injection Hα as Hcd.
        assert (cd0 ## C) as Hd0C.
        { intros y Hy1 Hy2.
          assert (csub x b y ∈ gsub x b cd0) as Hy3
            by (apply elem_of_map; eauto).
          rewrite <-Hcd in Hy3.
          destruct (decide (y = x)) as [->|Hne]; [done|].
          rewrite csub_ne in Hy3 by done. clear -Hy3 Hy2 HsC. set_solver. }
        assert (proc_step (C, F ⊎ {[+ f +]}) (PSess (SLink cd0))
                  (C ∖ sentc (SLink cd0), F ⊎ {[+ f0 +]})) as Horig
          by (eapply PStepSession; [exact Hf0|done]).
        pose proof (Hnolinkx _ _ Horig) as Hxcd.
        rewrite gsub_id in Hcd by done. subst cd'.
        pose proof (Prel_S_step _ _ _ _ _ _ HP Horig) as Hc'. simpl in Hc'.
        destruct Hc' as (c1 & d1 & Σ1 & sc & sd & -> & Hne1 & HΣeq
                          & Hcd1 & Hdd1 & Hdu & Hcont).
        exists c1, d1, Σ1, sc, sd.
        split_and!; try done.
        rewrite <-echsubst_singleton, <-echsubst_disj_union.
        apply (IHn n' ltac:(lia) Σ1 T (C ∖ ∅) _ x b);
          [ |clear -HxC; set_solver
           |intros Hb; specialize (HbC ltac:(clear -Hb; set_solver));
            rewrite HΣeq, !dom_insert_L in HbC; clear -HbC; set_solver
           |done|done].
        rewrite HΣeq, !dom_insert_L in HxΣ. clear -HxΣ. set_solver.
Qed.
