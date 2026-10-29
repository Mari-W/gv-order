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

    The input and new clauses quantify over values (respectively fresh
    names) that may mention the renamed-away name x again; those cases
    are closed by instantiating the original's clause at an α-variant
    (x transposed to a fresh z) and repairing with the transposition
    transport of the relation ([Equivariance.rel_swap]). With worlds,
    this needs x unknown to the world, which is exactly when the
    renamed process can receive or create x at all (fresh receives,
    the freshness guard of [new]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Chain Equivariance.

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

(** ** α-variants that avoid given names

    [walpha_av X W Σ q r]: an α-variant whose renaming steps introduce
    no name of X. Every α-variant can be made to avoid X by a final
    transposition of names the world and the interface do not know
    ([walpha_norm]), which the relation does not notice
    ([Prel_swap_fix]). *)

Inductive walpha_av (X : gset chan) (W : world) (Σ : senv) : proc → proc → Prop :=
  | walpha_av_refl p : walpha_av X W Σ p p
  | walpha_av_step p q a b :
      a ∈ p.1 → b ∉ p.1 → b ∉ echans p.2 → b ∉ dom Σ → wfresh W b → b ∉ X →
      walpha_av X W Σ (pswap a b p) q → walpha_av X W Σ p q.

Lemma walpha_av_walpha X W Σ p q : walpha_av X W Σ p q → walpha W Σ p q.
Proof. induction 1; econstructor; eauto. Qed.

Lemma wfresh_pick (W : world) (Y : gset chan) : ∃ z, z ∉ Y ∧ wfresh W z.
Proof.
  set (Z := list_to_set (omap (λ p, match pn_root p with NChan c => Some c | _ => None end)
                              (elements (w_names W))) : gset chan).
  destruct (exist_fresh (Y ∪ Z)) as [z Hz]. exists z. split; [set_solver|].
  intros p Hp Hr. apply Hz, elem_of_union_r, elem_of_list_to_set, list_elem_of_omap.
  exists p. split; [by apply elem_of_elements|by rewrite Hr].
Qed.

Lemma walpha_av_mono X Y W Σ p q :
  Y ⊆ X → walpha_av X W Σ p q → walpha_av Y W Σ p q.
Proof. intros HXY. induction 1; econstructor; eauto. Qed.

(** Transposing two names the world and the interface do not know maps
    an α-variant avoiding both to one, with the same names avoided. *)
Lemma walpha_av_pswap X W Σ p q a b :
  world_wf W → wfresh W a → wfresh W b → a ∉ dom Σ → b ∉ dom Σ →
  walpha_av ({[a; b]} ∪ X) W Σ p q →
  walpha_av X W Σ (pswap a b p) (pswap a b q).
Proof.
  intros HW Ha Hb HaΣ HbΣ.
  induction 1 as [p|p q c d Hc Hd HdE HdΣ Hdw HdX _ IH]; [constructor|].
  assert (cswap a b d = d) as Hsd by (apply cswap_ne; set_solver).
  apply (walpha_av_step _ _ _ _ _ (cswap a b c) d).
  - destruct p; simpl in *. by apply elem_of_gswap.
  - destruct p; simpl in *. rewrite <-Hsd. by rewrite elem_of_gswap.
  - destruct p; simpl in *. rewrite echans_msswap, <-Hsd. by rewrite elem_of_gswap.
  - done.
  - done.
  - set_solver.
  - rewrite <-Hsd. by rewrite <-pswap_conj.
Qed.

Definition pswaps (L : list (chan * chan)) (q : proc) : proc :=
  foldr (λ ab r, pswap ab.1 ab.2 r) q L.

Definition swaps_ok (W : world) (Σ : senv) (L : list (chan * chan)) : Prop :=
  Forall (λ ab, wfresh W ab.1 ∧ wfresh W ab.2 ∧ ab.1 ∉ dom Σ ∧ ab.2 ∉ dom Σ) L.

Lemma Prel_pswaps n W Σ T q L :
  world_wf W → swaps_ok W Σ L → Prel n W Σ T q → Prel n W Σ T (pswaps L q).
Proof.
  intros HW HL HP. induction HL as [|[a b] L (? & ? & ? & ?) _ IH]; [done|].
  simpl. by apply Prel_swap_fix.
Qed.

Lemma walpha_norm W Σ p q (X : gset chan) :
  world_wf W → walpha W Σ p q →
  ∃ L, walpha_av X W Σ p (pswaps L q) ∧ swaps_ok W Σ L.
Proof.
  intros HW Hal. revert X.
  induction Hal as [p|p q a b Ha Hb HbE HbΣ Hbw _ IH]; intros X.
  { exists []. split; [constructor|constructor]. }
  destruct (decide (b ∈ X)) as [HbX|HbX].
  - destruct (wfresh_pick W (X ∪ p.1 ∪ echans p.2 ∪ dom Σ ∪ {[a; b]}))
      as (z & Hz & Hzw).
    destruct (IH ({[b; z]} ∪ X)) as (L & Hq1 & HL).
    exists ((b, z) :: L). split; [|constructor; [split_and!; simpl; [done|done|done|set_solver]|done]].
    apply (walpha_av_step _ _ _ _ _ a z); [done|set_solver|set_solver|set_solver|done|set_solver|].
    assert (pswap a z p = pswap b z (pswap a b p)) as ->.
    { rewrite pswap_conj, cswap_l, (cswap_ne b z a) by set_solver.
      rewrite (pswap_fresh b z p); [done|done|set_solver|done|set_solver]. }
    apply walpha_av_pswap; [done|done|done|done|set_solver|done].
  - destruct (IH X) as (L & Hq1 & HL).
    exists L. split; [|done]. by econstructor.
Qed.

(** The junk renaming commutes with an α-variant avoiding x and b. *)
Lemma msswap_echsubst a b' x b E :
  a ≠ x → a ≠ b → b' ≠ x → b' ≠ b →
  msswap a b' (echsubst x b E) = echsubst x b (msswap a b' E).
Proof.
  intros. rewrite echsubst_msswap. by rewrite !cswap_ne.
Qed.

Lemma walpha_av_junk W Σ q r x b :
  walpha_av {[x; b]} W Σ q r → x ∉ q.1 → b ∉ q.1 →
  walpha_av {[x; b]} W Σ (q.1, echsubst x b q.2) (r.1, echsubst x b r.2) ∧
  x ∉ r.1 ∧ b ∉ r.1.
Proof.
  induction 1 as [q|q r a b' Ha Hb' HbE HbΣ Hbw HbX _ IH]; intros Hx Hb.
  { split_and!; [constructor|done|done]. }
  assert (a ≠ x ∧ a ≠ b) as [Hax Hab] by (split; intros ->; done).
  assert (b' ≠ x ∧ b' ≠ b) as [Hbx Hbb] by set_solver.
  destruct q as [C E]; simpl in *.
  destruct IH as (IH & Hxr & Hbr).
  { simpl. rewrite elem_of_gswap'. by rewrite cswap_ne. }
  { simpl. rewrite elem_of_gswap'. by rewrite cswap_ne. }
  split_and!; [|done|done].
  apply (walpha_av_step _ _ _ _ _ a b'); simpl; [done|done| |done|done|done|].
  - pose proof (echans_echsubst_sup x b E). intros Hin.
    apply fchans_chsubst in Hin || idtac.
    apply elem_of_echans in Hin as (e & He & Hbe).
    unfold echsubst in He. apply elem_of_gmultiset_map in He as (e0 & -> & He0).
    apply fchans_chsubst in Hbe. apply HbE. apply elem_of_echans.
    exists e0. split; [done|]. set_solver.
  - unfold pswap at 1; simpl. rewrite msswap_echsubst by done. exact IH.
Qed.
