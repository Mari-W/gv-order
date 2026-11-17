(** * Harmony of a reduction semantics with the process steps (stage S1)

    [red] is a reduction semantics on soups (C, E) with evaluation
    contexts, defined without the labelled [tstep] and without the
    instrumented [istep], so [harmony] (red p p' ↔ preduction p p') is a
    real theorem. *)

From stdpp Require Import relations.
From GV Require Import lang.Process.

(** ** Evaluation contexts, innermost frame first *)

Definition ectx := list frame.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | [] => e
  | f :: K' => fill K' (fill_frame f e)
  end.

Definition ectx_val (K : ectx) : Prop := Forall frame_val K.

(** ** The pure reduction, label-free *)

Inductive head_red : expr → expr → Prop :=
  | HRedApp e v : is_val v → head_red (App (Lam e) v) (subst1 v e)
  | HRedLetU e : head_red (LetU EUnit e) e
  | HRedLetP u v e : is_val u → is_val v → head_red (LetP (Pair u v) e) (subst2 u v e)
  | HRedLet v e : is_val v → head_red (ELet v e) (subst1 v e)
  | HRedCase1 v e1 e2 : is_val v → head_red (Case (Inj1 v) e1 e2) (subst1 v e1)
  | HRedCase2 v e1 e2 : is_val v → head_red (Case (Inj2 v) e1 e2) (subst1 v e2)
  | HRedForce e : head_red (EForce (EBox e)) (subst1 (EBox e) e).

Definition vred (e e' : expr) : Prop :=
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧ head_red eh eh'.

(** ** The reduction semantics on soups *)

Inductive red : proc → proc → Prop :=
  | RedLift C E e e' :                                  (* LIFT *)
      vred e e' →
      red (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | RedNew C E K ℓ c :                                  (* NEW *)
      ectx_val K →
      c ∉ C → c ∉ echans E → c ∉ fchans (fill K (ENew ℓ)) →
      red (C, E ⊎ {[+ fill K (ENew ℓ) +]})
          (C ∪ {[c]}, E ⊎ {[+ fill K (Pair (Chan c⁺) (Chan c⁻)) +]})
  | RedNewAt C E K κ o c :                              (* NEW-AT *)
      ectx_val K →
      c ∉ C → c ∉ echans E → c ∉ fchans (fill K (ENewAt κ (Chan o))) →
      red (C, E ⊎ {[+ fill K (ENewAt κ (Chan o)) +]})
          (C ∪ {[c]}, E ⊎ {[+ fill K (Pair (Chan o) (Pair (Chan c⁺) (Chan c⁻))) +]})
  | RedSpawn C E K v :                                  (* SPAWN *)
      ectx_val K → is_val v →
      red (C, E ⊎ {[+ fill K (ESpawn v) +]})
          (C, E ⊎ {[+ fill K EUnit +]} ⊎ {[+ App v EUnit +]})
  | RedCom C E K K' v o :                               (* COM *)
      ectx_val K → ectx_val K' → is_val v →
      red (C, E ⊎ {[+ fill K (ESend (Pair v (Chan o))) +]} ⊎ {[+ fill K' (ERecv (Chan o‾)) +]})
          (C, E ⊎ {[+ fill K (Chan o) +]} ⊎ {[+ fill K' (Pair v (Chan o‾)) +]})
  | RedClose C E K K' o :                               (* CLOSE *)
      ectx_val K → ectx_val K' → ech o ∈ C →
      red (C, E ⊎ {[+ fill K (EClose (Chan o)) +]} ⊎ {[+ fill K' (EClose (Chan o‾)) +]})
          (C ∖ {[ech o]}, E ⊎ {[+ fill K EUnit +]} ⊎ {[+ fill K' EUnit +]})
  | RedChoice C E K K' i o :                            (* CHOICE *)
      ectx_val K → ectx_val K' →
      red (C, E ⊎ {[+ fill K (ESel i (Chan o)) +]} ⊎ {[+ fill K' (EBra (Chan o‾)) +]})
          (C, E ⊎ {[+ fill K (Chan o) +]} ⊎ {[+ fill K' (inj_of i (Chan o‾)) +]})
  | RedLinkL C E K o1 o2 :                              (* LINK *)
      (* the two orientations of the unordered pair over ordered syntax *)
      ectx_val K → ech o1 ∈ C →
      red (C, E ⊎ {[+ fill K (ELink (Pair (Chan o1) (Chan o2))) +]})
          (C ∖ {[ech o1]}, emapE (csub o1 o2) (E ⊎ {[+ fill K EUnit +]}))
  | RedLinkR C E K o1 o2 :
      ectx_val K → ech o2 ∈ C →
      red (C, E ⊎ {[+ fill K (ELink (Pair (Chan o1) (Chan o2))) +]})
          (C ∖ {[ech o2]}, emapE (csub o2 o1) (E ⊎ {[+ fill K EUnit +]})).

(** ** Contexts and labelled steps *)

Lemma fill_app K K' e : fill (K ++ K') e = fill K' (fill K e).
Proof. revert e. induction K as [|f K IH]; intros e; simpl; auto. Qed.

Lemma fill_tstep K e α e' :
  ectx_val K → tstep e α e' → tstep (fill K e) α (fill K e').
Proof.
  revert e e'. induction K as [|f K IH]; intros e e' HK Hst; simpl; [done|].
  inversion HK as [|? ? Hf HK']; subst. apply IH; [done|]. by apply t_act_ctx.
Qed.

Lemma tstep_fill_decomp e α e' :
  tstep e α e' →
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧ head_step eh α eh'.
Proof.
  induction 1 as [e α e' Hh|f e α e' Hf Hs (K & eh & eh' & HK & -> & -> & Hh)].
  - exists [], e, e'. split_and!; [apply Forall_nil|done..].
  - exists (K ++ [f]), eh, eh'. rewrite !fill_app. split_and!; [|done..].
    apply Forall_app_2; [done|]. by repeat constructor.
Qed.

Lemma head_red_head_step e e' : head_red e e' → head_step e LBeta e'.
Proof. destruct 1; by constructor. Qed.

Lemma head_step_beta_head_red e e' : head_step e LBeta e' → head_red e e'.
Proof. inversion 1; by constructor. Qed.

Lemma vred_reduction e e' : vred e e' ↔ reduction e e'.
Proof.
  split.
  - intros (K & eh & eh' & HK & -> & -> & Hh).
    apply fill_tstep; [done|]. apply tstep_head. by apply head_red_head_step.
  - intros Hst.
    apply tstep_fill_decomp in Hst as (K & eh & eh' & HK & -> & -> & Hh).
    exists K, eh, eh'. split_and!; try done. by apply head_step_beta_head_red.
Qed.

(** ** Harmony *)

Theorem harmony_forward p p' : red p p' → preduction p p'.
Proof.
  unfold preduction. rewrite pstep_iff.
  destruct 1 as [C E e e' Hv|C E K ℓ c HK Hc1 Hc2 Hc3|C E K κ o c HK Hc1 Hc2 Hc3
    |C E K v HK Hval|C E K K' v o HK HK' Hval|C E K K' o HK HK' Hc
    |C E K K' i o HK HK'|C E K o1 o2 HK Hc|C E K o1 o2 HK Hd].
  - apply ps_beta. by apply vred_reduction.
  - eapply ps_new; [|done|done|done]. apply fill_tstep; [done|]. apply tstep_head, t_act_new.
  - eapply ps_new_at; [|done|done|done]. apply fill_tstep; [done|].
    apply tstep_head, t_act_new_at.
  - eapply ps_spawn. apply fill_tstep; [done|]. apply tstep_head. by apply t_act_spawn.
  - eapply ps_msg.
    + apply fill_tstep; [done|]. apply tstep_head. by apply t_act_send.
    + apply fill_tstep; [done|]. apply tstep_head. by apply t_act_recv.
  - eapply ps_close; [..|done].
    + apply fill_tstep; [done|]. apply tstep_head, t_act_close.
    + apply fill_tstep; [done|]. apply tstep_head, t_act_close.
  - eapply (ps_choice _ _ _ i).
    + apply fill_tstep; [done|]. apply tstep_head, t_act_select.
    + apply fill_tstep; [done|]. apply tstep_head, t_act_branch.
  - eapply ps_link; [|done]. apply fill_tstep; [done|]. apply tstep_head, t_act_link.
  - eapply ps_link; [|done]. rewrite upair_comm.
    apply fill_tstep; [done|]. apply tstep_head, t_act_link.
Qed.

Lemma head_step_link_inv e os e' :
  head_step e (LSess (SLink os)) e' →
  ∃ o1 o2, e = ELink (Pair (Chan o1) (Chan o2)) ∧ os = {[o1; o2]} ∧ e' = EUnit.
Proof. inversion 1; eauto 8. Qed.

Theorem harmony_backward p p' : preduction p p' → red p p'.
Proof.
  unfold preduction. rewrite pstep_iff. intros Hst; inversion Hst; subst.
  - (* β *)
    apply RedLift. by apply vred_reduction.
  - (* new_ℓ *)
    match goal with H : tstep _ (LNew _ _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    inversion Hh; subst. by apply RedNew.
  - (* new_κ *)
    match goal with H : tstep _ (LNewAt _ _ _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    inversion Hh; subst. by apply RedNewAt.
  - (* spawn *)
    match goal with H : tstep _ (LSpawn _ _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    inversion Hh; subst. by apply RedSpawn.
  - (* message *)
    match goal with H : tstep _ (LSess (SSend _ _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    match goal with H : tstep _ (LSess (SRecv _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K' & fh & fh' & HK' & -> & -> & Hh') end.
    inversion Hh; subst. inversion Hh'; subst. by apply RedCom.
  - (* close *)
    match goal with H : tstep _ (LSess (SClose ?o)) _, H' : tstep _ (LSess (SClose ?o‾)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh);
      apply tstep_fill_decomp in H' as (K' & fh & fh' & HK' & -> & -> & Hh') end.
    inversion Hh; subst. inversion Hh'; subst. by apply RedClose.
  - (* choice *)
    match goal with H : tstep _ (LSess (SSel _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    match goal with H : tstep _ (LSess (SBra _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K' & fh & fh' & HK' & -> & -> & Hh') end.
    inversion Hh; subst. inversion Hh'; subst. by apply RedChoice.
  - (* link: recover the orientation of the pair *)
    match goal with H : tstep _ (LSess (SLink _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh) end.
    apply head_step_link_inv in Hh as (p1 & p2 & -> & Hp & ->).
    destruct (decide (p1 = p2)) as [<-|Hne].
    + assert (o1 = p1) as ->.
      { assert (o1 ∈ ({[p1; p1]} : gset cend)) as Hin by (rewrite <-Hp; set_solver).
        set_solver. }
      assert (o2 = p1) as ->.
      { assert (o2 ∈ ({[p1; p1]} : gset cend)) as Hin by (rewrite <-Hp; set_solver).
        set_solver. }
      by apply RedLinkL.
    + destruct (upair_eq_inv _ _ _ _ (eq_sym Hp) Hne) as [[-> ->]|[-> ->]].
      * by apply RedLinkL.
      * by apply RedLinkR.
Qed.

Theorem harmony p p' : red p p' ↔ preduction p p'.
Proof. split; [apply harmony_forward|apply harmony_backward]. Qed.
