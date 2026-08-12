(** * Harmony: a reduction semantics for process soups vs the τ-LTS

    Following the notes in harmony.lagda (the "Alternative": a direct
    reduction semantics on soups (C, E), no ∥/ν/≡ configuration
    calculus), adapted to GV♯:

    - the pure reduction −→V and the redex rules are phrased with
      genuine multi-frame evaluation contexts 𝓔 (lists of the
      one-level frames of Semantics.v, with the right-of-value
      side conditions), so the semantics is defined WITHOUT reference
      to the labelled [tstep] relation — harmony is then a real
      theorem, not a reformulation;
    - a [CLOSE] rule is added (GV♯'s P-Act-Close is a τ-step; the
      notes' COM/FORK/LIFTV inventory would make the backward
      direction fail);
    - COM and CLOSE carry the [c ∈ C] premise that P-Act-Msg /
      P-Act-Close require (the notes leave it to the ambient
      invariant fc(E) ⊆ C, which raw GV♯ processes do not carry);
    - FORK carries the full freshness of P-Act-Fork (new channel not
      in C, nor in the rest of the soup, nor in the forking thread —
      channels are free names here, there is no α-conversion);
    - the communicated value and the fork argument are values, as in
      the head rules.

    Main result (Harmony):
      red p p'  ↔  preduction p p'
    via the two context/label bridge lemmas [fill_tstep] and
    [tstep_fill_decomp]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Semantics.

(** ** Evaluation contexts

    𝓔 ::= [] | 𝓔 e | v 𝓔 | ⟨𝓔,e⟩ | ⟨v,𝓔⟩ | let ∗ = 𝓔 in e
        | let ⟨a,b⟩ = 𝓔 in e | inj1 𝓔 | inj2 𝓔 | case 𝓔 (a.e)(a.e)

    as lists of the one-level frames of Semantics.v, innermost frame
    first; [ectx_val] enforces the value side condition on the
    right-of-value frames. *)

Definition ectx := list frame.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | [] => e
  | f :: K' => fill K' (fill_frame f e)
  end.

Definition ectx_val (K : ectx) : Prop := Forall frame_val K.

(** ** The pure reduction M −→V M′ (label-free)

    The five β-redexes, then closure under evaluation contexts.
    This intentionally duplicates the LBeta cases of [head_step]:
    the reduction semantics must stand on its own. *)

Inductive head_red : expr → expr → Prop :=
  | HRedApp e v :
      is_val v →
      head_red (App (Lam e) v) (subst1 v e)
  | HRedLetU e :
      head_red (LetU EUnit e) e
  | HRedLetP u v e :
      is_val u → is_val v →
      head_red (LetP (Pair u v) e) (subst2 u v e)
  | HRedCase1 v e1 e2 :
      is_val v →
      head_red (Case (Inj1 v) e1 e2) (subst1 v e1)
  | HRedCase2 v e1 e2 :
      is_val v →
      head_red (Case (Inj2 v) e1 e2) (subst1 v e2)
  | HRedForce e :
      head_red (App EForce (EBox e)) (subst1 (EBox e) e).

Definition vred (e e' : expr) : Prop :=
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧
              head_red eh eh'.

(** ** The reduction semantics on soups *)

Inductive red : proc → proc → Prop :=
  | RedLift C E e e' :                                  (* LIFTV *)
      vred e e' →
      red (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | RedFork C E K v c :                                 (* FORK *)
      ectx_val K → is_val v →
      c ∉ C → c ∉ echans E → c ∉ fchans (fill K (App EFork v)) →
      red (C, E ⊎ {[+ fill K (App EFork v) +]})
          (C ∪ {[c]},
           E ⊎ {[+ fill K (Chan c) +]} ⊎ {[+ App v (Chan c) +]})
  | RedCom C E K K' v c :                               (* COM *)
      ectx_val K → ectx_val K' → is_val v →
      c ∈ C →
      red (C, E ⊎ {[+ fill K (App ESend (Pair v (Chan c))) +]}
             ⊎ {[+ fill K' (App ERecv (Chan c)) +]})
          (C, E ⊎ {[+ fill K (Chan c) +]}
             ⊎ {[+ fill K' (Pair v (Chan c)) +]})
  | RedClose C E K K' c :                               (* CLOSE *)
      ectx_val K → ectx_val K' →
      c ∈ C →
      red (C, E ⊎ {[+ fill K (App EClos (Chan c)) +]}
             ⊎ {[+ fill K' (App EClos (Chan c)) +]})
          (C ∖ {[c]},
           E ⊎ {[+ fill K EUnit +]} ⊎ {[+ fill K' EUnit +]})
  | RedLinkL C E K c d :                                (* LINK *)
      (* the paper's rule: the removed end is restricted and the whole
         resulting configuration is substituted; the two rules are the
         two orientations of the unordered pair over ordered syntax.
         The ends need not differ — a self-forwarding on a restricted
         name substitutes by the identity and releases the name, and
         the LTS admits it, so harmony would fail if [red] did not. *)
      ectx_val K → c ∈ C →
      red (C, E ⊎ {[+ fill K (App ELink (Pair (Chan c) (Chan d))) +]})
          (C ∖ {[c]}, echsubst c d (E ⊎ {[+ fill K EUnit +]}))
  | RedLinkR C E K c d :
      ectx_val K → d ∈ C →
      red (C, E ⊎ {[+ fill K (App ELink (Pair (Chan c) (Chan d))) +]})
          (C ∖ {[d]}, echsubst d c (E ⊎ {[+ fill K EUnit +]})).

(** ** The context/label bridge

    [fill_tstep]: filling a step into an evaluation context is a step
    (iterated [tstep_fill]).  [tstep_fill_decomp]: every labelled step
    decomposes as an evaluation context around a head step (induction
    on [tstep]; each congruence rule appends one frame, its value side
    condition supplying [ectx_val]). *)

Lemma fill_app K K' e : fill (K ++ K') e = fill K' (fill K e).
Proof. revert e. induction K as [|f K IH]; intros e; simpl; auto. Qed.

Lemma ectx_val_app K K' :
  ectx_val K → ectx_val K' → ectx_val (K ++ K').
Proof. apply Forall_app_2. Qed.

Lemma ectx_val_frame f : frame_val f → ectx_val [f].
Proof. intros Hf. by apply Forall_singleton. Qed.

Lemma fill_tstep K e α e' :
  ectx_val K → tstep e α e' → tstep (fill K e) α (fill K e').
Proof.
  revert e e'. induction K as [|f K IH]; intros e e' HK Hst; simpl;
    [done|].
  apply Forall_cons in HK as [Hf HK].
  apply IH; [done|]. by apply tstep_fill.
Qed.

Lemma tstep_fill_decomp e α e' :
  tstep e α e' →
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧
              head_step eh α eh'.
Proof.
  induction 1 as
    [f0 β f1 Hh
    |f0 β f1 g0 Hst IH|v0 g0 β g1 Hv Hst IH
    |f0 β f1 g0 Hst IH|v0 g0 β g1 Hv Hst IH
    |f0 β f1 g0 Hst IH|f0 β f1 g0 Hst IH
    |f0 β f1 Hst IH|f0 β f1 Hst IH|f0 β f1 g0 g1 Hst IH];
    [exists [], f0, f1; split_and!; [apply Forall_nil; done|done..]|..];
    destruct IH as (K & eh & eh' & HK & -> & -> & Hh);
    [ exists (K ++ [FAppL g0]), eh, eh'
    | exists (K ++ [FAppR v0]), eh, eh'
    | exists (K ++ [FPairL g0]), eh, eh'
    | exists (K ++ [FPairR v0]), eh, eh'
    | exists (K ++ [FLetU g0]), eh, eh'
    | exists (K ++ [FLetP g0]), eh, eh'
    | exists (K ++ [FInj1]), eh, eh'
    | exists (K ++ [FInj2]), eh, eh'
    | exists (K ++ [FCase g0 g1]), eh, eh' ];
    rewrite !fill_app; simpl;
    (split_and!; [|done..]);
    (apply ectx_val_app; [done|apply ectx_val_frame; done]).
Qed.

(** ** Pure reduction vs β-labelled steps *)

Lemma head_red_head_step e e' : head_red e e' → head_step e LBeta e'.
Proof. destruct 1; by constructor. Qed.

Lemma head_step_beta_head_red e e' : head_step e LBeta e' → head_red e e'.
Proof. inversion 1; by constructor. Qed.

Lemma vred_reduction e e' : vred e e' ↔ reduction e e'.
Proof.
  split.
  - intros (K & eh & eh' & HK & -> & -> & Hh).
    apply fill_tstep; [done|]. apply TStepHead.
    by apply head_red_head_step.
  - intros Hst.
    apply tstep_fill_decomp in Hst as (K & eh & eh' & HK & -> & -> & Hh).
    exists K, eh, eh'. split_and!; try done.
    by apply head_step_beta_head_red.
Qed.

(** ** Harmony *)

Theorem harmony_forward p p' : red p p' → preduction p p'.
Proof.
  destruct 1 as
    [C E e e' Hv|C E K v c HK Hval Hc1 Hc2 Hc3
    |C E K K' v c HK HK' Hval Hc|C E K K' c HK HK' Hc
    |C E K c d HK Hc|C E K c d HK Hd].
  - apply PStepBeta. by apply vred_reduction.
  - apply PStepFork; [|done|done|done].
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadFork.
  - eapply PStepMsg; [..|done].
    + apply fill_tstep; [done|]. apply TStepHead. by apply HeadSend.
    + apply fill_tstep; [done|]. apply TStepHead. by apply HeadRecv.
  - eapply PStepClose; [..|done].
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadClos.
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadClos.
  - apply PStepLink; [|done].
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadLink.
  - apply PStepLink; [|done].
    rewrite upair_comm.
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadLink.
Qed.

(** Head inversion for forwarding, keeping the label pair abstract so
    the unordered-set equation stays at the [gset] level (a bare
    [inversion] would inject through the mapset record). *)
Lemma head_step_link_inv e cd e' :
  head_step e (LSess (SLink cd)) e' →
  ∃ c d, e = App ELink (Pair (Chan c) (Chan d)) ∧ cd = {[c; d]} ∧
         e' = EUnit.
Proof. inversion 1; eauto 8. Qed.

Theorem harmony_backward p p' : preduction p p' → red p p'.
Proof.
  intros Hst; inversion Hst; subst.
  - (* P-Act-Beta *)
    apply RedLift. by apply vred_reduction.
  - (* P-Act-Fork *)
    match goal with H : tstep _ (LFork _ _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    inversion Hh; subst.
    by apply RedFork.
  - (* P-Act-Msg *)
    match goal with H : tstep _ (LSess (SSend _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    match goal with H : tstep _ (LSess (SRecv _ _)) _ |- _ =>
      apply tstep_fill_decomp in H
        as (K' & fh & fh' & HK' & -> & -> & Hh')
    end.
    inversion Hh; subst. inversion Hh'; subst.
    by apply RedCom.
  - (* P-Act-Close *)
    match goal with H : tstep _ (LSess (SClos _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    match goal with H : tstep _ (LSess (SClos _)) _ |- _ =>
      apply tstep_fill_decomp in H
        as (K' & fh & fh' & HK' & -> & -> & Hh')
    end.
    inversion Hh; subst. inversion Hh'; subst.
    by apply RedClose.
  - (* P-Act-Link: recover the orientation of the pair *)
    match goal with H : tstep _ (LSess (SLink _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    apply head_step_link_inv in Hh as (c0 & d0 & -> & Hp & ->).
    destruct (decide (c0 = d0)) as [->|Hne0].
    + (* the term names one channel twice, so the label's two ends
         coincide with it and the rule fires degenerately *)
      match goal with Hc : ?c ∈ _ |- _ =>
        assert (c = d0) as ->;
          [assert (c ∈ ({[d0; d0]} : gset chan)) as Hin
             by (rewrite <-Hp; clear; set_solver);
           clear -Hin; set_solver|]
      end.
      assert (d = d0) as ->.
      { assert (d ∈ ({[d0; d0]} : gset chan)) as Hin
          by (rewrite <-Hp; clear; set_solver).
        clear -Hin. set_solver. }
      by apply RedLinkL.
    + destruct (upair_eq_inv _ _ _ _ (eq_sym Hp) ltac:(congruence))
        as [[<- <-]|[<- <-]].
      * by apply RedLinkL.
      * by apply RedLinkR.
Qed.

Theorem harmony p p' : red p p' ↔ preduction p p'.
Proof. split; [apply harmony_forward|apply harmony_backward]. Qed.
