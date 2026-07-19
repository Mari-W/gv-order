(** * Labelled term semantics of GV♯ (Fig. 2)

    A labelled relation e --λ--> e' where labels λ (written α in the
    Coq code, as λ is reserved notation) record the effect:
    β for pure reductions, session labels σ (c?v, c!v, c!) for
    communication, and (νc)v for forks. *)

From stdpp Require Import base strings gmap relations.
From LRGV Require Export Syntax.

(** ** Labels *)

(** Session labels σ ::= c?v | c!v | c! *)
Inductive slabel :=
  | SRecv (c : chan) (v : expr)    (* c?v : receiving value v on c *)
  | SSend (c : chan) (v : expr)    (* c!v : sending value v on c *)
  | SClos (c : chan).              (* c!  : closing c *)

(** Term labels α ::= β | σ | (νc)v *)
Inductive tlabel :=
  | LBeta
  | LSess (σ : slabel)
  | LFork (c : chan) (v : expr).   (* (νc)v : fork of thread v on new c *)

Definition subj (σ : slabel) : chan :=
  match σ with SRecv c _ | SSend c _ | SClos c => c end.

(** Channels escaping the local scope due to a communication effect:
    an output c!v leaks the channels occurring in the message v. *)
Definition sentc (σ : slabel) : gset chan :=
  match σ with SSend _ v => fchans v | _ => ∅ end.

(** ** Head steps

    T-Act-Recv receives any value, not only closed ones: a receive
    step must exist for every value some sender might emit, or a
    send/receive pair could fail to synchronize at the process level
    (the composite would deadlock even though both components are
    semantically well-behaved — the logical relation at low step index
    admits open λ-values, so restricting reception to closed values
    would falsify compositionality of CONNECT at index 1). *)

Inductive head_step : expr → tlabel → expr → Prop :=
  | HeadApp e v :                                       (* T-Act-App *)
      is_val v →
      head_step (App (Lam e) v) LBeta (subst1 v e)
  | HeadLetU e :                                        (* T-Act-Let* *)
      head_step (LetU EUnit e) LBeta e
  | HeadLetP u v e :                                    (* T-Act-LetPair *)
      is_val u → is_val v →
      head_step (LetP (Pair u v) e) LBeta (subst2 u v e)
  | HeadFork v c :                                      (* T-Act-Fork *)
      is_val v →
      head_step (App EFork v) (LFork c v) (Chan c)
  | HeadRecv c v :                                      (* T-Act-Recv *)
      is_val v →
      head_step (App ERecv (Chan c)) (LSess (SRecv c v)) (Pair v (Chan c))
  | HeadSend v c :                                      (* T-Act-Send *)
      is_val v →
      head_step (App ESend (Pair v (Chan c))) (LSess (SSend c v)) (Chan c)
  | HeadClos c :                                        (* T-Act-Close *)
      head_step (App EClos (Chan c)) (LSess (SClos c)) EUnit.

(** ** Context closure (T-Act-Ctx)

    Evaluation contexts E ::= [] | E e | v E | ⟨E,e⟩ | ⟨v,E⟩
                            | let ∗ = E in e | let ⟨a,b⟩ = E in e
    realized as congruence rules (with value side conditions for the
    right-of-value frames). *)

Inductive tstep : expr → tlabel → expr → Prop :=
  | TStepHead e α e' :
      head_step e α e' → tstep e α e'
  | TStepAppL e1 α e1' e2 :
      tstep e1 α e1' → tstep (App e1 e2) α (App e1' e2)
  | TStepAppR v e2 α e2' :
      is_val v → tstep e2 α e2' → tstep (App v e2) α (App v e2')
  | TStepPairL e1 α e1' e2 :
      tstep e1 α e1' → tstep (Pair e1 e2) α (Pair e1' e2)
  | TStepPairR v e2 α e2' :
      is_val v → tstep e2 α e2' → tstep (Pair v e2) α (Pair v e2')
  | TStepLetU e1 α e1' e2 :
      tstep e1 α e1' → tstep (LetU e1 e2) α (LetU e1' e2)
  | TStepLetP e1 α e1' e2 :
      tstep e1 α e1' → tstep (LetP e1 e2) α (LetP e1' e2).

(** GV-style term reduction: just the pure steps. *)
Definition reduction (e e' : expr) : Prop := tstep e LBeta e'.
Notation red_star := (rtc reduction).

(** Irreducible terms (Def. 3.1). *)
Definition irred (e : expr) : Prop := ∀ α e', ¬ tstep e α e'.

(** ** Basic lemmas *)

Lemma val_head_step v α e' : head_step v α e' → is_val v → False.
Proof. by destruct 1. Qed.

Lemma val_no_tstep v α e' : tstep v α e' → is_val v → False.
Proof.
  induction 1; simpl; intros Hv; try done; eauto using val_head_step;
    apply andb_True in Hv as [? ?]; auto.
Qed.

Lemma val_irred v : is_val v → irred v.
Proof. intros ? α e' ?. eauto using val_no_tstep. Qed.

(** ** Step inversion by head constructor *)

Lemma tstep_app_inv e1 e2 α e' :
  tstep (App e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = App e1' e2)
  ∨ (is_val e1 ∧ ∃ e2', tstep e2 α e2' ∧ e' = App e1 e2')
  ∨ (is_val e1 ∧ is_val e2 ∧ head_step (App e1 e2) α e').
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; simpl; eauto 10.
Qed.

Lemma tstep_pair_inv e1 e2 α e' :
  tstep (Pair e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = Pair e1' e2)
  ∨ (is_val e1 ∧ ∃ e2', tstep e2 α e2' ∧ e' = Pair e1 e2').
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0.
Qed.

Lemma tstep_letu_inv e1 e2 α e' :
  tstep (LetU e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = LetU e1' e2)
  ∨ (e1 = EUnit ∧ α = LBeta ∧ e' = e2).
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; eauto 10.
Qed.

Lemma tstep_letp_inv e1 e2 α e' :
  tstep (LetP e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = LetP e1' e2)
  ∨ (∃ u v, e1 = Pair u v ∧ is_val u ∧ is_val v ∧
     α = LBeta ∧ e' = subst2 u v e2).
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; eauto 10.
Qed.

(** ** Evaluation frames

    One-level evaluation contexts, used to state closure of the
    logical relation under evaluation position generically. *)

Inductive frame :=
  | FAppL (e2 : expr)
  | FAppR (v1 : expr)
  | FPairL (e2 : expr)
  | FPairR (v1 : expr)
  | FLetU (e2 : expr)
  | FLetP (e2 : expr).

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | FAppL e2 => App e e2
  | FAppR v1 => App v1 e
  | FPairL e2 => Pair e e2
  | FPairR v1 => Pair v1 e
  | FLetU e2 => LetU e e2
  | FLetP e2 => LetP e e2
  end.

(** Right-of-value frames require the value side condition. *)
Definition frame_val (f : frame) : Prop :=
  match f with FAppR v1 | FPairR v1 => is_val v1 | _ => True end.

Lemma tstep_fill f e α e' :
  frame_val f → tstep e α e' →
  tstep (fill_frame f e) α (fill_frame f e').
Proof. destruct f; simpl; intros; eauto using tstep. Qed.

Lemma tstep_fill_inv f e α E' :
  frame_val f → ¬ is_val e →
  tstep (fill_frame f e) α E' →
  ∃ e', tstep e α e' ∧ E' = fill_frame f e'.
Proof.
  destruct f; simpl; intros Hf Hv Hst.
  - apply tstep_app_inv in Hst
      as [(e' & ? & ->)|[(Hval & _)|(Hval & _)]]; eauto.
    all: by destruct (Hv Hval).
  - apply tstep_app_inv in Hst
      as [(e' & Hst' & _)|[(_ & e' & ? & ->)|(_ & Hval & _)]]; eauto.
    + exfalso. eauto using val_no_tstep.
    + by destruct (Hv Hval).
  - apply tstep_pair_inv in Hst as [(e' & ? & ->)|(Hval & _)]; eauto.
    by destruct (Hv Hval).
  - apply tstep_pair_inv in Hst as [(e' & Hst' & _)|(_ & e' & ? & ->)]; eauto.
    exfalso. eauto using val_no_tstep.
  - apply tstep_letu_inv in Hst as [(e' & ? & ->)|(-> & _)]; eauto.
    by destruct Hv.
  - apply tstep_letp_inv in Hst
      as [(e' & ? & ->)|(u & v & -> & Hu & Hv' & _)]; eauto.
    exfalso. apply Hv. simpl. by apply andb_True.
Qed.

(** Values carried by communication labels are values. *)
Lemma head_step_label_val e α e' :
  head_step e α e' →
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LFork _ v => is_val v
  | _ => True
  end.
Proof. by destruct 1. Qed.

Lemma tstep_label_val e α e' :
  tstep e α e' →
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LFork _ v => is_val v
  | _ => True
  end.
Proof. induction 1; [by eapply head_step_label_val|done..]. Qed.

Lemma tstep_send_val e c v e' :
  tstep e (LSess (SSend c v)) e' → is_val v.
Proof. intros H. exact (tstep_label_val _ _ _ H). Qed.

(** Receives can be retargeted to any other value: the term LTS offers
    an input transition for every value. *)
Lemma recv_retarget e c w e' w' :
  tstep e (LSess (SRecv c w)) e' → is_val w' →
  ∃ e'', tstep e (LSess (SRecv c w')) e''.
Proof.
  intros H Hw'. remember (LSess (SRecv c w)) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. by apply HeadRecv.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetU.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetP.
Qed.
