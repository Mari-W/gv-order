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

(** ** Head steps *)

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
      is_val v → closed v →
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
