(** * Process LTS of GV♯ (Fig. 3) and deadlock freedom (§2.1)

    A process is a pair (C, E) of a finite set C of (restricted)
    channels and a finite multiset E of closed terms running in
    parallel. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Semantics.

Definition proc : Type := gset chan * gmultiset expr.

(** Process labels π ::= τ | σ *)
Inductive plabel :=
  | PTau
  | PSess (σ : slabel).

(** Channels occurring free in some thread of E. *)
Definition echans (E : gmultiset expr) : gset chan :=
  ⋃ (fchans <$> elements E).

(** ** The labelled transition relation (Fig. 3)

    In P-Act-Fork the new channel c must be globally fresh: not
    restricted yet, and not free in any thread (the paper keeps this
    implicit in the well-formedness of the "new" name). Rules
    P-Act-Msg and P-Act-Close write the paper's C ∪ {c} source as
    membership c ∈ C. *)

Inductive proc_step : proc → plabel → proc → Prop :=
  | PStepSession C E e σ e' :                          (* P-Act-Session *)
      tstep e (LSess σ) e' →
      subj σ ∉ C →
      proc_step (C, E ⊎ {[+ e +]}) (PSess σ)
                (C ∖ sentc σ, E ⊎ {[+ e' +]})
  | PStepBeta C E e e' :                               (* P-Act-Beta *)
      tstep e LBeta e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | PStepFork C E e c v e' :                           (* P-Act-Fork *)
      tstep e (LFork c v) e' →
      c ∉ C → c ∉ echans E → c ∉ fchans e →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∪ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]})
  | PStepMsg C E c v e e' f f' :                       (* P-Act-Msg *)
      tstep e (LSess (SSend c v)) e' →
      tstep f (LSess (SRecv c v)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepClose C E c e e' f f' :                       (* P-Act-Close *)
      tstep e (LSess (SClos c)) e' →
      tstep f (LSess (SClos c)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

(** Process reduction p --> p' is p --τ--> p'. *)
Definition preduction (p p' : proc) : Prop := proc_step p PTau p'.
Notation pred_star := (rtc preduction).

(** Irreducible processes (Def. 3.1). *)
Definition pirred (p : proc) : Prop := ∀ π p', ¬ proc_step p π p'.

(** ** Properties of processes (Defs. 2.4–2.6) *)

(** A terminated process has released all channels; the main thread
    has computed a value and all forked threads have reduced to ∗. *)
Definition terminated (p : proc) : Prop :=
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ (∀ e, e ∈ E → e = EUnit).

Definition safe (p : proc) : Prop :=
  terminated p ∨ ∃ p', preduction p p'.

Definition deadlock_free (p : proc) : Prop :=
  ∀ p', pred_star p p' → safe p'.

(** Inversion for session-labelled process transitions: only
    P-Act-Session can produce them. *)
Lemma proc_step_sess_inv C E σ p' :
  proc_step (C, E) (PSess σ) p' →
  ∃ E0 e e',
    E = E0 ⊎ {[+ e +]} ∧ tstep e (LSess σ) e' ∧ subj σ ∉ C ∧
    p' = (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
Proof. intros H. inversion H; simplify_eq. eauto 10. Qed.

(** ** Internalizing communication (Lemma 2.3)

    Two disjoint processes communicating over an external channel c can
    be put together and c closed over, turning the communication into
    an internal τ step. Note: following P-Act-Msg (Fig. 3), the
    combined channel set is unchanged — the channels sent along c stay
    in scope of the combined process (the draft's Eq. (9) instead
    subtracts sentc(c!v); that spot is marked "XXX (not yet)" in the
    margin, and is not derivable from Fig. 3 as stated). *)

Lemma internalize_comm C1 E1 C1' E1' C2 E2 C2' E2' c v :
  proc_step (C1, E1) (PSess (SSend c v)) (C1', E1') →
  proc_step (C2, E2) (PSess (SRecv c v)) (C2', E2') →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  proc_step (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) PTau
            (C1 ∪ C2 ∪ {[c]}, E1' ⊎ E2').
Proof.
  intros Hs Hr _ _ _.
  apply proc_step_sess_inv in Hs as (F1 & e & e' & -> & Hstep1 & _ & Heq1).
  apply proc_step_sess_inv in Hr as (F2 & f & f' & -> & Hstep2 & _ & Heq2).
  simplify_eq.
  assert (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})
          = (F1 ⊎ F2) ⊎ {[+ e +]} ⊎ {[+ f +]}) as -> by multiset_solver.
  assert (F1 ⊎ {[+ e' +]} ⊎ (F2 ⊎ {[+ f' +]})
          = (F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}) as -> by multiset_solver.
  eapply PStepMsg; [done|done|set_solver].
Qed.
