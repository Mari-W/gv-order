(** * Replication via unlimited types: a session factory

    The □ extension in action. [factory] is a banged fork — a
    replicable recipe for a fresh session. It is bound once and used
    twice (contraction at the □ type, [lsplit_bang]); each [Force]
    re-runs the suspended fork, so the two uses obtain two distinct
    private sessions served by two independent workers. A discarded
    factory ([typed_wk]) closes the weakening side. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import LogRel Compositionality Examples.

(** The worker is Examples.v's ff = λc. clos (send ⟨∗,c⟩), offering
    Sff = !∗.Close; forking it returns a ?∗.Close end. *)
Definition Srv : sty := SRcv TUnit SEnd.

Definition factory : expr := EBang (App EFork ff).

(** One use: force the factory and run the obtained session. *)
Definition useb : expr :=
  LetP (App ERecv (Force (Var 0)))
    (LetU (Var 1) (App EClos (Var 0))).

Definition repl_main : expr :=
  App (Lam (LetU useb useb)) factory.

Lemma lenv_only_r30 T : lenv_only [Some T; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_r31 T : lenv_only [None; Some T; None] 1 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma ff_typed : typed ∅ [] ff (TLolli (TSess Sff) TUnit).
Proof.
  apply typed_lam.
  eapply (typed_app _ ∅ ∅ _ [None] [Some (TSess Sff)] _ _ (TSess SEnd));
    [apply senv_split_empty_l|repeat constructor| |].
  - apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
    apply KTClos.
  - eapply (typed_app _ ∅ ∅ _ [None] [Some (TSess Sff)]
              _ _ (TProd TUnit (TSess Sff)));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTSend TUnit SEnd).
    + eapply (typed_pair _ ∅ ∅ _ [None] [Some (TSess Sff)]);
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_unit. auto using lenv_empty_nil, lenv_empty_cons.
      * apply typed_var, lenv_only_1.
Qed.

Lemma factory_typed : typed ∅ [] factory (TBang (TSess Srv)).
Proof.
  apply typed_bang; [intros o Ho; by apply elem_of_nil in Ho|].
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TLolli (TSess Sff) TUnit));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_konst; [apply lenv_empty_nil|]. apply (KTFork Sff).
  - apply ff_typed.
Qed.

Lemma useb_typed :
  typed ∅ [Some (TBang (TSess Srv))] useb TUnit.
Proof.
  eapply (typed_letp _ ∅ ∅ _ [Some (TBang (TSess Srv))] [None]
            _ _ TUnit (TSess SEnd));
    [apply senv_split_empty_l|repeat constructor| |].
  - (* recv (force s) : ∗ ⊗ Close *)
    eapply (typed_app _ ∅ ∅ _ [None] [Some (TBang (TSess Srv))]
              _ _ (TSess Srv));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTRecv TUnit SEnd).
    + apply typed_force, typed_var, lenv_only_1.
  - (* let ∗ = m in clos c' *)
    eapply (typed_letu _ ∅ ∅ _ [None; Some TUnit; None]
              [Some (TSess SEnd); None; None]);
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_var, lenv_only_r31.
    + eapply (typed_app _ ∅ ∅ _ [None; None; None]
                [Some (TSess SEnd); None; None] _ _ (TSess SEnd));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_konst;
          [by (repeat apply lenv_empty_cons; apply lenv_empty_nil)|].
        apply KTClos.
      * apply typed_var, lenv_only_r30.
Qed.

(** The factory is contracted: both uses consume the same □ entry. *)
Lemma repl_typed : ptyped ∅ (∅, {[+ repl_main +]}) TUnit.
Proof.
  apply ptyped_term; [constructor|].
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TBang (TSess Srv)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_lam.
    eapply (typed_letu _ ∅ ∅ _ [Some (TBang (TSess Srv))]
              [Some (TBang (TSess Srv))]);
      [apply senv_split_empty_l|apply lsplit_bang, lsplit_nil| |];
      apply useb_typed.
  - apply factory_typed.
Qed.

Corollary repl_deadlock_free : deadlock_free (∅, {[+ repl_main +]}).
Proof. eapply typed_deadlock_free, repl_typed. Qed.

(** Weakening: a □ resource may also be discarded outright. *)
Lemma discard_typed :
  ptyped ∅ (∅, {[+ App (Lam EUnit) factory +]}) TUnit.
Proof.
  apply ptyped_term; [constructor|].
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TBang (TSess Srv)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_lam.
    eapply typed_wk.
    + apply (typed_unit [None]).
      auto using lenv_empty_nil, lenv_empty_cons.
    + apply lwk_drop, lwk_nil.
  - apply factory_typed.
Qed.

Corollary discard_deadlock_free :
  deadlock_free (∅, {[+ App (Lam EUnit) factory +]}).
Proof. eapply typed_deadlock_free, discard_typed. Qed.
