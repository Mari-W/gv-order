(** * Replication via unlimited types: a session factory

    The □ extension in action. [factory] is a boxed fork — a
    replicable recipe for a fresh session. It is bound once and used
    twice (contraction at the □ type, [lsplit_unl]); each [Force]
    re-runs the suspended fork, so the two uses obtain two distinct
    private sessions served by two independent workers. A discarded
    factory ([typed_wk]) closes the weakening side.

    Since [EBox] binds its own occurrence (index 0 of the body is the
    thunk itself), a recipe that does not call itself simply weakens
    that binding away — [factory_typed] below. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Terms Fundamental Support Sync.

(** The worker is Examples.v's ff = λc. clos (send ⟨∗,c⟩), offering
    Sff = !∗.Close; forking it returns a ?∗.Close end. *)
Definition Srv : sty := SRcv TUnit SEnd.

Definition factory : expr := EBox (App EFork ff).

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

(** [ff] under one (unused) extra binding — the slot the recursive
    occurrence of a box occupies. *)
Lemma ff_typed_none : typed ∅ [None] ff (TLolli (TSess Sff) TUnit).
Proof.
  apply typed_lam.
  eapply (typed_app _ ∅ ∅ _ [None; None] [Some (TSess Sff); None]
            _ _ (TSess SEnd));
    [apply senv_split_empty_l|repeat constructor| |].
  - apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
    apply KTClos.
  - eapply (typed_app _ ∅ ∅ _ [None; None] [Some (TSess Sff); None]
              _ _ (TProd TUnit (TSess Sff)));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTSend TUnit SEnd).
    + eapply (typed_pair _ ∅ ∅ _ [None; None] [Some (TSess Sff); None]);
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_unit. auto using lenv_empty_nil, lenv_empty_cons.
      * apply typed_var, lenv_only_20.
Qed.

Lemma factory_typed : typed ∅ [] factory (TBox (TSess Srv)).
Proof.
  apply typed_box; [intros o Ho; by apply elem_of_nil in Ho|].
  (* the recipe never calls itself, so weaken the recursive binding away *)
  eapply typed_wk; [|apply lwk_drop; [done|apply lwk_nil]].
  eapply (typed_app _ ∅ ∅ _ [None] [None] _ _ (TLolli (TSess Sff) TUnit));
    [apply senv_split_empty_l|repeat constructor| |].
  - apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
    apply (KTFork Sff).
  - apply ff_typed_none.
Qed.

Lemma useb_typed :
  typed ∅ [Some (TBox (TSess Srv))] useb TUnit.
Proof.
  eapply (typed_letp _ ∅ ∅ _ [Some (TBox (TSess Srv))] [None]
            _ _ TUnit (TSess SEnd));
    [apply senv_split_empty_l|repeat constructor| |].
  - (* recv (force s) : ∗ ⊗ Close *)
    eapply (typed_app _ ∅ ∅ _ [None] [Some (TBox (TSess Srv))]
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
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TBox (TSess Srv)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_lam.
    eapply (typed_letu _ ∅ ∅ _ [Some (TBox (TSess Srv))]
              [Some (TBox (TSess Srv))]);
      [apply senv_split_empty_l|apply lsplit_unl; [done|apply lsplit_nil]| |];
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
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TBox (TSess Srv)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_lam.
    eapply typed_wk.
    + apply (typed_unit [None]).
      auto using lenv_empty_nil, lenv_empty_cons.
    + apply lwk_drop; [done|apply lwk_nil].
  - apply factory_typed.
Qed.

Corollary discard_deadlock_free :
  deadlock_free (∅, {[+ App (Lam EUnit) factory +]}).
Proof. eapply typed_deadlock_free, discard_typed. Qed.

(** ** The thunk really is recursive

    [!e] binds its own occurrence, so forcing unrolls one step rather
    than merely resuming a suspension: the canonical diverging term
    steps to itself. This is what makes [fix x.e ≔ force (!e)] work,
    and it is why the □ fragment is no longer normalizing — harmless
    here, since deadlock freedom only ever asks whether a process
    *can* step. *)
Definition omega : expr := Force (EBox (Force (Var 0))).

Lemma omega_loops : tstep omega LBeta omega.
Proof. apply TStepHead, (HeadForce (Force (Var 0))). Qed.
