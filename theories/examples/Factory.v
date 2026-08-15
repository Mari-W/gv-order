(** * Replication via unlimited types: a session factory

    The □ extension in action, phrased with the replication operators
    of §4.2: [S] := □(∗ ⊸ S) is the type of a replicable session,
    [repl] boxes a worker into a factory for fresh dual sessions, and
    [req] forces the factory and claims one. The paper treats [repl]
    and [req] as macros; here they are ordinary closed terms with the
    paper's types ([repl_op_typed], [req_op_typed]).

    [factory := repl (!ff)] is then a replicable recipe for a fresh
    session. It is bound once and used twice (contraction at the □
    type, [lsplit_unl]); each request re-runs the suspended fork, so
    the two uses obtain two distinct private sessions served by two
    independent workers. A discarded factory ([typed_wk]) closes the
    weakening side. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Terms Fundamental Support Sync.

(** The worker is Examples.v's ff = λc. clos (send ⟨∗,c⟩), offering
    Sff = !∗.Close; forking it returns a ?∗.Close end. *)
Definition Srv : sty := SRcv TUnit SEnd.

(** ** The replication operators (§4.2)

    [S] := □(∗ ⊸ S), and
      repl : □(S ⊸ ∗) ⊸ [dual S]     repl := λx. !(λ_. fork (force x))
      req  : [S] ⊸ S                 req  := λx. (force x) ∗

    Unit is linear here, so the paper's [λ_. …] consumes its argument
    with a let-∗. In [repl]'s thunk body, x sits under two binders —
    the thunk's self-binding and the inner λ — hence [Var 2]. *)

Definition replT (S : sty) : ty := TBox (TLolli TUnit (TSess S)).

Definition repl_op : expr :=
  Lam (EBox (Lam (LetU (Var 0) (App EFork (App EForce (Var 2)))))).

Definition req_op : expr :=
  Lam (App (App EForce (Var 0)) EUnit).

Lemma lenv_only_hd T Δ : lenv_only (Some T :: lenv_nones Δ) 0 T.
Proof.
  split; [done|]. intros [|y] T' H; simpl in H.
  - by simplify_eq.
  - exfalso. apply list_elem_of_lookup_2 in H.
    apply lenv_empty_nones in H. simplify_eq.
Qed.

Lemma lenv_only_r30 T : lenv_only [Some T; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_r31 T : lenv_only [None; Some T; None] 1 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_r32 T : lenv_only [None; None; Some T] 2 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma req_op_typed S Δ :
  lenv_empty Δ →
  typed ∅ Δ req_op (TLolli (replT S) (TSess S)).
Proof.
  intros HΔ. apply typed_lam.
  eapply (typed_app _ ∅ ∅ _ (Some (replT S) :: lenv_nones Δ) (None :: Δ)
            _ _ TUnit);
    [apply senv_split_empty_l|apply lsplit_l, lenv_split_nones_l| |].
  - apply typed_force, typed_var, lenv_only_hd.
  - apply typed_unit. intros o Ho.
    apply elem_of_cons in Ho as [->|Ho]; auto.
Qed.

Lemma repl_op_typed S :
  typed ∅ [] repl_op
    (TLolli (TBox (TLolli (TSess S) TUnit)) (replT (dual S))).
Proof.
  apply typed_lam. apply typed_box.
  { (* the captured x is boxed *)
    intros o Ho. apply elem_of_cons in Ho as [->|Ho];
      [|by apply elem_of_nil in Ho].
    right. eexists. split; [done|]. apply unlimited_box. }
  apply typed_lam.
  eapply (typed_letu _ ∅ ∅ _
            [Some TUnit; None; None]
            [None; Some (replT (dual S)); Some (TBox (TLolli (TSess S) TUnit))]);
    [apply senv_split_empty_l|repeat constructor| |].
  - apply typed_var, lenv_only_r30.
  - (* the thunk never calls itself, so weaken the recursive binding away *)
    eapply typed_wk;
      [|apply lwk_cons, lwk_drop; [done|apply lwk_cons, lwk_nil]].
    eapply (typed_app _ ∅ ∅ _ [None; None; None]
              [None; None; Some (TBox (TLolli (TSess S) TUnit))]
              _ _ (TLolli (TSess S) TUnit));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst;
        [by (repeat apply lenv_empty_cons; apply lenv_empty_nil)|].
      apply (KTFork S).
    + apply typed_force, typed_var, lenv_only_r32.
Qed.

(** ** The factory, built from the operators

    The boxed worker !ff : □(Sff ⊸ ∗) is the argument of [repl];
    since [dual Sff] computes to [Srv], the factory has type [Srv]. *)

Definition factory : expr := App repl_op (EBox ff).

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

(** The boxed worker: a recipe that does not call itself simply
    weakens the self-binding away. *)
Lemma boxff_typed : typed ∅ [] (EBox ff) (TBox (TLolli (TSess Sff) TUnit)).
Proof.
  apply typed_box; [intros o Ho; by apply elem_of_nil in Ho|].
  eapply typed_wk; [|apply lwk_drop; [done|apply lwk_nil]].
  apply ff_typed_none.
Qed.

Lemma factory_typed : typed ∅ [] factory (replT Srv).
Proof.
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TBox (TLolli (TSess Sff) TUnit)));
    [apply senv_split_empty_l|constructor| |].
  - (* dual Sff = Srv by computation *)
    apply (repl_op_typed Sff).
  - apply boxff_typed.
Qed.

(** One use: request a session from the factory and run it. *)
Definition useb : expr :=
  LetP (App ERecv (App req_op (Var 0)))
    (LetU (Var 1) (App EClos (Var 0))).

Definition repl_main : expr :=
  App (Lam (LetU useb useb)) factory.

Lemma useb_typed :
  typed ∅ [Some (replT Srv)] useb TUnit.
Proof.
  eapply (typed_letp _ ∅ ∅ _ [Some (replT Srv)] [None]
            _ _ TUnit (TSess SEnd));
    [apply senv_split_empty_l|repeat constructor| |].
  - (* recv (req f) : ∗ ⊗ Close *)
    eapply (typed_app _ ∅ ∅ _ [None] [Some (replT Srv)]
              _ _ (TSess Srv));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTRecv TUnit SEnd).
    + (* req f : Srv *)
      eapply (typed_app _ ∅ ∅ _ [None] [Some (replT Srv)]
                _ _ (replT Srv));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply req_op_typed. auto using lenv_empty_nil, lenv_empty_cons.
      * apply typed_var, lenv_only_1.
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
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (replT Srv));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_lam.
    eapply (typed_letu _ ∅ ∅ _ [Some (replT Srv)] [Some (replT Srv)]);
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
  eapply (typed_app _ ∅ ∅ _ [] [] _ _ (replT Srv));
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
Definition omega : expr := App EForce (EBox (App EForce (Var 0))).

Lemma omega_loops : tstep omega LBeta omega.
Proof. apply TStepHead, (HeadForce (App EForce (Var 0))). Qed.
