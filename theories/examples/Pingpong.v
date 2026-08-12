(** * A typed recursive session: ping-pong over µα.!(∗).α

    The recursion extension end to end: an equi-recursive session
    type (§4.3) used by genuinely recursive □-thunks (fix x.e ≔
    force (!x.e), §4.2), typed with the conversion rule [typed_conv].
    This closes the gap left by Replication.v, where the recursive
    binding was weakened away: [pinger] and [ponger] below re-force
    themselves after every exchange, so the composite process runs
    forever — and is still deadlock free.

    All conversion premises are discharged by [done]: the unfolding
    equations are closed computations of [unfoldS]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Terms Fundamental Support Factory.

(** The client's protocol: send a unit, then start over. Its dual
    computes to µα.?(∗).α — the polarity flip cancels on a variable
    that only occurs in tail position. *)
Definition Sloop : sty := SMu (SSnd TUnit (SVar 0)).

Lemma Sloop_unfold : unfoldS Sloop = SSnd TUnit Sloop.
Proof. done. Qed.

Lemma Sloop_dual : dual Sloop = SMu (SRcv TUnit (SVar 0)).
Proof. done. Qed.

(** fix f. λc. (force f) (send ⟨∗, c⟩) *)
Definition pinger : expr :=
  EBox (Lam (App (App EForce (Var 1)) (App ESend (Pair EUnit (Var 0))))).

(** fix f. λc. let ⟨u, c'⟩ = recv c in let ∗ = u in (force f) c' *)
Definition ponger : expr :=
  EBox (Lam (LetP (App ERecv (Var 0))
                (LetU (Var 1) (App (App EForce (Var 3)) (Var 0))))).

Definition Tping : ty := TLolli (TSess Sloop) TUnit.
Definition Tpong : ty := TLolli (TSess (dual Sloop)) TUnit.

Lemma lenv_only_r40 T : lenv_only [Some T; None; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|[|y]]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_r41 T : lenv_only [None; Some T; None; None] 1 T.
Proof.
  split; [done|]. intros [|[|[|[|y]]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_r43 T : lenv_only [None; None; None; Some T] 3 T.
Proof.
  split; [done|]. intros [|[|[|[|y]]]] T' H; simplify_eq/=; auto.
Qed.

Lemma pinger_typed : typed ∅ [] pinger (TBox Tping).
Proof.
  apply typed_box; [intros o Ho; by apply elem_of_nil in Ho|].
  apply typed_lam.
  eapply (typed_app _ ∅ ∅ _ [None; Some (TBox Tping)]
            [Some (TSess Sloop); None] _ _ (TSess Sloop));
    [apply senv_split_empty_l|repeat constructor| |].
  - apply typed_force, typed_var, lenv_only_21.
  - eapply (typed_app _ ∅ ∅ _ [None; None] [Some (TSess Sloop); None]
              _ _ (TProd TUnit (TSess (SSnd TUnit Sloop))));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTSend TUnit Sloop).
    + eapply (typed_pair _ ∅ ∅ _ [None; None] [Some (TSess Sloop); None]);
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_unit. auto using lenv_empty_nil, lenv_empty_cons.
      * (* the conversion: c : µα.!(∗).α  ⇒  c : !(∗).µα.!(∗).α *)
        apply (typed_conv _ _ _ Sloop); [done|].
        apply typed_var, lenv_only_20.
Qed.

Lemma ponger_typed : typed ∅ [] ponger (TBox Tpong).
Proof.
  apply typed_box; [intros o Ho; by apply elem_of_nil in Ho|].
  apply typed_lam.
  eapply (typed_letp _ ∅ ∅ _ [Some (TSess (dual Sloop)); None]
            [None; Some (TBox Tpong)] _ _ TUnit (TSess (dual Sloop)));
    [apply senv_split_empty_l|repeat constructor| |].
  - (* recv c : ∗ ⊗ (µα.?(∗).α) *)
    eapply (typed_app _ ∅ ∅ _ [None; None]
              [Some (TSess (dual Sloop)); None] _ _
              (TSess (SRcv TUnit (dual Sloop))));
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
      apply (KTRecv TUnit (dual Sloop)).
    + (* the conversion: c : µα.?(∗).α  ⇒  c : ?(∗).µα.?(∗).α *)
      apply (typed_conv _ _ _ (dual Sloop)); [done|].
      apply typed_var, lenv_only_20.
  - eapply (typed_letu _ ∅ ∅ _ [None; Some TUnit; None; None]
              [Some (TSess (dual Sloop)); None; None; Some (TBox Tpong)]);
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_var, lenv_only_r41.
    + eapply (typed_app _ ∅ ∅ _ [None; None; None; Some (TBox Tpong)]
                [Some (TSess (dual Sloop)); None; None; None] _ _
                (TSess (dual Sloop)));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_force, typed_var, lenv_only_r43.
      * apply typed_var, lenv_only_r40.
Qed.

(** The two endpoints, applied to their channel. *)
Definition ping (c : chan) : expr := App (App EForce pinger) (Chan c).
Definition pong (c : chan) : expr := App (App EForce ponger) (Chan c).

Lemma ping_typed c : typed {[c := Sloop]} [] (ping c) TUnit.
Proof.
  eapply (typed_app _ ∅ {[c := Sloop]} _ [] [] _ _ (TSess Sloop));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_force, pinger_typed.
  - apply typed_chan. auto using lenv_empty_nil.
Qed.

Lemma pong_typed c : typed {[c := dual Sloop]} [] (pong c) TUnit.
Proof.
  eapply (typed_app _ ∅ {[c := dual Sloop]} _ [] [] _ _
            (TSess (dual Sloop)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_force, ponger_typed.
  - apply typed_chan. auto using lenv_empty_nil.
Qed.

(** The composite: both ends of c connected, running forever. *)
Lemma pingpong_typed c :
  ptyped ∅ ({[c]}, {[+ ping c +]} ⊎ {[+ pong c +]}) TUnit.
Proof.
  replace ({[c]} : gset chan) with (∅ ∪ ∅ ∪ {[c]} : gset chan)
    by set_solver.
  eapply (ptyped_connect _ ∅ ∅ c Sloop);
    [apply senv_split_empty_l|set_solver..| |].
  - apply ptyped_term; [constructor|]. apply ping_typed.
  - apply ptyped_term; [constructor|]. apply pong_typed.
Qed.

Corollary pingpong_deadlock_free c :
  deadlock_free ({[c]}, {[+ ping c +]} ⊎ {[+ pong c +]}).
Proof. eapply typed_deadlock_free, pingpong_typed. Qed.

Print Assumptions pingpong_deadlock_free.
