(** * Forwarding between an internal and an external channel (§4.4)

    The mixed case of the link operator, as a program: a forwarder
    holds one end of a restricted channel [c] together with an
    EXTERNAL channel [d], and its peer talks on [c] only.  The
    forwarding label ↔{c,d} never reaches the interface — one of its
    subjects is restricted — so the fusion is the τ-step P-Act-Link:
    [c] is retired and the peer is retargeted onto [d] by the
    substitution.  Afterwards the peer serves the external session
    [d] directly.

      ⟨{c} ; clos (send ⟨∗,c⟩) ∥ link ⟨c,d⟩⟩        Σ = d : !∗.Close
        ⟶τ  ⟨∅ ; clos (send ⟨∗,d⟩) ∥ ∗⟩            ([handoff_fuse])

    Both the initial process and the retargeted residual are typed at
    the SAME interface {d : !∗.Close} — the τ-step changes who serves
    [d], not what is offered — and hence both are in the process
    relation ([fundamental_proc]).  This is the reduction-clause
    reading of the link extension: the labelled cases O-Link/Q-Link
    cover only forwardings with both ends external, while the
    internal–external case is governed by the τ-clause of the
    relation, at an unchanged interface. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Import Terms Fundamental Support Sync.

Local Open Scope string_scope.

(** The peer's protocol on the internal channel is Sync.v's
    Sff = !∗.Close; the forwarder holds the dual end ?∗.Close. *)
Definition Sfw : sty := SRcv TUnit SEnd.

(** clos (send ⟨∗, x⟩) — send a unit on x, then close it. *)
Definition sender (x : chan) : expr :=
  App EClos (App ESend (Pair EUnit (Chan x))).

(** link ⟨c, d⟩ — the forwarder holding the internal end c and the
    external channel d. *)
Definition fwd : expr := App ELink (Pair (Chan "c") (Chan "d")).

Definition handoff : proc := ({["c"]}, {[+ sender "c" +]} ⊎ {[+ fwd +]}).
Definition residual : proc := (∅, {[+ sender "d" +]} ⊎ {[+ EUnit +]}).

(** ** Typing *)

Lemma sender_typed x : typed {[x := Sff]} [] (sender x) TUnit.
Proof.
  eapply (typed_app _ ∅ {[x := Sff]} _ [] [] _ _ (TSess SEnd));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_konst; [apply lenv_empty_nil|]. apply KTClos.
  - eapply (typed_app _ ∅ {[x := Sff]} _ [] [] _ _ (TProd TUnit (TSess Sff)));
      [apply senv_split_empty_l|constructor| |].
    + apply typed_konst; [apply lenv_empty_nil|]. apply (KTSend TUnit SEnd).
    + eapply (typed_pair _ ∅ {[x := Sff]} _ [] []);
        [apply senv_split_empty_l|constructor| |].
      * apply typed_unit, lenv_empty_nil.
      * apply typed_chan, lenv_empty_nil.
Qed.

Lemma fwd_typed : typed (<["c" := Sfw]> {["d" := Sff]}) [] fwd TUnit.
Proof.
  eapply (typed_app _ ∅ _ _ [] [] _ _ (TProd (TSess Sfw) (TSess Sff)));
    [apply senv_split_empty_l|constructor| |].
  - apply typed_konst; [apply lenv_empty_nil|].
    (* link at S := ?∗.Close; dual S computes to Sff *)
    apply (KTLink Sfw).
  - eapply (typed_pair _ {["c" := Sfw]} {["d" := Sff]} _ [] []);
      [|constructor
       |apply typed_chan, lenv_empty_nil
       |apply typed_chan, lenv_empty_nil].
    split.
    + by rewrite insert_union_singleton_l.
    + apply map_disjoint_singleton_l, lookup_singleton_ne. done.
Qed.

(** The composite: P-Connect over the (now internal) channel c.  The
    external d belongs to the forwarder's side of the split. *)
Lemma handoff_ptyped : ptyped {["d" := Sff]} handoff TUnit.
Proof.
  unfold handoff.
  replace ({["c"]} : gset chan) with (∅ ∪ ∅ ∪ {["c"]} : gset chan)
    by set_solver.
  eapply (ptyped_connect _ ∅ {["d" := Sff]} "c" Sff
            ∅ {[+ sender "c" +]} ∅ {[+ fwd +]}).
  - apply senv_split_empty_l.
  - rewrite dom_empty_L. set_solver.
  - rewrite dom_singleton_L. apply not_elem_of_singleton. done.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply ptyped_term; [constructor|]. apply sender_typed.
  - (* dual Sff computes to Sfw *)
    apply ptyped_term; [constructor|]. apply fwd_typed.
Qed.

(** …so the whole process is in the process relation, at the
    non-empty interface {d : !∗.Close}. *)
Theorem handoff_sem_ptyped : sem_ptyped {["d" := Sff]} handoff TUnit.
Proof. apply fundamental_proc, handoff_ptyped. Qed.

(** ** The fusion, operationally

    P-Act-Link fires on the restricted end c: no label is emitted, c
    is retired, and the substitution [d/c] retargets the peer. *)
Lemma handoff_fuse : proc_step handoff PTau residual.
Proof.
  unfold handoff, residual.
  replace (∅ : gset chan) with ({["c"]} ∖ {["c"]} : gset chan)
    by set_solver.
  replace ({[+ sender "d" +]} ⊎ {[+ EUnit +]})
    with (echsubst "c" "d" ({[+ sender "c" +]} ⊎ {[+ EUnit +]}));
    [|by rewrite echsubst_disj_union, !echsubst_singleton].
  apply PStepLink; [|set_solver].
  apply TStepHead. apply HeadLink.
Qed.

(** The retargeted residual is typed — and in the relation — at the
    SAME interface: the peer now serves the external session d
    directly. *)
Lemma residual_ptyped : ptyped {["d" := Sff]} residual TUnit.
Proof.
  unfold residual.
  replace (∅ : gset chan) with (∅ ∪ ∅ : gset chan) by set_solver.
  eapply (ptyped_independent _ {["d" := Sff]} ∅
            ∅ {[+ sender "d" +]} ∅ {[+ EUnit +]}).
  - apply senv_split_comm, senv_split_empty_l.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply ptyped_term; [constructor|]. apply sender_typed.
  - apply ptyped_term; [constructor|]. apply typed_unit, lenv_empty_nil.
Qed.

Corollary residual_sem_ptyped : sem_ptyped {["d" := Sff]} residual TUnit.
Proof. apply fundamental_proc, residual_ptyped. Qed.

(** And indeed the retargeted peer OFFERS on d — the send that would
    have been forwarded now crosses the interface directly (as a
    labelled step via P-Act-Session, d being free). *)
Lemma sender_offers x :
  tstep (sender x) (LSess (SSend x EUnit)) (App EClos (Chan x)).
Proof. apply TStepAppR; [done|]. apply TStepHead. by apply HeadSend. Qed.
