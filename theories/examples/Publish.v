(** * Delegation: publishing a channel over another

    Two threads sharing two restricted channels, one of which is sent
    away.  The proof commits the delegated channel to a protocol on
    the fly, with no syntactic annotation, and exhibits the receiving
    thread as its owner -- the first example to exercise the send case
    of the process relation with a non-empty owner family. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Support.

Local Open Scope string_scope.


(** ** publish: delegation of a private channel

    Two threads share the private channels c and d cyclically (the
    untypable topology of [cycle_proc]), but after the synchronization
    on c the first thread sends its end of d to the environment over
    the external channel e and closes e; the second thread then serves
    d externally.

      t1 := let ∗ = clos c in let e' = send ⟨d, e⟩ in clos e'
      t2 := let ∗ = clos c in let ⟨m,d'⟩ = recv d in let ∗ = m in clos d'

    The process belongs to the logical relation at
    e : !(Sess (!∗.Close)).Close: at the moment of the send, the proof
    commits d — on the fly, with no syntactic annotation — to the
    protocol ?∗.Close, sending the extruded end at the dual type and
    exhibiting t2 as the singleton owner family for d (the σe of
    Fig. 5, case 3).  This is the first example exercising the send
    case with σe ≠ ∅. *)

Definition pubK1 : expr :=
  App (Lam (App EClos (Var 0)))
      (App ESend (Pair (Chan "d") (Chan "e"))).
Definition pubKB : expr := LetU (Var 1) (App EClos (Var 0)).

Definition pubT1 : expr := LetU (App EClos (Chan "c")) pubK1.
Definition pubT2 : expr :=
  LetU (App EClos (Chan "c")) (LetP (App ERecv (Chan "d")) pubKB).

Definition publish_proc : proc :=
  ({["c"; "d"]}, {[+ pubT1 +]} ⊎ {[+ pubT2 +]}).

(** The environment interface of publish: e delivers one delegated
    channel, typed with the dual of the committed protocol, and is
    then closed. *)
Definition Spub : sty := SSnd (TSess (SSnd TUnit SEnd)) SEnd.

(** Intermediate stages of the two threads. *)
Definition pubA1 : expr := LetU EUnit pubK1.
Definition pubA3 : expr := App (Lam (App EClos (Var 0))) (Chan "e").
Definition pubA4 : expr := App EClos (Chan "e").
Definition pubB1 : expr := LetU EUnit (LetP (App ERecv (Chan "d")) pubKB).
Definition pubB2 : expr := LetP (App ERecv (Chan "d")) pubKB.
Definition pubB3 : expr := LetP (Pair EUnit (Chan "d")) pubKB.
Definition pubB4 : expr := LetU EUnit (App EClos (Chan "d")).
Definition pubB5 : expr := App EClos (Chan "d").

(** The protocol committed to d, seen from its residual (receiving)
    end, still owned by the second thread after the delegation. *)
Definition Spriv : sty := SRcv TUnit SEnd.

(** The reachability invariant for publish: every configuration
    reachable from the initial one, each paired with its environment
    interface.  After the delegation of d over e the process splits
    into the continuation piece (owner of e, the A-thread) and the
    owner piece for d (the B-thread), each tracked separately. *)
Inductive pubI : senv → ty → proc → Prop :=
  | PI00 : pubI {["e" := Spub]} TUnit
             ({["c"; "d"]}, {[+ pubT1 +]} ⊎ {[+ pubT2 +]})
  | PI11 : pubI {["e" := Spub]} TUnit
             ({["d"]}, {[+ pubA1 +]} ⊎ {[+ pubB1 +]})
  | PI12 : pubI {["e" := Spub]} TUnit
             ({["d"]}, {[+ pubA1 +]} ⊎ {[+ pubB2 +]})
  | PI21 : pubI {["e" := Spub]} TUnit
             ({["d"]}, {[+ pubK1 +]} ⊎ {[+ pubB1 +]})
  | PI22 : pubI {["e" := Spub]} TUnit
             ({["d"]}, {[+ pubK1 +]} ⊎ {[+ pubB2 +]})
  | PIA3 : pubI {["e" := SEnd]} TUnit (∅, {[+ pubA3 +]})
  | PIA4 : pubI {["e" := SEnd]} TUnit (∅, {[+ pubA4 +]})
  | PIB1 : pubI {["d" := Spriv]} TUnit (∅, {[+ pubB1 +]})
  | PIB2 : pubI {["d" := Spriv]} TUnit (∅, {[+ pubB2 +]})
  | PIB3 : pubI {["d" := SEnd]} TUnit (∅, {[+ pubB3 +]})
  | PIB4 : pubI {["d" := SEnd]} TUnit (∅, {[+ pubB4 +]})
  | PIB5 : pubI {["d" := SEnd]} TUnit (∅, {[+ pubB5 +]})
  | PIunit : pubI ∅ TUnit (∅, {[+ EUnit +]}).

(** The send obligation (case 3 of [inv_case]): the first thread sends
    its end of d over e.  This is where d is committed — on the fly,
    with no syntactic annotation — to the protocol ?∗.Close: the value
    Chan d is typed at the dual !∗.Close against σe = {d ↦ Spriv}, and
    the partner thread B (at either of its two stages) is exhibited as
    the singleton owner family for d. *)
Lemma pubI_send_case B :
  pubI {["d" := Spriv]} TUnit (∅, {[+ B +]}) →
  inv_case pubI {["e" := Spub]} TUnit
    ({["d"]}, {[+ pubK1 +]} ⊎ {[+ B +]})
    (PSess (SSend "e" (Chan "d")))
    ({["d"]} ∖ sentc (SSend "e" (Chan "d")), {[+ B +]} ⊎ {[+ pubA3 +]}).
Proof.
  intros HB.
  exists ∅, ∅, (TSess (SSnd TUnit SEnd)), SEnd, {["d" := Spriv]}, ∅,
    ∅, {[+ pubA3 +]}, ∅, {[+ B +]}, TUnit, TUnit.
  split_and!.
  - by rewrite !(left_id ∅ (∪)).
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - set_solver.
  - set_solver.
  - set_solver.
  - simpl. set_solver.
  - set_solver.
  - set_solver.
  - simpl. set_solver.
  - set_solver.
  - simpl. multiset_solver.
  - intros n. rewrite map_fmap_singleton.
    rewrite (left_id ∅ (∪)). apply Vrel_chan.
  - apply PIA3.
  - apply extrusion_split_single; [set_solver|set_solver|exact HB].
  - left. done.
Qed.

Lemma pubI_invariant : proc_invariant pubI.
Proof.
  intros Σ T p HI. destruct HI; split.
  (* PI00: irreducibility refuted by the c-synchronization *)
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubT1 +]} ⊎ {[+ pubT2 +]})
      with ((∅ ⊎ {[+ pubT1 +]} ⊎ {[+ pubT2 +]}) : gmultiset expr)
      by multiset_solver.
    eapply PStepClose;
      [apply TStepLetU, TStepHead, HeadClos..|set_solver].
  (* PI00: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subject c is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_clos_inv in Hs as [Hα _]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close: the c-synchronization *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]];
          apply tstep_letu_clos_inv in Hse as [Hle ->];
          apply tstep_letu_clos_inv in Hsf as [Hlf ->]
      end; simplify_eq; simpl; intros _;
        replace ({["c"; "d"]} ∖ {["c"]} : gset chan)
          with ({["d"]} : gset chan) by set_solver.
      * replace (∅ ⊎ {[+ LetU EUnit pubK1 +]}
           ⊎ {[+ LetU EUnit (LetP (App ERecv (Chan "d")) pubKB) +]})
          with ({[+ pubA1 +]} ⊎ {[+ pubB1 +]} : gmultiset expr)
          by (unfold pubA1, pubB1; multiset_solver).
        apply PI11.
      * replace (∅ ⊎ {[+ LetU EUnit (LetP (App ERecv (Chan "d")) pubKB) +]}
           ⊎ {[+ LetU EUnit pubK1 +]})
          with ({[+ pubA1 +]} ⊎ {[+ pubB1 +]} : gmultiset expr)
          by (unfold pubA1, pubB1; multiset_solver).
        apply PI11.
  (* PI11: irreducibility refuted by β on pubB1 *)
    + (* internal forwarding: no forwarding redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_clos_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  (* PI11: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* beta on either thread *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          apply tstep_letu_unit_inv in Hs as [_ ->]
      end; intros _.
      * replace ({[+ pubB1 +]} ⊎ {[+ pubK1 +]})
          with ({[+ pubK1 +]} ⊎ {[+ pubB1 +]} : gmultiset expr)
          by multiset_solver.
        apply PI21.
      * apply PI12.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hse as [Hα _]
      end; simplify_eq.
  (* PI12: irreducibility refuted by β on pubA1 *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubA1 +]} ⊎ {[+ pubB2 +]})
      with ({[+ pubB2 +]} ⊎ {[+ pubA1 +]} : gmultiset expr)
      by multiset_solver.
    eapply PStepBeta. apply TStepHead, HeadLetU.
  (* PI12: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: only the recv on d, whose subject is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_letu_unit_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta on pubA1 *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          [apply tstep_letu_unit_inv in Hs as [_ ->]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _);
           simplify_eq]
      end.
      intros _.
      replace ({[+ pubB2 +]} ⊎ {[+ pubK1 +]})
        with ({[+ pubK1 +]} ⊎ {[+ pubB2 +]} : gmultiset expr)
        by multiset_solver.
      apply PI22.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_letu_unit_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply tstep_letu_unit_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply tstep_letu_unit_inv in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (v0 & _ & Hα & _)]
      end; simplify_eq.
  (* PI21: irreducibility refuted by β on pubB1 *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_letu_unit_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  (* PI21: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: the send on e fires *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs
             as [Hα ->]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
      apply pubI_send_case, PIB1.
    + (* beta on pubB1 *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> ->]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs
             as [Hα _]; simplify_eq
          |apply tstep_letu_unit_inv in Hs as [_ ->]]
      end.
      intros _. apply PI22.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* msg: no thread receives *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _,
        Hr : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> ->]|[-> ->]]];
          [apply tstep_letu_unit_inv in Hr as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hse as [Hα _]
          |apply tstep_letu_unit_inv in Hse as [Hα _]]
      end; simplify_eq.
  (* PI22: irreducibility refuted by the send on e *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SSend "e" (Chan "d")))).
    replace ({[+ pubK1 +]} ⊎ {[+ pubB2 +]})
      with ({[+ pubB2 +]} ⊎ {[+ pubK1 +]} : gmultiset expr)
      by multiset_solver.
    eapply PStepSession.
    + apply TStepAppR; [done|]. apply TStepHead. by apply HeadSend.
    + set_solver.
  (* PI22: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: send fires, recv blocked *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs
             as [Hα ->]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
      * apply pubI_send_case, PIB2.
      * exfalso. simpl in *. set_solver.
    + (* beta: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
    + (* msg: the send is on e, the receive on d *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _,
        Hr : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> ->]|[-> ->]]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _];
           apply tstep_letp_recv_inv in Hr as (v0 & _ & Hα' & _)
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (v0 & _ & Hα & _)]
      end; simplify_eq.
  (* PIA3: irreducibility refuted by β *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply (tstep_lam_send_inv _ (Chan "d") _ _ _ I) in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubA3 +]})
      with ((∅ ⊎ {[+ pubA3 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepBeta. apply TStepHead. by apply HeadApp.
  (* PIA3: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_lam_chan_inv in Hs as [Hα _]
      end; simplify_eq.
    + match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_lam_chan_inv in Hs as [_ ->]
      end.
      intros _.
      replace (subst1 (Chan "e") (App EClos (Var 0))) with pubA4 by done.
      replace (∅ ⊎ {[+ pubA4 +]})
        with ({[+ pubA4 +]} : gmultiset expr) by multiset_solver.
      apply PIA4.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_lam_chan_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIA4: irreducibility refuted by the close on e *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_lam_chan_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SClos "e"))).
    replace ({[+ pubA4 +]})
      with ((∅ ⊎ {[+ pubA4 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepSession; [apply TStepHead, HeadClos|set_solver].
  (* PIA4: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* the close on e fires *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα ->]
      end; simplify_eq.
      exists ∅. split_and!.
      * done.
      * set_solver.
      * replace (∅ ∖ sentc (SClos "e")) with (∅ : gset chan) by set_solver.
        replace (∅ ⊎ {[+ EUnit +]})
          with ({[+ EUnit +]} : gmultiset expr) by multiset_solver.
        apply PIunit.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIB1: irreducibility refuted by β *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubB1 +]})
      with ((∅ ⊎ {[+ pubB1 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepBeta. apply TStepHead, HeadLetU.
  (* PIB1: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [_ ->]
      end.
      intros _.
      replace (∅ ⊎ {[+ LetP (App ERecv (Chan "d")) pubKB +]})
        with ({[+ pubB2 +]} : gmultiset expr)
        by (unfold pubB2; multiset_solver).
      apply PIB2.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIB2: irreducibility refuted by the recv on d *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SRecv "d" EUnit))).
    replace ({[+ pubB2 +]})
      with ((∅ ⊎ {[+ pubB2 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepSession; [|set_solver].
    apply TStepLetP, TStepHead. by apply HeadRecv.
  (* PIB2: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* the recv on d fires *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letp_recv_inv in Hs as (v0 & Hv & Hα & ->)
      end; simplify_eq.
      exists ∅, TUnit, SEnd. split_and!.
      * done.
      * set_solver.
      * intros j Σ2 _ _ _ HV.
        apply Vrel_unit_iff in HV as [-> ->].
        rewrite (left_id ∅ (∪)).
        replace (∅ ∖ sentc (SRecv "d" EUnit)) with (∅ : gset chan)
          by set_solver.
        replace (∅ ⊎ {[+ LetP (Pair EUnit (Chan "d")) pubKB +]})
          with ({[+ pubB3 +]} : gmultiset expr)
          by (unfold pubB3; multiset_solver).
        apply PIB3.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIB3: irreducibility refuted by β *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letp_recv_inv in Hs as (v0 & _ & Hα & _)
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubB3 +]})
      with ((∅ ⊎ {[+ pubB3 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepBeta. apply TStepHead. by apply HeadLetP.
  (* PIB3: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply (tstep_letp_pair_inv EUnit (Chan "d") _ _ _ I I) in Hs
            as [Hα _]
      end; simplify_eq.
    + match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply (tstep_letp_pair_inv EUnit (Chan "d") _ _ _ I I) in Hs
            as [_ ->]
      end.
      intros _.
      replace (subst2 EUnit (Chan "d") pubKB) with pubB4 by done.
      replace (∅ ⊎ {[+ pubB4 +]})
        with ({[+ pubB4 +]} : gmultiset expr) by multiset_solver.
      apply PIB4.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply (tstep_letp_pair_inv EUnit (Chan "d") _ _ _ I I) in Hs
            as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIB4: irreducibility refuted by β *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply (tstep_letp_pair_inv EUnit (Chan "d") _ _ _ I I) in Hs
            as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ pubB4 +]})
      with ((∅ ⊎ {[+ pubB4 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepBeta. apply TStepHead, HeadLetU.
  (* PIB4: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [_ ->]
      end.
      intros _.
      replace (∅ ⊎ {[+ App EClos (Chan "d") +]})
        with ({[+ pubB5 +]} : gmultiset expr)
        by (unfold pubB5; multiset_solver).
      apply PIB5.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIB5: irreducibility refuted by the close on d *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SClos "d"))).
    replace ({[+ pubB5 +]})
      with ((∅ ⊎ {[+ pubB5 +]}) : gmultiset expr) by multiset_solver.
    eapply PStepSession; [apply TStepHead, HeadClos|set_solver].
  (* PIB5: steps *)
  - intros π p' Hst.
    inversion Hst; subst.
    + (* the close on d fires *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα ->]
      end; simplify_eq.
      exists ∅. split_and!.
      * done.
      * set_solver.
      * replace (∅ ∖ sentc (SClos "d")) with (∅ : gset chan) by set_solver.
        replace (∅ ⊎ {[+ EUnit +]})
          with ({[+ EUnit +]} : gmultiset expr) by multiset_solver.
        apply PIunit.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + exfalso. by eapply gmultiset_two_singleton_inv.
    + exfalso. by eapply gmultiset_two_singleton_inv.
  (* PIunit: terminated *)
    + (* internal forwarding: no forwarding redex *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]},
        Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [-> ->];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
  - intros _.
    exists EUnit, ∅. split_and!.
    + f_equal. multiset_solver.
    + done.
    + intros n. apply Vrel_unit.
    + intros e He. exfalso. multiset_solver.
  (* PIunit: no steps *)
  - intros π p' Hst. exfalso.
    inversion Hst; subst;
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]}, Hs : tstep ?e _ _ |- _ =>
          apply gmultiset_singleton_inv in Heq as [_ ->];
          eapply val_no_tstep in Hs; done
      end.
Qed.

(** publish is untypable (two threads sharing two restricted channels
    admit no P-Connect tree) yet semantically well-typed: [pubI] is a
    proc invariant, so the invariant rule [Prel_by_invariant] applies;
    the on-the-fly commitment of d happens in [pubI_send_case]. *)
Example publish_sem_ptyped : sem_ptyped {["e" := Spub]} publish_proc TUnit.
Proof.
  intro n. eapply Prel_by_invariant; [exact pubI_invariant|apply PI00].
Qed.

Print Assumptions publish_sem_ptyped.
