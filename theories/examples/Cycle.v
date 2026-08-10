(** * Example 2.9: cycle

    Two threads sharing two restricted channels -- a cyclic topology,
    untypable for it -- that nevertheless runs to termination along
    its one reduction sequence.  The first example of a process the
    relation accepts and the type system rejects. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Support Sync Blocked.

Local Open Scope string_scope.


(** ** Example 2.2 / 3.14: the safe cyclic process

    cycle = ({c,d}, ⟨let ∗ = clos c in clos d, let ∗ = clos c in clos d⟩):
    same thread [tA] twice — the deadlock [blocked] with the second
    thread's channel order agreeing instead of clashing. *)

Definition cycle_proc : proc := ({["c"; "d"]}, {[+ tA +]} ⊎ {[+ tA +]}).

(** The intermediate thread shape after closing c. *)
Notation cycA := (LetU EUnit (App EClos (Chan "d"))).

(** Stage p4 = ({}, ⟨∗, ∗⟩): irreducible and terminated. *)
Lemma cycle_rel4 n : Prel n ∅ TUnit (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros _. exists EUnit, {[+ EUnit +]}. split_and!.
    + done.
    + done.
    + apply Vrel_unit.
    + intros e He. by apply gmultiset_elem_of_singleton in He.
  - intros π p' Hst. exfalso.
    inversion Hst; subst;
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]} ⊎ {[+ _ +]},
        Hs : tstep ?e _ _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          eapply val_no_tstep in Hs; done
      end.
Qed.

(** Stage p3 = ({d}, ⟨clos d, clos d⟩): the only step closes d. *)
Lemma cycle_rel3 n :
  Prel n ∅ TUnit
    ({["d"]}, {[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]})
      with ((∅ ⊎ {[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]})
        : gmultiset expr)
      by multiset_solver.
    eapply PStepClose; [apply TStepHead, HeadClos..|set_solver].
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subject d is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta: no β redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg: no send label *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close: the d-synchronization *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]];
          apply tstep_clos_inv in Hse as [Hle ->];
          apply tstep_clos_inv in Hsf as [Hlf ->]
      end; simplify_eq; simpl; intros _.
      all: replace ({["d"]} ∖ {["d"]} : gset chan) with (∅ : gset chan)
        by set_solver.
      all: replace (∅ ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]})
        with ({[+ EUnit +]} ⊎ {[+ EUnit +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel4.
    + (* internal forwarding: no forwarding redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
Qed.

(** Stage p2 = ({d}, ⟨clos d, let ∗ = ∗ in clos d⟩): only the β step. *)
Lemma cycle_rel2 n :
  Prel n ∅ TUnit ({["d"]}, {[+ App EClos (Chan "d") +]} ⊎ {[+ cycA +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          [apply tstep_clos_inv in Hs as [Hα _]; simplify_eq
          |apply tstep_letu_unit_inv in Hs as [_ ->]]
      end.
      intros _. apply cycle_rel3.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* close: partner thread has no close label *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> ->]|[-> ->]]];
          [apply tstep_letu_unit_inv in Hsf as [Hα _]
          |apply tstep_letu_unit_inv in Hse as [Hα _]]
      end; simplify_eq.
    + (* internal forwarding: no forwarding redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
Qed.

(** Stage p1 = ({d}, ⟨let ∗ = ∗ in clos d, let ∗ = ∗ in clos d⟩). *)
Lemma cycle_rel1 n :
  Prel n ∅ TUnit ({["d"]}, {[+ cycA +]} ⊎ {[+ cycA +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* beta *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          apply tstep_letu_unit_inv in Hs as [_ ->]
      end.
      all: intros _.
      all: replace ({[+ cycA +]} ⊎ {[+ App EClos (Chan "d") +]})
        with ({[+ App EClos (Chan "d") +]} ⊎ {[+ cycA +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel2.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hse as [Hα _]
      end; simplify_eq.
    + (* internal forwarding: no forwarding redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
Qed.

(** Stage p0 = cycle: the only step closes c. *)
Lemma cycle_rel0 n : Prel n ∅ TUnit cycle_proc.
Proof.
  destruct n as [|n]; [apply Prel_0|].
  unfold cycle_proc.
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ tA +]} ⊎ {[+ tA +]})
      with ((∅ ⊎ {[+ tA +]} ⊎ {[+ tA +]}) : gmultiset expr) by multiset_solver.
    eapply PStepClose;
      [apply TStepLetU, TStepHead, HeadClos..|set_solver].
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subject c is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close: the c-synchronization *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]];
          apply tstep_blocked_inv in Hse as [Hle ->];
          apply tstep_blocked_inv in Hsf as [Hlf ->]
      end; simplify_eq; simpl; intros _.
      all: replace ({["c"; "d"]} ∖ {["c"]} : gset chan)
        with ({["d"]} : gset chan) by set_solver.
      all: replace (∅ ⊎ {[+ cycA +]} ⊎ {[+ cycA +]})
        with ({[+ cycA +]} ⊎ {[+ cycA +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel1.
    + (* internal forwarding: no forwarding redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
Qed.

(** Example 3.14: cycle satisfies the semantic judgment directly —
    exhibiting an inhabitant of the process relation without going
    through the fundamental theorem — and is hence deadlock free
    despite being untypable (Example 2.11). *)
Example cycle_sem_ptyped : sem_ptyped ∅ cycle_proc TUnit.
Proof. intro n. apply cycle_rel0. Qed.

Corollary cycle_deadlock_free : deadlock_free cycle_proc.
Proof. eapply adequacy, cycle_sem_ptyped. Qed.

(** The composition of sync (typable, hence semantically typed by the
    fundamental theorem) and cycle (semantically typed directly), via
    P-Independent (Theorem 3.12), is deadlock free. *)
Corollary sync_cycle_deadlock_free :
  deadlock_free ({["c"; "d"]}, {[+ sync_main +]} ⊎ ({[+ tA +]} ⊎ {[+ tA +]})).
Proof.
  eapply adequacy.
  replace ({["c"; "d"]} : gset chan)
    with (∅ ∪ {["c"; "d"]} : gset chan) by set_solver.
  apply (sem_ptyped_independent ∅ ∅ ∅ ∅ {[+ sync_main +]}
           {["c"; "d"]} ({[+ tA +]} ⊎ {[+ tA +]}) TUnit);
    [constructor|apply senv_split_empty_l|set_solver..
    |exact (fundamental_proc _ _ _ sync_typed)
    |exact cycle_sem_ptyped].
Qed.

Print Assumptions cycle_deadlock_free.
Print Assumptions sync_cycle_deadlock_free.
