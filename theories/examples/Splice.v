(** * The degenerate self-forwarding, as a program (§4.5)

    The one example that exercises a self-forwarding — a [link] whose
    two ends have become the same channel.  Scheduler.v never produces
    one: there the splice always joins distinct names.  Here it is
    manufactured by retargeting, which is the only way it arises.

    A broker splices two sessions with the forwarding operator:
    [link ⟨a, b⟩] makes everything arriving on [a] leave on [b] and
    vice versa.  Installing a relay is the natural way to hand a
    session off without copying messages.

    Suppose the install is issued twice — a retry that did not notice
    the first one succeeded, or two brokers on a redundant path both
    splicing the same pair of endpoints:

      ⟨{a,b};  link ⟨a,b⟩  ∥  link ⟨a,b⟩⟩

    This is NOT syntactically typable.  Each relay needs [a : S] and
    [b : dual S], so both channels are used by both threads, while
    P-Connect joins two components over exactly ONE restricted channel;
    no derivation puts two threads on two shared channels.  (Same
    reason as [publish] in Examples.v: the process graph has a cycle,
    and GV's typing only builds trees.)

    It is nevertheless deadlock free, which is a real robustness
    property — **duplicate splices are idempotent**.  Whichever relay
    fires first retires its end and retargets the soup, which rewrites
    the other relay into a self-forwarding on the surviving name; the
    degenerate case of P-Act-Link then releases that name and the
    configuration terminates.

    Under the old head rule, which required the two ends to differ, the
    second relay became the stuck [link ⟨b,b⟩] — a non-unit thread that
    could not step, i.e. a deadlock manufactured by retargeting.  This
    example is the configuration that used to be the counterexample to
    compositionality, read as a program rather than as a wedge. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Terms Fundamental Invariant.

Local Open Scope string_scope.

(** [link ⟨c,d⟩] as a term. *)
Definition fwd (c d : chan) : expr := App ELink (Pair (Chan c) (Chan d)).

Lemma fwd_step c d :
  tstep (fwd c d) (LSess (SLink {[c; d]})) EUnit.
Proof. apply TStepHead, HeadLink. Qed.

Definition ra : chan := "a".
Definition rb : chan := "b".

Definition relay_proc : proc :=
  ({[ra; rb]}, {[+ fwd ra rb +]} ⊎ {[+ fwd ra rb +]}).

(** ** Thread-level inversion

    [link ⟨c,d⟩] is a head redex, so its only transition is the
    forwarding offer. *)
Lemma tstep_fwd_inv c d α e' :
  tstep (fwd c d) α e' → α = LSess (SLink {[c; d]}) ∧ e' = EUnit.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - match goal with Hs : tstep ELink _ _ |- _ =>
      exfalso; eapply val_no_tstep; [exact Hs|done] end.
  - match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      exfalso; eapply val_no_tstep; [exact Hs|done] end.
Qed.

Lemma acting_thread (E0 : gmultiset expr) e u v :
  E0 ⊎ {[+ e +]} = {[+ u +]} ⊎ {[+ v +]} → e = u ∨ e = v.
Proof.
  intros Heq.
  assert (e ∈ ({[+ u +]} ⊎ {[+ v +]} : gmultiset expr)) as Hin
    by multiset_solver.
  apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
    apply gmultiset_elem_of_singleton in Hin; auto.
Qed.

(** In every reachable configuration each thread is a unit or a
    forwarder, so the only label any of them emits is a forwarding. *)
Ltac relay_label :=
  match goal with
  | Heq : ?E0 ⊎ {[+ ?e +]} = _, Hs : tstep ?e _ _ |- _ =>
      apply acting_thread in Heq as [-> | ->];
      [ first [ apply tstep_fwd_inv in Hs as [? ?]
              | exfalso; eapply val_no_tstep; [exact Hs|done] ]
      | first [ apply tstep_fwd_inv in Hs as [? ?]
              | exfalso; eapply val_no_tstep; [exact Hs|done] ] ]
  end.

(** ** The reachable set *)

Definition relayI (p : proc) : Prop :=
  p = relay_proc
  ∨ p = ({[rb]}, {[+ fwd rb rb +]} ⊎ {[+ EUnit +]})
  ∨ p = ({[ra]}, {[+ fwd ra ra +]} ⊎ {[+ EUnit +]})
  ∨ p = (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).

Lemma relayI_echans p : relayI p → echans p.2 ⊆ p.1.
Proof.
  intros Hp; destruct Hp as [-> | [-> | [-> | ->]]]; simpl;
    rewrite echans_disj_union, !echans_singleton;
    unfold fwd; simpl; clear; set_solver.
Qed.

(** The first splice retires [a] and rewrites the sibling relay into a
    self-forwarding on [b]. *)
Lemma relay_step1 :
  proc_step relay_proc PTau ({[rb]}, {[+ fwd rb rb +]} ⊎ {[+ EUnit +]}).
Proof.
  unfold relay_proc.
  assert (({[ra; rb]} : gset chan) ∖ {[ra]} = {[rb]}) as <-
    by (clear; set_solver).
  replace ({[+ fwd ra rb +]} ⊎ {[+ fwd ra rb +]})
    with (({[+ fwd ra rb +]} : gmultiset expr) ⊎ {[+ fwd ra rb +]})
    by multiset_solver.
  assert (echsubst ra rb ({[+ fwd ra rb +]} ⊎ {[+ EUnit +]})
          = {[+ fwd rb rb +]} ⊎ {[+ EUnit +]}) as <-.
  { rewrite echsubst_disj_union, !echsubst_singleton. done. }
  apply PStepLink; [apply fwd_step|clear; set_solver].
Qed.

(** The self-forwarding on the surviving name dissolves, releasing it. *)
Lemma relay_selfstep x :
  proc_step ({[x]}, {[+ fwd x x +]} ⊎ {[+ EUnit +]}) PTau
            (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).
Proof.
  replace ({[+ fwd x x +]} ⊎ {[+ EUnit +]})
    with (({[+ EUnit +]} : gmultiset expr) ⊎ {[+ fwd x x +]})
    by multiset_solver.
  assert (({[x]} : gset chan) ∖ {[x]} = ∅) as <- by (clear; set_solver).
  assert (echsubst x x ({[+ EUnit +]} ⊎ {[+ EUnit +]})
          = {[+ EUnit +]} ⊎ {[+ EUnit +]}) as <-
    by (rewrite echsubst_refl; done).
  apply PStepLink; [apply fwd_step|clear; set_solver].
Qed.

Lemma relayI_irred p :
  relayI p → pirred p → p.1 = ∅ ∧ p.2 ≠ ∅ ∧ (∀ e, e ∈ p.2 → e = EUnit).
Proof.
  intros Hp Hirr; destruct Hp as [-> | [-> | [-> | ->]]].
  - exfalso. eapply (Hirr PTau). apply relay_step1.
  - exfalso. eapply (Hirr PTau). apply relay_selfstep.
  - exfalso. eapply (Hirr PTau). apply relay_selfstep.
  - simpl. split_and!; [done|multiset_solver|].
    intros e He. multiset_solver.
Qed.

(** ** Closure under reduction *)

(** From a doubled relay, either end may be retired: the label is an
    unordered pair, so both orientations of P-Act-Link apply. *)
Lemma relay_split c d E0 :
  E0 ⊎ {[+ fwd ra rb +]} = {[+ fwd ra rb +]} ⊎ {[+ fwd ra rb +]} →
  {[c; d]} = ({[ra; rb]} : gset chan) →
  c ∈ ({[ra; rb]} : gset chan) →
  relayI ({[ra; rb]} ∖ {[c]}, echsubst c d (E0 ⊎ {[+ EUnit +]})).
Proof.
  intros HE Hcd Hc.
  assert (E0 = {[+ fwd ra rb +]}) as -> by multiset_solver.
  assert (c ≠ d) as Hne.
  { intros ->. assert (ra ∈ ({[d; d]} : gset chan)) as Hin
      by (rewrite Hcd; clear; set_solver).
    assert (rb ∈ ({[d; d]} : gset chan)) as Hin2
      by (rewrite Hcd; clear; set_solver).
    clear -Hin Hin2. set_solver. }
  destruct (upair_eq_inv _ _ _ _ Hcd Hne) as [[-> ->]|[-> ->]].
  - right; left.
    assert (({[ra; rb]} : gset chan) ∖ {[ra]} = {[rb]}) as ->
      by (clear; set_solver).
    f_equal. rewrite echsubst_disj_union, !echsubst_singleton. done.
  - right; right; left.
    assert (({[ra; rb]} : gset chan) ∖ {[rb]} = {[ra]}) as ->
      by (clear; set_solver).
    f_equal. rewrite echsubst_disj_union, !echsubst_singleton. done.
Qed.

(** The degenerate relay retires its single name. *)
Lemma relay_self_split x c d E0 :
  E0 ⊎ {[+ fwd x x +]} = {[+ fwd x x +]} ⊎ {[+ EUnit +]} →
  {[c; d]} = ({[x; x]} : gset chan) →
  relayI ({[x]} ∖ {[c]}, echsubst c d (E0 ⊎ {[+ EUnit +]})).
Proof.
  intros HE Hcd.
  assert (E0 = {[+ EUnit +]}) as -> by multiset_solver.
  assert (c = x) as ->.
  { assert (c ∈ ({[x; x]} : gset chan)) as Hin
      by (rewrite <-Hcd; clear; set_solver).
    clear -Hin. set_solver. }
  assert (d = x) as ->.
  { assert (d ∈ ({[x; x]} : gset chan)) as Hin
      by (rewrite <-Hcd; clear; set_solver).
    clear -Hin. set_solver. }
  right; right; right.
  assert (({[x]} : gset chan) ∖ {[x]} = ∅) as -> by (clear; set_solver).
  f_equal. by rewrite echsubst_refl.
Qed.

Lemma relayI_step p p' : relayI p → preduction p p' → relayI p'.
Proof.
  intros Hp Hst. unfold preduction in Hst.
  destruct Hp as [-> | [-> | [-> | ->]]]; inversion Hst; subst;
    try (exfalso; relay_label; simplify_eq; fail).
  - (* the doubled relay splices *)
    match goal with
    | Heq : ?E0 ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
        assert (e = fwd ra rb) as He by multiset_solver;
        rewrite He in Hs, Heq;
        apply tstep_fwd_inv in Hs as [Hα ->]
    end.
    match goal with Hα : LSess (SLink ?cd) = LSess (SLink ?ee) |- _ =>
      assert (cd = ee) as Hcd by congruence end.
    eapply relay_split; [done|exact Hcd|done].
  - (* the surviving self-forwarding dissolves *)
    match goal with
    | Heq : ?E0 ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
        apply acting_thread in Heq as Hsh; destruct Hsh as [-> | ->];
        [ apply tstep_fwd_inv in Hs as [Hα ->]
        | exfalso; eapply val_no_tstep; [exact Hs|done] ]
    end.
    match goal with Hα : LSess (SLink ?cd) = LSess (SLink ?ee) |- _ =>
      assert (cd = ee) as Hcd by congruence end.
    eapply relay_self_split; [multiset_solver|exact Hcd].
  - match goal with
    | Heq : ?E0 ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
        apply acting_thread in Heq as Hsh; destruct Hsh as [-> | ->];
        [ apply tstep_fwd_inv in Hs as [Hα ->]
        | exfalso; eapply val_no_tstep; [exact Hs|done] ]
    end.
    match goal with Hα : LSess (SLink ?cd) = LSess (SLink ?ee) |- _ =>
      assert (cd = ee) as Hcd by congruence end.
    eapply relay_self_split; [multiset_solver|exact Hcd].
Qed.

(** ** Deadlock freedom *)

Lemma relayI_closed : closed_invariant relayI.
Proof.
  intros p Hp. split_and!.
  - by apply relayI_echans.
  - by apply relayI_irred.
  - intros p' Hst. by eapply relayI_step.
Qed.

Theorem relay_deadlock_free : deadlock_free relay_proc.
Proof. eapply closed_deadlock_free; [exact relayI_closed|by left]. Qed.

(** …and, being closed and semantically well typed, it also satisfies
    the process relation at the empty interface. *)
Corollary relay_sem_ptyped : sem_ptyped ∅ relay_proc TUnit.
Proof. eapply sem_ptyped_closed; [exact relayI_closed|by left]. Qed.
