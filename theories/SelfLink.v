(** * Self-forwardings are visible, and the poison configurations dissolve

    Two facts that pin down the change to T-Act-Link (dropping the
    [c ≠ d] side condition), stated against the configurations that
    used to be counterexamples (commit 25c38d8).

    1. [selflink_unrelated]: a configuration carrying a self-forwarding
       on a FREE channel is not in the relation. Previously the redex
       was stuck, so no clause ever examined it and the configuration
       was related ([dead_related]) — which is what made the eager
       renaming transport false. Now it offers the singleton label
       [{[c]}], and the forwarding clause cannot satisfy it: that
       clause demands two DISTINCT ends carrying dual protocols, and a
       singleton is not a two-element set.

    2. [poison_terminates]: the configuration that killed INDEPENDENT
       without cross premises (C4) now runs to a terminated state
       instead of wedging. The first forwarding retires [c] and
       substitutes, turning the second into a self-forwarding on the
       restricted [d]; that fires as the internal rule with both ends
       equal, where the substitution is the identity and the name is
       simply released. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Import LogRel Retarget.

Definition c0 : chan := "c".
Definition d0 : chan := "d".

Lemma c0_neq_d0 : c0 ≠ d0.
Proof. done. Qed.

(** ** A free self-forwarding is refuted by the relation *)

Definition selflink (c : chan) : expr := App ELink (Pair (Chan c) (Chan c)).

Lemma selflink_step c :
  tstep (selflink c) (LSess (SLink {[c]})) EUnit.
Proof.
  apply TStepHead.
  assert (({[c; c]} : gset chan) = {[c]}) as <- by (clear; set_solver).
  apply HeadLink.
Qed.

(** The offer is enabled whenever the channel is not restricted, and no
    instance of the forwarding clause can meet it. *)
Lemma selflink_unrelated n c E :
  ¬ Prel (S n) ∅ TUnit (∅, E ⊎ {[+ selflink c +]}).
Proof.
  intros HP.
  assert (proc_step (∅, E ⊎ {[+ selflink c +]})
            (PSess (SLink {[c]}))
            (∅ ∖ sentc (SLink {[c]}), E ⊎ {[+ EUnit +]})) as Hst.
  { apply PStepSession; [apply selflink_step|clear; set_solver]. }
  pose proof (Prel_S_step _ _ _ _ _ _ HP Hst) as Hc. simpl in Hc.
  destruct Hc as (c1 & d1 & Σ1 & sc & sd & Hset & Hne & _).
  (* a singleton cannot be a two-element set *)
  apply Hne.
  assert (c1 ∈ ({[c]} : gset chan)) as H1
    by (rewrite Hset; clear; set_solver).
  assert (d1 ∈ ({[c]} : gset chan)) as H2
    by (rewrite Hset; clear; set_solver).
  apply elem_of_singleton in H1. apply elem_of_singleton in H2.
  congruence.
Qed.

(** ** The C4 poison configuration now terminates *)

Definition fwd (c d : chan) : expr := App ELink (Pair (Chan c) (Chan d)).

Lemma fwd_step c d :
  tstep (fwd c d) (LSess (SLink {[c; d]})) EUnit.
Proof. apply TStepHead, HeadLink. Qed.

(** ⟨{c,d}; link(c,d) ∥ link(c,d)⟩ — each half was related on its own,
    and before the change the composite wedged: the first forwarding
    rewrote the second into the stuck [link(d,d)]. *)
Definition poison : proc :=
  ({[c0; d0]}, {[+ fwd c0 d0 +]} ⊎ {[+ fwd c0 d0 +]}).

Lemma poison_step1 :
  proc_step poison PTau ({[d0]}, {[+ fwd d0 d0 +]} ⊎ {[+ EUnit +]}).
Proof.
  unfold poison.
  assert (({[c0; d0]} : gset chan) ∖ {[c0]} = {[d0]}) as <-
    by (clear; set_solver).
  replace ({[+ fwd c0 d0 +]} ⊎ {[+ fwd c0 d0 +]})
    with (({[+ fwd c0 d0 +]} : gmultiset expr) ⊎ {[+ fwd c0 d0 +]})
    by multiset_solver.
  assert (echsubst c0 d0 ({[+ fwd c0 d0 +]} ⊎ {[+ EUnit +]})
          = {[+ fwd d0 d0 +]} ⊎ {[+ EUnit +]}) as <-.
  { unfold echsubst.
    rewrite gmultiset_map_disj_union, !gmultiset_map_singleton.
    done. }
  apply PStepLink; [apply fwd_step|clear; set_solver].
Qed.

(** The second forwarding is now degenerate on a RESTRICTED name, so
    the internal rule fires with both ends equal: the substitution is
    the identity and the name is released. *)
Lemma poison_step2 :
  proc_step ({[d0]}, {[+ fwd d0 d0 +]} ⊎ {[+ EUnit +]}) PTau
            (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).
Proof.
  replace ({[+ fwd d0 d0 +]} ⊎ {[+ EUnit +]})
    with (({[+ EUnit +]} : gmultiset expr) ⊎ {[+ fwd d0 d0 +]})
    by multiset_solver.
  assert (({[d0]} : gset chan) ∖ {[d0]} = ∅) as <- by (clear; set_solver).
  assert (echsubst d0 d0 ({[+ EUnit +]} ⊎ {[+ EUnit +]})
          = {[+ EUnit +]} ⊎ {[+ EUnit +]}) as <-.
  { unfold echsubst.
    rewrite gmultiset_map_disj_union, !gmultiset_map_singleton. done. }
  apply PStepLink; [apply fwd_step|clear; set_solver].
Qed.

(** …and what it reaches is terminated: no restricted names left, every
    thread a unit. Before the change this configuration was stuck with
    a non-unit thread, which is exactly what made it a counterexample. *)
Lemma poison_terminates :
  ∃ q, rtc preduction poison q ∧ terminated q.
Proof.
  exists (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}). split.
  - eapply rtc_l; [apply poison_step1|].
    eapply rtc_l; [apply poison_step2|]. apply rtc_refl.
  - exists EUnit, {[+ EUnit +]}. split_and!; [done|done|].
    intros e He. by apply gmultiset_elem_of_singleton in He.
Qed.

(** The two orientations of a forwarding between restricted ends are
    interchangeable ([Prel_link_orient], Retarget.v): retiring either
    end of a fully restricted forwarding gives the same configuration
    up to the transposition of the two names. *)

(** ** A self-forwarding is never well typed

    The extended head rule admits [link (c,c)], which the static system
    cannot produce: [link] consumes a LINEAR pair ⟨S, dual S⟩, so the
    two components are typed under disjoint channel environments, and
    naming the same channel twice needs [{[c := s]} ##ₘ {[c := s']}].
    So on the statically typed fragment the widened rule is invisible;
    it exists for the configurations only the logical relation
    accepts. *)

Lemma typed_chan_inv Σ Δ c T : typed Σ Δ (Chan c) T → ∃ s, Σ = {[c := s]}.
Proof.
  intros H. remember (Chan c) as e eqn:He.
  induction H; simplify_eq; eauto.
Qed.

(** The linear pair ⟨c, c⟩ has no typing: its two components would be
    typed under disjoint environments, both equal to {c}. *)
Lemma typed_pair_chan_same Σ Δ c T :
  ¬ typed Σ Δ (Pair (Chan c) (Chan c)) T.
Proof.
  intros H. remember (Pair (Chan c) (Chan c)) as e eqn:He.
  induction H; simplify_eq; eauto.
  match goal with
  | H1 : typed _ _ (Chan _) _, H2 : typed _ _ (Chan _) _,
    Hsp : senv_split _ _ _ |- _ =>
      apply typed_chan_inv in H1 as (s1 & ->);
      apply typed_chan_inv in H2 as (s2 & ->);
      destruct Hsp as [_ Hdisj]
  end.
  apply map_disjoint_dom in Hdisj.
  rewrite !dom_singleton_L in Hdisj. clear -Hdisj. set_solver.
Qed.

Lemma selflink_untypable Σ Δ c T :
  ¬ typed Σ Δ (App ELink (Pair (Chan c) (Chan c))) T.
Proof.
  intros H. remember (App ELink (Pair (Chan c) (Chan c))) as e eqn:He.
  induction H; simplify_eq; eauto.
  match goal with Hp : typed _ _ (Pair _ _) _ |- _ =>
    exact (typed_pair_chan_same _ _ _ _ Hp) end.
Qed.
