(** * A self-forwarding is visible, and never well typed

    Two facts pinning down the change to T-Act-Link (dropping the
    [c ≠ d] side condition), one semantic and one syntactic.

    1. [selflink_unrelated]: a configuration carrying a self-forwarding
       on a FREE channel is not in the relation.  Previously the redex
       was stuck, so no clause ever examined it and the configuration
       was vacuously related — which is what made the eager renaming
       transport false.  Now it offers the singleton label [{[c]}], and
       the forwarding clause cannot satisfy it: that clause demands two
       DISTINCT ends carrying dual protocols, and a singleton is not a
       two-element set.

    2. [selflink_untypable]: no self-forwarding is well typed, so the
       widened rule is invisible on the statically typed fragment.  The
       paper remarks that the two ends of a forwarding label "are
       different"; this is that remark as a theorem.

    The RESTRICTED case — where the rule fires and releases the name —
    is exercised as a program in Relay.v. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Import Relation Renaming.

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
