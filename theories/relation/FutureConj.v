(** * Readiness is conjunctive in the future (sharp edges 146)

    t runs with future F when F holds the points the thread still acts
    on after t. Readiness asks every offered entry below every point of
    F and reads F nowhere else, so it splits into the empty future and
    the singleton futures ([below_rest_conj], [ready_t_conj]). The link
    disjunct of [ready_t] is resolved by induction on the finite set F,
    with no classical axiom.

    The same split for the term relation, E_F = E_∅ ∩ ⋂_{q ∈ F} E_{q},
    is open. Its inclusion from left to right is [Erel_future]. The other
    inclusion fails to go through because O-New picks its world W′ for
    each future separately, and two fresh extensions of W by the same
    name need not join into a strict world. The splits of O-Spawn and
    O-Send are chosen for each future too. *)

From stdpp Require Import base gmap.
From LRGV Require Import relation.Readiness.

Lemma below_rest_conj W Θ off (F : gset point) :
  below_rest W Θ off F ↔ below_rest W Θ off ∅ ∧ ∀ q, q ∈ F → below_rest W Θ off {[q]}.
Proof.
  split.
  - intros H. split; [eapply below_rest_future; [|exact H]; set_solver|].
    intros q Hq. eapply below_rest_future; [|exact H]. set_solver.
  - intros [H0 H] k e Ho He. split; [exact (proj1 (H0 k e Ho He))|].
    intros y Hy. exact (proj2 (H y Hy k e Ho He) y ltac:(set_solver)).
Qed.

Lemma ready_t_conj W Θ (F : gset point) t :
  ready_t W Θ F t ↔ ready_t W Θ ∅ t ∧ ∀ q, q ∈ F → ready_t W Θ {[q]} t.
Proof.
  split.
  - intros H. split; [eapply ready_t_future; [|exact H]; set_solver|].
    intros q Hq. eapply ready_t_future; [|exact H]. set_solver.
  - intros [H0 H]. induction F as [|q F Hq IH] using set_ind_L; [done|].
    assert (ready_t W Θ F t) as HF by (apply IH; intros; apply H; set_solver).
    intros Hs. destruct (HF Hs) as [Hv [Hl|HbF]]; [by split; [|left]|].
    destruct (H q ltac:(set_solver) Hs) as [_ [Hl|Hbq]]; [by split; [|left]|].
    split; [done|right]. apply below_rest_conj. split.
    + eapply below_rest_future; [|exact HbF]; set_solver.
    + intros y Hy. apply elem_of_union in Hy as [Hy%elem_of_singleton|Hy]; [by subst|].
      eapply below_rest_future; [|exact HbF]; set_solver.
Qed.
