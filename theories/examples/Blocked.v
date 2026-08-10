(** * Example 2.8: blocked

    The classic two-thread deadlock: each thread waits to close the
    channel the other holds first.  Shown irreducible and unsafe, and
    therefore outside the logical relation -- adequacy read
    contrapositively. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Support.

Local Open Scope string_scope.


Definition tA : expr := LetU (App EClos (Chan "c")) (App EClos (Chan "d")).
Definition tB : expr := LetU (App EClos (Chan "d")) (App EClos (Chan "c")).
Definition blocked : proc := ({["c"; "d"]}, {[+ tA +]} ⊎ {[+ tB +]}).

(** The only transition of let ∗ = clos ch1 in clos ch2 is closing ch1. *)
Lemma tstep_blocked_inv ch1 ch2 α e' :
  tstep (LetU (App EClos (Chan ch1)) (App EClos (Chan ch2))) α e' →
  α = LSess (SClos ch1) ∧ e' = LetU EUnit (App EClos (Chan ch2)).
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - match goal with Hs : tstep (App _ _) _ _ |- _ =>
      apply tstep_clos_inv in Hs as [-> ->]; auto end.
Qed.

Lemma blocked_pirred : pirred blocked.
Proof.
  intros π p' Hstep. inversion Hstep; subst.
  - (* session *)
    match goal with Hs : tstep ?e (LSess _) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LSess _) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq; set_solver.
  - (* beta *)
    match goal with Hs : tstep ?e LBeta _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* fork *)
    match goal with Hs : tstep ?e (LFork _ _) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LFork _ _) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* msg *)
    match goal with Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LSess (SSend _ _)) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* close *)
    match goal with
      Heq : ?E0 ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _ |- _ =>
      assert (e ∈ E0 ⊎ {[+ e +]} ⊎ {[+ f +]}) as HinE by multiset_solver;
      assert (f ∈ E0 ⊎ {[+ e +]} ⊎ {[+ f +]}) as HinF by multiset_solver;
      rewrite Heq in HinE; rewrite Heq in HinF
    end.
    apply gmultiset_elem_of_disj_union in HinE as [HinE|HinE];
      apply gmultiset_elem_of_singleton in HinE;
      apply gmultiset_elem_of_disj_union in HinF as [HinF|HinF];
      apply gmultiset_elem_of_singleton in HinF; subst;
      repeat match goal with
        Hs : tstep _ (LSess (SClos _)) _ |- _ =>
          apply tstep_blocked_inv in Hs as [? ?] end;
      simplify_eq;
      (* the two threads picked the same term: multiset count is off *)
      multiset_solver.
  - (* internal forwarding: no forwarding redex *)
    match goal with Hs : tstep ?e (LSess (SLink _)) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LSess (SLink _)) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
Qed.

Example blocked_not_safe : ¬ safe blocked.
Proof.
  intros [Hterm|[p' Hstep]].
  - destruct Hterm as (v & E & Heq & _).
    unfold blocked in Heq.
    assert ({["c"; "d"]} = (∅ : gset chan)) as Hc by congruence.
    set_solver.
  - exact (blocked_pirred _ _ Hstep).
Qed.

Example blocked_not_deadlock_free : ¬ deadlock_free blocked.
Proof.
  intros Hdf. apply blocked_not_safe, Hdf, rtc_refl.
Qed.

(** ** Negative check: blocked is not in the logical relation

    (at any environment and type, at any positive index): it is
    irreducible but holds restricted channels, so the termination
    clause of the process relation rejects it. *)
Lemma blocked_not_Prel Σ T n : ¬ Prel (S n) Σ T blocked.
Proof.
  intros HP.
  destruct (Prel_S_irred _ _ _ _ HP blocked_pirred) as (v & E & Heq & _).
  unfold blocked in Heq.
  assert ({["c"; "d"]} = (∅ : gset chan)) as Hcd
    by exact (f_equal fst Heq).
  set_solver.
Qed.

Corollary blocked_not_sem_ptyped Σ T : ¬ sem_ptyped Σ blocked T.
Proof. intros H. exact (blocked_not_Prel Σ T 0 (H 1)). Qed.
