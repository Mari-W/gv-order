(** * Runs, weak fairness and lock freedom (lock-freedom plan §0)

    A run is a sequence of configurations with the label of every
    step. A maximal run is infinite, or finite and ending in a stuck
    configuration. A finite maximal run is represented by repeating its
    stuck end with the empty label forever, so every run is a function
    on ℕ.

    Weak fairness is per thread: from every position on, every thread
    eventually takes part in a step or is disabled. Classically this is
    the usual form, that no thread is enabled at every position from
    some point on without taking part in a step from that point on. The
    form here is the constructive one, and it is the one the criterion
    uses.

    A thread is pending when its redex is a session action, a link
    included. A run is lock free when every pending thread later takes
    part in a step. A process is lock free when every weakly fair
    maximal run from a lifting of it is lock free. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Instr.

Definition stuck (q : config) : Prop := ∀ L q', ¬ istep q L q'.

Definition run_step (r : nat → config) (l : nat → gset nat) (i : nat) : Prop :=
  istep (r i) (l i) (r (S i)) ∨ (stuck (r i) ∧ r (S i) = r i ∧ l i = ∅).

Definition maximal (r : nat → config) (l : nat → gset nat) : Prop := ∀ i, run_step r l i.

Definition wfair (r : nat → config) (l : nat → gset nat) : Prop :=
  ∀ t i, ∃ j, i ≤ j ∧ (t ∈ l j ∨ ¬ enabled (r j) t).

Definition lf_run (r : nat → config) (l : nat → gset nat) : Prop :=
  ∀ i t, pend (r i) t → ∃ j, i ≤ j ∧ t ∈ l j.

Definition lock_free (p : proc) : Prop :=
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → lf_run r l.

(** Padovani's lock freedom (padovani2014deadlock, Definition II.1,
    p4): from every reachable state with a pending action, some
    continuation performs it. It needs no fairness. A pending action is
    named by its thread rather than by its channel, because a link may
    rename the channel meanwhile. *)
Definition lock_free_reach (p : proc) : Prop :=
  ∀ q t, pred_star p (erase q) → pend q t →
    ∃ q1 L q2, isteps q q1 ∧ istep q1 L q2 ∧ t ∈ L.

(** ** Dependencies

    A pending thread t waits for s when s is another thread that
    mentions a channel of t's redex. In a well-typed configuration s
    holds the partner end. [local_progress] says that the chain of
    waits from every pending thread reaches an enabled thread. *)

Definition waits (q : config) (t s : nat) : Prop :=
  s ≠ t ∧ ∃ e a S c es, q.2 !! t = Some e ∧ act e = Some a ∧ asubjs a = Some S ∧
    c ∈ S ∧ q.2 !! s = Some es ∧ c ∈ fchans es.

Definition local_progress (q : config) : Prop :=
  ∀ t, pend q t → ∃ s, rtc (waits q) t s ∧ enabled q s.

Lemma waits_pend q t s : waits q t s → pend q t.
Proof.
  intros (_ & e & a & S & c & es & He & Ha & HS & _). exists e, a.
  split_and!; [done|done|]. unfold is_sess. by rewrite HS.
Qed.

(** ** Runs from a process reach reachable states *)

Section runs.
  Context (r : nat → config) (l : nat → gset nat) (Hmax : maximal r l).

  Lemma run_reach i : pred_star (erase (r 0)) (erase (r i)).
  Proof.
    induction i as [|i IH]; [done|]. etrans; [exact IH|].
    destruct (Hmax i) as [Hs|(_ & -> & _)]; [|done].
    apply rtc_once. by eapply istep_erase.
  Qed.

  Lemma run_other i t e :
    t ∉ l i → (r i).2 !! t = Some e → ∃ g, (r (S i)).2 !! t = Some (emap g e).
  Proof.
    intros Ht He. destruct (Hmax i) as [Hs|(_ & -> & _)].
    - by eapply istep_other.
    - exists id. rewrite He. f_equal. clear. induction e; simpl; f_equal; auto.
  Qed.

  Lemma run_pend i t : t ∉ l i → pend (r i) t → pend (r (S i)) t.
  Proof.
    intros Ht Hp. destruct (Hmax i) as [Hs|(_ & -> & _)]; [|done].
    by eapply istep_other_pend.
  Qed.

  Lemma run_admin i t : t ∉ l i → admin_at (r i) t → admin_at (r (S i)) t.
  Proof.
    intros Ht Hp. destruct (Hmax i) as [Hs|(_ & -> & _)]; [|done].
    by eapply istep_other_admin.
  Qed.

  Lemma run_admin_step i t e a :
    t ∈ l i → (r i).2 !! t = Some e → act e = Some a → is_admin a →
    ∃ α e', admin_lbl α ∧ tstep e α e' ∧ (r (S i)).2 !! t = Some e'.
  Proof.
    intros Ht He Ha Had. destruct (Hmax i) as [Hs|(_ & _ & Hl)].
    - by eapply admin_step.
    - rewrite Hl in Ht. set_solver.
  Qed.
End runs.
