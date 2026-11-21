(** * A maximal weakly fair run exists, and Padovani-style lock freedom

    Every configuration starts a maximal weakly fair run
    ([fair_run_exists]). The run follows a round robin over thread
    numbers ([rr]). At position n the scheduler targets the thread rr n
    and takes a step in which it takes part when it is enabled, any step
    otherwise, and repeats a stuck end. The round robin visits 0, then
    0 1 2, then 0 1 2 3 4, and so on, so every thread is targeted at
    arbitrarily late positions. The semantics alone decides the run,
    typing plays no part.

    A run is a function on ℕ and the steps are propositions ([istep]).
    Picking a step at every position is dependent choice, and deciding
    whether the target is enabled is excluded middle. Both are explicit
    hypotheses of the lemma, never axioms.

    [lock_free] keeps quantifying over every maximal weakly fair run.
    From it and the existence of runs follows the reachability form of
    Padovani 2014, Def. II.1, per thread ([lock_free_padovani]). Every
    thread pending in a configuration reachable from p takes part in a
    step of some configuration reachable from there. *)

From stdpp Require Import relations.
From GV Require Export lockfree.Fair.

(** ** Classical hypotheses *)

Definition excluded_middle : Prop := ∀ P : Prop, P ∨ ¬ P.

Definition dependent_choice : Prop :=
  ∀ (A : Type) (R : A → A → Prop), (∀ x, ∃ y, R x y) →
  ∀ x0, ∃ f : nat → A, f 0 = x0 ∧ ∀ n, R (f n) (f (S n)).

(** ** Round robin over thread numbers *)

Definition rr (n : nat) : nat := n - Nat.sqrt n * Nat.sqrt n.

Lemma rr_inf t i : ∃ j, i ≤ j ∧ rr j = t.
Proof.
  set (k := i + t). exists (k * k + t). unfold rr.
  assert (Nat.sqrt (k * k + t) = k) as ->.
  { apply Nat.sqrt_unique. split; [lia|]. unfold k. nia. }
  split; [unfold k; nia|lia].
Qed.

(** ** One step of the scheduler *)

Definition rr_step (n : nat) (q : config) (l : option event) (q' : config) : Prop :=
  (∃ ev, l = Some ev ∧ itstep q ev q' ∧ (tenabled q (rr n) → rr n ∈ ev_parts ev)) ∨
  (stuck q ∧ q' = q ∧ l = None).

Lemma rr_step_total (EM : excluded_middle) n q : ∃ l q', rr_step n q l q'.
Proof.
  destruct (EM (tenabled q (rr n))) as [(ev & q' & Hs & Ht)|Hn].
  - exists (Some ev), q'. left. eauto.
  - destruct (EM (∃ ev q', itstep q ev q')) as [(ev & q' & Hs)|Hs].
    + exists (Some ev), q'. left. exists ev. split_and!; [done|done|]. intros; contradiction.
    + exists None, q. right. split_and!; [|done|done]. intros ev q' H. apply Hs. eauto.
Qed.

(** The state of the scheduler: the position, the configuration and the
    event that led to it. *)
Definition rr_rel (x y : nat * config * option event) : Prop :=
  y.1.1 = S x.1.1 ∧ rr_step x.1.1 x.1.2 y.2 y.1.2.

(** ** Existence *)

Theorem fair_run_exists (EM : excluded_middle) (DC : dependent_choice) q :
  ∃ r l, r 0 = q ∧ maximal r l ∧ wfair r l.
Proof.
  destruct (DC _ rr_rel) with (x0 := (0, q, @None event)) as (f & Hf0 & Hf).
  { intros [[n q0] l0]. destruct (rr_step_total EM n q0) as (l & q' & Hs).
    exists (S n, q', l). by split. }
  assert (∀ i, (f i).1.1 = i) as Hn.
  { induction i as [|i IH]; [by rewrite Hf0|]. destruct (Hf i) as [-> _]. by rewrite IH. }
  exists (λ i, (f i).1.2), (λ i, (f (S i)).2). split_and!.
  - by rewrite Hf0.
  - intros i. destruct (Hf i) as [_ Hs]. rewrite Hn in Hs.
    destruct Hs as [(ev & Hl & Hst & _)|(Hst & Heq & Hl)]; [left; eauto|right; auto].
  - intros t i. destruct (rr_inf t i) as (j & Hij & Hj). exists j. split; [done|].
    destruct (Hf j) as [_ Hs]. rewrite Hn in Hs. unfold rr_step in Hs. rewrite Hj in Hs.
    destruct Hs as [(ev & Hl & Hst & Hp)|(Hst & _ & _)].
    + destruct (EM (tenabled (f j).1.2 t)) as [He|He]; [left|by right].
      rewrite Hl. simpl. auto.
    + right. intros (ev & q' & Hs' & _). by eapply Hst.
Qed.

(** A process starts a maximal weakly fair run from any lifting of it. *)
Corollary fair_run_exists_proc (EM : excluded_middle) (DC : dependent_choice) p :
  ∃ r l, erase (r 0) = p ∧ maximal r l ∧ wfair r l.
Proof.
  destruct (erase_surj p) as [q Hq].
  destruct (fair_run_exists EM DC q) as (r & l & Hr0 & Hmax & Hfair).
  exists r, l. rewrite Hr0. auto.
Qed.

(** ** Runs with a finite prefix *)

Definition rcons {A} (a : A) (f : nat → A) (i : nat) : A :=
  match i with 0 => a | S i => f i end.

Lemma run_cons q0 ev r l :
  itstep q0 ev (r 0) → maximal r l → wfair r l →
  maximal (rcons q0 r) (rcons (Some ev) l) ∧ wfair (rcons q0 r) (rcons (Some ev) l).
Proof.
  intros Hs Hmax Hfair. split.
  - intros [|i]; [left; eauto|exact (Hmax i)].
  - intros t i. destruct (Hfair t (pred i)) as (j & Hij & Hj).
    exists (S j). split; [lia|exact Hj].
Qed.

Lemma run_prefix q0 q :
  itsteps q0 q → ∀ r l, r 0 = q → maximal r l → wfair r l →
  ∃ r' l' k, r' 0 = q0 ∧ maximal r' l' ∧ wfair r' l' ∧ ∀ i, r' (k + i) = r i ∧ l' (k + i) = l i.
Proof.
  induction 1 as [q|q0 q1 q Hs _ IH]; intros r l Hr0 Hmax Hfair.
  - subst q. exists r, l, 0. auto.
  - destruct (IH r l Hr0 Hmax Hfair) as (r' & l' & k & Hr'0 & Hmax' & Hfair' & Hk).
    destruct Hs as [ev Hs]. rewrite <-Hr'0 in Hs.
    destruct (run_cons q0 ev r' l' Hs Hmax' Hfair') as [Hmax'' Hfair''].
    exists (rcons q0 r'), (rcons (Some ev) l'), (S k). split_and!; auto.
Qed.

Lemma run_itsteps r l : maximal r l → ∀ i n, itsteps (r i) (r (i + n)).
Proof.
  intros Hmax i n. induction n as [|n IH]; [by rewrite Nat.add_0_r|].
  rewrite Nat.add_succ_r. destruct (Hmax (i + n)) as [(ev & _ & Hs)|(_ & -> & _)]; [|done].
  eapply rtc_r; [exact IH|]. by exists ev.
Qed.

(** ** Padovani-style lock freedom, per thread *)

Definition lf_padovani (p : proc) : Prop :=
  ∀ q0 q t, erase q0 = p → itsteps q0 q → pend q t →
  ∃ q1 ev q2, itsteps q q1 ∧ itstep q1 ev q2 ∧ t ∈ ev_parts ev.

Theorem lock_free_padovani (EM : excluded_middle) (DC : dependent_choice) p :
  lock_free p → lf_padovani p.
Proof.
  intros Hlf q0 q t H0 Hs Hp.
  destruct (fair_run_exists EM DC q) as (r & l & Hr0 & Hmax & Hfair).
  destruct (run_prefix q0 q Hs r l Hr0 Hmax Hfair)
    as (r' & l' & k & Hr'0 & Hmax' & Hfair' & Hk).
  assert (r' k = q) as Hrk.
  { destruct (Hk 0) as [Hk0 _]. by rewrite Nat.add_0_r, Hr0 in Hk0. }
  rewrite <-Hrk in Hp.
  destruct (Hlf r' l' ltac:(by rewrite Hr'0) Hmax' Hfair' k t Hp) as (j & Hkj & Hj).
  destruct (Hmax' j) as [(ev & Hl & Hst)|(_ & _ & Hl)]; rewrite Hl in Hj; [|set_solver].
  exists (r' j), ev, (r' (S j)). split_and!; [|done|done].
  rewrite <-Hrk. replace j with (k + (j - k)) by lia. apply (run_itsteps r' l' Hmax').
Qed.

(** ** Plausibility: a configuration with two threads starts such a run *)

Example fair_run_two_threads (EM : excluded_middle) (DC : dependent_choice) :
  ∃ r l, r 0 = (∅, {[0 := EUnit; 1 := EUnit]}) ∧ maximal r l ∧ wfair r l.
Proof. apply fair_run_exists; done. Qed.
