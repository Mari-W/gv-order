(** * Adequacy of the live relation (liveness.md §1, §8)

    A closed process in the live relation at every index is deadlock
    free, and from every reachable state every sequence of τ steps of
    β, new and spawn is finite. Hence every maximal run terminates or
    performs infinitely many channel steps ([live_runs]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveUnfold.

Local Set Warnings "-register-all".

(** ** One step of a closed process *)

Lemma disjoint_dom_empty (C : gset chan) : C ## dom (∅ : senv).
Proof. rewrite dom_empty_L. apply disjoint_empty_r. Qed.

(** Every τ lowers the index by at most two and may grow the world. *)
Lemma LPrel_tau n W T p p' :
  LPrel (S (S n)) W ∅ T p → preduction p p' → ∃ W', LPrel n W' ∅ T p'.
Proof.
  intros HP Hst. apply LPrel_S_iff in HP.
  destruct (HP W (wext_r_refl W)) as (_ & _ & HA & HC & HL & _).
  apply ptau_classify in Hst as [Ha|[Hc|Hl]].
  - destruct (HA p' Ha (disjoint_dom_empty _) ∅) as (N & W' & _ & _ & HP').
    exists W'. eapply LPrel_down; [|exact HP']. lia.
  - destruct (HC p' Hc (disjoint_dom_empty _)) as (N & W' & _ & _ & HP').
    exists W'. exact HP'.
  - destruct (HL p' Hl (disjoint_dom_empty _)) as (N & W' & _ & _ & HP').
    exists W'. eapply LPrel_down; [|exact HP']. lia.
Qed.

(** A run of m steps lowers the index by at most 2m. *)
Lemma LPrel_steps m : ∀ W n T p p',
  nsteps preduction m p p' → LPrel (2 * m + n) W ∅ T p → ∃ W', LPrel n W' ∅ T p'.
Proof.
  induction m as [|m IH]; intros W n T p p' Hrun HP.
  { inversion Hrun; subst. by exists W. }
  inversion Hrun as [|? ? q ? Hpq Hqr]; subst.
  replace (2 * S m + n) with (S (S (2 * m + n))) in HP by lia.
  destruct (LPrel_tau _ _ _ _ _ HP Hpq) as (W' & HP').
  exact (IH W' n T q p' Hqr HP').
Qed.

(** With an empty interface no session label is allowed. *)
Lemma LPobl_empty Vl Pl n W T p σ p' : LPobl Vl Pl n W ∅ T p σ p' → False.
Proof.
  destruct σ as [c w|c w|c|cd|c b|c b]; simpl.
  - intros (Σ1 & m & U & s & k & Heq & _). exact (senv_hd_not_empty _ _ _ _ Heq).
  - intros (?&?&?&?&?&?&?&?&Heq&_). exact (senv_hd_not_empty _ _ _ _ Heq).
  - intros (Σ1 & k & Heq & _). exact (senv_hd_not_empty _ _ _ _ Heq).
  - intros (c & d & Σ1 & sc & sd & kc & kd & _ & _ & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
  - intros (Σ1 & s1 & s2 & k & Heq & _). exact (senv_hd_not_empty _ _ _ _ Heq).
  - intros (Σ1 & s1 & s2 & k & Heq & _). exact (senv_hd_not_empty _ _ _ _ Heq).
Qed.

Lemma LPrel_safe n W T p : LPrel (S n) W ∅ T p → safe p.
Proof.
  intros HP. apply LPrel_S_iff in HP.
  destruct (HP W (wext_r_refl W)) as (Hs & _ & _ & _ & _ & Hσ).
  destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - left. destruct (Hs Hirr) as (v & E & -> & Hv & _ & HE). exists v, E. auto.
  - right. destruct π as [|σ].
    + by exists p'.
    + exfalso. exact (LPobl_empty _ _ _ _ _ _ _ _ (Hσ σ p' Hst)).
Qed.

(** ** The τ layer is well founded *)

Lemma LPrel_acc n W T p : LPrel (S n) W ∅ T p → Acc (λ y x, padmin x y) p.
Proof.
  intros HP. cut (∀ W Σ T p, LPrel (S n) W Σ T p → Σ = ∅ → Acc (λ y x, padmin x y) p).
  { intros H. by apply (H W ∅ T p). }
  clear W T p HP. refine (LPrel_S_ind n (λ W Σ T p, Σ = ∅ → Acc (λ y x, padmin x y) p) _).
  intros W Σ T p H ->.
  constructor. intros p' Ha.
  destruct (H W (wext_r_refl W)) as (_ & _ & HA & _).
  destruct (HA p' Ha (disjoint_dom_empty _) ∅) as (N & W' & _ & _ & _ & HΦ).
  by apply HΦ.
Qed.

(** ** The adequacy statements *)

Definition no_tau_divergence (p : proc) : Prop :=
  ∀ q, pred_star p q → Acc (λ y x, padmin x y) q.

Lemma live_reach W T p q :
  (∀ n, LPrel n W ∅ T p) → pred_star p q → ∀ n, ∃ W', LPrel n W' ∅ T q.
Proof.
  intros HP Hq n. apply rtc_nsteps_1 in Hq as [m Hm].
  exact (LPrel_steps m W n T p q Hm (HP (2 * m + n))).
Qed.

Theorem live_deadlock_free W T p : (∀ n, LPrel n W ∅ T p) → deadlock_free p.
Proof.
  intros HP q Hq. destruct (live_reach W T p q HP Hq 1) as (W' & HP').
  by eapply (LPrel_safe 0).
Qed.

Theorem live_no_tau_divergence W T p : (∀ n, LPrel n W ∅ T p) → no_tau_divergence p.
Proof.
  intros HP q Hq. destruct (live_reach W T p q HP Hq 1) as (W' & HP').
  by eapply (LPrel_acc 0).
Qed.

(** Theorem (live adequacy). *)
Theorem live_adequacy W T p :
  (∀ n, LPrel n W ∅ T p) → deadlock_free p ∧ no_tau_divergence p.
Proof. intros HP. split; [by eapply live_deadlock_free|by eapply live_no_tau_divergence]. Qed.

(** ** Runs

    A finite maximal run ends in a terminated state. An infinite run
    takes a channel step after every position. *)

Corollary live_finite_runs W T p q :
  (∀ n, LPrel n W ∅ T p) → pred_star p q → (∀ q', ¬ preduction q q') → terminated q.
Proof.
  intros HP Hq Hmax. destruct (live_deadlock_free W T p HP q Hq) as [Ht|(q' & Hst)]; [done|].
  by destruct (Hmax q').
Qed.

Corollary live_runs W T p (f : nat → proc) :
  (∀ n, LPrel n W ∅ T p) → f 0 = p → (∀ i, preduction (f i) (f (S i))) →
  ∀ i, ∃ j, i ≤ j ∧ pchan (f j) (f (S j)).
Proof.
  intros HP Hf0 Hrun i.
  assert (pred_star p (f i)) as Hreach.
  { rewrite <-Hf0. clear HP Hf0. induction i as [|i IH]; [done|].
    eapply rtc_r; [exact IH|apply Hrun]. }
  pose proof (live_no_tau_divergence W T p HP (f i) Hreach) as Hacc.
  remember (f i) as q eqn:Hq. revert i Hq Hreach.
  induction Hacc as [q _ IH]. intros i -> Hreach.
  destruct (proj1 (ptau_classify _ _) (Hrun i)) as [Ha|Hc].
  - destruct (IH (f (S i)) Ha (S i) eq_refl) as (j & Hj & Hjc).
    + eapply rtc_r; [exact Hreach|apply Hrun].
    + exists j. split; [lia|done].
  - exists i. split; [lia|done].
Qed.
