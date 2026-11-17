(** * Individual progress (lock-freedom plan §9)

    [thread_progress]: in a weakly fair maximal run from a lock-free
    process without τ-divergence, every thread, from every position on,
    later stops (its term has no redex) or takes part in a channel step
    (a step on a redex that is not administrative). Read for all
    positions, this says that every thread stops or takes part in
    infinitely many channel steps. [stopped_forever] says that a stopped
    thread stays stopped, and [thread_progress_val] turns stopping into
    reaching a value for a process whose stopped threads are values.

    The hypotheses are those that adequacy supplies anyway. [lock_free]
    comes from [lf_adequacy], [no_tau_divergence] from [live_adequacy],
    and [links_restricted] from the soup ([lf_links_restricted]).

    Proof. A thread at a non-administrative redex is pending, so lock
    freedom makes it take part, and at its first step it still has that
    redex up to renaming. A thread at an administrative redex is enabled
    until it takes part, so weak fairness fires it, and the step lowers
    the admin measure of [thread_acc]. Constructive, no axiom. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Criterion.

Definition stopped (q : config) (t : nat) : Prop :=
  ∃ e, q.2 !! t = Some e ∧ act e = None.

Definition chan_part (r : nat → config) (l : nat → gset nat) (j t : nat) : Prop :=
  t ∈ l j ∧ ∃ e a, (r j).2 !! t = Some e ∧ act e = Some a ∧ ¬ is_admin a.

Definition thread_progress_run (r : nat → config) (l : nat → gset nat) : Prop :=
  ∀ i t e, (r i).2 !! t = Some e → ∃ j, i ≤ j ∧ (stopped (r j) t ∨ chan_part r l j t).

Lemma not_admin_sess a : ¬ is_admin a → is_sess a.
Proof. destruct a; simpl; unfold is_sess; simpl; try (intros _; by eexists); done. Qed.

Section runs.
  Context (r : nat → config) (l : nat → gset nat) (Hmax : maximal r l).

  (** A thread that does not take part keeps its term up to renaming. *)
  Lemma run_keep k t e :
    (r k).2 !! t = Some e →
    ∀ m, k ≤ m → (∀ m', k ≤ m' < m → t ∉ l m') → ∃ g, (r m).2 !! t = Some (emap g e).
  Proof.
    intros He m Hkm. induction Hkm as [|m Hkm IH]; intros Hnot.
    - exists id. by rewrite emap_id.
    - destruct IH as [g Hg]; [intros m' ?; apply Hnot; lia|].
      destruct (run_other r l Hmax m t (emap g e)) as [g' Hg']; [apply Hnot; lia|done|].
      exists (g' ∘ g). by rewrite Hg', emap_emap.
  Qed.

  (** A stopped thread takes part in no step. *)
  Lemma stopped_not_part k t : stopped (r k) t → t ∉ l k.
  Proof.
    intros (e & He & Ha) Ht. destruct (Hmax k) as [Hs|(_ & _ & Hl)].
    - destruct (istep_actor _ _ _ t e Hs Ht He) as (α & e' & Hst & _).
      destruct (act_step _ _ _ Hst) as (a & Ha' & _). congruence.
    - rewrite Hl in Ht. set_solver.
  Qed.

  Lemma stopped_forever j t : stopped (r j) t → ∀ m, j ≤ m → stopped (r m) t.
  Proof.
    intros Hs m Hjm. induction Hjm as [|m Hjm IH]; [done|].
    destruct IH as (e & He & Ha).
    destruct (run_other r l Hmax m t e) as [g Hg]; [apply stopped_not_part; by exists e|done|].
    exists (emap g e). by rewrite act_emap, Ha.
  Qed.
End runs.

Section progress.
  Context (p : proc) (r : nat → config) (l : nat → gset nat).
  Context (Hr0 : erase (r 0) = p) (Hmax : maximal r l) (Hfair : wfair r l).
  Context (Hlf : lock_free p) (Hnd : no_tau_divergence p) (Hlr : links_restricted p).

  Lemma tp_reach k : pred_star p (erase (r k)).
  Proof. rewrite <-Hr0. by apply (run_reach r l Hmax). Qed.

  Lemma tp_fair_persist t k (P : nat → Prop) :
    P k → (∀ m, k ≤ m → P m → t ∉ l m → P (S m)) → (∀ m, P m → enabled (r m) t) →
    ∃ j, k ≤ j ∧ t ∈ l j.
  Proof.
    intros Hk Hstep Hen. destruct (Hfair t k) as (j & Hkj & [Hj|Hj]); [eauto|].
    assert (∀ m, k ≤ m → m ≤ j → (∃ j', k ≤ j' ∧ t ∈ l j') ∨ P m) as Hscan.
    { intros m Hkm Hmj. induction Hkm as [|m Hkm IH]; [by right|].
      destruct IH as [?|HP]; [lia|by left|].
      destruct (decide (t ∈ l m)) as [Ht|Ht]; [left; exists m; split; [lia|done]|].
      right. by apply Hstep. }
    destruct (Hscan j Hkj (Nat.le_refl _)) as [?|HP]; [done|]. by destruct (Hj (Hen _ HP)).
  Qed.

  (** The first position from k on at which t takes part. *)
  Lemma first_part k t j :
    k ≤ j → t ∈ l j → ∃ m, k ≤ m ∧ t ∈ l m ∧ ∀ m', k ≤ m' < m → t ∉ l m'.
  Proof.
    intros Hkj Hj. destruct (first_hit (λ m, t ∈ l m) k j Hkj Hj) as (m & Hm & Hmt & Hf).
    exists m. split_and!; [lia|done|done].
  Qed.

  Lemma tp_acc x :
    Acc tR x → ∀ k t e, (r k).2 !! t = Some e → cerase e = x →
      ∃ j, k ≤ j ∧ (stopped (r j) t ∨ chan_part r l j t).
  Proof.
    induction 1 as [x _ IH]. intros k t e He Hx.
    destruct (act e) as [a|] eqn:Ha; [|exists k; split; [lia|left; by exists e]].
    destruct (is_admin_dec a) as [Had|Hnad].
    - (* an administrative redex: weak fairness fires it *)
      destruct (tp_fair_persist t k (λ m, admin_at (r m) t)) as (j0 & Hj0 & Htj0).
      + by exists e, a.
      + intros m _ Hm Htm. by apply (run_admin r l Hmax).
      + intros m (e' & a' & He' & Ha' & Had').
        apply (admin_enabled (r m) t e' a' He' Ha' Had'). intros c d ->.
        apply (Hlr (erase (r m)) (soup (delete t (r m).2)) e' c d (tp_reach m)); [|done].
        simpl. by apply soup_delete.
      + destruct (first_part k t j0 Hj0 Htj0) as (m & Hkm & Htm & Hf).
        destruct (run_keep r l Hmax k t e He m Hkm Hf) as [g Hg].
        destruct (run_admin_step r l Hmax m t (emap g e) (amap g a) Htm Hg)
          as (α & e2 & g' & Hα & Hst & He2).
        { by rewrite act_emap, Ha. }
        { by apply amap_admin. }
        assert (tR (cerase (emap g' e2)) x) as HtR.
        { rewrite cerase_emap, <-Hx, <-(cerase_emap g e). by eapply tR_step. }
        destruct (IH _ HtR (S m) t (emap g' e2) He2 eq_refl) as (j & Hj & Hres).
        exists j. split; [lia|done].
    - (* a session redex: lock freedom fires it, and it is a channel step *)
      assert (pend (r k) t) as Hp by (exists e, a; split_and!; [done|done|by apply not_admin_sess]).
      destruct (Hlf r l Hr0 Hmax Hfair k t Hp) as (j0 & Hj0 & Htj0).
      destruct (first_part k t j0 Hj0 Htj0) as (m & Hkm & Htm & Hf).
      destruct (run_keep r l Hmax k t e He m Hkm Hf) as [g Hg].
      exists m. split; [done|right]. split; [done|].
      exists (emap g e), (amap g a). split_and!; [done|by rewrite act_emap, Ha|].
      by rewrite amap_admin.
  Qed.
End progress.

(** ** Individual progress *)

Theorem thread_progress p :
  lock_free p → no_tau_divergence p → links_restricted p →
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → thread_progress_run r l.
Proof.
  intros Hlf Hnd Hlr r l Hr0 Hmax Hfair i t e He.
  refine (tp_acc p r l Hr0 Hmax Hfair Hlf Hlr (cerase e) _ i t e He eq_refl).
  apply (thread_acc p (r i) t e Hlr Hnd); [|done].
  rewrite <-Hr0. by apply (run_reach r l Hmax).
Qed.

(** A stopped thread of a reachable configuration is a value. Typing
    supplies it ([prim T] for the main thread, ∗ for spawned ones). *)
Definition threads_safe (p : proc) : Prop :=
  ∀ q t e, pred_star p (erase q) → q.2 !! t = Some e → act e = None → is_val e.

Corollary thread_progress_val p :
  lock_free p → no_tau_divergence p → links_restricted p → threads_safe p →
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l →
  ∀ i t e, (r i).2 !! t = Some e →
    ∃ j, i ≤ j ∧
      ((∃ v, is_val v ∧ ∀ m, j ≤ m → ∃ g, (r m).2 !! t = Some (emap g v)) ∨
       chan_part r l j t).
Proof.
  intros Hlf Hnd Hlr Hsafe r l Hr0 Hmax Hfair i t e He.
  destruct (thread_progress p Hlf Hnd Hlr r l Hr0 Hmax Hfair i t e He)
    as (j & Hij & [Hs|Hc]); [|exists j; by split; [|right]].
  exists j. split; [done|left]. destruct Hs as (v & Hv & Ha). exists v. split.
  - apply (Hsafe (r j) t v); [|done|done]. rewrite <-Hr0. by apply (run_reach r l Hmax).
  - intros m Hjm. apply (run_keep r l Hmax j t v Hv m Hjm).
    intros m' Hm'. apply (stopped_not_part r l Hmax).
    apply (stopped_forever r l Hmax j); [by exists v|lia].
Qed.
