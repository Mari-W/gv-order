(** * The lock-freedom criterion (lock-freedom plan §3.3)

    [lf_criterion] derives [lock_free] from four hypotheses: local
    progress in every reachable state, [no_tau_divergence], and the two
    bounds [fuel_bound] and [rank_bound] on runs. The bounds are
    abstract. Stage 2 instantiates them from the budgeted relation.

    Proof. For a thread t pending on an end of rank e, by well-founded
    induction on e, then by induction on the fuel of the partner end,
    then by induction on the admin measure of its holder s
    (TauThread.v). Local progress gives the holder. The holder takes
    part in a later step: by weak fairness when its redex is
    administrative, and by the rank hypothesis and the outer induction
    when it is blocked. A step of the holder lowers the fuel, unless it
    is administrative, and then it lowers the admin measure. When t
    itself is enabled, its offer persists and weak fairness fires it. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Fair lockfree.TauThread.

(** ** The bounds

    [fuel_bound]. fu k t is the fuel of the partner of the end that the
    pending thread t waits on, at position k. While t waits, every step
    either lowers it, or keeps the holders of the partner end and lets
    them take only administrative steps. So a holder acts on the partner
    end within fu k t of its own steps on other entries, or it blocks.
    Two linearity clauses come with it. The holder is unique, and an
    enabled pending thread stays enabled until it takes part (an offer
    persists until it fires). Both hold of well-typed configurations
    and are not facts of the untyped semantics.

    [rank_bound]. A well-founded relation R on ends and the end we k t
    that t waits on at position k. The end of a waiting thread does
    not change while it waits. A pending holder of the partner end
    waits on a smaller end, unless t is already enabled. *)

Definition fuel_bound (r : nat → config) (l : nat → gset nat) : Prop :=
  ∃ fu : nat → nat → nat,
    (∀ k t s s', pend (r k) t → waits (r k) t s → waits (r k) t s' → s = s') ∧
    (∀ k t, pend (r k) t → enabled (r k) t → t ∉ l k → enabled (r (S k)) t) ∧
    (∀ k t, pend (r k) t → t ∉ l k →
       fu (S k) t < fu k t ∨
       (fu (S k) t = fu k t ∧ (∀ s, waits (r (S k)) t s ↔ waits (r k) t s) ∧
        ∀ s, waits (r k) t s → s ∈ l k → admin_at (r k) s)).

Definition rank_bound (r : nat → config) (l : nat → gset nat) : Prop :=
  ∃ (E : Type) (R : E → E → Prop) (we : nat → nat → E),
    well_founded R ∧
    (∀ k t, pend (r k) t → t ∉ l k → we (S k) t = we k t) ∧
    (∀ k t s, pend (r k) t → waits (r k) t s → pend (r k) s →
       enabled (r k) t ∨ R (we k s) (we k t)).

(** ** Scanning a run *)

Lemma first_hit (Q : nat → Prop) `{∀ n, Decision (Q n)} k j :
  k ≤ j → Q j → ∃ m, k ≤ m ≤ j ∧ Q m ∧ ∀ m', k ≤ m' < m → ¬ Q m'.
Proof.
  intros Hkj. replace j with (k + (j - k)) by lia. generalize (j - k) as d. clear Hkj j.
  intros d. revert k. induction d as [|d IH]; intros k HQ.
  - exists k. split_and!; [lia|lia|by rewrite Nat.add_0_r in HQ|lia].
  - destruct (decide (Q k)) as [Hk|Hk].
    + exists k. split_and!; [lia|lia|done|lia].
    + destruct (IH (S k)) as (m & Hm & Hq & Hf); [by replace (S k + d) with (k + S d) by lia|].
      exists m. split_and!; [lia|lia|done|]. intros m' Hm'.
      destruct (decide (m' = k)) as [->|Hne]; [done|]. apply Hf. lia.
Qed.

Section criterion.
  Context (p : proc) (r : nat → config) (l : nat → gset nat).
  Context (Hr0 : erase (r 0) = p) (Hmax : maximal r l) (Hfair : wfair r l).
  Context (HLP : ∀ q, pred_star p (erase q) → local_progress q).
  Context (Hnd : no_tau_divergence p) (Hlr : links_restricted p).
  Context (fu : nat → nat → nat).
  Context (Huniq : ∀ k t s s', pend (r k) t → waits (r k) t s → waits (r k) t s' → s = s').
  Context (Hpers : ∀ k t, pend (r k) t → enabled (r k) t → t ∉ l k → enabled (r (S k)) t).
  Context (Hfuel : ∀ k t, pend (r k) t → t ∉ l k →
       fu (S k) t < fu k t ∨
       (fu (S k) t = fu k t ∧ (∀ s, waits (r (S k)) t s ↔ waits (r k) t s) ∧
        ∀ s, waits (r k) t s → s ∈ l k → admin_at (r k) s)).
  Context (E : Type) (R : E → E → Prop) (we : nat → nat → E) (HR : well_founded R).
  Context (Hstab : ∀ k t, pend (r k) t → t ∉ l k → we (S k) t = we k t).
  Context (Hrank : ∀ k t s, pend (r k) t → waits (r k) t s → pend (r k) s →
       enabled (r k) t ∨ R (we k s) (we k t)).

  Lemma reach k : pred_star p (erase (r k)).
  Proof. rewrite <-Hr0. by apply (run_reach r l Hmax). Qed.

  (** A property that persists while t does not take part, and that
      keeps t enabled, makes t take part. *)
  Lemma fair_persist t k (P : nat → Prop) :
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

  Lemma enabled_fires k t : pend (r k) t → enabled (r k) t → ∃ j, k ≤ j ∧ t ∈ l j.
  Proof.
    intros Hp He. apply (fair_persist t k (λ m, pend (r m) t ∧ enabled (r m) t)).
    - done.
    - intros m _ [Hpm Hem] Ht. split; [by apply (run_pend r l Hmax)|by apply Hpers].
    - by intros m [_ ?].
  Qed.

  (** Step A. The holder of a waiting thread takes part later, unless
      the waiting thread does. *)
  Lemma holder_moves e
      (IHr : ∀ e', R e' e → ∀ k s, we k s = e' → pend (r k) s → ∃ j, k ≤ j ∧ s ∈ l j)
      k t s :
    we k t = e → pend (r k) t → waits (r k) t s →
    (∃ j, k ≤ j ∧ t ∈ l j) ∨ (∃ j, k ≤ j ∧ s ∈ l j).
  Proof.
    intros Hwe Hp Hw.
    destruct (HLP (r k) (reach k) t Hp) as (u & Hch & Hen).
    destruct Hch as [|t s1 u Hw1 Hch]; [left; by apply enabled_fires|].
    rewrite <-(Huniq k t s s1 Hp Hw Hw1) in Hch.
    assert (enabled (r k) s ∨ pend (r k) s) as Hs.
    { destruct Hch as [|s s2 u Hw2 _]; [by left|right; by eapply waits_pend]. }
    pose proof Hw as Hw0.
    destruct Hw as (_ & e0 & a0 & S0 & c0 & es & _ & _ & _ & _ & Hes & _).
    destruct (act es) as [a|] eqn:Ha.
    - destruct (admin_or_sess a) as [Had|Hse].
      + right. destruct Had as [Had _]. apply (fair_persist s k (λ m, admin_at (r m) s)).
        * by exists es, a.
        * intros m _ Hm Hsm. by apply (run_admin r l Hmax).
        * intros m (es' & a' & Hes' & Ha' & Had').
          apply (admin_enabled (r m) s es' a' Hes' Ha' Had'). intros c d ->.
          apply (Hlr (erase (r m)) (soup (delete s (r m).2)) es' c d (reach m)); [|done].
          simpl. by apply soup_delete.
      + assert (pend (r k) s) as Hps by (by exists es, a).
        destruct (Hrank k t s Hp Hw0 Hps) as [Hent|HR'].
        * left. by apply enabled_fires.
        * right. apply (IHr (we k s)); [by rewrite <-Hwe|done|done].
    - exfalso. destruct Hs as [Hen'|(es' & a' & Hes' & Ha' & _)].
      + destruct (enabled_act _ _ _ Hen' Hes) as [a' Ha']. congruence.
      + congruence.
  Qed.

  (** The core: induction on the fuel and on the admin measure of the
      holder, for a fixed rank. *)
  Lemma core e
      (IHr : ∀ e', R e' e → ∀ k s, we k s = e' → pend (r k) s → ∃ j, k ≤ j ∧ s ∈ l j) :
    ∀ n k t, fu k t = n → we k t = e → pend (r k) t → ∃ j, k ≤ j ∧ t ∈ l j.
  Proof.
    intros n. induction n as [n IHn] using lt_wf_ind. intros k0 t Hfu0 Hwe0 Hp0.
    (* a fuel drop at any later position closes the goal *)
    assert (∀ m, k0 ≤ m → pend (r m) t → we m t = e → t ∉ l m → fu (S m) t < n →
              ∃ j, k0 ≤ j ∧ t ∈ l j) as Hdrop.
    { intros m Hm Hpm Hwm Ht Hlt.
      destruct (IHn (fu (S m) t) Hlt (S m) t eq_refl) as (j & Hj & Htj).
      - rewrite Hstab; done.
      - by apply (run_pend r l Hmax).
      - exists j. split; [lia|done]. }
    destruct (HLP (r k0) (reach k0) t Hp0) as (u & Hch & Hen).
    destruct Hch as [|t s u Hw _]; [by apply enabled_fires|].
    destruct Hw as [Hst Hw']. pose proof (conj Hst Hw') as Hw.
    destruct Hw' as (_ & _ & _ & _ & es & _ & _ & _ & _ & Hes & _).
    pose proof (thread_acc p (r k0) s es Hlr Hnd (reach k0) Hes) as Hacc.
    remember (cerase es) as x eqn:Hx.
    assert (∀ k, k0 ≤ k → fu k t = n → we k t = e → pend (r k) t → waits (r k) t s →
              ∀ es, (r k).2 !! s = Some es → cerase es = x → ∃ j, k0 ≤ j ∧ t ∈ l j)
      as Hinner; [|by apply (Hinner k0 (Nat.le_refl _) Hfu0 Hwe0 Hp0 Hw es Hes)].
    clear Hes Hx es Hw Hst Hen u. revert x Hacc.
    induction 1 as [x _ IHx]. intros k Hk Hfu Hwe Hp Hw es Hes Hx.
    destruct (holder_moves e IHr k t s Hwe Hp Hw) as [(j & Hj & Htj)|(j1 & Hj1 & Hsj1)].
    { exists j. split; [lia|done]. }
    set (Q := λ m, t ∈ l m ∨ fu (S m) t < fu m t ∨ s ∈ l m).
    assert (∀ m, Decision (Q m)) by (intros m; unfold Q; apply _).
    destruct (first_hit Q k j1 Hj1 (or_intror (or_intror Hsj1))) as (m & Hm & HQm & Hfirst).
    (* the invariant up to m *)
    assert (∀ m', k ≤ m' → m' ≤ m →
       pend (r m') t ∧ we m' t = e ∧ fu m' t = n ∧ waits (r m') t s ∧
       ∃ es', (r m').2 !! s = Some es' ∧ cerase es' = x) as Hinv.
    { intros m' Hkm' Hm'm. induction Hkm' as [|m' Hkm' IH].
      - split_and!; [done|done|done|done|]. by exists es.
      - destruct IH as (Hpm & Hwm & Hfm & Hwsm & es' & Hes' & Hx'); [lia|].
        assert (¬ Q m') as HnQ by (apply Hfirst; lia).
        assert (t ∉ l m') as Htm by (intros ?; apply HnQ; by left).
        assert (s ∉ l m') as Hsm by (intros ?; apply HnQ; by right; right).
        destruct (Hfuel m' t Hpm Htm) as [Hlt|(Hfeq & Hwiff & _)];
          [destruct HnQ; by right; left|].
        split_and!.
        + by apply (run_pend r l Hmax).
        + by rewrite Hstab.
        + lia.
        + by apply Hwiff.
        + destruct (run_other r l Hmax m' s es' Hsm Hes') as [g Hg].
          exists (emap g es'). split; [done|]. by rewrite cerase_emap. }
    destruct (Hinv m ltac:(lia) (Nat.le_refl _)) as (Hpm & Hwm & Hfm & Hwsm & es' & Hes' & Hx').
    destruct (decide (t ∈ l m)) as [Htm|Htm]; [exists m; split; [lia|done]|].
    destruct (Hfuel m t Hpm Htm) as [Hlt|(Hfeq & Hwiff & Hadm)].
    { apply (Hdrop m); [lia|done|done|done|lia]. }
    destruct HQm as [?|[Hlt|Hsm]]; [done|lia|].
    destruct (Hadm s Hwsm Hsm) as (es'' & a & Hes'' & Ha & Had).
    rewrite Hes' in Hes''. injection Hes'' as <-.
    destruct (run_admin_step r l Hmax m s es' a Hsm Hes' Ha Had) as (α & e2 & g & Hα & Hst2 & He2).
    assert (tR (cerase (emap g e2)) x) as HtR
      by (rewrite cerase_emap, <-Hx'; by eapply tR_step).
    assert (fu (S m) t = n) as Hfn by lia.
    assert (we (S m) t = e) as Hwn by (by rewrite Hstab).
    assert (pend (r (S m)) t) as Hpn by (by apply (run_pend r l Hmax)).
    assert (waits (r (S m)) t s) as Hwsn by (by apply Hwiff).
    exact (IHx (cerase (emap g e2)) HtR (S m) ltac:(lia) Hfn Hwn Hpn Hwsn (emap g e2) He2 eq_refl).
  Qed.

  Theorem lf_run_criterion : lf_run r l.
  Proof.
    intros i t Hp.
    cut (∀ e k s, we k s = e → pend (r k) s → ∃ j, k ≤ j ∧ s ∈ l j); [eauto|].
    intros e. induction (HR e) as [e _ IHr]. intros k s Hwe Hps.
    exact (core e IHr (fu k s) k s eq_refl Hwe Hps).
  Qed.
End criterion.

(** ** The criterion *)

Theorem lf_criterion p :
  (∀ q, pred_star p (erase q) → local_progress q) →
  no_tau_divergence p → links_restricted p →
  (∀ r l, erase (r 0) = p → maximal r l → fuel_bound r l) →
  (∀ r l, erase (r 0) = p → maximal r l → rank_bound r l) →
  lock_free p.
Proof.
  intros HLP Hnd Hlr Hfb Hrb r l Hr0 Hmax Hfair.
  destruct (Hfb r l Hr0 Hmax) as (fu & Huniq & Hpers & Hfuel).
  destruct (Hrb r l Hr0 Hmax) as (E & R & we & HR & Hstab & Hrank).
  exact (lf_run_criterion p r l Hr0 Hmax Hfair HLP Hnd Hlr fu Huniq Hpers Hfuel E R we HR
    Hstab Hrank).
Qed.
