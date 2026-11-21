(** * The soup along runs (stage S8, proposal §2.12)

      lfsoup_step : a ∈ S^{N,W} _ (S n)⟦∅ ⊢ T⟧ → itstep (s_q a) ev q' →
                    lf_next N a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧

    The state after a step is a function of the state, the event and the
    next configuration ([lf_next]). So a soup at every index at the start
    of a run is a soup at every index at every position of it, at the
    state the run computes ([lfsoup_run]). *)

From stdpp Require Import relations.
From GV Require Export soup.SoupLink.

Theorem lfsoup_step N W T a n ev q' :
  a ∈ S^{N,W} _ (S n)⟦∅ ⊢ T⟧ → itstep (s_q a) ev q' → lf_next N a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof.
  destruct a as [[C Mq] K]. intros (A & Π & U & Hs) [Hst Hτ]. cbn [s_q] in Hst.
  inversion Hst as [C0 M0 i e e' Hi Hs'|C0 M0 i e ℓ c e' Hi Hs' HC Hc|C0 M0 i e κ o c e' Hi Hs' HC Hc
    |C0 M0 i j e v e' Hi Hs' Hj
    |C0 M0 i j o v e e' f f' Hij Hi Hj He Hf|C0 M0 i j o e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j o b e e' f f' Hij Hi Hj He Hf|C0 M0 i e o1 o2 e' Hi Hs' HC
    |C0 M0 i e σ e' Hi Hs' HC]; subst.
  - exists A, Π, U. exact (step_beta _ _ _ _ _ _ _ _ _ _ Hs i e e' Hi Hs').
  - destruct (step_new _ _ _ _ _ _ _ _ _ _ Hs i e ℓ c e' Hi Hs' HC) as (A' & Π' & H). by exists A', Π', U.
  - destruct (step_new_at _ _ _ _ _ _ _ _ _ _ Hs i e κ o c e' Hi Hs' HC) as (A' & Π' & H). by exists A', Π', U.
  - eexists _, _, _. exact (step_spawn _ _ _ _ _ _ _ _ _ _ Hs i j e v e' Hi Hs' Hj).
  - destruct (step_msg _ _ _ _ _ _ _ _ _ _ Hs i j e e' f f' o v Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_close _ _ _ _ _ _ _ _ _ _ Hs i j e e' f f' o Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_choice _ _ _ _ _ _ _ _ _ _ Hs i j e e' f f' o b Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_link _ _ _ _ _ _ _ _ _ _ Hs i e o1 o2 e' Hi Hs') as (A' & Π' & H).
    by exists A', Π', U.
  - by unfold ev_tau in Hτ.
Qed.

(** A soup at every index stays one along a step. *)
Corollary lfsoup_step_all N W T a ev q' :
  (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → itstep (s_q a) ev q' → ∀ n, lf_next N a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof. intros H Hst n. apply (lfsoup_step N W T a n ev q'); [apply H|done]. Qed.

Lemma lf_run_state_q N a0 r l k : s_q a0 = r 0 → s_q (lf_run_state N a0 r l k) = r k.
Proof. intros H0. destruct k as [|k]; [done|]. simpl. unfold lf_upd. by destruct (l k). Qed.

Theorem lfsoup_run N W T a0 r l :
  maximal r l → s_q a0 = r 0 → (∀ n, a0 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) →
  ∀ k n, lf_run_state N a0 r l k ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof.
  intros Hmax H0 Hs k. induction k as [|k IH]; [done|]. intros n. simpl. unfold lf_upd.
  destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)]; rewrite Hl.
  - apply (lfsoup_step_all N W T _ ev); [done|]. by rewrite lf_run_state_q.
  - destruct (lf_run_state N a0 r l k) as [q K] eqn:E. rewrite Heq.
    pose proof (lf_run_state_q N a0 r l k H0) as Hq. rewrite E in Hq. simpl in Hq. subst q. apply IH.
Qed.

(** Every configuration reachable by closed steps carries a soup at
    every index. *)
Theorem lfsoup_isteps N W T a q' :
  (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → itsteps (s_q a) q' →
  ∃ a', s_q a' = q' ∧ ∀ n, a' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof.
  intros Hs Hst. remember (s_q a) as q eqn:Hq. revert a Hq Hs.
  induction Hst as [q|q q1 q2 [ev H1] _ IH]; intros a Hq Hs.
  - by exists a.
  - subst q. apply (IH (lf_next N a ev q1)); [done|]. by apply lfsoup_step_all.
Qed.
