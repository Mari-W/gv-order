(** * The soup along runs (stage S8, proposal §2.12, stage 2 of 2026-11-21)

      lfsoup_step : a ∈ S^{N,W} _ α⟦∅ ⊢ T⟧ → itstep (s_q a) ev q' →
                    ∀ β < α, ∃ tc. tc ok ∧ lf_next tc a ev q' ∈ S^{N,W} _ β⟦∅ ⊢ T⟧

    The state after a step is a function of the state, the event, the
    next configuration and the tickets tc a creation chooses ([lf_next]).
    The choice is made at each level. A soup at every level picks one
    choice for every level by the existential property of the step
    index ([lfsoup_step_all], relation/ExProp.v), under excluded middle
    and functional choice as hypotheses. A soup at every level at the
    start of a run is then a soup at every level at every position of it,
    at the states the run and one choice per position compute
    ([lfsoup_run]). *)

From stdpp Require Import relations.
From GV Require Export relation.ExProp soup.SoupLink.

(** The tickets of a step that creates nothing. *)
Definition tc0 : fuel * fuel := (Some 0, Some 0).

Lemma tc0_ok N : tsum_ok (Some N) tc0.1 tc0.2.
Proof. unfold tsum_ok. simpl. lia. Qed.

Theorem lfsoup_step N W T a n ev q' :
  a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧ → itstep (s_q a) ev q' →
  ∀ lv, olt lv n → ∃ tc, tsum_ok (Some N) tc.1 tc.2 ∧ lf_next tc a ev q' ∈ S^{N,W} _ lv⟦∅ ⊢ T⟧.
Proof.
  destruct a as [[C Mq] K]. intros (A & Π & U & Hs) [Hst Hτ] lv Hlv. cbn [s_q] in Hst.
  inversion Hst as [C0 M0 i e e' Hi Hs'|C0 M0 i e ℓ c e' Hi Hs' HC Hc|C0 M0 i e κ o c e' Hi Hs' HC Hc
    |C0 M0 i j e v e' Hi Hs' Hj
    |C0 M0 i j o v e e' f f' Hij Hi Hj He Hf|C0 M0 i j o e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j o b e e' f f' Hij Hi Hj He Hf|C0 M0 i e o1 o2 e' Hi Hs' HC
    |C0 M0 i e σ e' Hi Hs' HC]; subst.
  - exists tc0. split; [apply tc0_ok|]. exists A, Π, U. exact (step_beta _ _ lv Hlv _ _ _ _ _ _ _ _ Hs i e e' Hi Hs').
  - destruct (step_new _ _ lv Hlv _ _ _ _ _ _ _ _ Hs i e ℓ c e' Hi Hs' HC) as (tn & A' & Π' & Htn & H).
    exists tn. split; [done|]. by exists A', Π', U.
  - destruct (step_new_at _ _ lv Hlv _ _ _ _ _ _ _ _ Hs i e κ o c e' Hi Hs' HC) as (tn & A' & Π' & Htn & H).
    exists tn. split; [done|]. by exists A', Π', U.
  - exists tc0. split; [apply tc0_ok|]. eexists _, _, _. exact (step_spawn _ _ lv Hlv _ _ _ _ _ _ _ _ Hs tc0 i j e v e' Hi Hs' Hj).
  - exists tc0. split; [apply tc0_ok|].
    destruct (step_msg _ _ lv Hlv _ _ _ _ _ _ _ _ Hs tc0 i j e e' f f' o v Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - exists tc0. split; [apply tc0_ok|].
    destruct (step_close _ _ lv Hlv _ _ _ _ _ _ _ _ Hs tc0 i j e e' f f' o Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - exists tc0. split; [apply tc0_ok|].
    destruct (step_choice _ _ lv Hlv _ _ _ _ _ _ _ _ Hs tc0 i j e e' f f' o b Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - exists tc0. split; [apply tc0_ok|].
    destruct (step_link _ _ lv Hlv _ _ _ _ _ _ _ _ Hs tc0 i e o1 o2 e' Hi Hs') as (A' & Π' & H).
    by exists A', Π', U.
  - by unfold ev_tau in Hτ.
Qed.

(** The soup is down-closed in the level. *)
Lemma Soup_down N W T a n m : ole m n → a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧ → a ∈ S^{N,W} _ m⟦∅ ⊢ T⟧.
Proof.
  intros Hm (A & Π & U & Hs). exists A, Π, U. constructor; try apply Hs.
  - intros t e He. eapply Erel_down; [exact Hm|]. by apply (sp_rel _ _ _ _ _ _ _ _ _ Hs).
  - intros t e He. eapply FuelE_down; [exact Hm|]. by apply (sp_fuel _ _ _ _ _ _ _ _ _ Hs).
Qed.

Section classical.
  Context (EM : excluded_middle) (FC : functional_choice).

  (** A soup at every index stays one along a step, at one choice of
      tickets for every index. *)
  Corollary lfsoup_step_all N W T a ev q' :
    (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → itstep (s_q a) ev q' →
    ∃ tc, tsum_ok (Some N) tc.1 tc.2 ∧ ∀ n, lf_next tc a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
  Proof.
    intros H Hst.
    destruct (exist_prop EM FC (fuel * fuel)
      (λ tc n, tsum_ok (Some N) tc.1 tc.2 ∧ lf_next tc a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧)) as (tc & Htc).
    - intros tc n1 n2 Hn [H1 H2]. split; [done|]. by eapply Soup_down.
    - intros n. apply (lfsoup_step N W T a (osucc n) ev q'); [apply H|done|apply olt_succ].
    - exists tc. split; [exact (proj1 (Htc ozero))|]. intros n. exact (proj2 (Htc n)).
  Qed.

  Lemma lf_run_state_q tcs a0 r l k : s_q a0 = r 0 → s_q (lf_run_state tcs a0 r l k) = r k.
  Proof. intros H0. destruct k as [|k]; [done|]. simpl. unfold lf_upd. by destruct (l k). Qed.

  (** One choice of tickets per position, read off the state at it. *)
  Theorem lfsoup_run N W T a0 r l :
    maximal r l → s_q a0 = r 0 → (∀ n, a0 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) →
    ∃ tcs, ∀ k n, lf_run_state tcs a0 r l k ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
  Proof.
    intros Hmax H0 Hs.
    assert (∀ ak : lfstate * nat, ∃ tc : fuel * fuel,
      (∀ n, ak.1 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → s_q ak.1 = r ak.2 →
      ∀ n, lf_upd tc ak.1 (l ak.2) (r (S ak.2)) ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) as Hch.
    { intros [a k]. simpl.
      destruct (EM ((∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) ∧ s_q a = r k)) as [[Ha Hq]|Hno];
        [|exists tc0; intros Ha Hq; by destruct Hno].
      destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)]; rewrite Hl.
      - rewrite <-Hq in Hst. destruct (lfsoup_step_all N W T a ev _ Ha Hst) as (tc & _ & Htc).
        exists tc. intros _ _. exact Htc.
      - exists tc0. intros _ _ n. simpl. destruct a as [q K]. simpl in Hq. subst q. rewrite Heq. apply Ha. }
    destruct (FC _ _ _ Hch) as [g Hg].
    set (st := fix st (k : nat) : lfstate :=
      match k with 0 => a0 | S k' => lf_upd (g (st k', k')) (st k') (l k') (r k) end).
    exists (λ k, g (st k, k)).
    assert (∀ k, lf_run_state (λ k, g (st k, k)) a0 r l k = st k) as Est.
    { induction k as [|k IH]; [done|]. simpl. by rewrite IH. }
    intros k. rewrite Est. induction k as [|k IH]; [done|].
    simpl. apply (Hg (st k, k)); [exact IH|].
    rewrite <-(Est k). by apply lf_run_state_q.
  Qed.

End classical.

(** Every configuration reachable by closed steps carries a soup at
    every index, chosen per index. *)
Theorem lfsoup_isteps N W T q q' :
  (∀ n, ∃ a, s_q a = q ∧ a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → itsteps q q' →
  ∀ n, ∃ a', s_q a' = q' ∧ a' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof.
  intros Hs Hst. revert Hs.
  induction Hst as [q|q q1 q2 [ev H1] _ IH]; intros Hs; [done|].
  apply IH. intros n. destruct (Hs (osucc n)) as (a & <- & Ha).
  destruct (lfsoup_step N W T a (osucc n) ev q1 Ha H1 n (olt_succ n)) as (tc & _ & Htc).
  by exists (lf_next tc a ev q1).
Qed.
