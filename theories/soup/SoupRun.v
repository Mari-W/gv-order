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

(** The choice of a step that creates nothing, in the world W. *)
Definition tc0 (W : world) : tchoice := TChoice (Some 0) (Some 0) (pvar 0) W.

Lemma tc0_ok N W : tsum_ok (Some N) (tc_m1 (tc0 W)) (tc_m2 (tc0 W)).
Proof. unfold tsum_ok. simpl. lia. Qed.

Theorem lfsoup_step N W T a n ev q' :
  a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧ → itstep (s_q a) ev q' →
  ∀ lv, olt lv n → ∃ tc, tsum_ok (Some N) (tc_m1 tc) (tc_m2 tc) ∧
    wext (s_W a) (s_W (lf_next tc a ev q')) ∧ lf_next tc a ev q' ∈ S^{N,W} _ lv⟦∅ ⊢ T⟧.
Proof.
  destruct a as [[C Mq] K Wa]. intros (HWa & A & Π & U & Hs) [Hst Hτ] lv Hlv. cbn [s_q s_W] in *.
  inversion Hst as [C0 M0 i α e e' Hi Hs' [-> | ->]|C0 M0 i e c e' Hi Hs' HC Hc
    |C0 M0 i j e v e' Hi Hs' Hj
    |C0 M0 i j o v e e' f f' Hij Hi Hj He Hf|C0 M0 i j o e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j o b e e' f f' Hij Hi Hj He Hf|C0 M0 i e o1 o2 e' Hi Hs' HC
    |C0 M0 i e σ e' Hi Hs' HC]; subst.
  3: { destruct (step_new _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs i e c e' Hi Hs' HC) as (tn & A' & Π' & Htn & HWn & H).
    exists tn. split; [done|]. split; [done|]. split; [by eapply wext_trans|]. by exists A', Π', U. }
  all: try (exists (tc0 Wa); split; [apply tc0_ok|]; split; [apply wext_refl|]; split; [done|]).
  - exists A, Π, U. exact (step_beta _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs i e e' Hi Hs').
  - exists A, Π, U. exact (step_force _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs i e e' Hi Hs').
  - eexists _, _, _. exact (step_spawn _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs (tc0 Wa) i j e v e' Hi Hs' Hj).
  - destruct (step_msg _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs (tc0 Wa) i j e e' f f' o v Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_close _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs (tc0 Wa) i j e e' f f' o Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_choice _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs (tc0 Wa) i j e e' f f' o b Hij Hi Hj He Hf) as (A' & Π' & H).
    by exists A', Π', U.
  - destruct (step_link _ _ lv Hlv _ _ _ _ _ _ _ _ _ Hs (tc0 Wa) i e o1 o2 e' Hi Hs') as (A' & Π' & H).
    by exists A', Π', U.
  - by unfold ev_tau in Hτ.
Qed.

(** The soup is down-closed in the level. *)
Lemma Soup_down N W T a n m : ole m n → a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧ → a ∈ S^{N,W} _ m⟦∅ ⊢ T⟧.
Proof.
  intros Hm (HW & A & Π & U & Hs). split; [done|]. exists A, Π, U. constructor; try apply Hs.
  - intros t e He. eapply Erel_down; [exact Hm|]. by apply (sp_rel _ _ _ _ _ _ _ _ _ _ Hs).
  - intros t e He. eapply FuelE_down; [exact Hm|]. by apply (sp_fuel _ _ _ _ _ _ _ _ _ _ Hs).
Qed.

Section classical.
  Context (EM : excluded_middle) (FC : functional_choice).

  (** A soup at every index stays one along a step, at one choice of
      tickets for every index. *)
  Corollary lfsoup_step_all N W T a ev q' :
    (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → itstep (s_q a) ev q' →
    ∃ tc, tsum_ok (Some N) (tc_m1 tc) (tc_m2 tc) ∧ wext (s_W a) (s_W (lf_next tc a ev q')) ∧
      ∀ n, lf_next tc a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
  Proof.
    intros H Hst.
    destruct (exist_prop EM FC tchoice
      (λ tc n, tsum_ok (Some N) (tc_m1 tc) (tc_m2 tc) ∧ wext (s_W a) (s_W (lf_next tc a ev q')) ∧
         lf_next tc a ev q' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧)) as (tc & Htc).
    - intros tc n1 n2 Hn (H1 & H2 & H3). split_and!; [done|done|]. by eapply Soup_down.
    - intros n. apply (lfsoup_step N W T a (osucc n) ev q'); [apply H|done|apply olt_succ].
    - exists tc. split_and!; [exact (proj1 (Htc ozero))|exact (proj1 (proj2 (Htc ozero)))|].
      intros n. exact (proj2 (proj2 (Htc n))).
  Qed.

  Lemma lf_run_state_q tcs a0 r l k : s_q a0 = r 0 → s_q (lf_run_state tcs a0 r l k) = r k.
  Proof. intros H0. destruct k as [|k]; [done|]. simpl. unfold lf_upd. by destruct (l k). Qed.

  (** One choice of tickets per position, read off the state at it. *)
  Theorem lfsoup_run N W T a0 r l :
    maximal r l → s_q a0 = r 0 → (∀ n, a0 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) →
    ∃ tcs, (∀ k n, lf_run_state tcs a0 r l k ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) ∧
      ∀ k, wext (s_W (lf_run_state tcs a0 r l k)) (s_W (lf_run_state tcs a0 r l (S k))).
  Proof.
    intros Hmax H0 Hs.
    assert (∀ ak : lfstate * nat, ∃ tc : tchoice,
      (∀ n, ak.1 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → s_q ak.1 = r ak.2 →
      wext (s_W ak.1) (s_W (lf_upd tc ak.1 (l ak.2) (r (S ak.2)))) ∧
      ∀ n, lf_upd tc ak.1 (l ak.2) (r (S ak.2)) ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) as Hch.
    { intros [a k]. simpl.
      destruct (EM ((∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) ∧ s_q a = r k)) as [[Ha Hq]|Hno];
        [|exists (tc0 (s_W a)); intros Ha Hq; by destruct Hno].
      destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)]; rewrite Hl.
      - rewrite <-Hq in Hst. destruct (lfsoup_step_all N W T a ev _ Ha Hst) as (tc & _ & HW & Htc).
        exists tc. intros _ _. split; [exact HW|exact Htc].
      - exists (tc0 (s_W a)). intros _ _. split; [apply wext_refl|]. intros n. simpl.
        destruct a as [q K Wa]. simpl in Hq. subst q. rewrite Heq. apply Ha. }
    destruct (FC _ _ _ Hch) as [g Hg].
    set (st := fix st (k : nat) : lfstate :=
      match k with 0 => a0 | S k' => lf_upd (g (st k', k')) (st k') (l k') (r k) end).
    exists (λ k, g (st k, k)).
    assert (∀ k, lf_run_state (λ k, g (st k, k)) a0 r l k = st k) as Est.
    { induction k as [|k IH]; [done|]. simpl. by rewrite IH. }
    assert (∀ k n, st k ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) as Hall.
    { intros k. induction k as [|k IH]; [done|].
      simpl. apply (Hg (st k, k)); [exact IH|].
      rewrite <-(Est k). by apply lf_run_state_q. }
    split; [intros k; rewrite Est; apply Hall|].
    intros k. rewrite !Est. simpl. apply (Hg (st k, k)); [apply Hall|].
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
  destruct (lfsoup_step N W T a (osucc n) ev q1 Ha H1 n (olt_succ n)) as (tc & _ & _ & Htc).
  by exists (lf_next tc a ev q1).
Qed.
