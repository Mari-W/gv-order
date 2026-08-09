(** * Milner's cyclic scheduler, with an agent that splices itself out

    The canonical example of a process that is deadlock free but that
    Curry-Howard session typing rejects.  Dardha and Gay use it to
    motivate priority-based typing (FoSSaCS 2018, Example 1), and state
    outright that it "is not typable in the original type systems by
    Caires-Pfenning and Wadler" — Wadler's system being the one GV♯
    refines.  Their argument is worth repeating: one could break the
    starting agent into two parallel halves to recover a tree, but that
    changes the design, and for a scheduler that runs a SECOND round
    the redesign is impossible, because the input that ends a round
    determines the output that begins the next.

    Here the ring is n = 3 and runs one round.  Agents [ag0] and [ag2]
    do the work; the middle agent [ag1] is a forwarder that splices its
    predecessor directly to its successor and drops out:

        ag0 ──r0── ag1 ──r1── ag2                ag1 ≜ link ⟨r1, r0⟩
         └───────── r2 ─────────┘

    Three threads on three channels is a cycle, so no P-Connect tree
    exists and the configuration is untypable.  It is deadlock free
    because [ag0] sends before it receives: reverse those two actions
    and the ring wedges (Dardha and Gay's Example 3, the deadlocked
    twin of their Example 2).

    The forwarding is what makes the topology collapse.  After [ag1]
    fires, its two channels are merged and it becomes ∗, leaving [ag0]
    and [ag2] sharing the merged channel and [r2] — two threads on two
    channels, which is exactly the minimal cyclic process of Dardha and
    Gay's Example 2.  The ring is untypable before the splice and still
    untypable after it. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import LogRel Compositionality Method.

Local Open Scope string_scope.

Definition r0 : chan := "r0".
Definition r1 : chan := "r1".
Definition r2 : chan := "r2".

(** ** The agents *)

(** clos (send ⟨∗, c⟩) — deliver the token on c and hang up. *)
Definition sendclose (c : chan) : expr :=
  App EClos (App ESend (Pair EUnit (Chan c))).

(** let ⟨x,d⟩ = recv c in let ∗ = x in clos d — collect and hang up. *)
Definition recvclose (c : chan) : expr :=
  LetP (App ERecv (Chan c)) (LetU (Var 1) (App EClos (Var 0))).

(** ag0 starts the round on r0, then waits for it to come back on r2. *)
Definition ag0 : expr := LetU (sendclose r0) (recvclose r2).

(** ag1 forwards between its two neighbours instead of relaying by
    hand: [link] merges r1 and r0 and retires the agent. *)
Definition ag1 : expr := App ELink (Pair (Chan r1) (Chan r0)).

(** ag2 waits on r1, then passes the token on to r2. *)
Definition ag2 : expr :=
  LetP (App ERecv (Chan r1))
       (LetU (Var 1) (LetU (App EClos (Var 0)) (sendclose r2))).

Definition sched : proc :=
  ({[r0; r1; r2]}, {[+ ag0 +]} ⊎ {[+ ag1 +]} ⊎ {[+ ag2 +]}).

(** ** The states after the splice

    The forwarding label is unordered, so either end may be retired.
    Both outcomes have the same shape with the surviving name [m], so
    the trace below is stated once and instantiated at [m = r0] and
    [m = r1]. *)

Definition a0_send (m : chan) : expr := LetU (sendclose m) (recvclose r2).
Definition a0_clos (m : chan) : expr :=
  LetU (App EClos (Chan m)) (recvclose r2).
Definition a0_beta : expr := LetU EUnit (recvclose r2).

Definition a2_recv (m : chan) : expr :=
  LetP (App ERecv (Chan m))
       (LetU (Var 1) (LetU (App EClos (Var 0)) (sendclose r2))).
Definition a2_pair (m : chan) : expr :=
  LetP (Pair EUnit (Chan m))
       (LetU (Var 1) (LetU (App EClos (Var 0)) (sendclose r2))).
Definition a2_unit (m : chan) : expr :=
  LetU EUnit (LetU (App EClos (Chan m)) (sendclose r2)).
Definition a2_clos (m : chan) : expr :=
  LetU (App EClos (Chan m)) (sendclose r2).
Definition a2_beta : expr := LetU EUnit (sendclose r2).

Definition a0_recvd : expr :=
  LetP (Pair EUnit (Chan r2)) (LetU (Var 1) (App EClos (Var 0))).
Definition a0_unit : expr := LetU EUnit (App EClos (Chan r2)).

Definition st (C : gset chan) (u v w : expr) : proc :=
  (C, {[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]}).

Definition p1 (m : chan) : proc :=
  st {[m; r2]} (a0_send m) EUnit (a2_recv m).
Definition p2 (m : chan) : proc :=
  st {[m; r2]} (a0_clos m) EUnit (a2_pair m).
Definition p3 (m : chan) : proc :=
  st {[m; r2]} (a0_clos m) EUnit (a2_unit m).
Definition p4 (m : chan) : proc :=
  st {[m; r2]} (a0_clos m) EUnit (a2_clos m).
Definition p5 : proc := st {[r2]} a0_beta EUnit a2_beta.
Definition p6a : proc := st {[r2]} (recvclose r2) EUnit a2_beta.
Definition p6b : proc := st {[r2]} a0_beta EUnit (sendclose r2).
Definition p7 : proc := st {[r2]} (recvclose r2) EUnit (sendclose r2).
Definition p8 : proc := st {[r2]} a0_recvd EUnit (App EClos (Chan r2)).
Definition p9 : proc := st {[r2]} a0_unit EUnit (App EClos (Chan r2)).
Definition p10 : proc :=
  st {[r2]} (App EClos (Chan r2)) EUnit (App EClos (Chan r2)).
Definition p11 : proc := st ∅ EUnit EUnit EUnit.

(** ** The trace

    Every step below is forced: at each state exactly one redex is
    enabled, except at [p5], where the two surviving agents each have
    an independent β to perform. *)

Lemma sched_splice_r0 : proc_step sched PTau (p1 r0).
Proof.
  unfold sched, p1, st.
  assert (({[r0; r1; r2]} : gset chan) ∖ {[r1]} = {[r0; r2]}) as <-
    by (clear; set_solver).
  replace ({[+ ag0 +]} ⊎ {[+ ag1 +]} ⊎ {[+ ag2 +]})
    with (({[+ ag0 +]} ⊎ {[+ ag2 +]}) ⊎ {[+ ag1 +]} : gmultiset expr)
    by multiset_solver.
  assert (echsubst r1 r0 ({[+ ag0 +]} ⊎ {[+ ag2 +]} ⊎ {[+ EUnit +]})
          = {[+ a0_send r0 +]} ⊎ {[+ EUnit +]} ⊎ {[+ a2_recv r0 +]}) as <-.
  { rewrite !echsubst_disj_union, !echsubst_singleton.
    unfold ag0, ag2, a0_send, a2_recv, sendclose, recvclose. simpl.
    multiset_solver. }
  apply (PStepLink _ _ _ r1 r0); [|clear; set_solver].
  apply TStepHead. apply HeadLink.
Qed.

Lemma sched_splice_r1 : proc_step sched PTau (p1 r1).
Proof.
  unfold sched, p1, st.
  assert (({[r0; r1; r2]} : gset chan) ∖ {[r0]} = {[r1; r2]}) as <-
    by (clear; set_solver).
  replace ({[+ ag0 +]} ⊎ {[+ ag1 +]} ⊎ {[+ ag2 +]})
    with (({[+ ag0 +]} ⊎ {[+ ag2 +]}) ⊎ {[+ ag1 +]} : gmultiset expr)
    by multiset_solver.
  assert (echsubst r0 r1 ({[+ ag0 +]} ⊎ {[+ ag2 +]} ⊎ {[+ EUnit +]})
          = {[+ a0_send r1 +]} ⊎ {[+ EUnit +]} ⊎ {[+ a2_recv r1 +]}) as <-.
  { rewrite !echsubst_disj_union, !echsubst_singleton.
    unfold ag0, ag2, a0_send, a2_recv, sendclose, recvclose. simpl.
    multiset_solver. }
  assert (({[r1; r0]} : gset chan) = {[r0; r1]}) as Hp by (clear; set_solver).
  apply (PStepLink _ _ _ r0 r1); [|clear; set_solver].
  apply TStepHead. rewrite <-Hp. apply HeadLink.
Qed.

(** *** Thread-level steps used by the trace *)

Lemma send_step m : tstep (a0_send m) (LSess (SSend m EUnit)) (a0_clos m).
Proof.
  apply TStepLetU. apply TStepAppR; [done|].
  apply TStepHead. apply (HeadSend EUnit m). done.
Qed.

Lemma recv_step m : tstep (a2_recv m) (LSess (SRecv m EUnit)) (a2_pair m).
Proof.
  apply TStepLetP. apply TStepHead. apply (HeadRecv m EUnit). done.
Qed.

Lemma a0_clos_step m : tstep (a0_clos m) (LSess (SClos m)) a0_beta.
Proof. apply TStepLetU. apply TStepHead. apply HeadClos. Qed.

Lemma a2_clos_step m : tstep (a2_clos m) (LSess (SClos m)) a2_beta.
Proof. apply TStepLetU. apply TStepHead. apply HeadClos. Qed.

Lemma a2_pair_step m : tstep (a2_pair m) LBeta (a2_unit m).
Proof. apply TStepHead. apply (HeadLetP EUnit (Chan m)); done. Qed.

Lemma a2_unit_step m : tstep (a2_unit m) LBeta (a2_clos m).
Proof. apply TStepHead. apply HeadLetU. Qed.

Lemma a0_beta_step : tstep a0_beta LBeta (recvclose r2).
Proof. apply TStepHead. apply HeadLetU. Qed.

Lemma a2_beta_step : tstep a2_beta LBeta (sendclose r2).
Proof. apply TStepHead. apply HeadLetU. Qed.

Lemma send2_step :
  tstep (sendclose r2) (LSess (SSend r2 EUnit)) (App EClos (Chan r2)).
Proof.
  apply TStepAppR; [done|]. apply TStepHead. apply (HeadSend EUnit r2). done.
Qed.

Lemma recv2_step :
  tstep (recvclose r2) (LSess (SRecv r2 EUnit)) a0_recvd.
Proof. apply TStepLetP. apply TStepHead. apply (HeadRecv r2 EUnit). done. Qed.

Lemma a0_recvd_step : tstep a0_recvd LBeta a0_unit.
Proof. apply TStepHead. apply (HeadLetP EUnit (Chan r2)); done. Qed.

Lemma a0_unit_step : tstep a0_unit LBeta (App EClos (Chan r2)).
Proof. apply TStepHead. apply HeadLetU. Qed.

Lemma clos2_step : tstep (App EClos (Chan r2)) (LSess (SClos r2)) EUnit.
Proof. apply TStepHead. apply HeadClos. Qed.

(** *** Lifting a thread step to the three-thread soup *)

Lemma st_beta1 C u v w u' :
  tstep u LBeta u' → proc_step (st C u v w) PTau (st C u' v w).
Proof.
  intros H. unfold st.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with (({[+ v +]} ⊎ {[+ w +]}) ⊎ {[+ u +]} : gmultiset expr)
    by multiset_solver.
  replace ({[+ u' +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with (({[+ v +]} ⊎ {[+ w +]}) ⊎ {[+ u' +]} : gmultiset expr)
    by multiset_solver.
  by apply PStepBeta.
Qed.

Lemma st_beta3 C u v w w' :
  tstep w LBeta w' → proc_step (st C u v w) PTau (st C u v w').
Proof.
  intros H. unfold st.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with (({[+ u +]} ⊎ {[+ v +]}) ⊎ {[+ w +]} : gmultiset expr)
    by multiset_solver.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w' +]})
    with (({[+ u +]} ⊎ {[+ v +]}) ⊎ {[+ w' +]} : gmultiset expr)
    by multiset_solver.
  by apply PStepBeta.
Qed.

Lemma st_msg C u v w u' w' c :
  tstep u (LSess (SSend c EUnit)) u' →
  tstep w (LSess (SRecv c EUnit)) w' →
  c ∈ C → proc_step (st C u v w) PTau (st C u' v w').
Proof.
  intros Hs Hr Hc. unfold st.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with ({[+ v +]} ⊎ {[+ u +]} ⊎ {[+ w +]} : gmultiset expr)
    by multiset_solver.
  replace ({[+ u' +]} ⊎ {[+ v +]} ⊎ {[+ w' +]})
    with ({[+ v +]} ⊎ {[+ u' +]} ⊎ {[+ w' +]} : gmultiset expr)
    by multiset_solver.
  by eapply PStepMsg.
Qed.

Lemma st_msg_r C u v w u' w' c :
  tstep w (LSess (SSend c EUnit)) w' →
  tstep u (LSess (SRecv c EUnit)) u' →
  c ∈ C → proc_step (st C u v w) PTau (st C u' v w').
Proof.
  intros Hs Hr Hc. unfold st.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with ({[+ v +]} ⊎ {[+ w +]} ⊎ {[+ u +]} : gmultiset expr)
    by multiset_solver.
  replace ({[+ u' +]} ⊎ {[+ v +]} ⊎ {[+ w' +]})
    with ({[+ v +]} ⊎ {[+ w' +]} ⊎ {[+ u' +]} : gmultiset expr)
    by multiset_solver.
  by eapply PStepMsg.
Qed.

Lemma st_close C u v w u' w' c :
  tstep u (LSess (SClos c)) u' →
  tstep w (LSess (SClos c)) w' →
  c ∈ C → proc_step (st C u v w) PTau (st (C ∖ {[c]}) u' v w').
Proof.
  intros Hs Hr Hc. unfold st.
  replace ({[+ u +]} ⊎ {[+ v +]} ⊎ {[+ w +]})
    with ({[+ v +]} ⊎ {[+ u +]} ⊎ {[+ w +]} : gmultiset expr)
    by multiset_solver.
  replace ({[+ u' +]} ⊎ {[+ v +]} ⊎ {[+ w' +]})
    with ({[+ v +]} ⊎ {[+ u' +]} ⊎ {[+ w' +]} : gmultiset expr)
    by multiset_solver.
  by eapply PStepClose.
Qed.

(** Closing a channel, with the resulting restricted set given
    explicitly so the caller never has to rewrite under a set literal. *)
Lemma st_close' C D u v w u' w' c :
  tstep u (LSess (SClos c)) u' →
  tstep w (LSess (SClos c)) w' →
  c ∈ C → D = C ∖ {[c]} →
  proc_step (st C u v w) PTau (st D u' v w').
Proof. intros Hs Hr Hc ->. by eapply st_close. Qed.

(** *** The round, step by step *)

Lemma step_p1 m : proc_step (p1 m) PTau (p2 m).
Proof.
  eapply st_msg; [apply send_step|apply recv_step|clear; set_solver].
Qed.

Lemma step_p2 m : proc_step (p2 m) PTau (p3 m).
Proof. apply st_beta3, a2_pair_step. Qed.

Lemma step_p3 m : proc_step (p3 m) PTau (p4 m).
Proof. apply st_beta3, a2_unit_step. Qed.

Lemma step_p4 m : m ≠ r2 → proc_step (p4 m) PTau p5.
Proof.
  intros Hm. unfold p4, p5.
  eapply st_close';
    [apply a0_clos_step|apply a2_clos_step
    |clear; set_solver|clear -Hm; set_solver].
Qed.

Lemma step_p5a : proc_step p5 PTau p6a.
Proof. apply st_beta1, a0_beta_step. Qed.

Lemma step_p5b : proc_step p5 PTau p6b.
Proof. apply st_beta3, a2_beta_step. Qed.

Lemma step_p6a : proc_step p6a PTau p7.
Proof. apply st_beta3, a2_beta_step. Qed.

Lemma step_p6b : proc_step p6b PTau p7.
Proof. apply st_beta1, a0_beta_step. Qed.

Lemma step_p7 : proc_step p7 PTau p8.
Proof.
  eapply st_msg_r; [apply send2_step|apply recv2_step|clear; set_solver].
Qed.

Lemma step_p8 : proc_step p8 PTau p9.
Proof. apply st_beta1, a0_recvd_step. Qed.

Lemma step_p9 : proc_step p9 PTau p10.
Proof. apply st_beta1, a0_unit_step. Qed.

Lemma step_p10 : proc_step p10 PTau p11.
Proof.
  unfold p10, p11.
  eapply st_close';
    [apply clos2_step|apply clos2_step|clear; set_solver|clear; set_solver].
Qed.

(** The round completes: no restricted names left, every thread ∗. *)
Theorem sched_terminates :
  ∃ q, rtc preduction sched q ∧ terminated q.
Proof.
  exists p11. split.
  - eapply rtc_l; [apply sched_splice_r0|].
    eapply rtc_l; [apply (step_p1 r0)|].
    eapply rtc_l; [apply (step_p2 r0)|].
    eapply rtc_l; [apply (step_p3 r0)|].
    eapply rtc_l; [apply (step_p4 r0); done|].
    eapply rtc_l; [apply step_p5a|].
    eapply rtc_l; [apply step_p6a|].
    eapply rtc_l; [apply step_p7|].
    eapply rtc_l; [apply step_p8|].
    eapply rtc_l; [apply step_p9|].
    eapply rtc_l; [apply step_p10|].
    apply rtc_refl.
  - exists EUnit, ({[+ EUnit +]} ⊎ {[+ EUnit +]}). split_and!.
    + unfold p11, st. f_equal. multiset_solver.
    + done.
    + intros e He. multiset_solver.
Qed.
