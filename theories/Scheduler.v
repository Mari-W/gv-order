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

(** ** Inversion: what each thread can do

    Every thread of every reachable configuration is one of the terms
    below, and each has exactly one possible transition (a receive is
    determined only up to the value it accepts).  These are what turn
    the trace above into an exhaustive description of the reachable
    set. *)

Ltac kill_val :=
  match goal with
  | Hs : tstep ?v _ _ |- _ =>
      exfalso; eapply val_no_tstep; [exact Hs|done]
  end.

Lemma inv_clos c α e' :
  tstep (App EClos (Chan c)) α e' → α = LSess (SClos c) ∧ e' = EUnit.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - kill_val.
  - kill_val.
Qed.

Lemma inv_sendapp c α e' :
  tstep (App ESend (Pair EUnit (Chan c))) α e' →
  α = LSess (SSend c EUnit) ∧ e' = Chan c.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - kill_val.
  - kill_val.
Qed.

Lemma inv_sendclose c α e' :
  tstep (sendclose c) α e' →
  α = LSess (SSend c EUnit) ∧ e' = App EClos (Chan c).
Proof.
  intros H. unfold sendclose in H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - kill_val.
  - match goal with Hs : tstep (App ESend _) _ _ |- _ =>
      apply inv_sendapp in Hs as [-> ->] end. done.
Qed.

Lemma inv_recvapp c α e' :
  tstep (App ERecv (Chan c)) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv c v) ∧ e' = Pair v (Chan c).
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    eauto.
  - kill_val.
  - kill_val.
Qed.

Lemma inv_letu_nonunit e1 e2 α e' :
  e1 ≠ EUnit →
  tstep (LetU e1 e2) α e' →
  ∃ e1', tstep e1 α e1' ∧ e' = LetU e1' e2.
Proof.
  intros Hne H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - eauto.
Qed.

Lemma inv_letu_unit e2 α e' :
  tstep (LetU EUnit e2) α e' → α = LBeta ∧ e' = e2.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - kill_val.
Qed.

Lemma inv_letp_pair u v e2 α e' :
  is_val u → is_val v →
  tstep (LetP (Pair u v) e2) α e' → α = LBeta ∧ e' = subst2 u v e2.
Proof.
  intros Hu Hv H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      exfalso; eapply val_no_tstep; [exact Hs|] end.
    simpl. by rewrite (is_val_true _ Hu), (is_val_true _ Hv).
Qed.

Lemma inv_letp_recv c e2 α e' :
  tstep (LetP (App ERecv (Chan c)) e2) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv c v) ∧ e' = LetP (Pair v (Chan c)) e2.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - match goal with Hs : tstep (App ERecv _) _ _ |- _ =>
      apply inv_recvapp in Hs as (v & Hv & -> & ->) end. eauto.
Qed.

Lemma inv_link α e' :
  tstep ag1 α e' → α = LSess (SLink {[r1; r0]}) ∧ e' = EUnit.
Proof.
  intros H. unfold ag1 in H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst end.
    done.
  - kill_val.
  - kill_val.
Qed.

(** *** The same, phrased for the named thread states *)

Lemma inv_a0_send m α e' :
  tstep (a0_send m) α e' → α = LSess (SSend m EUnit) ∧ e' = a0_clos m.
Proof.
  intros H. apply inv_letu_nonunit in H as (e1' & Hs & ->); [|done].
  apply inv_sendclose in Hs as [-> ->]. done.
Qed.

Lemma inv_a0_clos m α e' :
  tstep (a0_clos m) α e' → α = LSess (SClos m) ∧ e' = a0_beta.
Proof.
  intros H. apply inv_letu_nonunit in H as (e1' & Hs & ->); [|done].
  apply inv_clos in Hs as [-> ->]. done.
Qed.

Lemma inv_a0_beta α e' :
  tstep a0_beta α e' → α = LBeta ∧ e' = recvclose r2.
Proof. apply inv_letu_unit. Qed.

Lemma inv_recvclose c α e' :
  tstep (recvclose c) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv c v) ∧
       e' = LetP (Pair v (Chan c)) (LetU (Var 1) (App EClos (Var 0))).
Proof. apply inv_letp_recv. Qed.

Lemma inv_a0_recvd α e' :
  tstep a0_recvd α e' → α = LBeta ∧ e' = a0_unit.
Proof.
  intros H. apply inv_letp_pair in H as [-> ->]; [done|done|done].
Qed.

Lemma inv_a0_unit α e' :
  tstep a0_unit α e' → α = LBeta ∧ e' = App EClos (Chan r2).
Proof. apply inv_letu_unit. Qed.

Lemma inv_a2_recv m α e' :
  tstep (a2_recv m) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv m v) ∧
       e' = LetP (Pair v (Chan m))
              (LetU (Var 1) (LetU (App EClos (Var 0)) (sendclose r2))).
Proof. apply inv_letp_recv. Qed.

Lemma inv_a2_pair m α e' :
  tstep (a2_pair m) α e' → α = LBeta ∧ e' = a2_unit m.
Proof.
  intros H. apply inv_letp_pair in H as [-> ->]; [done|done|done].
Qed.

Lemma inv_a2_unit m α e' :
  tstep (a2_unit m) α e' → α = LBeta ∧ e' = a2_clos m.
Proof. apply inv_letu_unit. Qed.

Lemma inv_a2_clos m α e' :
  tstep (a2_clos m) α e' → α = LSess (SClos m) ∧ e' = a2_beta.
Proof.
  intros H. apply inv_letu_nonunit in H as (e1' & Hs & ->); [|done].
  apply inv_clos in Hs as [-> ->]. done.
Qed.

Lemma inv_a2_beta α e' :
  tstep a2_beta α e' → α = LBeta ∧ e' = sendclose r2.
Proof. apply inv_letu_unit. Qed.

(** *** Locating the acting thread in a three-thread soup *)

Lemma pair_inv (E : gmultiset expr) e x y :
  E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ y +]} →
  (e = x ∧ E = {[+ y +]}) ∨ (e = y ∧ E = {[+ x +]}).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    apply gmultiset_elem_of_singleton in He; subst;
    [left|right]; (split; [done|multiset_solver]).
Qed.

Lemma triple_inv (E : gmultiset expr) e x y z :
  E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} →
  (e = x ∧ E = {[+ y +]} ⊎ {[+ z +]})
  ∨ (e = y ∧ E = {[+ x +]} ⊎ {[+ z +]})
  ∨ (e = z ∧ E = {[+ x +]} ⊎ {[+ y +]}).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    [apply gmultiset_elem_of_disj_union in He as [He|He]|];
    apply gmultiset_elem_of_singleton in He; subst;
    [left|right; left|right; right]; (split; [done|multiset_solver]).
Qed.

Lemma triple_inv2 (E : gmultiset expr) e f x y z :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} →
  (e = x ∧ f = y ∧ E = {[+ z +]}) ∨ (e = x ∧ f = z ∧ E = {[+ y +]})
  ∨ (e = y ∧ f = x ∧ E = {[+ z +]}) ∨ (e = y ∧ f = z ∧ E = {[+ x +]})
  ∨ (e = z ∧ f = x ∧ E = {[+ y +]}) ∨ (e = z ∧ f = y ∧ E = {[+ x +]}).
Proof.
  intros Heq.
  assert (E ⊎ {[+ e +]} = ({[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]}) ∖ {[+ f +]})
    as Heq' by multiset_solver.
  assert (f ∈ ({[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} : gmultiset expr)) as Hf
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in Hf as [Hf|Hf];
    [apply gmultiset_elem_of_disj_union in Hf as [Hf|Hf]|];
    apply gmultiset_elem_of_singleton in Hf; subst;
    [ assert (E ⊎ {[+ e +]} = {[+ y +]} ⊎ {[+ z +]}) as He by multiset_solver
    | assert (E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ z +]}) as He by multiset_solver
    | assert (E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ y +]}) as He by multiset_solver ];
    (apply pair_inv in He as [[-> ->]|[-> ->]]).
  - right; right; left. done.
  - right; right; right; right; left. done.
  - left. done.
  - right; right; right; right; right. done.
  - right; left. done.
  - right; right; right; left. done.
Qed.

(** ** Closure of the reachable set

    [inv_act] reads off what the acting thread did.  Every thread of
    every reachable configuration is one of the named states, so after
    it fires the transition label is concrete and [simplify_eq] kills
    the rules that cannot have applied. *)

Ltac inv_act :=
  repeat match goal with
  | H : tstep EUnit _ _ |- _ => exfalso; eapply val_no_tstep; [exact H|done]
  | H : tstep ag1 _ _ |- _ => apply inv_link in H as [? ?]
  | H : tstep (a0_send _) _ _ |- _ => apply inv_a0_send in H as [? ?]
  | H : tstep (a0_clos _) _ _ |- _ => apply inv_a0_clos in H as [? ?]
  | H : tstep a0_beta _ _ |- _ => apply inv_a0_beta in H as [? ?]
  | H : tstep a0_recvd _ _ |- _ => apply inv_a0_recvd in H as [? ?]
  | H : tstep a0_unit _ _ |- _ => apply inv_a0_unit in H as [? ?]
  | H : tstep (a2_recv _) _ _ |- _ => apply inv_a2_recv in H as (? & ? & ? & ?)
  | H : tstep (a2_pair _) _ _ |- _ => apply inv_a2_pair in H as [? ?]
  | H : tstep (a2_unit _) _ _ |- _ => apply inv_a2_unit in H as [? ?]
  | H : tstep (a2_clos _) _ _ |- _ => apply inv_a2_clos in H as [? ?]
  | H : tstep a2_beta _ _ |- _ => apply inv_a2_beta in H as [? ?]
  | H : tstep (recvclose _) _ _ |- _ =>
      apply inv_recvclose in H as (? & ? & ? & ?)
  | H : tstep (sendclose _) _ _ |- _ => apply inv_sendclose in H as [? ?]
  | H : tstep (App EClos (Chan _)) _ _ |- _ => apply inv_clos in H as [? ?]
  end.

Ltac split1 :=
  match goal with
  | Heq : _ ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply triple_inv in Heq as [[-> ->]|[[-> ->]|[-> ->]]]
  end.

Ltac split2 :=
  match goal with
  | Heq : _ ⊎ {[+ _ +]} ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply triple_inv2 in Heq
        as [(->&->&->)|[(->&->&->)|[(->&->&->)|[(->&->&->)|[(->&->&->)|(->&->&->)]]]]]
  end.

(** A τ step of a three-thread soup is a β, a fork, a message, a close
    or a forwarding; the shape of the equation says how many threads
    took part. *)
Ltac st_cases Hst :=
  inversion Hst; subst;
  [ split1 | split1 | split2 | split2 | split1 ];
  inv_act; simplify_eq.

(** *** One characterisation per reachable configuration *)

Lemma inv_p2 m p' : preduction (p2 m) p' → p' = p3 m.
Proof.
  intros Hst. unfold preduction, p2, st in Hst. st_cases Hst.
  all: unfold p3, st; f_equal; multiset_solver.
Qed.

Lemma inv_p3 m p' : preduction (p3 m) p' → p' = p4 m.
Proof.
  intros Hst. unfold preduction, p3, st in Hst. st_cases Hst.
  all: unfold p4, st; f_equal; multiset_solver.
Qed.

Lemma inv_p6a p' : preduction p6a p' → p' = p7.
Proof.
  intros Hst. unfold preduction, p6a, st in Hst. st_cases Hst.
  all: unfold p7, st; f_equal; multiset_solver.
Qed.

Lemma inv_p6b p' : preduction p6b p' → p' = p7.
Proof.
  intros Hst. unfold preduction, p6b, st in Hst. st_cases Hst.
  all: unfold p7, st; f_equal; multiset_solver.
Qed.

Lemma inv_p8 p' : preduction p8 p' → p' = p9.
Proof.
  intros Hst. unfold preduction, p8, st in Hst. st_cases Hst.
  all: unfold p9, st; f_equal; multiset_solver.
Qed.

Lemma inv_p9 p' : preduction p9 p' → p' = p10.
Proof.
  intros Hst. unfold preduction, p9, st in Hst. st_cases Hst.
  all: unfold p10, st; f_equal; multiset_solver.
Qed.

Lemma inv_p11 p' : preduction p11 p' → False.
Proof.
  intros Hst. unfold preduction, p11, st in Hst. st_cases Hst.
Qed.

Lemma inv_p1 m p' : preduction (p1 m) p' → p' = p2 m.
Proof.
  intros Hst. unfold preduction, p1, st in Hst. st_cases Hst.
  all: unfold p2, st; f_equal; multiset_solver.
Qed.

Lemma inv_p7 p' : preduction p7 p' → p' = p8.
Proof.
  intros Hst. unfold preduction, p7, st in Hst. st_cases Hst.
  all: unfold p8, st; f_equal; multiset_solver.
Qed.

Lemma inv_p4 m p' : m ≠ r2 → preduction (p4 m) p' → p' = p5.
Proof.
  intros Hm Hst. unfold preduction, p4, st in Hst. st_cases Hst.
  all: unfold p5, st; f_equal;
       first [ clear -Hm; set_solver | multiset_solver ].
Qed.

Lemma inv_p10 p' : preduction p10 p' → p' = p11.
Proof.
  intros Hst. unfold preduction, p10, st in Hst. st_cases Hst.
  all: unfold p11, st; f_equal;
       first [ clear; set_solver | multiset_solver ].
Qed.

Lemma inv_p5 p' : preduction p5 p' → p' = p6a ∨ p' = p6b.
Proof.
  intros Hst. unfold preduction, p5, st in Hst. st_cases Hst.
  all: first [ left; unfold p6a, st; f_equal; multiset_solver
             | right; unfold p6b, st; f_equal; multiset_solver ].
Qed.

(** *** The splice itself

    The forwarding label is unordered and both ends are restricted, so
    P-Act-Link applies in two ways; the two results are the same
    configuration with the roles of r0 and r1 exchanged. *)

Lemma splice_eq_r0 :
  echsubst r1 r0 ({[+ ag0 +]} ⊎ {[+ ag2 +]} ⊎ {[+ EUnit +]})
  = {[+ a0_send r0 +]} ⊎ {[+ EUnit +]} ⊎ {[+ a2_recv r0 +]}.
Proof.
  rewrite !echsubst_disj_union, !echsubst_singleton.
  unfold ag0, ag2, a0_send, a2_recv, sendclose, recvclose. simpl.
  multiset_solver.
Qed.

Lemma splice_eq_r1 :
  echsubst r0 r1 ({[+ ag0 +]} ⊎ {[+ ag2 +]} ⊎ {[+ EUnit +]})
  = {[+ a0_send r1 +]} ⊎ {[+ EUnit +]} ⊎ {[+ a2_recv r1 +]}.
Proof.
  rewrite !echsubst_disj_union, !echsubst_singleton.
  unfold ag0, ag2, a0_send, a2_recv, sendclose, recvclose. simpl.
  multiset_solver.
Qed.

Ltac inv_act_sched :=
  repeat match goal with
  | H : tstep ag0 _ _ |- _ => apply (inv_a0_send r0) in H as [? ?]
  | H : tstep ag1 _ _ |- _ => apply inv_link in H as [? ->]
  | H : tstep ag2 _ _ |- _ => apply (inv_a2_recv r1) in H as (? & ? & ? & ?)
  end.

Lemma inv_sched p' : preduction sched p' → p' = p1 r0 ∨ p' = p1 r1.
Proof.
  intros Hst. unfold preduction, sched in Hst.
  inversion Hst; subst.
  - (* β: every thread's redex is a communication *)
    exfalso. split1; inv_act_sched; simplify_eq.
  - (* fork *)
    exfalso. split1; inv_act_sched; simplify_eq.
  - (* message: ag0 offers on r0 and ag2 on r1, never the same channel *)
    exfalso. split2; inv_act_sched; simplify_eq.
  - (* close: no thread is closing *)
    exfalso. split2; inv_act_sched; simplify_eq.
  - (* the splice *)
    split1; inv_act_sched; [exfalso; simplify_eq| |exfalso; simplify_eq].
    match goal with
    | |- (_ ∖ {[?c]}, echsubst ?c ?d _) = _ ∨ _ =>
        assert (({[c; d]} : gset chan) = {[r1; r0]}) as Hcd by congruence;
        assert (c ≠ d) as Hne
          by (intros Heq; rewrite Heq in Hcd;
              assert (r1 ∈ ({[d; d]} : gset chan)) as Hin1
                by (rewrite Hcd; clear; set_solver);
              assert (r0 ∈ ({[d; d]} : gset chan)) as Hin2
                by (rewrite Hcd; clear; set_solver);
              clear -Hin1 Hin2; set_solver)
    end.
    destruct (upair_eq_inv _ _ _ _ Hcd Hne) as [[-> ->]|[-> ->]].
    + left. unfold p1, st. rewrite splice_eq_r0.
      f_equal; clear; set_solver.
    + right. unfold p1, st. rewrite splice_eq_r1.
      f_equal; clear; set_solver.
Qed.

(** ** Deadlock freedom

    The reachable set.  The four states between the splice and the
    first close are parametrised by the surviving name, since either
    end of the forwarding may be retired. *)

Definition schedI (p : proc) : Prop :=
  p = sched
  ∨ (∃ m, (m = r0 ∨ m = r1) ∧
          (p = p1 m ∨ p = p2 m ∨ p = p3 m ∨ p = p4 m))
  ∨ p = p5 ∨ p = p6a ∨ p = p6b ∨ p = p7
  ∨ p = p8 ∨ p = p9 ∨ p = p10 ∨ p = p11.

Ltac schedI_cases Hp :=
  destruct Hp as [-> | [(m & Hm & [-> | [-> | [-> | ->]]])
    | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].

(** Every thread mentions only restricted channels. *)
Lemma schedI_echans p : schedI p → echans p.2 ⊆ p.1.
Proof.
  intros Hp. schedI_cases Hp.
  all: unfold sched, p1, p2, p3, p4, p5, p6a, p6b, p7, p8, p9, p10, p11, st;
       simpl; rewrite !echans_disj_union, !echans_singleton;
       unfold ag0, ag1, ag2, a0_send, a0_clos, a0_beta, a0_recvd, a0_unit,
              a2_recv, a2_pair, a2_unit, a2_clos, a2_beta,
              sendclose, recvclose;
       simpl; clear; set_solver.
Qed.

(** Only the final state is irreducible, and it has released both
    channels and reduced every thread to ∗. *)
Lemma schedI_irred p :
  schedI p → pirred p → p.1 = ∅ ∧ p.2 ≠ ∅ ∧ (∀ e, e ∈ p.2 → e = EUnit).
Proof.
  intros Hp Hirr. schedI_cases Hp.
  - exfalso. eapply (Hirr PTau). apply sched_splice_r0.
  - exfalso. eapply (Hirr PTau). apply (step_p1 m).
  - exfalso. eapply (Hirr PTau). apply (step_p2 m).
  - exfalso. eapply (Hirr PTau). apply (step_p3 m).
  - exfalso. eapply (Hirr PTau). apply (step_p4 m).
    destruct Hm as [-> | ->]; done.
  - exfalso. eapply (Hirr PTau). apply step_p5a.
  - exfalso. eapply (Hirr PTau). apply step_p6a.
  - exfalso. eapply (Hirr PTau). apply step_p6b.
  - exfalso. eapply (Hirr PTau). apply step_p7.
  - exfalso. eapply (Hirr PTau). apply step_p8.
  - exfalso. eapply (Hirr PTau). apply step_p9.
  - exfalso. eapply (Hirr PTau). apply step_p10.
  - unfold p11, st. simpl. split_and!.
    + done.
    + multiset_solver.
    + intros e He. multiset_solver.
Qed.

(** Membership in the reachable set, for the non-parametric states. *)
Ltac inI := unfold schedI; repeat (first [ by left | right ]); try done.

Ltac inIm m := unfold schedI; right; left; exists m; split;
               [ first [ assumption | by left | by right ] | ];
               repeat (first [ by left | right ]); try done.

Lemma schedI_step p p' : schedI p → preduction p p' → schedI p'.
Proof.
  intros Hp Hst. schedI_cases Hp.
  - apply inv_sched in Hst as [-> | ->].
    + inIm r0.
    + inIm r1.
  - apply inv_p1 in Hst as ->. inIm m.
  - apply inv_p2 in Hst as ->. inIm m.
  - apply inv_p3 in Hst as ->. inIm m.
  - apply inv_p4 in Hst as ->; [inI|destruct Hm as [-> | ->]; done].
  - apply inv_p5 in Hst as [-> | ->]; inI.
  - apply inv_p6a in Hst as ->. inI.
  - apply inv_p6b in Hst as ->. inI.
  - apply inv_p7 in Hst as ->. inI.
  - apply inv_p8 in Hst as ->. inI.
  - apply inv_p9 in Hst as ->. inI.
  - apply inv_p10 in Hst as ->. inI.
  - exfalso. by eapply inv_p11.
Qed.

Lemma schedI_closed : closed_invariant schedI.
Proof.
  intros p Hp. split_and!.
  - by apply schedI_echans.
  - by apply schedI_irred.
  - intros p' Hst. by eapply schedI_step.
Qed.

(** The cyclic scheduler is deadlock free, though no P-Connect tree
    types it. *)
Theorem sched_deadlock_free : deadlock_free sched.
Proof. eapply closed_deadlock_free; [exact schedI_closed|by left]. Qed.

(** …and semantically well typed at the empty interface, so it can be
    composed with syntactically typed code by the semantic P-Connect. *)
Corollary sched_sem_ptyped : sem_ptyped ∅ sched TUnit.
Proof. eapply sem_ptyped_closed; [exact schedI_closed|by left]. Qed.
