(** * Milner's cyclic scheduler of Dardha and Gay: typable

    Example 1 of Dardha and Gay (dardha2018new p. 3), the whole program,
    with k = 3 agents. Each agent A_i sits on a ring and has a spoke to
    its own collector P_i.

      Sched = (ν a_i b_i)(ν c_i d_{(i+1) mod 3})
                (A_0 | A_1 | A_2 | P_0 | P_1 | P_2)
      A_0 = c_0[n_0]. d_0(x_0). a_0[m_0]. close_0
      A_i = d_i(x_i). a_i[m_i]. c_i[n_i]. close_i     for 0 < i < 3
      P_i = b_i(y_i). Q_i

    A_0 starts the round by sending on c_0, waits for the token on d_0,
    reports to its collector on a_0 and stops. Every other agent waits
    on d_i, reports on a_i and passes the token on c_i. The ring is
    closed by c_i and d_{(i+1) mod 3} being the two ends of one channel,
    so A_0 reads on d_0 what A_2 wrote on c_2.

    Here:

      A_0 = let () = close (send ⟨∗, c_0⟩) in                      (main)
            let () = recvclose d_0 in close (send ⟨∗, a_0⟩)
      A_i = let () = recvclose d_i in                              (spawned)
            let () = close (send ⟨∗, a_i⟩) in close (send ⟨∗, c_i⟩)
      P_i = recvclose b_i                                          (spawned)
      recvclose r = let (x, r) = recv r in let () = x in close r

      c_i, a_i : (!∗.Close)@…        d_i, b_i : (?∗.Close)@…

    Simplifications. The calculus has no integers, so the token n_i, the
    result m_i and the received values x_i, y_i are ∗ and the message
    types are !∗.Close and ?∗.Close. The continuation Q_i of a collector
    is ∗, so P_i reads the result and closes. Dardha and Gay's close_i
    is the session end, which here is the [close] after each
    communication. The program runs one round, as theirs does.

    Points. The six channels sit at the points of one root. The first
    [new] creates the ring channel of A_0 at a fresh ι with the empty
    creation constraint, and every later channel is created by
    [t_new_at] at ι+2k, a point the hypothesis of the first [new] makes
    known. Reading the two ends of a channel as one point:

      c_0, d_1 : ι      a_1, b_1 : ι+2    c_1, d_2 : ι+4
      a_2, b_2 : ι+6    c_2, d_0 : ι+8    a_0, b_0 : ι+10

    Every fact the derivation needs is ι+j ≺ ι+k with j < k, which
    program order gives ([slt_po_lt]). This is the order of Dardha and
    Gay's priorities for Sched (dardha2018new p. 9), which for k = 3
    reads d_1 : 0, a_1 : 1, c_1 : 2, d_2 : 2, a_2 : 3, c_2 : 4, d_0 : 4,
    a_0 : 5, with c_0 : 0 and b_i at the priority of a_i. Two of their
    priorities coincide for the two ends of one channel, and one point
    here carries both ends.

    The reversed agent is rejected. If A_0 waits on d_0 before sending
    on c_0 the derivation asks ι+8 ≺ ι, while A_1 asks ι ≺ ι+4 and A_2
    asks ι+4 ≺ ι+8, and the three give a cycle.

    examples/Scheduler.v has a reduced variant, three agents without
    collectors and one of them a [link]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** The agents. The innermost body of the six [new]s sees
    b_0 at 0, a_0 at 1, d_0 at 2, c_2 at 3, b_2 at 4, a_2 at 5,
    d_2 at 6, c_1 at 7, b_1 at 8, a_1 at 9, d_1 at 10, c_0 at 11.
    A thunk shifts them all by one. *)

Definition ms_ag1 : expr :=
  Lam (LetU (Var 0)
    (LetU (recvclose (Var 11)) (LetU (sendclose (Var 10)) (sendclose (Var 8))))).

Definition ms_ag2 : expr :=
  Lam (LetU (Var 0)
    (LetU (recvclose (Var 7)) (LetU (sendclose (Var 6)) (sendclose (Var 4))))).

Definition ms_col0 : expr := Lam (LetU (Var 0) (recvclose (Var 1))).
Definition ms_col1 : expr := Lam (LetU (Var 0) (recvclose (Var 9))).
Definition ms_col2 : expr := Lam (LetU (Var 0) (recvclose (Var 5))).

Definition ms_ag0 : expr :=
  LetU (sendclose (Var 11)) (LetU (recvclose (Var 2)) (sendclose (Var 1))).

Definition ms_main : expr :=
  let_new_pair (let_new_pair (let_new_pair (let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ms_ag1)
      (LetU (App ESpawn ms_ag2)
        (LetU (App ESpawn ms_col0)
          (LetU (App ESpawn ms_col1)
            (LetU (App ESpawn ms_col2) ms_ag0)))))))))).

(** A send and a close on one channel at (0, j), inside a λ whose upper
    point is (0, u). *)
Ltac ms_send HW j u :=
  unfold sendclose; tstep;
  [ tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 j)); cbn; set_solver|done|];
    po_gate HW (pv 0 u)
  | apply KTClos
  | done
  | po_gate HW (pv 0 u) ].

(** A receive and a close on one channel, inside such a λ. *)
Ltac ms_recv HW u :=
  unfold recvclose; tstep;
  [ tstep; [tstep|apply KTRecv|kscope|]; po_gate HW (pv 0 u)
  | cbn; tstep; [tstep|]; cbn; tstep; [tstep|apply KTClos|done|];
    po_gate HW (pv 0 u) ].

Lemma ms_typed W : strict W → typed W ∅ [] ∅ [] (∅, None) ms_main TUnit.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold ms_main.
  (* the ring channel of A_0 at a fresh ι, then five channels at ι+2k *)
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sd [] []); [constructor|set_solver|].
  fresh_clean.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pv 0 2) HWs);
    [eapply skn_inst; [by left|by left|done]|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pv 0 4) HWs);
    [eapply skn_inst; [by left|by left|done]|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pv 0 6) HWs);
    [eapply skn_inst; [by left|by left|done]|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pv 0 8) HWs);
    [eapply skn_inst; [by left|by left|done]|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (pv 0 10) HWs);
    [eapply skn_inst; [by left|by left|done]|]. cbn.
  (* A_1: recv d_1 at ι, send a_1 at ι+2, send c_1 at ι+4 *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 5)) (Some (pv 0 0)) 0);
      [set_solver|lb_po HW|].
    cbn. tstep; [tstep|]. cbn. tstep; [ms_recv HW 5|].
    cbn. tstep; [ms_send HW 2 5|ms_send HW 4 5]. }
  (* A_2: recv d_2 at ι+4, send a_2 at ι+6, send c_2 at ι+8 *)
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 9)) (Some (pv 0 4)) 0);
      [set_solver|lb_po HW|].
    cbn. tstep; [tstep|]. cbn. tstep; [ms_recv HW 9|].
    cbn. tstep; [ms_send HW 6 9|ms_send HW 8 9]. }
  (* the collectors: recv b_i *)
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 11)) (Some (pv 0 10)) 0);
      [set_solver|lb_po HW|].
    cbn. tstep; [tstep|]. cbn. ms_recv HW 11. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 3)) (Some (pv 0 2)) 0);
      [set_solver|lb_po HW|].
    cbn. tstep; [tstep|]. cbn. ms_recv HW 3. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 7)) (Some (pv 0 6)) 0);
      [set_solver|lb_po HW|].
    cbn. tstep; [tstep|]. cbn. ms_recv HW 7. }
  (* A_0: send c_0 at ι, recv d_0 at ι+8, send a_0 at ι+10 *)
  cbn. unfold ms_ag0. tstep.
  { unfold sendclose. tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)); cbn; set_solver|done|].
      po_gate0 HW.
    - apply KTClos.
    - done.
    - po_gate0 HW. }
  cbn. tstep.
  { unfold recvclose. tstep.
    - tstep; [tstep|apply KTRecv|kscope|]. po_gate0 HW.
    - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|]. po_gate0 HW. }
  cbn. unfold sendclose. tstep.
  - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 10)); cbn; set_solver|done|].
    po_gate0 HW.
  - apply KTClos.
  - done.
  - po_gate0 HW.
Qed.

Theorem ms_deadlock_free : deadlock_free (∅, {[+ ms_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply ms_typed, Wpo_strict.
Qed.
