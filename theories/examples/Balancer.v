(** * The load balancer (Examples 2.10 and 3.16)

    lb replies to requests on a channel c shared with the environment
    by delegating the two expected answers to two forked workers. It
    violates linearity in several ways at once — the server and both
    workers hold c, and there is a genuine race on c when both workers
    are ready to answer — so it is untypable; but every interleaving
    is compatible with the interface, and it is in the logical
    relation at c : ?∗.!∗.!∗.Close directly ([lb_sem_ptyped]).
    Composed with the syntactically typable client q via semantic
    P-Connect, the closed composite is deadlock free
    ([lb_deadlock_free]).

    This is the paper's example of liberality on the *external*
    interface, as opposed to Scheduler.v, which is closed and makes
    the point about cyclic topology instead.

    Sugar: [let x = e1 in e2] is [App (Lam e2) e1]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import Terms Fundamental Invariant Support.

Local Open Scope string_scope.

(** ** Definitions (Example 2.10)

    worker := λs. let ⟨m,s⟩ = recv s in let ∗ = m in
                  let c' = send ⟨∗,c⟩ in clos s
    srv    := let ⟨m,c'⟩ = recv c in let ∗ = m in
              let w1' = send ⟨∗,w1⟩ in let w2' = send ⟨∗,w2⟩ in
              let ∗ = clos w1' in let ∗ = clos w2' in clos c'
    lb     := let w1 = fork worker in let w2 = fork worker in srv *)

(** The worker continuation after the receive: m = Var 1, s' = Var 0. *)
Definition wK : expr :=
  LetU (Var 1)
    (App (Lam (App EClos (Var 1)))
         (App ESend (Pair EUnit (Chan "c")))).

Definition worker : expr :=
  Lam (LetP (App ERecv (Var 0)) wK).

(** srv with w1 = Var 1, w2 = Var 0 (bound by the outer sugar-lets). *)
Definition srv2 : expr :=
  LetP (App ERecv (Chan "c"))
    (* binders: c' = Var 0, m = Var 1; hence w2 = Var 2, w1 = Var 3 *)
    (LetU (Var 1)
       (App (Lam
          (* w1' = Var 0, c' = Var 1, w2 = Var 3, w1 = Var 4 *)
          (App (Lam
             (* w2' = Var 0, w1' = Var 1, c' = Var 2 *)
             (LetU (App EClos (Var 1))
                (LetU (App EClos (Var 0))
                   (App EClos (Var 2)))))
             (App ESend (Pair EUnit (Var 3)))))   (* send to w2 *)
          (App ESend (Pair EUnit (Var 3))))).      (* send to w1 *)

Definition lb : expr :=
  App (Lam (App (Lam srv2) (App EFork worker)))
      (App EFork worker).

(** The typable client q (for the P-Connect composition):
    q := let c1 = send ⟨∗,c⟩ in let ⟨m,c2⟩ = recv c1 in let ∗ = m in
         let ⟨m,c3⟩ = recv c2 in let ∗ = m in clos c3 *)
Definition q : expr :=
  App (Lam
     (LetP (App ERecv (Var 0))
        (LetU (Var 1)
           (LetP (App ERecv (Var 0))
              (LetU (Var 1) (App EClos (Var 0)))))))
    (App ESend (Pair EUnit (Chan "c"))).

(** The session type of c on the lb side, and its stages. *)
Definition Slb : sty := SRcv TUnit (SSnd TUnit (SSnd TUnit SEnd)).

(** ** Thread stages

    Worker thread on channel x (fchans ⊆ {x, c}):
    - [wk0]: forked, not yet applied
    - [wk1]: receive on x in evaluation position
    - [wk2]: received ⟨∗, x⟩ (post-message redex)
    - [wk3]: let ∗ = ∗ β-redex
    - [wk4]: send on c in evaluation position (external)
    - [wk5]: send done, β-redex
    - [wk6]: close on x in evaluation position (internal, with srv) *)
Definition wk0 (x : chan) : expr := App worker (Chan x).
Definition wk1 (x : chan) : expr := LetP (App ERecv (Chan x)) wK.
Definition wk2 (x : chan) : expr := LetP (Pair EUnit (Chan x)) wK.
Definition wk3 (x : chan) : expr :=
  LetU EUnit
    (App (Lam (App EClos (Chan x)))
         (App ESend (Pair EUnit (Chan "c")))).
Definition wk4 (x : chan) : expr :=
  App (Lam (App EClos (Chan x)))
      (App ESend (Pair EUnit (Chan "c"))).
Definition wk5 (x : chan) : expr :=
  App (Lam (App EClos (Chan x))) (Chan "c").
Definition wk6 (x : chan) : expr := App EClos (Chan x).

(** srv thread stages after both forks (parametric in w1 w2).

    The two-send continuation with c', w1' instantiated step by step:
    - [sv0]: receive on c in evaluation position (external)
    - [sv1]: received ⟨∗, c⟩
    - [sv2]: let ∗ = ∗ β-redex
    - [sv3]: send on w1 in evaluation position (internal)
    - [sv4]: send-to-w1 done, β-redex
    - [sv5]: send on w2 in evaluation position (internal)
    - [sv6]: send-to-w2 done, β-redex
    - [sv7]: close w1 in evaluation position (internal)
    - [sv8]: let ∗ = ∗ β-redex
    - [sv9]: close w2 in evaluation position (internal)
    - [sv10]: let ∗ = ∗ β-redex
    - [sv11]: close c in evaluation position (external) *)

(** Body of srv after the receive, with c' = Var 0, m = Var 1
    (w1, w2 already substituted). *)
Definition svA (w1 w2 : chan) : expr :=
  LetU (Var 1)
    (App (Lam
       (App (Lam
          (LetU (App EClos (Var 1))
             (LetU (App EClos (Var 0))
                (App EClos (Var 2)))))
          (App ESend (Pair EUnit (Chan w2)))))
       (App ESend (Pair EUnit (Chan w1)))).

Definition sv0 (w1 w2 : chan) : expr :=
  LetP (App ERecv (Chan "c")) (svA w1 w2).
Definition sv1 (w1 w2 : chan) : expr :=
  LetP (Pair EUnit (Chan "c")) (svA w1 w2).
(** After the LetP β: c' ↦ Chan "c", m ↦ ∗. *)
Definition sv2 (w1 w2 : chan) : expr :=
  LetU EUnit
    (App (Lam
       (App (Lam
          (LetU (App EClos (Var 1))
             (LetU (App EClos (Var 0))
                (App EClos (Chan "c")))))
          (App ESend (Pair EUnit (Chan w2)))))
       (App ESend (Pair EUnit (Chan w1)))).
Definition sv3 (w1 w2 : chan) : expr :=
  App (Lam
     (App (Lam
        (LetU (App EClos (Var 1))
           (LetU (App EClos (Var 0))
              (App EClos (Chan "c")))))
        (App ESend (Pair EUnit (Chan w2)))))
    (App ESend (Pair EUnit (Chan w1))).
Definition sv4 (w1 w2 : chan) : expr :=
  App (Lam
     (App (Lam
        (LetU (App EClos (Var 1))
           (LetU (App EClos (Var 0))
              (App EClos (Chan "c")))))
        (App ESend (Pair EUnit (Chan w2)))))
    (Chan w1).
(** After the w1' β: w1' ↦ Chan w1. *)
Definition sv5 (w1 w2 : chan) : expr :=
  App (Lam
     (LetU (App EClos (Chan w1))
        (LetU (App EClos (Var 0))
           (App EClos (Chan "c")))))
    (App ESend (Pair EUnit (Chan w2))).
Definition sv6 (w1 w2 : chan) : expr :=
  App (Lam
     (LetU (App EClos (Chan w1))
        (LetU (App EClos (Var 0))
           (App EClos (Chan "c")))))
    (Chan w2).
Definition sv7 (w1 w2 : chan) : expr :=
  LetU (App EClos (Chan w1))
    (LetU (App EClos (Chan w2)) (App EClos (Chan "c"))).
Definition sv8 (w1 w2 : chan) : expr :=
  LetU EUnit
    (LetU (App EClos (Chan w2)) (App EClos (Chan "c"))).
Definition sv9 (w1 w2 : chan) : expr :=
  LetU (App EClos (Chan w2)) (App EClos (Chan "c")).
Definition sv10 (w1 w2 : chan) : expr :=
  LetU EUnit (App EClos (Chan "c")).
Definition sv11 (w1 w2 : chan) : expr := App EClos (Chan "c").

(** ** Sanity: the substitution arithmetic is right.

    Head β of the applied worker yields the receive-ready stage;
    receiving the signal and reducing yields the send stage; and the
    initial process forks and βs to ⟨sv0, wk0, wk0⟩. *)

Lemma wk0_step x : tstep (wk0 x) LBeta (wk1 x).
Proof.
  apply TStepHead.
  apply (HeadApp (LetP (App ERecv (Var 0)) wK) (Chan x) I).
Qed.

Lemma wk2_step x : tstep (wk2 x) LBeta (wk3 x).
Proof.
  apply TStepHead.
  apply (HeadLetP EUnit (Chan x) wK I I).
Qed.

Lemma wk5_step x : tstep (wk5 x) LBeta (wk6 x).
Proof.
  apply TStepHead.
  apply (HeadApp (App EClos (Chan x)) (Chan "c") I).
Qed.

Lemma sv1_step w1 w2 : tstep (sv1 w1 w2) LBeta (sv2 w1 w2).
Proof.
  apply TStepHead.
  apply (HeadLetP EUnit (Chan "c") (svA w1 w2) I I).
Qed.

Lemma sv2_step w1 w2 : tstep (sv2 w1 w2) LBeta (sv3 w1 w2).
Proof. apply TStepHead, HeadLetU. Qed.

Lemma sv4_step w1 w2 : tstep (sv4 w1 w2) LBeta (sv5 w1 w2).
Proof.
  assert (sv5 w1 w2 = subst1 (Chan w1)
    (App (Lam
       (LetU (App EClos (Var 1))
          (LetU (App EClos (Var 0)) (App EClos (Chan "c")))))
       (App ESend (Pair EUnit (Chan w2))))) as -> by reflexivity.
  apply TStepHead, (HeadApp _ (Chan w1) I).
Qed.

Lemma sv6_step w1 w2 : tstep (sv6 w1 w2) LBeta (sv7 w1 w2).
Proof.
  assert (sv7 w1 w2 = subst1 (Chan w2)
    (LetU (App EClos (Chan w1))
       (LetU (App EClos (Var 0)) (App EClos (Chan "c"))))) as ->
    by reflexivity.
  apply TStepHead, (HeadApp _ (Chan w2) I).
Qed.

Lemma lb_fork1 w1 :
  tstep lb (LFork w1 worker)
    (App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1)).
Proof. apply TStepAppR; [done|]. apply TStepHead, HeadFork. done. Qed.

Lemma lb_beta1 w1 :
  tstep (App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1)) LBeta
    (App (Lam (subst (up (Chan w1 .: Var)) srv2)) (App EFork worker)).
Proof.
  apply TStepHead.
  apply (HeadApp (App (Lam srv2) (App EFork worker)) (Chan w1) I).
Qed.

Lemma lb_beta2 w1 w2 :
  tstep (App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2)) LBeta
    (sv0 w1 w2).
Proof.
  assert (subst1 (Chan w2) (subst (up (Chan w1 .: Var)) srv2) = sv0 w1 w2)
    as <-.
  { unfold subst1. rewrite subst_subst. reflexivity. }
  apply TStepHead.
  apply (HeadApp _ (Chan w2) I).
Qed.

(** ** Session-type stages of c

    Slb = ?∗.S2, S2 = !∗.S1, S1 = !∗.Close; the stage advances with
    the server's receive and each completed worker send. *)

Definition S1 : sty := SSnd TUnit SEnd.
Definition S2 : sty := SSnd TUnit S1.

(** Worker-stage dispatch, and the session stage of c as seen at
    srv stages s ∈ {8,9} (only worker2's send can be outstanding). *)
Definition wstage (k : nat) (x : chan) : expr :=
  match k with
  | 0 => wk0 x | 1 => wk1 x | 2 => wk2 x | 3 => wk3 x
  | 4 => wk4 x | 5 => wk5 x | _ => wk6 x
  end.

Definition w2sty (k : nat) : sty :=
  match k with 5 | 6 => SEnd | _ => S1 end.

(** ** Dispatch functions for the reachability invariant

    Worker thread including the terminated stage (k = 7), srv-stage
    dispatch, the session stage of c computed from the progress
    counters, the restricted set per srv stage, and the shape of the
    valid region of the counter space. *)

Definition wthread (k : nat) (x : chan) : expr :=
  if decide (k = 7)%nat then EUnit else wstage k x.

Definition sstage (s : nat) (w1 w2 : chan) : expr :=
  match s with 0 => sv0 w1 w2 | 1 => sv1 w1 w2 | 2 => sv2 w1 w2
  | 3 => sv3 w1 w2 | 4 => sv4 w1 w2 | 5 => sv5 w1 w2 | 6 => sv6 w1 w2
  | 7 => sv7 w1 w2 | 8 => sv8 w1 w2 | 9 => sv9 w1 w2 | 10 => sv10 w1 w2
  | _ => sv11 w1 w2 end.

Definition sentk (k : nat) : nat := if decide (5 ≤ k)%nat then 1 else 0.

Definition lbsty (s k1 k2 : nat) : sty :=
  if decide (s = 0)%nat then Slb
  else match (sentk k1 + sentk k2)%nat with
       | 0 => S2 | 1 => S1 | _ => SEnd end.

Definition lbC (w1 w2 : chan) (s : nat) : gset chan :=
  if decide (s ≤ 7)%nat then {[w1; w2]}
  else if decide (s ≤ 9)%nat then {[w2]} else ∅.

Definition lbvalid (s k1 k2 : nat) : Prop :=
  (s ≤ 11)%nat ∧
  match s with
  | 0 | 1 | 2 | 3 => (k1 ≤ 1)%nat ∧ (k2 ≤ 1)%nat
  | 4 | 5 => (2 ≤ k1 ≤ 6)%nat ∧ (k2 ≤ 1)%nat
  | 6 | 7 => (2 ≤ k1 ≤ 6)%nat ∧ (2 ≤ k2 ≤ 6)%nat
  | 8 | 9 => k1 = 7%nat ∧ (2 ≤ k2 ≤ 6)%nat
  | _ => k1 = 7%nat ∧ k2 = 7%nat
  end.

(** ** Multiset inversions for three-thread processes *)

Lemma gmultiset_triple_inv (E : gmultiset expr) e x y z :
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

Lemma gmultiset_triple_inv2 (E : gmultiset expr) e f x y z :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} →
  (e = x ∧ f = y ∧ E = {[+ z +]}) ∨ (e = x ∧ f = z ∧ E = {[+ y +]})
  ∨ (e = y ∧ f = x ∧ E = {[+ z +]}) ∨ (e = y ∧ f = z ∧ E = {[+ x +]})
  ∨ (e = z ∧ f = x ∧ E = {[+ y +]}) ∨ (e = z ∧ f = y ∧ E = {[+ x +]}).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} ⊎ {[+ z +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    [apply gmultiset_elem_of_disj_union in He as [He|He]|];
    apply gmultiset_elem_of_singleton in He; subst.
  - assert (E ⊎ {[+ f +]} = {[+ y +]} ⊎ {[+ z +]}) as HE by multiset_solver.
    apply gmultiset_pair_inv in HE as [[-> ->]|[-> ->]];
      [left; auto|right; left; auto].
  - assert (E ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ z +]}) as HE by multiset_solver.
    apply gmultiset_pair_inv in HE as [[-> ->]|[-> ->]];
      [right; right; left; auto|right; right; right; left; auto].
  - assert (E ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ y +]}) as HE by multiset_solver.
    apply gmultiset_pair_inv in HE as [[-> ->]|[-> ->]];
      [do 4 right; left; auto|do 5 right; auto].
Qed.

(** ** Step inversion for the stage-term shapes

    Generic single-transition inversions for the five redex shapes the
    stage terms are built from, then one corollary per stage term
    (wk6 and sv11 are [tstep_clos_inv] from Examples.v). *)

Lemma tstep_send_unit_inv c α e' :
  tstep (App ESend (Pair EUnit (Chan c))) α e' →
  α = LSess (SSend c EUnit) ∧ e' = Chan c.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Konst _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

Lemma tstep_letp_pair_unit_inv c K α e' :
  tstep (LetP (Pair EUnit (Chan c)) K) α e' →
  α = LBeta ∧ e' = subst2 EUnit (Chan c) K.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

(** Per-stage corollaries: worker stages.  The generic shape
    inversions [tstep_recv_chan_inv], [tstep_letp_recv_inv],
    [tstep_lam_val_inv], [tstep_lam_chan_inv], [tstep_lam_send_inv],
    [tstep_lam_fork_inv], [tstep_letu_clos_inv] come from Method.v. *)

Lemma tstep_wk0_inv x α e' : tstep (wk0 x) α e' → α = LBeta ∧ e' = wk1 x.
Proof. intros H. apply tstep_lam_chan_inv in H as [-> ->]. auto. Qed.

Lemma tstep_wk1_inv x α e' :
  tstep (wk1 x) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv x v) ∧ e' = LetP (Pair v (Chan x)) wK.
Proof. apply tstep_letp_recv_inv. Qed.

Lemma tstep_wk2_inv x α e' : tstep (wk2 x) α e' → α = LBeta ∧ e' = wk3 x.
Proof. intros H. apply tstep_letp_pair_unit_inv in H as [-> ->]. auto. Qed.

Lemma tstep_wk3_inv x α e' : tstep (wk3 x) α e' → α = LBeta ∧ e' = wk4 x.
Proof. apply tstep_letu_unit_inv. Qed.

Lemma tstep_wk4_inv x α e' :
  tstep (wk4 x) α e' → α = LSess (SSend "c" EUnit) ∧ e' = wk5 x.
Proof. intros H. exact (tstep_lam_send_inv _ EUnit _ _ _ I H). Qed.

Lemma tstep_wk5_inv x α e' : tstep (wk5 x) α e' → α = LBeta ∧ e' = wk6 x.
Proof. intros H. apply tstep_lam_chan_inv in H as [-> ->]. auto. Qed.

(** Per-stage corollaries: srv stages. *)

Lemma tstep_sv0_inv w1 w2 α e' :
  tstep (sv0 w1 w2) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv "c" v) ∧
       e' = LetP (Pair v (Chan "c")) (svA w1 w2).
Proof. apply tstep_letp_recv_inv. Qed.

Lemma tstep_sv1_inv w1 w2 α e' :
  tstep (sv1 w1 w2) α e' → α = LBeta ∧ e' = sv2 w1 w2.
Proof. intros H. apply tstep_letp_pair_unit_inv in H as [-> ->]. auto. Qed.

Lemma tstep_sv2_inv w1 w2 α e' :
  tstep (sv2 w1 w2) α e' → α = LBeta ∧ e' = sv3 w1 w2.
Proof. apply tstep_letu_unit_inv. Qed.

Lemma tstep_sv3_inv w1 w2 α e' :
  tstep (sv3 w1 w2) α e' →
  α = LSess (SSend w1 EUnit) ∧ e' = sv4 w1 w2.
Proof. intros H. exact (tstep_lam_send_inv _ EUnit _ _ _ I H). Qed.

Lemma tstep_sv4_inv w1 w2 α e' :
  tstep (sv4 w1 w2) α e' → α = LBeta ∧ e' = sv5 w1 w2.
Proof. intros H. apply tstep_lam_chan_inv in H as [-> ->]. auto. Qed.

Lemma tstep_sv5_inv w1 w2 α e' :
  tstep (sv5 w1 w2) α e' →
  α = LSess (SSend w2 EUnit) ∧ e' = sv6 w1 w2.
Proof. intros H. exact (tstep_lam_send_inv _ EUnit _ _ _ I H). Qed.

Lemma tstep_sv6_inv w1 w2 α e' :
  tstep (sv6 w1 w2) α e' → α = LBeta ∧ e' = sv7 w1 w2.
Proof. intros H. apply tstep_lam_chan_inv in H as [-> ->]. auto. Qed.

Lemma tstep_sv7_inv w1 w2 α e' :
  tstep (sv7 w1 w2) α e' → α = LSess (SClos w1) ∧ e' = sv8 w1 w2.
Proof. apply tstep_letu_clos_inv. Qed.

Lemma tstep_sv8_inv w1 w2 α e' :
  tstep (sv8 w1 w2) α e' → α = LBeta ∧ e' = sv9 w1 w2.
Proof. apply tstep_letu_unit_inv. Qed.

Lemma tstep_sv9_inv w1 w2 α e' :
  tstep (sv9 w1 w2) α e' → α = LSess (SClos w2) ∧ e' = sv10 w1 w2.
Proof. apply tstep_letu_clos_inv. Qed.

Lemma tstep_sv10_inv w1 w2 α e' :
  tstep (sv10 w1 w2) α e' → α = LBeta ∧ e' = sv11 w1 w2.
Proof. apply tstep_letu_unit_inv. Qed.

(** Pre-phase main-thread shapes: the initial thread and the
    intermediate main threads fork resp. β, and nothing else. *)

Lemma tstep_lb_fork_inv α e' :
  tstep lb α e' →
  ∃ w, α = LFork w worker
       ∧ e' = App (Lam (App (Lam srv2) (App EFork worker))) (Chan w).
Proof. intros H. exact (tstep_lam_fork_inv _ _ _ _ H I). Qed.

Lemma tstep_pre2_fork_inv w1 α e' :
  tstep (App (Lam (subst (up (Chan w1 .: Var)) srv2)) (App EFork worker))
    α e' →
  ∃ w, α = LFork w worker
       ∧ e' = App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w).
Proof. intros H. exact (tstep_lam_fork_inv _ _ _ _ H I). Qed.

Lemma tstep_pre1_beta_inv w1 α e' :
  tstep (App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1)) α e' →
  α = LBeta
  ∧ e' = App (Lam (subst (up (Chan w1 .: Var)) srv2)) (App EFork worker).
Proof. intros H. apply tstep_lam_chan_inv in H as [-> ->]. auto. Qed.

Lemma tstep_pre3_beta_inv w1 w2 α e' :
  tstep (App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2)) α e' →
  α = LBeta ∧ e' = sv0 w1 w2.
Proof.
  intros H. apply tstep_lam_chan_inv in H as [-> ->]. split; [done|].
  unfold subst1. rewrite subst_subst. reflexivity.
Qed.

(** ** The missing trivial step-existence lemmas *)

Lemma wk3_step x : tstep (wk3 x) LBeta (wk4 x).
Proof. apply TStepHead, HeadLetU. Qed.

Lemma sv8_step w1 w2 : tstep (sv8 w1 w2) LBeta (sv9 w1 w2).
Proof. apply TStepHead, HeadLetU. Qed.

Lemma sv10_step w1 w2 : tstep (sv10 w1 w2) LBeta (sv11 w1 w2).
Proof. apply TStepHead, HeadLetU. Qed.


(** ** The reachability invariant

    Every configuration reachable from (∅, {lb}), paired with its
    environment interface: the four pre-phase shapes (before the two
    forks and βs complete), the main phase indexed by the progress
    counters, and the terminal configuration. *)

Inductive lbI : senv → ty → proc → Prop :=
  | LIp0 : lbI {["c" := Slb]} TUnit (∅, {[+ lb +]})
  | LIp1 w1 k1 : w1 ≠ "c" → (k1 ≤ 1)%nat →
      lbI {["c" := Slb]} TUnit
        ({[w1]}, {[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
                 ⊎ {[+ wstage k1 w1 +]})
  | LIp2 w1 k1 : w1 ≠ "c" → (k1 ≤ 1)%nat →
      lbI {["c" := Slb]} TUnit
        ({[w1]}, {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (App EFork worker) +]}
                 ⊎ {[+ wstage k1 w1 +]})
  | LIp3 w1 w2 k1 k2 : w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
      (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
      lbI {["c" := Slb]} TUnit
        ({[w1; w2]}, {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                           (Chan w2) +]}
                     ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]})
  | LImain w1 w2 s k1 k2 : w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
      lbvalid s k1 k2 →
      lbI {["c" := lbsty s k1 k2]} TUnit
        (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                      ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
  | LIterm : lbI ∅ TUnit
      (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}).

(** ** Tactic toolkit for the step obligations

    [lb_split] destructs the multiset equation produced by inverting
    [proc_step] against a concrete two- or three-thread pool;
    [lb_tinv Hs] inverts a [tstep] hypothesis on any of the known
    thread shapes and simplifies the resulting label equation, closing
    the goal when the label is impossible; [lb_kill] (used after
    [lb_split]) disposes of a branch in which every thread choice is
    refuted by the label analysis (plus a subject-not-restricted
    contradiction). *)

Ltac lb_split :=
  match goal with
  | Heq : _ ⊎ {[+ _ +]} ⊎ {[+ _ +]} = {[+ _ +]} |- _ =>
      exfalso; by eapply gmultiset_two_singleton_inv
  | Heq : _ ⊎ {[+ _ +]} ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply gmultiset_triple_inv2 in Heq
        as [(->&->&->)|[(->&->&->)|[(->&->&->)|[(->&->&->)
           |[(->&->&->)|(->&->&->)]]]]]
  | Heq : _ ⊎ {[+ _ +]} ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]]
  | Heq : _ ⊎ {[+ _ +]} = {[+ _ +]} |- _ =>
      apply gmultiset_singleton_inv in Heq as [-> ->]
  | Heq : _ ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply gmultiset_triple_inv in Heq as [[-> ->]|[[-> ->]|[-> ->]]]
  | Heq : _ ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]]
  end.

Ltac lb_tinv Hs :=
  first
    [ apply tstep_wk0_inv in Hs as [? ?]
    | apply tstep_wk1_inv in Hs as (? & ? & ? & ?)
    | apply tstep_wk2_inv in Hs as [? ?]
    | apply tstep_wk3_inv in Hs as [? ?]
    | apply tstep_wk4_inv in Hs as [? ?]
    | apply tstep_wk5_inv in Hs as [? ?]
    | apply tstep_sv0_inv in Hs as (? & ? & ? & ?)
    | apply tstep_sv1_inv in Hs as [? ?]
    | apply tstep_sv2_inv in Hs as [? ?]
    | apply tstep_sv3_inv in Hs as [? ?]
    | apply tstep_sv4_inv in Hs as [? ?]
    | apply tstep_sv5_inv in Hs as [? ?]
    | apply tstep_sv6_inv in Hs as [? ?]
    | apply tstep_sv7_inv in Hs as [? ?]
    | apply tstep_sv8_inv in Hs as [? ?]
    | apply tstep_sv9_inv in Hs as [? ?]
    | apply tstep_sv10_inv in Hs as [? ?]
    | apply tstep_clos_inv in Hs as [? ?]
    | apply tstep_pre1_beta_inv in Hs as [? ?]
    | apply tstep_pre3_beta_inv in Hs as [? ?]
    | apply tstep_lb_fork_inv in Hs as (? & ? & ?)
    | apply tstep_pre2_fork_inv in Hs as (? & ? & ?)
    | exfalso; eapply val_no_tstep in Hs; [exact Hs|done]
    ]; simplify_eq.

Ltac lb_kill :=
  repeat match goal with Hs : tstep _ _ _ |- _ => lb_tinv Hs end;
  try done;
  try (exfalso; simpl in *; set_solver).

(** Close a successor-membership goal by the [LImain] constructor with
    concrete counters, discharging the side conditions. *)
Ltac lb_next w1 w2 s k1 k2 :=
  apply (LImain w1 w2 s k1 k2);
    [done|done|done|unfold lbvalid; split_and!; lia].

(** ** Group obligation lemmas

    For each constructor group of [lbI], both clauses of
    [proc_invariant], as standalone lemmas.  The [LImain] cases with
    s ∈ {8..11} are dispatched to one helper lemma per configuration
    (worker1 is terminated there; only worker2 and srv still move). *)

(** Terminal: ⟨∗, ∗, ∗⟩ with everything closed. *)
Lemma lbI_case_term :
  (pirred (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) →
   ∃ v E, ((∅, {[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n ∅ TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p' →
     inv_case lbI ∅ TUnit
       (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p').
Proof.
  split.
  - intros _. exists EUnit, ({[+ EUnit +]} ⊎ {[+ EUnit +]}). split_and!.
    + f_equal. multiset_solver.
    + done.
    + intros n. apply Vrel_unit.
    + intros e He. apply gmultiset_elem_of_disj_union in He as [He|He];
        by apply gmultiset_elem_of_singleton in He.
  - intros π p' Hst. exfalso. inversion Hst; subst; lb_split; lb_kill.
Qed.

(** s = 11: only the external close on c; continuation is terminal. *)
Lemma lbI_main_11 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred (∅, {[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) →
   ∃ v E, ((∅, {[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (∅, {[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       (∅, {[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SClos "c"))).
    replace ({[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]})
      with (({[+ EUnit +]} ⊎ {[+ EUnit +]}) ⊎ {[+ sv11 w1 w2 +]}
        : gmultiset expr) by multiset_solver.
    eapply (PStepSession _ _ _ (SClos "c"));
      [apply TStepHead, HeadClos|set_solver].
  - intros π p' Hst. inversion Hst; subst.
    + (* session: the close on c *)
      lb_split; [|lb_kill..].
      match goal with Hs : tstep _ (LSess _) _ |- _ =>
        apply tstep_clos_inv in Hs as [Hα ->] end.
      simplify_eq. simpl.
      exists ∅. split_and!; [done|set_solver|].
      replace (∅ ∖ ∅ : gset chan) with (∅ : gset chan) by set_solver.
      apply LIterm.
    + (* beta *) lb_split; lb_kill.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 10: only the β step to s = 11. *)
Lemma lbI_main_10 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred (∅, {[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) →
   ∃ v E, ((∅, {[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (∅, {[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       (∅, {[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]})
      with (({[+ EUnit +]} ⊎ {[+ EUnit +]}) ⊎ {[+ sv10 w1 w2 +]}
        : gmultiset expr) by multiset_solver.
    eapply PStepBeta, sv10_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: srv advances to s = 11 *)
      lb_split; [|lb_kill..].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_sv10_inv in Hs as [_ ->] end.
      intros _.
      replace (({[+ EUnit +]} ⊎ {[+ EUnit +]}) ⊎ {[+ sv11 w1 w2 +]})
        with ({[+ sv11 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}
          : gmultiset expr) by multiset_solver.
      lb_next w1 w2 11 7 7.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 9, k2 = 2: only worker2's β step. *)
Lemma lbI_main_9_2 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk2_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: worker2 advances to k2 = 3 *)
      lb_split; [lb_kill|lb_kill|].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_wk2_inv in Hs as [_ ->] end.
      intros _. lb_next w1 w2 9 7 3.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 9, k2 = 3: only worker2's β step. *)
Lemma lbI_main_9_3 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk3_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: worker2 advances to k2 = 4 *)
      lb_split; [lb_kill|lb_kill|].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_wk3_inv in Hs as [_ ->] end.
      intros _. lb_next w1 w2 9 7 4.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 9, k2 = 4: the external send on c; σ advances S1 → Close. *)
Lemma lbI_main_9_4 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SSend "c" EUnit))).
    eapply (PStepSession _ _ _ (SSend "c" EUnit)).
    + apply TStepAppR; [done|]. apply TStepHead, (HeadSend EUnit "c" I).
    + simpl. set_solver.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: srv's close is blocked; worker2 sends on c *)
      lb_split; [lb_kill|lb_kill|].
      match goal with Hs : tstep _ (LSess _) _ |- _ =>
        apply tstep_wk4_inv in Hs as [Hα ->] end.
      simplify_eq. simpl.
      exists ∅, ∅, TUnit, SEnd, ∅, ∅, {[w2]},
        ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}),
        ∅, ∅, TUnit, TUnit.
      split_and!.
      * by rewrite !(left_id (∅ : senv) (∪)).
      * apply map_disjoint_empty_l.
      * apply map_disjoint_empty_l.
      * apply map_disjoint_empty_l.
      * set_solver.
      * set_solver.
      * set_solver.
      * simpl. set_solver.
      * set_solver.
      * set_solver.
      * simpl. set_solver.
      * set_solver.
      * simpl. multiset_solver.
      * intros n. rewrite fmap_empty.
        rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
      * lb_next w1 w2 9 7 5.
      * apply topo_split_nil.
      * left; done.
    + (* beta *) lb_split; lb_kill.
    + (* fork *) lb_split; lb_kill.
    + (* msg: the send has no internal partner ("c" ∉ C) *)
      lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 9, k2 = 5: only worker2's β step. *)
Lemma lbI_main_9_5 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk5_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: worker2 advances to k2 = 6 *)
      lb_split; [lb_kill|lb_kill|].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_wk5_inv in Hs as [_ ->] end.
      intros _. lb_next w1 w2 9 7 6.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 9, k2 = 6: the internal close on w2, to (s, k2) = (10, 7). *)
Lemma lbI_main_9_6 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       ({[w2]}, {[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]})
      with (({[+ EUnit +]} : gmultiset expr)
            ⊎ {[+ sv9 w1 w2 +]} ⊎ {[+ wk6 w2 +]})
      by multiset_solver.
    eapply PStepClose;
      [apply TStepLetU, TStepHead, HeadClos
      |apply TStepHead, HeadClos
      |set_solver].
  - intros π p' Hst. inversion Hst; subst.
    + (* session: both closes have subject w2 ∈ C *) lb_split; lb_kill.
    + (* beta *) lb_split; lb_kill.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close: the w2 synchronization with srv *)
      lb_split.
      * lb_kill.
      * (* srv paired with worker2 *)
        match goal with Hs : tstep (sv9 _ _) _ _ |- _ =>
          apply tstep_sv9_inv in Hs as [Hα ->] end.
        match goal with Hs : tstep (wk6 _) _ _ |- _ =>
          apply tstep_clos_inv in Hs as [Hα' ->] end.
        simplify_eq. intros _.
        replace ({[w2]} ∖ {[w2]} : gset chan) with (∅ : gset chan)
          by set_solver.
        replace ({[+ EUnit +]} ⊎ {[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]})
          with ({[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 10 7 7.
      * lb_kill.
      * lb_kill.
      * (* worker2 paired with srv *)
        match goal with Hs : tstep (wk6 _) _ _ |- _ =>
          apply tstep_clos_inv in Hs as [Hα ->] end.
        match goal with Hs : tstep (sv9 _ _) _ _ |- _ =>
          apply tstep_sv9_inv in Hs as [Hα' ->] end.
        simplify_eq. intros _.
        replace ({[w2]} ∖ {[w2]} : gset chan) with (∅ : gset chan)
          by set_solver.
        replace ({[+ EUnit +]} ⊎ {[+ EUnit +]} ⊎ {[+ sv10 w1 w2 +]})
          with ({[+ sv10 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 10 7 7.
      * lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 8, k2 = 2: srv's β and worker2's β. *)
Lemma lbI_main_8_2 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk2_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: srv to s = 9, or worker2 to k2 = 3 *)
      lb_split; [|lb_kill|].
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_sv8_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ EUnit +]} ⊎ {[+ wk2 w2 +]}) ⊎ {[+ sv9 w1 w2 +]})
          with ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk2 w2 +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 9 7 2.
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_wk2_inv in Hs as [_ ->] end.
        intros _. lb_next w1 w2 8 7 3.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 8, k2 = 3: srv's β and worker2's β. *)
Lemma lbI_main_8_3 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk3_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: srv to s = 9, or worker2 to k2 = 4 *)
      lb_split; [|lb_kill|].
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_sv8_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ EUnit +]} ⊎ {[+ wk3 w2 +]}) ⊎ {[+ sv9 w1 w2 +]})
          with ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk3 w2 +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 9 7 3.
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_wk3_inv in Hs as [_ ->] end.
        intros _. lb_next w1 w2 8 7 4.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 8, k2 = 4: srv's β, and worker2's external send on c. *)
Lemma lbI_main_8_4 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := S1]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) π p' →
     inv_case lbI {["c" := S1]} TUnit
       ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]})
      with (({[+ EUnit +]} : gmultiset expr)
            ⊎ {[+ wk4 w2 +]} ⊎ {[+ sv8 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv8_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: worker2's send on c is enabled *)
      lb_split; [lb_kill|lb_kill|].
      match goal with Hs : tstep _ (LSess _) _ |- _ =>
        apply tstep_wk4_inv in Hs as [Hα ->] end.
      simplify_eq. simpl.
      exists ∅, ∅, TUnit, SEnd, ∅, ∅, {[w2]},
        ({[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}),
        ∅, ∅, TUnit, TUnit.
      split_and!.
      * by rewrite !(left_id (∅ : senv) (∪)).
      * apply map_disjoint_empty_l.
      * apply map_disjoint_empty_l.
      * apply map_disjoint_empty_l.
      * set_solver.
      * set_solver.
      * set_solver.
      * simpl. set_solver.
      * set_solver.
      * set_solver.
      * simpl. set_solver.
      * set_solver.
      * simpl. multiset_solver.
      * intros n. rewrite fmap_empty.
        rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
      * lb_next w1 w2 8 7 5.
      * apply topo_split_nil.
      * left; done.
    + (* beta: srv advances to s = 9 *)
      lb_split; [|lb_kill..].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_sv8_inv in Hs as [_ ->] end.
      intros _.
      replace (({[+ EUnit +]} ⊎ {[+ wk4 w2 +]}) ⊎ {[+ sv9 w1 w2 +]})
        with ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk4 w2 +]}
          : gmultiset expr) by multiset_solver.
      lb_next w1 w2 9 7 4.
    + (* fork *) lb_split; lb_kill.
    + (* msg: the send has no internal partner ("c" ∉ C) *)
      lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 8, k2 = 5: srv's β and worker2's β. *)
Lemma lbI_main_8_5 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta. apply wk5_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta: srv to s = 9, or worker2 to k2 = 6 *)
      lb_split; [|lb_kill|].
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_sv8_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ EUnit +]} ⊎ {[+ wk5 w2 +]}) ⊎ {[+ sv9 w1 w2 +]})
          with ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk5 w2 +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 9 7 5.
      * match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_wk5_inv in Hs as [_ ->] end.
        intros _. lb_next w1 w2 8 7 6.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close *) lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** s = 8, k2 = 6: only srv's β (worker2's close has no partner
    until srv reaches s = 9). *)
Lemma lbI_main_8_6 w1 w2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 →
  (pirred ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) →
   ∃ v E, (({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := SEnd]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) π p' →
     inv_case lbI {["c" := SEnd]} TUnit
       ({[w2]}, {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]})
      with (({[+ EUnit +]} : gmultiset expr)
            ⊎ {[+ wk6 w2 +]} ⊎ {[+ sv8 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv8_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: worker2's close is blocked (w2 ∈ C) *)
      lb_split; lb_kill.
    + (* beta: srv advances to s = 9 *)
      lb_split; [|lb_kill..].
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_sv8_inv in Hs as [_ ->] end.
      intros _.
      replace (({[+ EUnit +]} ⊎ {[+ wk6 w2 +]}) ⊎ {[+ sv9 w1 w2 +]})
        with ({[+ sv9 w1 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ wk6 w2 +]}
          : gmultiset expr) by multiset_solver.
      lb_next w1 w2 9 7 6.
    + (* fork *) lb_split; lb_kill.
    + (* msg *) lb_split; lb_kill.
    + (* close: srv has no close label at s = 8 *)
      lb_split; lb_kill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** The [LImain] group obligations for the late stages s ∈ {8..11}:
    dispatch on the concrete stage and worker2 counter; the statements
    of the per-configuration lemmas are convertible to the dispatched
    goals. *)
Lemma lbI_case_main_late w1 w2 s k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → lbvalid s k1 k2 → (8 ≤ s)%nat →
  (pirred (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, ((lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                         ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty s k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty s k1 k2]} TUnit
       (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                     ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 [Hs Hk] Hlo.
  destruct s as [|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]; try lia.
  - (* s = 8 *)
    destruct Hk as [-> Hk2].
    destruct k2 as [|[|[|[|[|[|[|k2]]]]]]]; try lia.
    + exact (lbI_main_8_2 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_8_3 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_8_4 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_8_5 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_8_6 w1 w2 Hw1 Hw2 Hw12).
  - (* s = 9 *)
    destruct Hk as [-> Hk2].
    destruct k2 as [|[|[|[|[|[|[|k2]]]]]]]; try lia.
    + exact (lbI_main_9_2 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_9_3 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_9_4 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_9_5 w1 w2 Hw1 Hw2 Hw12).
    + exact (lbI_main_9_6 w1 w2 Hw1 Hw2 Hw12).
  - (* s = 10 *)
    destruct Hk as [-> ->]. exact (lbI_main_10 w1 w2 Hw1 Hw2 Hw12).
  - (* s = 11 *)
    destruct Hk as [-> ->]. exact (lbI_main_11 w1 w2 Hw1 Hw2 Hw12).
Qed.

(** Pre-phase: the initial thread forks worker1. *)
Lemma lbI_case_p0 :
  (pirred (∅, {[+ lb +]}) →
   ∃ v E, ((∅, {[+ lb +]}) : proc) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := Slb]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (∅, {[+ lb +]}) π p' →
     inv_case lbI {["c" := Slb]} TUnit (∅, {[+ lb +]}) π p').
Proof.
  split.
  - intros Hirr. exfalso.
    destruct (exist_fresh (echans (∅ : gmultiset expr) ∪ fchans lb))
      as [w Hw].
    eapply (Hirr PTau).
    replace ({[+ lb +]}) with ((∅ ⊎ {[+ lb +]}) : gmultiset expr)
      by multiset_solver.
    eapply (PStepFork _ _ _ w worker).
    + apply lb_fork1.
    + set_solver.
    + set_solver.
    + set_solver.
  - intros π p' Hst. inversion Hst; subst.
    + (* session *) lb_split; lb_kill.
    + (* beta *) lb_split; lb_kill.
    + (* fork: worker1 is spawned; the τ-guard makes it distinct
         from c *)
      lb_split.
      match goal with Hs : tstep _ (LFork _ _) _ |- _ =>
        apply tstep_lb_fork_inv in Hs as (w & [= <- ->] & ->) end.
      intros Hg. simpl in Hg. rewrite dom_singleton_L in Hg.
      match goal with |- lbI _ _ (_ ∪ {[?x]}, _) =>
        replace (∅ ∪ {[x]} : gset chan) with ({[x]} : gset chan)
          by set_solver;
        replace (∅ ⊎ {[+ App (Lam (App (Lam srv2) (App EFork worker)))
                          (Chan x) +]}
                 ⊎ {[+ App worker (Chan x) +]})
          with ({[+ App (Lam (App (Lam srv2) (App EFork worker)))
                    (Chan x) +]}
                ⊎ {[+ App worker (Chan x) +]} : gmultiset expr)
          by multiset_solver;
        apply (LIp1 x 0); [set_solver|lia]
      end.
    + (* msg *) lb_split.
    + (* close *) lb_split.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** Pre-phase: main β-redex before the second fork; worker1 warms up. *)
Lemma lbI_case_p1 w1 k1 :
  w1 ≠ "c" → (k1 ≤ 1)%nat →
  (pirred ({[w1]},
     {[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
     ⊎ {[+ wstage k1 w1 +]}) →
   ∃ v E, (({[w1]},
     {[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
     ⊎ {[+ wstage k1 w1 +]}) : proc) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := Slb]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1]},
     {[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
     ⊎ {[+ wstage k1 w1 +]}) π p' →
     inv_case lbI {["c" := Slb]} TUnit
       ({[w1]},
        {[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
        ⊎ {[+ wstage k1 w1 +]}) π p').
Proof.
  intros Hw1 Hk1. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ App (Lam (App (Lam srv2) (App EFork worker))) (Chan w1) +]}
             ⊎ {[+ wstage k1 w1 +]})
      with (({[+ wstage k1 w1 +]} : gmultiset expr)
            ⊎ {[+ App (Lam (App (Lam srv2) (App EFork worker)))
                  (Chan w1) +]})
      by multiset_solver.
    eapply PStepBeta. apply lb_beta1.
  - intros π p' Hst.
    destruct k1 as [|[|k1]]; [| |lia].
    + (* k1 = 0 *)
      change (wstage 0 w1) with (wk0 w1) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: main to pre2, or worker to k1 = 1 *)
        lb_split.
        -- match goal with Hs : tstep _ LBeta _ |- _ =>
             apply tstep_pre1_beta_inv in Hs as [_ ->] end.
           intros _.
           replace ({[+ wk0 w1 +]}
                    ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                          (App EFork worker) +]})
             with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (App EFork worker) +]}
                   ⊎ {[+ wk0 w1 +]} : gmultiset expr)
             by multiset_solver.
           apply (LIp2 w1 0); [done|lia].
        -- match goal with Hs : tstep _ LBeta _ |- _ =>
             apply tstep_wk0_inv in Hs as [_ ->] end.
           intros _. apply (LIp1 w1 1); [done|lia].
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
    + (* k1 = 1 *)
      change (wstage 1 w1) with (wk1 w1) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: only the main thread *)
        lb_split; [|lb_kill].
        match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_pre1_beta_inv in Hs as [_ ->] end.
        intros _.
        replace ({[+ wk1 w1 +]}
                 ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (App EFork worker) +]})
          with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                    (App EFork worker) +]}
                ⊎ {[+ wk1 w1 +]} : gmultiset expr)
          by multiset_solver.
        apply (LIp2 w1 1); [done|lia].
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** Pre-phase: main forks worker2; the fork guard supplies both
    freshness facts for the new channel. *)
Lemma lbI_case_p2 w1 k1 :
  w1 ≠ "c" → (k1 ≤ 1)%nat →
  (pirred ({[w1]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
           (App EFork worker) +]}
     ⊎ {[+ wstage k1 w1 +]}) →
   ∃ v E, (({[w1]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
           (App EFork worker) +]}
     ⊎ {[+ wstage k1 w1 +]}) : proc) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := Slb]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
           (App EFork worker) +]}
     ⊎ {[+ wstage k1 w1 +]}) π p' →
     inv_case lbI {["c" := Slb]} TUnit
       ({[w1]},
        {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
              (App EFork worker) +]}
        ⊎ {[+ wstage k1 w1 +]}) π p').
Proof.
  intros Hw1 Hk1. split.
  - intros Hirr. exfalso.
    destruct (exist_fresh
        ({[w1]} ∪ echans {[+ wstage k1 w1 +]}
         ∪ fchans (App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (App EFork worker)))) as [w Hw].
    eapply (Hirr PTau).
    replace ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                  (App EFork worker) +]}
             ⊎ {[+ wstage k1 w1 +]})
      with (({[+ wstage k1 w1 +]} : gmultiset expr)
            ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                  (App EFork worker) +]})
      by multiset_solver.
    eapply (PStepFork _ _ _ w worker).
    + apply TStepAppR; [done|]. apply TStepHead, HeadFork. done.
    + set_solver.
    + set_solver.
    + set_solver.
  - intros π p' Hst.
    destruct k1 as [|[|k1]]; [| |lia].
    + (* k1 = 0 *)
      change (wstage 0 w1) with (wk0 w1) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: only the worker *)
        lb_split; [lb_kill|].
        match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_wk0_inv in Hs as [_ ->] end.
        intros _. apply (LIp2 w1 1); [done|lia].
      * (* fork: worker2 is spawned *)
        lb_split; [|lb_kill].
        match goal with Hs : tstep _ (LFork _ _) _ |- _ =>
          apply tstep_pre2_fork_inv in Hs as (w & [= <- ->] & ->) end.
        intros Hg. simpl in Hg. rewrite dom_singleton_L in Hg.
        match goal with |- lbI _ _ (_ ∪ {[?x]}, _) =>
          replace ({[+ wk0 w1 +]}
                   ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                         (Chan x) +]}
                   ⊎ {[+ App worker (Chan x) +]})
            with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                      (Chan x) +]}
                  ⊎ {[+ wk0 w1 +]} ⊎ {[+ App worker (Chan x) +]}
                  : gmultiset expr)
            by multiset_solver;
          apply (LIp3 w1 x 0 0); [done|set_solver|set_solver|lia|lia]
        end.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
    + (* k1 = 1 *)
      change (wstage 1 w1) with (wk1 w1) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* fork: worker2 is spawned *)
        lb_split; [|lb_kill].
        match goal with Hs : tstep _ (LFork _ _) _ |- _ =>
          apply tstep_pre2_fork_inv in Hs as (w & [= <- ->] & ->) end.
        intros Hg. simpl in Hg. rewrite dom_singleton_L in Hg.
        match goal with |- lbI _ _ (_ ∪ {[?x]}, _) =>
          replace ({[+ wk1 w1 +]}
                   ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                         (Chan x) +]}
                   ⊎ {[+ App worker (Chan x) +]})
            with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                      (Chan x) +]}
                  ⊎ {[+ wk1 w1 +]} ⊎ {[+ App worker (Chan x) +]}
                  : gmultiset expr)
            by multiset_solver;
          apply (LIp3 w1 x 1 0); [done|set_solver|set_solver|lia|lia]
        end.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** Pre-phase: main β-redex to sv0; both workers alive. *)
Lemma lbI_case_p3 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2) +]}
     ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]}) →
   ∃ v E, (({[w1; w2]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2) +]}
     ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := Slb]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]},
     {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2) +]}
     ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]}) π p' →
     inv_case lbI {["c" := Slb]} TUnit
       ({[w1; w2]},
        {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2) +]}
        ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2)) (Chan w2) +]}
             ⊎ {[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]})
      with (({[+ wstage k1 w1 +]} ⊎ {[+ wstage k2 w2 +]} : gmultiset expr)
            ⊎ {[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                  (Chan w2) +]})
      by multiset_solver.
    eapply PStepBeta. apply lb_beta2.
  - intros π p' Hst.
    destruct k1 as [|[|k1]]; [| |lia].
    all: destruct k2 as [|[|k2]]; [| |lia].
    + (* k1 = 0, k2 = 0 *)
      change (wstage 0 w1) with (wk0 w1) in Hst.
      change (wstage 0 w2) with (wk0 w2) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: main, worker1, or worker2 *)
        lb_split.
        -- match goal with Hs : tstep _ LBeta _ |- _ =>
             apply tstep_pre3_beta_inv in Hs as [_ ->] end.
           intros _.
           replace (({[+ wk0 w1 +]} ⊎ {[+ wk0 w2 +]}) ⊎ {[+ sv0 w1 w2 +]})
             with ({[+ sv0 w1 w2 +]} ⊎ {[+ wk0 w1 +]} ⊎ {[+ wk0 w2 +]}
               : gmultiset expr) by multiset_solver.
           lb_next w1 w2 0 0 0.
        -- match goal with Hs : tstep (wk0 w1) LBeta _ |- _ =>
             apply tstep_wk0_inv in Hs as [_ ->] end.
           intros _.
           replace (({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                          (Chan w2) +]} ⊎ {[+ wk0 w2 +]}) ⊎ {[+ wk1 w1 +]})
             with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (Chan w2) +]}
                   ⊎ {[+ wk1 w1 +]} ⊎ {[+ wk0 w2 +]} : gmultiset expr)
             by multiset_solver.
           apply (LIp3 w1 w2 1 0); [done|done|done|lia|lia].
        -- match goal with Hs : tstep (wk0 w2) LBeta _ |- _ =>
             apply tstep_wk0_inv in Hs as [_ ->] end.
           intros _. apply (LIp3 w1 w2 0 1); [done|done|done|lia|lia].
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
    + (* k1 = 0, k2 = 1 *)
      change (wstage 0 w1) with (wk0 w1) in Hst.
      change (wstage 1 w2) with (wk1 w2) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: main or worker1 *)
        lb_split; [| |lb_kill].
        -- match goal with Hs : tstep _ LBeta _ |- _ =>
             apply tstep_pre3_beta_inv in Hs as [_ ->] end.
           intros _.
           replace (({[+ wk0 w1 +]} ⊎ {[+ wk1 w2 +]}) ⊎ {[+ sv0 w1 w2 +]})
             with ({[+ sv0 w1 w2 +]} ⊎ {[+ wk0 w1 +]} ⊎ {[+ wk1 w2 +]}
               : gmultiset expr) by multiset_solver.
           lb_next w1 w2 0 0 1.
        -- match goal with Hs : tstep (wk0 w1) LBeta _ |- _ =>
             apply tstep_wk0_inv in Hs as [_ ->] end.
           intros _.
           replace (({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                          (Chan w2) +]} ⊎ {[+ wk1 w2 +]}) ⊎ {[+ wk1 w1 +]})
             with ({[+ App (Lam (subst (up (Chan w1 .: Var)) srv2))
                       (Chan w2) +]}
                   ⊎ {[+ wk1 w1 +]} ⊎ {[+ wk1 w2 +]} : gmultiset expr)
             by multiset_solver.
           apply (LIp3 w1 w2 1 1); [done|done|done|lia|lia].
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
    + (* k1 = 1, k2 = 0 *)
      change (wstage 1 w1) with (wk1 w1) in Hst.
      change (wstage 0 w2) with (wk0 w2) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: main or worker2 *)
        lb_split; [|lb_kill|].
        -- match goal with Hs : tstep _ LBeta _ |- _ =>
             apply tstep_pre3_beta_inv in Hs as [_ ->] end.
           intros _.
           replace (({[+ wk1 w1 +]} ⊎ {[+ wk0 w2 +]}) ⊎ {[+ sv0 w1 w2 +]})
             with ({[+ sv0 w1 w2 +]} ⊎ {[+ wk1 w1 +]} ⊎ {[+ wk0 w2 +]}
               : gmultiset expr) by multiset_solver.
           lb_next w1 w2 0 1 0.
        -- match goal with Hs : tstep (wk0 w2) LBeta _ |- _ =>
             apply tstep_wk0_inv in Hs as [_ ->] end.
           intros _. apply (LIp3 w1 w2 1 1); [done|done|done|lia|lia].
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
    + (* k1 = 1, k2 = 1 *)
      change (wstage 1 w1) with (wk1 w1) in Hst.
      change (wstage 1 w2) with (wk1 w2) in Hst.
      inversion Hst; subst.
      * lb_split; lb_kill.
      * (* beta: only the main thread *)
        lb_split; [|lb_kill|lb_kill].
        match goal with Hs : tstep _ LBeta _ |- _ =>
          apply tstep_pre3_beta_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ wk1 w1 +]} ⊎ {[+ wk1 w2 +]}) ⊎ {[+ sv0 w1 w2 +]})
          with ({[+ sv0 w1 w2 +]} ⊎ {[+ wk1 w1 +]} ⊎ {[+ wk1 w2 +]}
            : gmultiset expr) by multiset_solver.
        lb_next w1 w2 0 1 1.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * lb_split; lb_kill.
      * (* internal forwarding: no forwarding redex *) lb_split; lb_kill.
Qed.

(** ** The [LImain] band s ∈ {4..7}

    Both workers are parametric here, so instead of enumerating the
    counter space we classify the transitions of an abstract worker
    thread once per counter band, and prove one lemma per srv stage
    with the counters kept abstract.  [tstep_wthread_mid_inv] is the
    complete transition table of a worker at k ∈ {2..6},
    [tstep_wthread_lo_inv] the one at k ∈ {0,1}. *)

Lemma tstep_wthread_mid_inv k x α e' :
  tstep (wthread k x) α e' → (2 ≤ k ≤ 6)%nat →
  ((2 ≤ k ≤ 5)%nat ∧ (k ≠ 4)%nat ∧ α = LBeta ∧ e' = wthread (S k) x)
  ∨ ((k = 4)%nat ∧ α = LSess (SSend "c" EUnit) ∧ e' = wthread 5 x)
  ∨ ((k = 6)%nat ∧ α = LSess (SClos x) ∧ e' = EUnit).
Proof.
  intros H Hk.
  destruct k as [|[|[|[|[|[|[|k]]]]]]]; try lia.
  - apply tstep_wk2_inv in H as [-> ->].
    left. split_and!; [lia|lia|lia|done|done].
  - apply tstep_wk3_inv in H as [-> ->].
    left. split_and!; [lia|lia|lia|done|done].
  - apply tstep_wk4_inv in H as [-> ->]. right; left. split_and!; done.
  - apply tstep_wk5_inv in H as [-> ->].
    left. split_and!; [lia|lia|lia|done|done].
  - apply tstep_clos_inv in H as [-> ->]. right; right. split_and!; done.
Qed.

Lemma tstep_wthread_lo_inv k x α e' :
  tstep (wthread k x) α e' → (k ≤ 1)%nat →
  ((k = 0)%nat ∧ α = LBeta ∧ e' = wthread 1 x)
  ∨ ((k = 1)%nat ∧ ∃ v, is_val v ∧ α = LSess (SRecv x v)
       ∧ e' = LetP (Pair v (Chan x)) wK).
Proof.
  intros H Hk.
  destruct k as [|[|k]]; try lia.
  - apply tstep_wk0_inv in H as [-> ->]. left. split_and!; done.
  - apply tstep_wk1_inv in H as (v & Hv & -> & ->). right.
    split; [done|]. by exists v.
Qed.

(** Step existence for the mid-band redexes. *)

Lemma wthread_beta_step k x :
  (2 ≤ k ≤ 5)%nat → (k ≠ 4)%nat →
  tstep (wthread k x) LBeta (wthread (S k) x).
Proof.
  intros Hk Hk4. destruct k as [|[|[|[|[|[|k]]]]]]; try lia.
  - apply wk2_step.
  - apply wk3_step.
  - apply wk5_step.
Qed.

Lemma wk4_send_step x :
  tstep (wk4 x) (LSess (SSend "c" EUnit)) (wk5 x).
Proof. apply TStepAppR; [done|]. apply TStepHead, (HeadSend EUnit "c" I). Qed.

Lemma sv5_send_step w1 w2 :
  tstep (sv5 w1 w2) (LSess (SSend w2 EUnit)) (sv6 w1 w2).
Proof. apply TStepAppR; [done|]. apply TStepHead, (HeadSend EUnit w2 I). Qed.

Lemma wk1_recv_step x :
  tstep (wk1 x) (LSess (SRecv x EUnit)) (wk2 x).
Proof. apply TStepLetP, TStepHead, (HeadRecv x EUnit I). Qed.

Lemma sv7_close_step w1 w2 :
  tstep (sv7 w1 w2) (LSess (SClos w1)) (sv8 w1 w2).
Proof. apply TStepLetU, TStepHead, HeadClos. Qed.

(** How the session stage of c recomputes when a counter moves. *)

Lemma sentk_S k : (k ≠ 4)%nat → sentk (S k) = sentk k.
Proof. intros Hk. unfold sentk. do 2 destruct (decide _); lia. Qed.

Lemma lbsty_S_l s k1 k2 : (k1 ≠ 4)%nat →
  lbsty s (S k1) k2 = lbsty s k1 k2.
Proof. intros Hk. unfold lbsty. rewrite sentk_S; done. Qed.

Lemma lbsty_S_r s k1 k2 : (k2 ≠ 4)%nat →
  lbsty s k1 (S k2) = lbsty s k1 k2.
Proof. intros Hk. unfold lbsty. rewrite sentk_S; done. Qed.

Lemma lbsty_send_l s k2 : (s ≠ 0)%nat →
  lbsty s 4 k2 = SSnd TUnit (lbsty s 5 k2).
Proof.
  intros Hs. unfold lbsty.
  destruct (decide (s = 0)); [lia|].
  unfold sentk. destruct (decide (5 ≤ k2)%nat); done.
Qed.

Lemma lbsty_send_r s k1 : (s ≠ 0)%nat →
  lbsty s k1 4 = SSnd TUnit (lbsty s k1 5).
Proof.
  intros Hs. unfold lbsty.
  destruct (decide (s = 0)); [lia|].
  unfold sentk. destruct (decide (5 ≤ k1)%nat); done.
Qed.

(** Classify a worker tstep hypothesis by its counter band; label
    mismatches are discharged on the fly. *)

Ltac lb_wmid Hs Hk :=
  let Hr := fresh "Hwr" in let Hr4 := fresh "Hwr4" in
  let Hl := fresh "Hwl" in let Hc := fresh "Hwc" in
  pose proof (tstep_wthread_mid_inv _ _ _ _ Hs Hk) as Hc;
  clear Hs;
  destruct Hc as [(Hr & Hr4 & Hl & ->)|[(-> & Hl & ->)|(-> & Hl & ->)]];
  simplify_eq.

Ltac lb_wlo Hs Hk :=
  let Hl := fresh "Hwl" in let Hv := fresh "Hwv" in
  let v := fresh "v" in let Hc := fresh "Hwc" in
  pose proof (tstep_wthread_lo_inv _ _ _ _ Hs Hk) as Hc;
  clear Hs;
  destruct Hc as [(-> & Hl & ->)|(-> & (v & Hv & Hl & ->))];
  simplify_eq.

(** Kill a branch: classify every abstract worker tstep, then run the
    concrete-shape killer. *)
Ltac lb_wkill :=
  repeat match goal with
    | Hs : tstep (wthread ?k ?x) _ _, Hk : (2 ≤ ?k ≤ 6)%nat |- _ =>
        lb_wmid Hs Hk
    | Hs : tstep (wthread ?k ?x) _ _, Hk : (?k ≤ 1)%nat |- _ =>
        lb_wlo Hs Hk
    end;
  lb_kill.

(** s = 4: srv β to s = 5; worker1 in the mid band, worker2 warming
    up.  Worker1's send at k1 = 4 is the only enabled session step. *)
Lemma lbI_main_4 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (2 ≤ k1 ≤ 6)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv4 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv4 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 4 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv4 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 4 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv4 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv4 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
             ⊎ {[+ wthread k2 w2 +]})
      with (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}
             : gmultiset expr) ⊎ {[+ sv4 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv4_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: only worker1's send on c can fire *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        -- (* k1 = 4: the external send *)
           rewrite (lbsty_send_l 4 k2); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 4 5 k2), ∅, ∅, {[w1; w2]},
             ({[+ sv4 w1 w2 +]} ⊎ {[+ wthread 5 w1 +]}
              ⊎ {[+ wthread k2 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 4 5 k2.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k1 = 6: close blocked, w1 ∈ C *)
           exfalso. simpl in *. set_solver.
      * (* worker2: k2 = 1 recv blocked, w2 ∈ C *)
        match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        exfalso. simpl in *. set_solver.
    + (* beta: srv, worker1 (k1 ∈ {2,3,5}), or worker2 (k2 = 0) *)
      lb_split.
      * match goal with Hs : tstep (sv4 _ _) _ _ |- _ =>
          apply tstep_sv4_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ sv5 w1 w2 +]})
          with ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 5 k1 k2.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        intros _.
        rewrite <-(lbsty_S_l 4 k1 k2); [|lia].
        replace (({[+ sv4 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread (S k1) w1 +]})
          with ({[+ sv4 w1 w2 +]} ⊎ {[+ wthread (S k1) w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 4 (S k1) k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 4 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg *) lb_split; lb_wkill.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 5: srv offers the send on w2; it pairs internally with
    worker2's recv at k2 = 1, advancing to (s, k2) = (6, 2). *)
Lemma lbI_main_5 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (2 ≤ k1 ≤ 6)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 5 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 5 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    destruct (decide (k1 = 4)%nat) as [->|Hk14];
      [|destruct (decide (k1 = 6)%nat) as [->|Hk16]].
    + (* k1 = 4: worker1's external send *)
      eapply Hirr.
      replace ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread 4 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ sv5 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]}
               : gmultiset expr) ⊎ {[+ wthread 4 w1 +]})
        by multiset_solver.
      eapply (PStepSession _ _ _ (SSend "c" EUnit));
        [apply wk4_send_step|simpl; set_solver].
    + (* k1 = 6: worker2 β at k2 = 0, or the internal message *)
      destruct k2 as [|[|k2]]; [| |lia].
      * eapply Hirr.
        replace ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread 6 w1 +]}
                 ⊎ {[+ wthread 0 w2 +]})
          with (({[+ sv5 w1 w2 +]} ⊎ {[+ wthread 6 w1 +]}
                 : gmultiset expr) ⊎ {[+ wthread 0 w2 +]})
          by multiset_solver.
        eapply PStepBeta. apply wk0_step.
      * eapply Hirr.
        replace ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread 6 w1 +]}
                 ⊎ {[+ wthread 1 w2 +]})
          with (({[+ wthread 6 w1 +]} : gmultiset expr)
                ⊎ {[+ sv5 w1 w2 +]} ⊎ {[+ wthread 1 w2 +]})
          by multiset_solver.
        eapply PStepMsg;
          [apply sv5_send_step|apply wk1_recv_step|set_solver].
    + (* k1 ∈ {2,3,5}: worker1 β *)
      eapply Hirr.
      replace ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ sv5 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]}
               : gmultiset expr) ⊎ {[+ wthread k1 w1 +]})
        by multiset_solver.
      eapply PStepBeta. apply wthread_beta_step; lia.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: srv's send on w2 is blocked; only worker1's send *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        -- (* k1 = 4: the external send *)
           rewrite (lbsty_send_l 5 k2); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 5 5 k2), ∅, ∅, {[w1; w2]},
             ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread 5 w1 +]}
              ⊎ {[+ wthread k2 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 5 5 k2.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k1 = 6: close blocked, w1 ∈ C *)
           exfalso. simpl in *. set_solver.
      * (* worker2: k2 = 1 recv blocked, w2 ∈ C *)
        match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        exfalso. simpl in *. set_solver.
    + (* beta: worker1 (k1 ∈ {2,3,5}) or worker2 (k2 = 0) *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        intros _.
        rewrite <-(lbsty_S_l 5 k1 k2); [|lia].
        replace (({[+ sv5 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread (S k1) w1 +]})
          with ({[+ sv5 w1 w2 +]} ⊎ {[+ wthread (S k1) w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 5 (S k1) k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 5 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg: the internal w2 message *)
      lb_split; [lb_wkill| |lb_wkill|lb_wkill|lb_wkill|lb_wkill].
      match goal with Hs : tstep (sv5 _ _) _ _ |- _ =>
        apply tstep_sv5_inv in Hs as [Hα ->] end.
      simplify_eq.
      match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
        lb_wlo Hs Hk2 end.
      (* k2 = 1: the received value is forced to EUnit *)
      intros _.
      change (LetP (Pair EUnit (Chan w2)) wK) with (wthread 2 w2).
      replace ({[+ wthread k1 w1 +]} ⊎ {[+ sv6 w1 w2 +]}
               ⊎ {[+ wthread 2 w2 +]})
        with ({[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
              ⊎ {[+ wthread 2 w2 +]} : gmultiset expr)
        by multiset_solver.
      lb_next w1 w2 6 k1 2.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 6: srv β to s = 7; both workers in the mid band, so either
    worker's send on c can fire externally. *)
Lemma lbI_main_6 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (2 ≤ k1 ≤ 6)%nat → (2 ≤ k2 ≤ 6)%nat →
  (pirred ({[w1; w2]}, {[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 6 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 6 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
             ⊎ {[+ wthread k2 w2 +]})
      with (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}
             : gmultiset expr) ⊎ {[+ sv6 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv6_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: either worker's send on c *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        -- (* k1 = 4: worker1's external send *)
           rewrite (lbsty_send_l 6 k2); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 6 5 k2), ∅, ∅, {[w1; w2]},
             ({[+ sv6 w1 w2 +]} ⊎ {[+ wthread 5 w1 +]}
              ⊎ {[+ wthread k2 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 6 5 k2.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k1 = 6: close blocked, w1 ∈ C *)
           exfalso. simpl in *. set_solver.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wmid Hs Hk2 end.
        -- (* k2 = 4: worker2's external send *)
           rewrite (lbsty_send_r 6 k1); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 6 k1 5), ∅, ∅, {[w1; w2]},
             ({[+ sv6 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
              ⊎ {[+ wthread 5 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 6 k1 5.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k2 = 6: close blocked, w2 ∈ C *)
           exfalso. simpl in *. set_solver.
    + (* beta: srv, or either worker at k ∈ {2,3,5} *)
      lb_split.
      * match goal with Hs : tstep (sv6 _ _) _ _ |- _ =>
          apply tstep_sv6_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ sv7 w1 w2 +]})
          with ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 7 k1 k2.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        intros _.
        rewrite <-(lbsty_S_l 6 k1 k2); [|lia].
        replace (({[+ sv6 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread (S k1) w1 +]})
          with ({[+ sv6 w1 w2 +]} ⊎ {[+ wthread (S k1) w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 6 (S k1) k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wmid Hs Hk2 end.
        intros _.
        rewrite <-(lbsty_S_r 6 k1 k2); [|lia].
        lb_next w1 w2 6 k1 (S k2).
    + (* fork *) lb_split; lb_wkill.
    + (* msg *) lb_split; lb_wkill.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 7: srv offers the close on w1; it pairs internally with
    worker1 at k1 = 6, advancing to (s, k1) = (8, 7) and releasing w1
    from the restricted set. *)
Lemma lbI_main_7 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (2 ≤ k1 ≤ 6)%nat → (2 ≤ k2 ≤ 6)%nat →
  (pirred ({[w1; w2]}, {[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 7 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 7 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    destruct (decide (k1 = 4)%nat) as [->|Hk14];
      [|destruct (decide (k1 = 6)%nat) as [->|Hk16]].
    + (* k1 = 4: worker1's external send *)
      eapply Hirr.
      replace ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread 4 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]}
               : gmultiset expr) ⊎ {[+ wthread 4 w1 +]})
        by multiset_solver.
      eapply (PStepSession _ _ _ (SSend "c" EUnit));
        [apply wk4_send_step|simpl; set_solver].
    + (* k1 = 6: the internal close on w1 *)
      eapply Hirr.
      replace ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread 6 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ wthread k2 w2 +]} : gmultiset expr)
              ⊎ {[+ sv7 w1 w2 +]} ⊎ {[+ wthread 6 w1 +]})
        by multiset_solver.
      eapply PStepClose;
        [apply sv7_close_step|apply TStepHead, HeadClos|set_solver].
    + (* k1 ∈ {2,3,5}: worker1 β *)
      eapply Hirr.
      replace ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]}
               : gmultiset expr) ⊎ {[+ wthread k1 w1 +]})
        by multiset_solver.
      eapply PStepBeta. apply wthread_beta_step; lia.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: srv's close is blocked; either worker's send *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        -- (* k1 = 4: worker1's external send *)
           rewrite (lbsty_send_l 7 k2); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 7 5 k2), ∅, ∅, {[w1; w2]},
             ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread 5 w1 +]}
              ⊎ {[+ wthread k2 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 7 5 k2.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k1 = 6: close blocked externally, w1 ∈ C *)
           exfalso. simpl in *. set_solver.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wmid Hs Hk2 end.
        -- (* k2 = 4: worker2's external send *)
           rewrite (lbsty_send_r 7 k1); [|lia]. simpl.
           exists ∅, ∅, TUnit, (lbsty 7 k1 5), ∅, ∅, {[w1; w2]},
             ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
              ⊎ {[+ wthread 5 w2 +]}),
             ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ by rewrite !(left_id (∅ : senv) (∪)).
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ apply map_disjoint_empty_l.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ simpl. set_solver.
           ++ set_solver.
           ++ simpl. multiset_solver.
           ++ intros n. rewrite fmap_empty.
              rewrite (left_id (∅ : senv) (∪)). apply Vrel_unit.
           ++ lb_next w1 w2 7 k1 5.
           ++ apply topo_split_nil.
           ++ left; done.
        -- (* k2 = 6: close blocked, w2 ∈ C *)
           exfalso. simpl in *. set_solver.
    + (* beta: either worker at k ∈ {2,3,5} *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        intros _.
        rewrite <-(lbsty_S_l 7 k1 k2); [|lia].
        replace (({[+ sv7 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread (S k1) w1 +]})
          with ({[+ sv7 w1 w2 +]} ⊎ {[+ wthread (S k1) w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 7 (S k1) k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wmid Hs Hk2 end.
        intros _.
        rewrite <-(lbsty_S_r 7 k1 k2); [|lia].
        lb_next w1 w2 7 k1 (S k2).
    + (* fork *) lb_split; lb_wkill.
    + (* msg *) lb_split; lb_wkill.
    + (* close: the w1 synchronization with worker1 *)
      lb_split; [|lb_wkill| |lb_wkill|lb_wkill|lb_wkill].
      * (* srv paired with worker1 *)
        match goal with Hs : tstep (sv7 _ _) _ _ |- _ =>
          apply tstep_sv7_inv in Hs as [Hα ->] end.
        simplify_eq.
        match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        intros _.
        replace ({[w1; w2]} ∖ {[w1]}) with ({[w2]} : gset chan)
          by set_solver.
        replace ({[+ wthread k2 w2 +]} ⊎ {[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]})
          with ({[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 8 7 k2.
      * (* worker1 paired with srv *)
        match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wmid Hs Hk1 end.
        match goal with Hs : tstep (sv7 _ _) _ _ |- _ =>
          apply tstep_sv7_inv in Hs as [Hα ->] end.
        simplify_eq.
        intros _.
        replace ({[w1; w2]} ∖ {[w1]}) with ({[w2]} : gset chan)
          by set_solver.
        replace ({[+ wthread k2 w2 +]} ⊎ {[+ EUnit +]} ⊎ {[+ sv8 w1 w2 +]})
          with ({[+ sv8 w1 w2 +]} ⊎ {[+ EUnit +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 8 7 k2.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** The [LImain] group obligations for the mid stages s ∈ {4..7}:
    dispatch on the concrete srv stage; the per-stage lemmas keep the
    worker counters abstract and their statements are convertible to
    the dispatched goals. *)
Lemma lbI_case_main_mid w1 w2 s k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → lbvalid s k1 k2 →
  (4 ≤ s ≤ 7)%nat →
  (pirred (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, ((lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                         ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty s k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty s k1 k2]} TUnit
       (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                     ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 [Hs Hk] Hband.
  destruct s as [|[|[|[|[|[|[|[|s]]]]]]]]; try lia.
  - (* s = 4 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_4 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 5 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_5 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 6 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_6 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 7 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_7 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
Qed.

(** ** The [LImain] band s ∈ {0..3}

    Both workers are in the low band (k ∈ {0,1}), so every session
    stage of c is either Slb (s = 0) or S2 (s ∈ {1,2,3}).  The new
    obligation of this band is the external receive on c at s = 0;
    the s = 3 send on w1 pairs internally with worker1's receive at
    k1 = 1, entering the mid band at (s, k1) = (4, 2). *)

Lemma sv0_recv_step w1 w2 :
  tstep (sv0 w1 w2) (LSess (SRecv "c" EUnit)) (sv1 w1 w2).
Proof. apply TStepLetP, TStepHead, (HeadRecv "c" EUnit I). Qed.

Lemma sv3_send_step w1 w2 :
  tstep (sv3 w1 w2) (LSess (SSend w1 EUnit)) (sv4 w1 w2).
Proof. apply TStepAppR; [done|]. apply TStepHead, (HeadSend EUnit w1 I). Qed.

(** With both workers in the low band no send has completed, so the
    session stage of c past the receive is S2. *)
Lemma lbsty_lo s k1 k2 :
  (s ≠ 0)%nat → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat → lbsty s k1 k2 = S2.
Proof.
  intros Hs Hk1 Hk2. unfold lbsty, sentk.
  destruct (decide (s = 0)%nat); [lia|].
  destruct (decide (5 ≤ k1)%nat); [lia|].
  destruct (decide (5 ≤ k2)%nat); [lia|]. done.
Qed.

(** s = 0: the external receive on c; the received value is forced to
    EUnit, advancing to s = 1 with σ = S2. *)
Lemma lbI_main_0 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv0 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv0 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 0 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv0 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 0 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv0 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr (PSess (SRecv "c" EUnit))).
    replace ({[+ sv0 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
             ⊎ {[+ wthread k2 w2 +]})
      with (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}
             : gmultiset expr) ⊎ {[+ sv0 w1 w2 +]})
      by multiset_solver.
    eapply (PStepSession _ _ _ (SRecv "c" EUnit));
      [apply sv0_recv_step|set_solver].
  - intros π p' Hst. inversion Hst; subst.
    + (* session: the external receive on c *)
      lb_split; [|lb_wkill|lb_wkill].
      match goal with Hs : tstep (sv0 _ _) _ _ |- _ =>
        apply tstep_sv0_inv in Hs as (v & Hv & Hα & ->) end.
      simplify_eq. simpl.
      exists ∅, TUnit, S2. split_and!; [done|set_solver|].
      intros j Σ2 Hd2 Hc2 Hfr HV.
      apply Vrel_unit_iff in HV as [-> ->].
      rewrite (left_id (∅ : senv) (∪)).
      change (LetP (Pair EUnit (Chan "c")) (svA w1 w2)) with (sv1 w1 w2).
      replace (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
               ⊎ {[+ sv1 w1 w2 +]})
        with ({[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
              ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
        by multiset_solver.
      rewrite <-(lbsty_lo 1 k1 k2); [|lia|lia|lia].
      replace ({[w1; w2]} ∖ ∅ : gset chan) with ({[w1; w2]} : gset chan)
        by set_solver.
      lb_next w1 w2 1 k1 k2.
    + (* beta: either worker at k = 0 *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wlo Hs Hk1 end.
        intros _.
        replace (({[+ sv0 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread 1 w1 +]})
          with ({[+ sv0 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 0 1 k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 0 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg: nobody can send in this band *) lb_split; lb_wkill.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 1: srv β to s = 2; workers may warm up. *)
Lemma lbI_main_1 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 1 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 1 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv1 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
             ⊎ {[+ wthread k2 w2 +]})
      with (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}
             : gmultiset expr) ⊎ {[+ sv1 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv1_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: worker receives are blocked (w_i ∈ C) *)
      lb_split; lb_wkill.
    + (* beta: srv to s = 2, or either worker at k = 0 *)
      lb_split.
      * match goal with Hs : tstep (sv1 _ _) _ _ |- _ =>
          apply tstep_sv1_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ sv2 w1 w2 +]})
          with ({[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 2 k1 k2.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wlo Hs Hk1 end.
        intros _.
        replace (({[+ sv1 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread 1 w1 +]})
          with ({[+ sv1 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 1 1 k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 1 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg *) lb_split; lb_wkill.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 2: srv β to s = 3; workers may warm up. *)
Lemma lbI_main_2 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 2 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 2 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ sv2 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
             ⊎ {[+ wthread k2 w2 +]})
      with (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}
             : gmultiset expr) ⊎ {[+ sv2 w1 w2 +]})
      by multiset_solver.
    eapply PStepBeta. apply sv2_step.
  - intros π p' Hst. inversion Hst; subst.
    + (* session: worker receives are blocked (w_i ∈ C) *)
      lb_split; lb_wkill.
    + (* beta: srv to s = 3, or either worker at k = 0 *)
      lb_split.
      * match goal with Hs : tstep (sv2 _ _) _ _ |- _ =>
          apply tstep_sv2_inv in Hs as [_ ->] end.
        intros _.
        replace (({[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ sv3 w1 w2 +]})
          with ({[+ sv3 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 3 k1 k2.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wlo Hs Hk1 end.
        intros _.
        replace (({[+ sv2 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread 1 w1 +]})
          with ({[+ sv2 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 2 1 k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 2 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg *) lb_split; lb_wkill.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** s = 3: srv offers the send on w1; it pairs internally with
    worker1's receive at k1 = 1, entering the mid band at
    (s, k1) = (4, 2). *)
Lemma lbI_main_3 w1 w2 k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → (k1 ≤ 1)%nat → (k2 ≤ 1)%nat →
  (pirred ({[w1; w2]}, {[+ sv3 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, (({[w1; w2]}, {[+ sv3 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                        ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty 3 k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step ({[w1; w2]}, {[+ sv3 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                       ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty 3 k1 k2]} TUnit
       ({[w1; w2]}, {[+ sv3 w1 w2 +]} ⊎ {[+ wthread k1 w1 +]}
                    ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 Hk1 Hk2. split.
  - intros Hirr. exfalso.
    destruct k1 as [|[|k1]]; [| |lia].
    + (* k1 = 0: worker1 β *)
      eapply (Hirr PTau).
      replace ({[+ sv3 w1 w2 +]} ⊎ {[+ wthread 0 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ sv3 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]}
               : gmultiset expr) ⊎ {[+ wthread 0 w1 +]})
        by multiset_solver.
      eapply PStepBeta. apply wk0_step.
    + (* k1 = 1: the internal message on w1 *)
      eapply (Hirr PTau).
      replace ({[+ sv3 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]}
               ⊎ {[+ wthread k2 w2 +]})
        with (({[+ wthread k2 w2 +]} : gmultiset expr)
              ⊎ {[+ sv3 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]})
        by multiset_solver.
      eapply PStepMsg;
        [apply sv3_send_step|apply wk1_recv_step|set_solver].
  - intros π p' Hst. inversion Hst; subst.
    + (* session: srv's send and the worker receives are all blocked *)
      lb_split; lb_wkill.
    + (* beta: either worker at k = 0 *)
      lb_split.
      * lb_kill.
      * match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
          lb_wlo Hs Hk1 end.
        intros _.
        replace (({[+ sv3 w1 w2 +]} ⊎ {[+ wthread k2 w2 +]})
                 ⊎ {[+ wthread 1 w1 +]})
          with ({[+ sv3 w1 w2 +]} ⊎ {[+ wthread 1 w1 +]}
                ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
          by multiset_solver.
        lb_next w1 w2 3 1 k2.
      * match goal with Hs : tstep (wthread k2 w2) _ _ |- _ =>
          lb_wlo Hs Hk2 end.
        intros _. lb_next w1 w2 3 k1 1.
    + (* fork *) lb_split; lb_wkill.
    + (* msg: the internal w1 message *)
      lb_split; [ |lb_wkill|lb_wkill|lb_wkill|lb_wkill|lb_wkill].
      match goal with Hs : tstep (sv3 _ _) _ _ |- _ =>
        apply tstep_sv3_inv in Hs as [Hα ->] end.
      simplify_eq.
      match goal with Hs : tstep (wthread k1 w1) _ _ |- _ =>
        lb_wlo Hs Hk1 end.
      (* k1 = 1: the received value is forced to EUnit *)
      intros _.
      change (LetP (Pair EUnit (Chan w1)) wK) with (wthread 2 w1).
      replace ({[+ wthread k2 w2 +]} ⊎ {[+ sv4 w1 w2 +]}
               ⊎ {[+ wthread 2 w1 +]})
        with ({[+ sv4 w1 w2 +]} ⊎ {[+ wthread 2 w1 +]}
              ⊎ {[+ wthread k2 w2 +]} : gmultiset expr)
        by multiset_solver.
      lb_next w1 w2 4 2 k2.
    + (* close *) lb_split; lb_wkill.
    + (* internal forwarding: no forwarding redex *) lb_split; lb_wkill.
Qed.

(** The [LImain] group obligations for the early stages s ∈ {0..3}:
    dispatch on the concrete srv stage; the per-stage lemmas keep the
    worker counters abstract and their statements are convertible to
    the dispatched goals. *)
Lemma lbI_case_main_early w1 w2 s k1 k2 :
  w1 ≠ "c" → w2 ≠ "c" → w1 ≠ w2 → lbvalid s k1 k2 → (s ≤ 3)%nat →
  (pirred (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) →
   ∃ v E, ((lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                         ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) : proc)
            = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
          (∀ n, Vrel n {["c" := lbsty s k1 k2]} TUnit v) ∧
          (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                        ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p' →
     inv_case lbI {["c" := lbsty s k1 k2]} TUnit
       (lbC w1 w2 s, {[+ sstage s w1 w2 +]}
                     ⊎ {[+ wthread k1 w1 +]} ⊎ {[+ wthread k2 w2 +]}) π p').
Proof.
  intros Hw1 Hw2 Hw12 [Hs Hk] Hband.
  destruct s as [|[|[|[|s]]]]; try lia.
  - (* s = 0 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_0 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 1 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_1 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 2 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_2 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
  - (* s = 3 *)
    destruct Hk as [Hk1 Hk2].
    exact (lbI_main_3 w1 w2 k1 k2 Hw1 Hw2 Hw12 Hk1 Hk2).
Qed.

(** ** Assembly: the invariant rule and the semantic judgment *)

Lemma lbI_invariant : proc_invariant lbI.
Proof.
  intros Σ T p HI. destruct HI.
  - exact lbI_case_p0.
  - by apply lbI_case_p1.
  - by apply lbI_case_p2.
  - by apply lbI_case_p3.
  - (* LImain: dispatch on the srv stage *)
    destruct (decide (s ≤ 3)%nat) as [Hs3|Hs3];
      [by apply lbI_case_main_early|].
    destruct (decide (s ≤ 7)%nat) as [Hs7|Hs7].
    + apply lbI_case_main_mid; auto; lia.
    + apply lbI_case_main_late; auto; lia.
  - exact lbI_case_term.
Qed.

(** Example 3.16: lb inhabits the logical relation at
    c : ?∗.!∗.!∗.Close, at every step index — although it is
    syntactically untypable (w1, w2 and c are each used non-linearly
    across the server and the workers). *)
Theorem lb_sem_ptyped : sem_ptyped {["c" := Slb]} (∅, {[+ lb +]}) TUnit.
Proof.
  intro n. eapply Prel_by_invariant; [exact lbI_invariant|apply LIp0].
Qed.

(** ** The typable client q, and the composition *)

Lemma lenv_only_30 T : lenv_only [Some T; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_31 T : lenv_only [None; Some T; None] 1 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_50 T : lenv_only [Some T; None; None; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|[|[|[|y]]]]]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_51 T : lenv_only [None; Some T; None; None; None] 1 T.
Proof.
  split; [done|]. intros [|[|[|[|[|[|y]]]]]] T' H; simplify_eq/=; auto.
Qed.

(** q is syntactically typed at the dual interface !∗.?∗.?∗.Close. *)
Lemma q_typed :
  ptyped {["c" := dual Slb]} (∅, {[+ q +]}) TUnit.
Proof.
  apply ptyped_term; [constructor|].
  (* q = (λ c1. B) (send ⟨∗,c⟩), with c : !∗.?∗.?∗.Close *)
  eapply (typed_app _ ∅ {["c" := dual Slb]} _ [] [] _ _
            (TSess (SRcv TUnit (SRcv TUnit SEnd))));
    [apply senv_split_empty_l|constructor| |].
  - (* the abstraction *)
    apply typed_lam.
    (* B = let ⟨m,c2⟩ = recv c1 in … at c1 : ?∗.?∗.Close *)
    eapply (typed_letp _ ∅ ∅ _ [Some (TSess (SRcv TUnit (SRcv TUnit SEnd)))]
              [None] _ _ TUnit (TSess (SRcv TUnit SEnd)));
      [apply senv_split_empty_l|repeat constructor| |].
    + eapply (typed_app _ ∅ ∅ _ [None]
                [Some (TSess (SRcv TUnit (SRcv TUnit SEnd)))]
                _ _ (TSess (SRcv TUnit (SRcv TUnit SEnd))));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_konst;
          [by (repeat apply lenv_empty_cons; apply lenv_empty_nil)|].
        apply (KTRecv TUnit (SRcv TUnit SEnd)).
      * apply typed_var, lenv_only_1.
    + (* let ∗ = m in …, with c2 : ?∗.Close at idx 0, m : ∗ at idx 1 *)
      eapply (typed_letu _ ∅ ∅ _ [None; Some TUnit; None]
                [Some (TSess (SRcv TUnit SEnd)); None; None]);
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_var, lenv_only_31.
      * (* let ⟨m,c3⟩ = recv c2 in … *)
        eapply (typed_letp _ ∅ ∅ _
                  [Some (TSess (SRcv TUnit SEnd)); None; None]
                  [None; None; None] _ _ TUnit (TSess SEnd));
          [apply senv_split_empty_l|repeat constructor| |].
        { eapply (typed_app _ ∅ ∅ _ [None; None; None]
                    [Some (TSess (SRcv TUnit SEnd)); None; None]
                    _ _ (TSess (SRcv TUnit SEnd)));
            [apply senv_split_empty_l|repeat constructor| |].
          - apply typed_konst;
              [by (repeat apply lenv_empty_cons; apply lenv_empty_nil)|].
            apply (KTRecv TUnit SEnd).
          - apply typed_var, lenv_only_30. }
        (* let ∗ = m in clos c3 *)
        eapply (typed_letu _ ∅ ∅ _ [None; Some TUnit; None; None; None]
                  [Some (TSess SEnd); None; None; None; None]);
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_var, lenv_only_51. }
        eapply (typed_app _ ∅ ∅ _
                  [None; None; None; None; None]
                  [Some (TSess SEnd); None; None; None; None]
                  _ _ (TSess SEnd));
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_konst;
            [by (repeat apply lenv_empty_cons; apply lenv_empty_nil)|].
          apply KTClos. }
        { apply typed_var, lenv_only_50. }
  - (* send ⟨∗,c⟩ : ?∗.?∗.Close *)
    eapply (typed_app _ ∅ {["c" := dual Slb]} _ [] []
              _ _ (TProd TUnit
                     (TSess (SSnd TUnit (SRcv TUnit (SRcv TUnit SEnd))))));
      [apply senv_split_empty_l|constructor| |].
    + apply typed_konst; [apply lenv_empty_nil|].
      apply (KTSend TUnit (SRcv TUnit (SRcv TUnit SEnd))).
    + eapply (typed_pair _ ∅ {["c" := dual Slb]} _ [] []);
        [apply senv_split_empty_l|constructor| |].
      * apply typed_unit, lenv_empty_nil.
      * apply typed_chan, lenv_empty_nil.
Qed.

(** Deadlock freedom of the closed composite ({c}, ⟨lb, q⟩): semantic
    P-Connect plugs the untypable lb against the typed client, and
    adequacy concludes. *)
Theorem lb_deadlock_free :
  deadlock_free (∅ ∪ ∅ ∪ {["c"]}, {[+ lb +]} ⊎ {[+ q +]}).
Proof.
  apply adequacy with (T := TUnit).
  apply (sem_ptyped_connect ∅ ∅ ∅ "c" Slb ∅ {[+ lb +]} ∅ {[+ q +]} TUnit);
    [constructor|apply senv_split_empty_l
    |set_solver|set_solver|set_solver|set_solver|set_solver
    |set_solver|set_solver|set_solver|set_solver| |].
  - rewrite insert_empty. exact lb_sem_ptyped.
  - rewrite insert_empty. exact (fundamental_proc _ _ _ q_typed).
Qed.
