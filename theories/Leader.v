(** * Leader election (§4.1): untypable, but in the logical relation

    Three threads share a channel d: ld0 sends false then true on d and
    closes it; ld1 and ld2 each receive one boolean on d (a race), then
    synchronize by closing cs; ld2 closes d; the thread that received
    true announces the election result on the interface channel c by
    sending its token (left for ld1, right for ld2) and closing c —
    the simulated select on c : Close ⊕ Close = !(∗+∗).Close.

    d has three users and c two potential users, so the process is
    untypable (linearity), and it is not reachable from a single closed
    term. We prove membership in the process logical relation directly,
    with the invariant method of Method.v, then compose with a
    syntactically typed client q via P-Connect and conclude deadlock
    freedom of the closed composite — the paper's p0.

    The paper's Appendix A trace is followed exactly, with two
    repairs: the interface channel c is not restricted in p0 (its
    final transitions are environment-facing, so c ∉ C), and the
    transmitted choice is the boolean token inj_i ∗ (the type
    Close ⊕ Close unfolds to !(∗+∗).Close under the branch/choice
    simulation with both continuations trivial). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import LogRel Compositionality Method Examples.

Local Open Scope string_scope.

(** ** Booleans as sums, and the one-shot choice protocol *)

Notation TBool := (TSum TUnit TUnit).
Notation ETrue := (Inj1 EUnit).
Notation EFalse := (Inj2 EUnit).

Definition bv (b : bool) : expr := if b then ETrue else EFalse.

Lemma bv_val b : is_val (bv b).
Proof. by destruct b. Qed.

Lemma fchans_bv b : fchans (bv b) = ∅.
Proof. by destruct b. Qed.

Lemma Vrel_bv n b : Vrel n ∅ TBool (bv b).
Proof.
  destruct b; simpl; [apply Vrel_inj1|apply Vrel_inj2]; apply Vrel_unit.
Qed.

(** if-then-else: case analysis consuming the unit payload. Only used
    with closed branches (the Case binder does not capture). *)
Definition eif (b e1 e2 : expr) : expr :=
  Case b (LetU (Var 0) e1) (LetU (Var 0) e2).

(** The interface protocol "Close ⊕ Close": one bit, then close. *)
Definition Slead : sty := SSnd TBool SEnd.

(** The two selections on c. *)
Definition selL : expr := App EClos (App ESend (Pair ETrue (Chan "c"))).
Definition selR : expr := App EClos (App ESend (Pair EFalse (Chan "c"))).

(** ** The three threads *)

Definition ld0 : expr :=
  App EClos (App ESend (Pair ETrue (App ESend (Pair EFalse (Chan "d"))))).
Definition ld1body : expr :=
  LetU (App EClos (Chan "cs")) (eif (Var 1) selL EUnit).
Definition ld1 : expr := LetP (App ERecv (Chan "d")) ld1body.
Definition ld2body : expr :=
  LetU (App EClos (Chan "cs"))
    (LetU (App EClos (Var 0)) (eif (Var 1) selR EUnit)).
Definition ld2 : expr := LetP (App ERecv (Chan "d")) ld2body.

Definition leader_proc : proc :=
  ({["cs"; "d"]}, {[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]}).

(** ** Stage dispatch

    Each thread's reachable local states. [l1k]/[l2m] are parametrized
    by the received boolean b; the false-holder finishes at stage 6
    (resp. 8), the true-holder continues through the send and close
    on c to stage 8 (resp. 10). *)

Definition l0s (s : nat) : expr :=
  match s with
  | 0 => ld0
  | 1 => App EClos (App ESend (Pair ETrue (Chan "d")))
  | 2 => App EClos (Chan "d")
  | _ => EUnit
  end.

Definition l1k (k : nat) (b : bool) : expr :=
  match k with
  | 0 => ld1
  | 1 => LetP (Pair (bv b) (Chan "d")) ld1body
  | 2 => LetU (App EClos (Chan "cs")) (eif (bv b) selL EUnit)
  | 3 => LetU EUnit (eif (bv b) selL EUnit)
  | 4 => eif (bv b) selL EUnit
  | 5 => LetU EUnit (if b then selL else EUnit)
  | 6 => if b then selL else EUnit
  | 7 => App EClos (Chan "c")
  | _ => EUnit
  end.

Definition l2m (m : nat) (b : bool) : expr :=
  match m with
  | 0 => ld2
  | 1 => LetP (Pair (bv b) (Chan "d")) ld2body
  | 2 => LetU (App EClos (Chan "cs"))
           (LetU (App EClos (Chan "d")) (eif (bv b) selR EUnit))
  | 3 => LetU EUnit (LetU (App EClos (Chan "d")) (eif (bv b) selR EUnit))
  | 4 => LetU (App EClos (Chan "d")) (eif (bv b) selR EUnit)
  | 5 => LetU EUnit (eif (bv b) selR EUnit)
  | 6 => eif (bv b) selR EUnit
  | 7 => LetU EUnit (if b then selR else EUnit)
  | 8 => if b then selR else EUnit
  | 9 => App EClos (Chan "c")
  | _ => EUnit
  end.

(** The interface environment as a function of the winner's progress
    on c: 0 = choice not yet sent, 1 = sent, 2 = closed. *)
Definition lΣ (cp : nat) : senv :=
  match cp with
  | 0 => {["c" := Slead]}
  | 1 => {["c" := SEnd]}
  | _ => ∅
  end.

(** Winner progress on c from the winner's stage: [jsel] is the stage
    at which the select redex sits (6 for ld1, 8 for ld2). *)
Definition cpk (jsel j : nat) : nat :=
  if decide (j ≤ jsel)%nat then 0 else if decide (j = S jsel)%nat then 1 else 2.

Definition lC (s : nat) : gset chan :=
  if decide (s = 2)%nat then {["d"]} else ∅.

(** β-substitution sanity: the LetP redexes step to stage 2. *)
Lemma ld1body_subst b : subst2 (bv b) (Chan "d") ld1body = l1k 2 b.
Proof. by destruct b. Qed.

Lemma ld2body_subst b : subst2 (bv b) (Chan "d") ld2body = l2m 2 b.
Proof. by destruct b. Qed.

(** ** The invariant

    Phases: LI0 nobody has received; LI1a/LI1b exactly the first
    boolean (false) delivered, to ld1 resp. ld2; LI2 both delivered
    (wb = "ld1 holds true"), cs not yet closed; LI3a/LI3b after the
    cs synchronization, split by winner. In LI3x, s and m are coupled
    by the d closure (a joint step of ld0 and ld2), and Σ follows the
    winner's progress on c. *)

Inductive leadI : senv → ty → proc → Prop :=
  | LI0 :
      leadI {["c" := Slead]} TUnit
        ({["cs"; "d"]}, {[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]})
  | LI1a k : (1 ≤ k ≤ 2)%nat →
      leadI {["c" := Slead]} TUnit
        ({["cs"; "d"]},
         {[+ l0s 1 +]} ⊎ {[+ l1k k false +]} ⊎ {[+ ld2 +]})
  | LI1b m : (1 ≤ m ≤ 2)%nat →
      leadI {["c" := Slead]} TUnit
        ({["cs"; "d"]},
         {[+ l0s 1 +]} ⊎ {[+ ld1 +]} ⊎ {[+ l2m m false +]})
  | LI2 (wb : bool) k m : (1 ≤ k ≤ 2)%nat → (1 ≤ m ≤ 2)%nat →
      leadI {["c" := Slead]} TUnit
        ({["cs"; "d"]},
         {[+ l0s 2 +]} ⊎ {[+ l1k k wb +]} ⊎ {[+ l2m m (negb wb) +]})
  | LI3a k m s : (3 ≤ k ≤ 8)%nat → (3 ≤ m ≤ 8)%nat →
      (s = 2 ∧ (m ≤ 4)%nat ∨ s = 3 ∧ (5 ≤ m)%nat) →
      leadI (lΣ (cpk 6 k)) TUnit
        (lC s, {[+ l0s s +]} ⊎ {[+ l1k k true +]} ⊎ {[+ l2m m false +]})
  | LI3b k m s : (3 ≤ k ≤ 6)%nat → (3 ≤ m ≤ 10)%nat →
      (s = 2 ∧ (m ≤ 4)%nat ∨ s = 3 ∧ (5 ≤ m)%nat) →
      leadI (lΣ (cpk 8 m)) TUnit
        (lC s, {[+ l0s s +]} ⊎ {[+ l1k k false +]} ⊎ {[+ l2m m true +]}).

(** ** Multiset inversion for three-thread processes *)

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

(** ** Transition inversions for the stage shapes *)

(** clos applied to a send redex: the send fires. *)
Lemma tstep_clos_send_inv v c α e' :
  is_val v →
  tstep (App EClos (App ESend (Pair v (Chan c)))) α e' →
  α = LSess (SSend c v) ∧ e' = App EClos (Chan c).
Proof.
  intros Hv H.
  apply tstep_app_inv in H
    as [(e1' & Hst & _)|[(_ & e2' & Hst & ->)|(_ & Hnv & _)]].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - apply tstep_send_val_inv in Hst as [-> ->]; auto.
  - done.
Qed.

(** ld0's first transition: the inner send fires. *)
Lemma tstep_ld0_inv α e' :
  tstep ld0 α e' → α = LSess (SSend "d" EFalse) ∧ e' = l0s 1.
Proof.
  intros H.
  apply tstep_app_inv in H
    as [(e1' & Hst & _)|[(_ & e2' & Hst & ->)|(_ & Hnv & _)]].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - apply tstep_app_inv in Hst
      as [(e1'' & Hst' & _)|[(_ & e2'' & Hst' & ->)|(_ & _ & Hh)]].
    + exfalso. eapply val_no_tstep; [exact Hst'|done].
    + apply tstep_pair_inv in Hst'
        as [(f1 & Hst'' & _)|(_ & f2 & Hst'' & ->)].
      * exfalso. eapply val_no_tstep; [exact Hst''|done].
      * apply tstep_send_val_inv in Hst'' as [-> ->]; auto.
    + inversion Hh.
  - done.
Qed.

Lemma tstep_ld0b_inv α e' :
  tstep (l0s 1) α e' → α = LSess (SSend "d" ETrue) ∧ e' = l0s 2.
Proof. apply tstep_clos_send_inv. done. Qed.

(** The case redex on a boolean: β to the chosen branch. Stated for
    the two concrete selections. *)
Lemma tstep_eifL_inv b α e' :
  tstep (eif (bv b) selL EUnit) α e' →
  α = LBeta ∧ e' = LetU EUnit (if b then selL else EUnit).
Proof.
  intros H. destruct b; simpl in H;
    apply tstep_case_inv in H
      as [(e'' & Hst & _)|[(v & Heq & _ & -> & ->)|(v & Heq & _ & -> & ->)]];
    simplify_eq; try done.
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
Qed.

Lemma tstep_eifR_inv b α e' :
  tstep (eif (bv b) selR EUnit) α e' →
  α = LBeta ∧ e' = LetU EUnit (if b then selR else EUnit).
Proof.
  intros H. destruct b; simpl in H;
    apply tstep_case_inv in H
      as [(e'' & Hst & _)|[(v & Heq & _ & -> & ->)|(v & Heq & _ & -> & ->)]];
    simplify_eq; try done.
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
Qed.

(** The selections: an external send on c, then a close on c. *)
Lemma tstep_selL_inv α e' :
  tstep selL α e' → α = LSess (SSend "c" ETrue) ∧ e' = App EClos (Chan "c").
Proof. apply tstep_clos_send_inv. done. Qed.

Lemma tstep_selR_inv α e' :
  tstep selR α e' → α = LSess (SSend "c" EFalse) ∧ e' = App EClos (Chan "c").
Proof. apply tstep_clos_send_inv. done. Qed.

(** ** The τ branch of [inv_case], as an introduction rule *)

Lemma inv_case_tau I Σ T p C' M' :
  (C' ## dom Σ → I Σ T (C', M')) → inv_case I Σ T p PTau (C', M').
Proof. intros H. exact H. Qed.

(** ** Step existence for the stage shapes *)

Lemma tstep_ld0_ex : tstep ld0 (LSess (SSend "d" EFalse)) (l0s 1).
Proof.
  apply TStepAppR; [done|]. apply TStepAppR; [done|].
  apply TStepPairR; [done|]. apply TStepHead. by apply HeadSend.
Qed.

Lemma tstep_l0s1_ex : tstep (l0s 1) (LSess (SSend "d" ETrue)) (l0s 2).
Proof. apply TStepAppR; [done|]. apply TStepHead. by apply HeadSend. Qed.

Lemma tstep_ld1_ex b : tstep ld1 (LSess (SRecv "d" (bv b))) (l1k 1 b).
Proof. apply TStepLetP, TStepHead. apply HeadRecv, bv_val. Qed.

Lemma tstep_ld2_ex b : tstep ld2 (LSess (SRecv "d" (bv b))) (l2m 1 b).
Proof. apply TStepLetP, TStepHead. apply HeadRecv, bv_val. Qed.

Lemma tstep_l1k1_ex b : tstep (l1k 1 b) LBeta (l1k 2 b).
Proof.
  rewrite <-(ld1body_subst b). apply TStepHead.
  apply HeadLetP; [apply bv_val|done].
Qed.

Lemma tstep_l2m1_ex b : tstep (l2m 1 b) LBeta (l2m 2 b).
Proof.
  rewrite <-(ld2body_subst b). apply TStepHead.
  apply HeadLetP; [apply bv_val|done].
Qed.

Lemma tstep_l1k2_ex b : tstep (l1k 2 b) (LSess (SClos "cs")) (l1k 3 b).
Proof. apply TStepLetU, TStepHead, HeadClos. Qed.

Lemma tstep_l2m2_ex b : tstep (l2m 2 b) (LSess (SClos "cs")) (l2m 3 b).
Proof. apply TStepLetU, TStepHead, HeadClos. Qed.

(** ** Obligation lemmas: one per invariant constructor

    Each lemma checks the two [proc_invariant] clauses for the
    configurations of one constructor group.  For LI0/LI1a/LI1b/LI2
    the configurations are never irreducible (a τ step is always
    enabled), all session-labelled steps are refuted (their subject is
    the restricted cs or d), and every real τ successor lands back in
    [leadI]. *)

Lemma leadI_case_0 :
  let p := ({["cs"; "d"]} : gset chan,
            {[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n {["c" := Slead]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI {["c" := Slead]} TUnit p π p').
Proof.
  cbv zeta. split.
  - (* never irreducible: ld0 delivers false to ld1 *)
    intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]})
      with (({[+ ld2 +]} ⊎ {[+ ld0 +]} ⊎ {[+ ld1 +]}) : gmultiset expr)
      by multiset_solver.
    eapply PStepMsg;
      [exact tstep_ld0_ex|exact (tstep_ld1_ex false)|set_solver].
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subjects cs/d are restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* msg: ld0 delivers false to ld1 (→ LI1a 1) or ld2 (→ LI1b 1) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&->)|[(->&->&->)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_ld0_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply tstep_ld0_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq; apply inv_case_tau; intros _.
      * (* → LI1a 1 *)
        replace ({[+ ld2 +]} ⊎ {[+ l0s 1 +]}
                   ⊎ {[+ LetP (Pair EFalse (Chan "d")) ld1body +]})
          with ({[+ l0s 1 +]} ⊎ {[+ LetP (Pair EFalse (Chan "d")) ld1body +]}
                  ⊎ {[+ ld2 +]} : gmultiset expr)
          by multiset_solver.
        apply (LI1a 1); lia.
      * (* → LI1b 1 *)
        replace ({[+ ld1 +]} ⊎ {[+ l0s 1 +]}
                   ⊎ {[+ LetP (Pair EFalse (Chan "d")) ld2body +]})
          with ({[+ l0s 1 +]} ⊎ {[+ ld1 +]}
                  ⊎ {[+ LetP (Pair EFalse (Chan "d")) ld2body +]}
                : gmultiset expr)
          by multiset_solver.
        apply (LI1b 1); lia.
    + (* close: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_ld0_inv in Hse as [Hα _]
          |apply tstep_ld0_inv in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq.
Qed.

Lemma leadI_case_1a k : (1 ≤ k ≤ 2)%nat →
  let p := ({["cs"; "d"]} : gset chan,
            {[+ l0s 1 +]} ⊎ {[+ l1k k false +]} ⊎ {[+ ld2 +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n {["c" := Slead]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI {["c" := Slead]} TUnit p π p').
Proof.
  intros Hk. cbv zeta. split.
  - (* never irreducible: l0s 1 delivers true to ld2 *)
    intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ l0s 1 +]} ⊎ {[+ l1k k false +]} ⊎ {[+ ld2 +]})
      with (({[+ l1k k false +]} ⊎ {[+ l0s 1 +]} ⊎ {[+ ld2 +]})
            : gmultiset expr)
      by multiset_solver.
    eapply PStepMsg;
      [exact tstep_l0s1_ex|exact (tstep_ld2_ex true)|set_solver].
  - assert (k = 1 ∨ k = 2) as [->| ->] by lia;
      intros π p' Hst; inversion Hst; subst.
    + (* k = 1, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 1, beta: the LetP redex fires (→ LI1a 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> ->]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [_ ->]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      rewrite ld1body_subst.
      replace ({[+ l0s 1 +]} ⊎ {[+ ld2 +]} ⊎ {[+ l1k 2 false +]})
        with ({[+ l0s 1 +]} ⊎ {[+ l1k 2 false +]} ⊎ {[+ ld2 +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI1a 2); lia.
    + (* k = 1, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* k = 1, msg: l0s 1 delivers true to ld2 (→ LI2 false 1 1) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&->)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hsf as [Hα2 _]
          |apply tstep_ld0b_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      replace ({[+ l1k 1 false +]} ⊎ {[+ l0s 2 +]}
                 ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld2body +]})
        with ({[+ l0s 2 +]} ⊎ {[+ l1k 1 false +]}
                ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld2body +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI2 false 1 1); lia.
    + (* k = 1, close: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_ld0b_inv in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* k = 2, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 2, beta: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* k = 2, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)]
      end; simplify_eq.
    + (* k = 2, msg: l0s 1 delivers true to ld2 (→ LI2 false 2 1) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&->)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply tstep_ld0b_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      replace ({[+ l1k 2 false +]} ⊎ {[+ l0s 2 +]}
                 ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld2body +]})
        with ({[+ l0s 2 +]} ⊎ {[+ l1k 2 false +]}
                ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld2body +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI2 false 2 1); lia.
    + (* k = 2, close: cs has only one closer here *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_ld0b_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)]
      end; simplify_eq.
Qed.

Lemma leadI_case_1b m : (1 ≤ m ≤ 2)%nat →
  let p := ({["cs"; "d"]} : gset chan,
            {[+ l0s 1 +]} ⊎ {[+ ld1 +]} ⊎ {[+ l2m m false +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n {["c" := Slead]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI {["c" := Slead]} TUnit p π p').
Proof.
  intros Hm. cbv zeta. split.
  - (* never irreducible: l0s 1 delivers true to ld1 *)
    intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ l0s 1 +]} ⊎ {[+ ld1 +]} ⊎ {[+ l2m m false +]})
      with (({[+ l2m m false +]} ⊎ {[+ l0s 1 +]} ⊎ {[+ ld1 +]})
            : gmultiset expr)
      by multiset_solver.
    eapply PStepMsg;
      [exact tstep_l0s1_ex|exact (tstep_ld1_ex true)|set_solver].
  - assert (m = 1 ∨ m = 2) as [->| ->] by lia;
      intros π p' Hst; inversion Hst; subst.
    + (* m = 1, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* m = 1, beta: the LetP redex fires (→ LI1b 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> ->]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [_ ->]]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      rewrite ld2body_subst.
      apply (LI1b 2); lia.
    + (* m = 1, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hs as [Hα _]]
      end; simplify_eq.
    + (* m = 1, msg: l0s 1 delivers true to ld1 (→ LI2 true 1 1) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&->)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hsf as [Hα2 _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      replace ({[+ l2m 1 false +]} ⊎ {[+ l0s 2 +]}
                 ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld1body +]})
        with ({[+ l0s 2 +]} ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld1body +]}
                ⊎ {[+ l2m 1 false +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI2 true 1 1); lia.
    + (* m = 1, close: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv false) (Chan "d") _ _ _
                    (bv_val false) I) in Hse as [Hα _]]
      end; simplify_eq.
    + (* m = 2, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* m = 2, beta: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* m = 2, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_ld0b_inv in Hs as [Hα _]
          |apply tstep_letp_recv_inv in Hs as (? & _ & Hα & _)
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* m = 2, msg: l0s 1 delivers true to ld1 (→ LI2 true 1 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&->)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα ->];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & ->)
          |apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      replace ({[+ l2m 2 false +]} ⊎ {[+ l0s 2 +]}
                 ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld1body +]})
        with ({[+ l0s 2 +]} ⊎ {[+ LetP (Pair ETrue (Chan "d")) ld1body +]}
                ⊎ {[+ l2m 2 false +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI2 true 1 2); lia.
    + (* m = 2, close: cs has only one closer here *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_ld0b_inv in Hse as [Hα _]
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letp_recv_inv in Hse as (? & _ & Hα & _)
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_ld0b_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_letp_recv_inv in Hsf as (? & _ & Hα2 & _)]
      end; simplify_eq.
Qed.

Lemma leadI_case_2 (wb : bool) k m : (1 ≤ k ≤ 2)%nat → (1 ≤ m ≤ 2)%nat →
  let p := ({["cs"; "d"]} : gset chan,
            {[+ l0s 2 +]} ⊎ {[+ l1k k wb +]} ⊎ {[+ l2m m (negb wb) +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n {["c" := Slead]} TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI {["c" := Slead]} TUnit p π p').
Proof.
  intros Hk Hm. cbv zeta. split.
  - (* never irreducible: a β step, or the cs synchronization *)
    intros Hirr. exfalso.
    assert (k = 1 ∨ k = 2) as [->| ->] by lia.
    + eapply (Hirr PTau).
      replace ({[+ l0s 2 +]} ⊎ {[+ l1k 1 wb +]} ⊎ {[+ l2m m (negb wb) +]})
        with (({[+ l0s 2 +]} ⊎ {[+ l2m m (negb wb) +]} ⊎ {[+ l1k 1 wb +]})
              : gmultiset expr)
        by multiset_solver.
      eapply PStepBeta. exact (tstep_l1k1_ex wb).
    + assert (m = 1 ∨ m = 2) as [->| ->] by lia.
      * eapply (Hirr PTau).
        eapply PStepBeta. exact (tstep_l2m1_ex (negb wb)).
      * eapply (Hirr PTau).
        eapply PStepClose;
          [exact (tstep_l1k2_ex wb)
          |exact (tstep_l2m2_ex (negb wb))
          |set_solver].
  - assert (k = 1 ∨ k = 2) as [->| ->] by lia;
      assert (m = 1 ∨ m = 2) as [->| ->] by lia;
      intros π p' Hst; inversion Hst; subst.
    + (* k = 1, m = 1, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 1, m = 1, beta: either LetP redex fires *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> ->]|[-> ->]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [_ ->]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [_ ->]]
      end; simplify_eq.
      * (* → LI2 wb 2 1 *)
        apply inv_case_tau; intros _.
        rewrite ld1body_subst.
        replace ({[+ l0s 2 +]} ⊎ {[+ l2m 1 (negb wb) +]} ⊎ {[+ l1k 2 wb +]})
          with ({[+ l0s 2 +]} ⊎ {[+ l1k 2 wb +]} ⊎ {[+ l2m 1 (negb wb) +]}
                : gmultiset expr)
          by multiset_solver.
        apply (LI2 wb 2 1); lia.
      * (* → LI2 wb 1 2 *)
        apply inv_case_tau; intros _.
        rewrite ld2body_subst.
        apply (LI2 wb 1 2); lia.
    + (* k = 1, m = 1, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [Hα _]]
      end; simplify_eq.
    + (* k = 1, m = 1, msg: no send *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_clos_inv in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 1, m = 1, close: no partner for l0s 2 *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hsf as [Hα2 _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hsf as [Hα2 _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 1, m = 2, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 1, m = 2, beta: the LetP redex fires (→ LI2 wb 2 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> ->]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [_ ->]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      rewrite ld1body_subst.
      replace ({[+ l0s 2 +]} ⊎ {[+ l2m 2 (negb wb) +]} ⊎ {[+ l1k 2 wb +]})
        with ({[+ l0s 2 +]} ⊎ {[+ l1k 2 wb +]} ⊎ {[+ l2m 2 (negb wb) +]}
              : gmultiset expr)
        by multiset_solver.
      apply (LI2 wb 2 2); lia.
    + (* k = 1, m = 2, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* k = 1, m = 2, msg: no send *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_clos_inv in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 1, m = 2, close: d and cs have single closers *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hsf as [Hα2 _]
          |apply tstep_clos_inv in Hse as [Hα _];
           apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply (tstep_letp_pair_inv (bv wb) (Chan "d") _ _ _
                    (bv_val wb) I) in Hsf as [Hα2 _]]
      end; simplify_eq.
    + (* k = 2, m = 1, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 2, m = 1, beta: the LetP redex fires (→ LI2 wb 2 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> ->]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [_ ->]]
      end; simplify_eq.
      apply inv_case_tau; intros _.
      rewrite ld2body_subst.
      apply (LI2 wb 2 2); lia.
    + (* k = 2, m = 1, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hs as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 1, msg: no send *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 1, close: d and cs have single closers *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|(->&->&_)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _];
           apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hsf as [Hα2 _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]
          |apply (tstep_letp_pair_inv (bv (negb wb)) (Chan "d") _ _ _
                    (bv_val (negb wb)) I) in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 2, session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* k = 2, m = 2, beta: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 2, fork: none *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_triple_inv in Heq as [[-> _]|[[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]
          |apply tstep_letu_clos_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 2, msg: no send *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hse : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&_)|[(->&_)|[(->&_)|[(->&_)|[(->&_)|(->&_)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]
          |apply tstep_letu_clos_inv in Hse as [Hα _]]
      end; simplify_eq.
    + (* k = 2, m = 2, close: the cs synchronization (→ LI3a/LI3b 3 3 2) *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)|[(->&->&->)
               |[(->&->&_)|(->&->&->)]]]]];
          [apply tstep_clos_inv in Hse as [Hα _];
           apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply tstep_clos_inv in Hse as [Hα _];
           apply tstep_letu_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα ->];
           apply tstep_letu_clos_inv in Hsf as [Hα2 ->]
          |apply tstep_letu_clos_inv in Hse as [Hα _];
           apply tstep_clos_inv in Hsf as [Hα2 _]
          |apply tstep_letu_clos_inv in Hse as [Hα ->];
           apply tstep_letu_clos_inv in Hsf as [Hα2 ->]]
      end; simplify_eq.
      * (* l1k closes first *)
        apply inv_case_tau; intros _.
        replace ({["cs"; "d"]} ∖ {["cs"]} : gset chan)
          with ({["d"]} : gset chan) by set_solver.
        destruct wb.
        -- apply (LI3a 3 3 2); [lia|lia|left; split; lia].
        -- apply (LI3b 3 3 2); [lia|lia|left; split; lia].
      * (* l2m closes first *)
        apply inv_case_tau; intros _.
        replace ({["cs"; "d"]} ∖ {["cs"]} : gset chan)
          with ({["d"]} : gset chan) by set_solver.
        replace ({[+ l0s 2 +]}
                   ⊎ {[+ LetU EUnit
                          (LetU (App EClos (Chan "d"))
                             (eif (bv (negb wb)) selR EUnit)) +]}
                   ⊎ {[+ LetU EUnit (eif (bv wb) selL EUnit) +]})
          with ({[+ l0s 2 +]} ⊎ {[+ LetU EUnit (eif (bv wb) selL EUnit) +]}
                  ⊎ {[+ LetU EUnit
                         (LetU (App EClos (Chan "d"))
                            (eif (bv (negb wb)) selR EUnit)) +]}
                : gmultiset expr)
          by multiset_solver.
        destruct wb.
        -- apply (LI3a 3 3 2); [lia|lia|left; split; lia].
        -- apply (LI3b 3 3 2); [lia|lia|left; split; lia].
Qed.

(** ** Helper facts about the stage-indexed sets *)

Lemma lC2 : lC 2 = {["d"]}.
Proof. done. Qed.

Lemma lC3 : lC 3 = ∅.
Proof. done. Qed.

Lemma c_not_lC s : "c" ∉ lC s.
Proof. unfold lC. case_decide; set_solver. Qed.

(** ** Step existence for the stages k ≥ 3 / m ≥ 3 *)

Lemma tstep_letu_unit_ex e : tstep (LetU EUnit e) LBeta e.
Proof. apply TStepHead, HeadLetU. Qed.

Lemma tstep_l1k4_ex b : tstep (l1k 4 b) LBeta (l1k 5 b).
Proof.
  destruct b; apply TStepHead; [by apply HeadCase1|by apply HeadCase2].
Qed.

Lemma tstep_l2m6_ex b : tstep (l2m 6 b) LBeta (l2m 7 b).
Proof.
  destruct b; apply TStepHead; [by apply HeadCase1|by apply HeadCase2].
Qed.

Lemma tstep_l0s2_ex : tstep (l0s 2) (LSess (SClos "d")) (l0s 3).
Proof. apply TStepHead, HeadClos. Qed.

Lemma tstep_l2m4_ex b : tstep (l2m 4 b) (LSess (SClos "d")) (l2m 5 b).
Proof. apply TStepLetU, TStepHead, HeadClos. Qed.

Lemma tstep_selL_ex : tstep selL (LSess (SSend "c" ETrue)) (l1k 7 true).
Proof. apply TStepAppR; [done|]. apply TStepHead. by apply HeadSend. Qed.

Lemma tstep_selR_ex : tstep selR (LSess (SSend "c" EFalse)) (l2m 9 true).
Proof. apply TStepAppR; [done|]. apply TStepHead. by apply HeadSend. Qed.

Lemma tstep_closc_ex : tstep (App EClos (Chan "c")) (LSess (SClos "c")) EUnit.
Proof. apply TStepHead, HeadClos. Qed.

(** ** Packaged inversion tactics for the high stages

    [stage_inv Hs] inverts a [tstep] hypothesis whose source is one of
    the stage shapes at k ≥ 3 / m ≥ 3 (or refutes it when the source is
    a value), leaving the label and successor equations; [thread3] /
    [thread32] identify the stepping thread(s) in the three-thread
    multiset. *)

Local Ltac stage_inv Hs :=
  first
    [ exfalso; eapply val_no_tstep; [exact Hs|done]
    | apply tstep_letu_unit_inv in Hs as [? ?]
    | apply tstep_letu_clos_inv in Hs as [? ?]
    | apply tstep_clos_inv in Hs as [? ?]
    | apply (tstep_eifL_inv true) in Hs as [? ?]
    | apply (tstep_eifL_inv false) in Hs as [? ?]
    | apply (tstep_eifR_inv true) in Hs as [? ?]
    | apply (tstep_eifR_inv false) in Hs as [? ?]
    | apply tstep_selL_inv in Hs as [? ?]
    | apply tstep_selR_inv in Hs as [? ?] ].

Local Ltac thread3 :=
  match goal with
  | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e _ _ |- _ =>
      apply gmultiset_triple_inv in Heq as [[-> ->]|[[-> ->]|[-> ->]]]
  end.

(** ** Obligations for LI3a: winner ld1, stages k ∈ [3,8], m ∈ [3,8] *)

Lemma leadI_case_3a k m s : (3 ≤ k ≤ 8)%nat → (3 ≤ m ≤ 8)%nat →
  (s = 2 ∧ (m ≤ 4)%nat ∨ s = 3 ∧ (5 ≤ m)%nat) →
  let p := (lC s, {[+ l0s s +]} ⊎ {[+ l1k k true +]} ⊎ {[+ l2m m false +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n (lΣ (cpk 6 k)) TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI (lΣ (cpk 6 k)) TUnit p π p').
Proof.
  intros Hk Hm Hsm. cbv zeta. split.
  - (* pirred clause *)
    destruct Hsm as [[-> Hm4]|[-> Hm5]].
    + (* s = 2: the m-side always steps *)
      intros Hirr. exfalso.
      assert (m = 3 ∨ m = 4) as [->| ->] by lia.
      * eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * eapply (Hirr PTau).
        replace ({[+ l0s 2 +]} ⊎ {[+ l1k k true +]} ⊎ {[+ l2m 4 false +]})
          with ({[+ l1k k true +]} ⊎ {[+ l0s 2 +]} ⊎ {[+ l2m 4 false +]}
                : gmultiset expr)
          by multiset_solver.
        eapply PStepClose;
          [exact tstep_l0s2_ex|exact (tstep_l2m4_ex false)
          |rewrite lC2; set_solver].
    + (* s = 3 *)
      assert (m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8) as [->|[->|[->| ->]]] by lia.
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_l2m6_ex false).
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * (* m = 8: the loser is done; the winner's stage decides *)
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia.
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 3 true +]} ⊎ {[+ l2m 8 false +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 8 false +]} ⊎ {[+ l1k 3 true +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_letu_unit_ex _).
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 4 true +]} ⊎ {[+ l2m 8 false +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 8 false +]} ⊎ {[+ l1k 4 true +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_l1k4_ex true).
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 5 true +]} ⊎ {[+ l2m 8 false +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 8 false +]} ⊎ {[+ l1k 5 true +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_letu_unit_ex _).
        -- intros Hirr; exfalso.
           eapply (Hirr (PSess (SSend "c" ETrue))).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 6 true +]} ⊎ {[+ l2m 8 false +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 8 false +]} ⊎ {[+ l1k 6 true +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepSession; [exact tstep_selL_ex|exact (c_not_lC 3)].
        -- intros Hirr; exfalso.
           eapply (Hirr (PSess (SClos "c"))).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 7 true +]} ⊎ {[+ l2m 8 false +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 8 false +]} ⊎ {[+ l1k 7 true +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepSession; [exact tstep_closc_ex|exact (c_not_lC 3)].
        -- (* k = 8: terminal configuration *)
           intros _.
           exists (l0s 3), ({[+ l1k 8 true +]} ⊎ {[+ l2m 8 false +]}).
           split_and!.
           ++ rewrite lC3. f_equal. multiset_solver.
           ++ done.
           ++ intros n. exact (Vrel_unit n).
           ++ intros e He.
              apply gmultiset_elem_of_disj_union in He as [He|He];
                apply gmultiset_elem_of_singleton in He; by subst.
  - (* step clause *)
    intros π p' Hst; inversion Hst; subst.
    + (* session steps *)
      thread3.
      * (* the l0s thread: closes d, which is restricted at s = 2 *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           match goal with Hn : subj _ ∉ _ |- _ =>
             rewrite lC2 in Hn; simpl in Hn end.
           set_solver.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* the l1k thread *)
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia.
        -- match goal with Hs : tstep (l1k 3 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l1k 4 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l1k 5 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- (* k = 6: the external send on c *)
           match goal with Hs : tstep (l1k 6 true) _ _ |- _ =>
             apply tstep_selL_inv in Hs as [Hα ->] end.
           simplify_eq.
           hnf.
           exists ∅, ∅, TBool, SEnd, ∅, ∅, (lC s),
             ({[+ l0s s +]} ⊎ {[+ l2m m false +]}
                ⊎ {[+ App EClos (Chan "c") +]}), ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ done.
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
           ++ intros n. rewrite fmap_empty. rewrite (left_id ∅ (∪)).
              exact (Vrel_bv n true).
           ++ replace ({[+ l0s s +]} ⊎ {[+ l2m m false +]}
                         ⊎ {[+ App EClos (Chan "c") +]})
                with ({[+ l0s s +]} ⊎ {[+ App EClos (Chan "c") +]}
                        ⊎ {[+ l2m m false +]} : gmultiset expr)
                by multiset_solver.
              apply (LI3a 7 m s); [lia|lia|exact Hsm].
           ++ exact (Powners_nil _).
           ++ left; done.
        -- (* k = 7: the external close on c *)
           match goal with Hs : tstep (l1k 7 true) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα ->] end.
           simplify_eq.
           hnf. exists ∅.
           split_and!.
           ++ done.
           ++ set_solver.
           ++ replace (lC s ∖ sentc (SClos "c")) with (lC s)
                by (simpl; set_solver).
              replace ({[+ l0s s +]} ⊎ {[+ l2m m false +]} ⊎ {[+ EUnit +]})
                with ({[+ l0s s +]} ⊎ {[+ EUnit +]} ⊎ {[+ l2m m false +]}
                      : gmultiset expr)
                by multiset_solver.
              apply (LI3a 8 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 8 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
      * (* the l2m thread: only the d-close at m = 4 has a session label *)
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia.
        -- match goal with Hs : tstep (l2m 3 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 4 false) _ _ |- _ =>
             apply tstep_letu_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           destruct Hsm as [[-> _]|[_ ?]]; [|lia].
           match goal with Hn : subj _ ∉ _ |- _ =>
             rewrite lC2 in Hn; simpl in Hn end.
           set_solver.
        -- match goal with Hs : tstep (l2m 5 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 6 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 7 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 8 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
    + (* beta steps *)
      thread3.
      * (* l0s: no beta *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end; simplify_eq.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l1k: beta at k ∈ {3,4,5} *)
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia.
        -- match goal with Hs : tstep (l1k 3 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m false +]}
                      ⊎ {[+ eif (bv true) selL EUnit +]})
             with ({[+ l0s s +]} ⊎ {[+ eif (bv true) selL EUnit +]}
                     ⊎ {[+ l2m m false +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3a 4 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 4 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m false +]}
                      ⊎ {[+ LetU EUnit (if true then selL else EUnit) +]})
             with ({[+ l0s s +]}
                     ⊎ {[+ LetU EUnit (if true then selL else EUnit) +]}
                     ⊎ {[+ l2m m false +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3a 5 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 5 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m false +]}
                      ⊎ {[+ if true then selL else EUnit +]})
             with ({[+ l0s s +]} ⊎ {[+ if true then selL else EUnit +]}
                     ⊎ {[+ l2m m false +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3a 6 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 6 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l1k 7 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l1k 8 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
      * (* l2m: beta at m ∈ {3,5,6,7} *)
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia.
        -- match goal with Hs : tstep (l2m 3 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3a k 4 s);
             [lia|lia|destruct Hsm as [[-> _]|[_ ?]]; [left; split; lia|lia]].
        -- match goal with Hs : tstep (l2m 4 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 5 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3a k 6 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 6 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3a k 7 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 7 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3a k 8 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 8 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
    + (* fork steps: no fork labels anywhere *)
      exfalso. thread3.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
    + (* msg steps: no receives at these stages — refute via the receiver *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|[(->&->&_)|(->&->&_)]]]]]
      end.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
    + (* close steps: only the joint d-close of l0s 2 and l2m 4 *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&->)|[(->&->&_)
               |[(->&->&_)|[(->&->&->)|(->&->&_)]]]]]
      end.
      * (* l0s with l1k: l1k never closes d *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
             as [->|[->|[->|[->|[->| ->]]]]] by lia;
             match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
               stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l0s with l2m: the genuine d-close at s = 2, m = 4 *)
        destruct Hsm as [[-> Hm4]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα ->] end.
           simplify_eq.
           assert (m = 3 ∨ m = 4) as [->| ->] by lia.
           ++ exfalso.
              match goal with Hs : tstep (l2m 3 false) _ _ |- _ =>
                stage_inv Hs end; simplify_eq.
           ++ match goal with Hs : tstep (l2m 4 false) _ _ |- _ =>
                apply tstep_letu_clos_inv in Hs as [Hα2 ->] end.
              simplify_eq.
              apply inv_case_tau; intros _.
              replace (lC 2 ∖ {["d"]}) with (∅ : gset chan)
                by (rewrite lC2; set_solver).
              replace ({[+ l1k k true +]} ⊎ {[+ EUnit +]}
                         ⊎ {[+ LetU EUnit (eif (bv false) selR EUnit) +]})
                with ({[+ EUnit +]} ⊎ {[+ l1k k true +]}
                        ⊎ {[+ LetU EUnit (eif (bv false) selR EUnit) +]}
                      : gmultiset expr)
                by multiset_solver.
              apply (LI3a k 5 3); [lia|lia|right; split; lia].
        -- exfalso.
           match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l1k with l0s: l1k can only close c, which is unrestricted *)
        exfalso.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq;
          match goal with Hc : "c" ∈ lC _ |- _ =>
            exact (c_not_lC _ Hc) end.
      * (* l1k with l2m: same *)
        exfalso.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq;
          match goal with Hc : "c" ∈ lC _ |- _ =>
            exact (c_not_lC _ Hc) end.
      * (* l2m with l0s: the genuine d-close, mirrored *)
        destruct Hsm as [[-> Hm4]|[-> Hm5]].
        -- assert (m = 3 ∨ m = 4) as [->| ->] by lia.
           ++ exfalso.
              match goal with Hs : tstep (l2m 3 false) _ _ |- _ =>
                stage_inv Hs end; simplify_eq.
           ++ match goal with Hs : tstep (l2m 4 false) _ _ |- _ =>
                apply tstep_letu_clos_inv in Hs as [Hα ->] end.
              simplify_eq.
              match goal with Hs : tstep (l0s 2) _ _ |- _ =>
                apply tstep_clos_inv in Hs as [Hα2 ->] end.
              apply inv_case_tau; intros _.
              replace (lC 2 ∖ {["d"]}) with (∅ : gset chan)
                by (rewrite lC2; set_solver).
              replace ({[+ l1k k true +]}
                         ⊎ {[+ LetU EUnit (eif (bv false) selR EUnit) +]}
                         ⊎ {[+ EUnit +]})
                with ({[+ EUnit +]} ⊎ {[+ l1k k true +]}
                        ⊎ {[+ LetU EUnit (eif (bv false) selR EUnit) +]}
                      : gmultiset expr)
                by multiset_solver.
              apply (LI3a k 5 3); [lia|lia|right; split; lia].
        -- exfalso.
           assert (m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8) as [->|[->|[->| ->]]] by lia;
             match goal with Hs : tstep (l2m _ _) (LSess (SClos _)) _ |- _ =>
               stage_inv Hs end; simplify_eq.
      * (* l2m with l1k: l1k cannot close d *)
        exfalso.
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8)
          as [->|[->|[->|[->|[->| ->]]]]] by lia;
          match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
Qed.

(** ** Obligations for LI3b: winner ld2, stages k ∈ [3,6], m ∈ [3,10] *)

Lemma leadI_case_3b k m s : (3 ≤ k ≤ 6)%nat → (3 ≤ m ≤ 10)%nat →
  (s = 2 ∧ (m ≤ 4)%nat ∨ s = 3 ∧ (5 ≤ m)%nat) →
  let p := (lC s, {[+ l0s s +]} ⊎ {[+ l1k k false +]} ⊎ {[+ l2m m true +]}) in
  (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
     (∀ n, Vrel n (lΣ (cpk 8 m)) TUnit v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
  (∀ π p', proc_step p π p' → inv_case leadI (lΣ (cpk 8 m)) TUnit p π p').
Proof.
  intros Hk Hm Hsm. cbv zeta. split.
  - (* pirred clause *)
    destruct Hsm as [[-> Hm4]|[-> Hm5]].
    + (* s = 2: the m-side always steps *)
      intros Hirr. exfalso.
      assert (m = 3 ∨ m = 4) as [->| ->] by lia.
      * eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * eapply (Hirr PTau).
        replace ({[+ l0s 2 +]} ⊎ {[+ l1k k false +]} ⊎ {[+ l2m 4 true +]})
          with ({[+ l1k k false +]} ⊎ {[+ l0s 2 +]} ⊎ {[+ l2m 4 true +]}
                : gmultiset expr)
          by multiset_solver.
        eapply PStepClose;
          [exact tstep_l0s2_ex|exact (tstep_l2m4_ex true)
          |rewrite lC2; set_solver].
    + (* s = 3 *)
      assert (m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10)
        as [->|[->|[->|[->|[->| ->]]]]] by lia.
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_l2m6_ex true).
      * intros Hirr; exfalso.
        eapply (Hirr PTau), PStepBeta, (tstep_letu_unit_ex _).
      * intros Hirr; exfalso.
        eapply (Hirr (PSess (SSend "c" EFalse))).
        eapply PStepSession; [exact tstep_selR_ex|exact (c_not_lC 3)].
      * intros Hirr; exfalso.
        eapply (Hirr (PSess (SClos "c"))).
        eapply PStepSession; [exact tstep_closc_ex|exact (c_not_lC 3)].
      * (* m = 10: the winner is done; the loser's stage decides *)
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia.
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 3 false +]} ⊎ {[+ l2m 10 true +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 10 true +]} ⊎ {[+ l1k 3 false +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_letu_unit_ex _).
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 4 false +]} ⊎ {[+ l2m 10 true +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 10 true +]} ⊎ {[+ l1k 4 false +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_l1k4_ex false).
        -- intros Hirr; exfalso.
           eapply (Hirr PTau).
           replace ({[+ l0s 3 +]} ⊎ {[+ l1k 5 false +]} ⊎ {[+ l2m 10 true +]})
             with ({[+ l0s 3 +]} ⊎ {[+ l2m 10 true +]} ⊎ {[+ l1k 5 false +]}
                   : gmultiset expr)
             by multiset_solver.
           eapply PStepBeta, (tstep_letu_unit_ex _).
        -- (* k = 6: terminal configuration *)
           intros _.
           exists (l0s 3), ({[+ l1k 6 false +]} ⊎ {[+ l2m 10 true +]}).
           split_and!.
           ++ rewrite lC3. f_equal. multiset_solver.
           ++ done.
           ++ intros n. exact (Vrel_unit n).
           ++ intros e He.
              apply gmultiset_elem_of_disj_union in He as [He|He];
                apply gmultiset_elem_of_singleton in He; by subst.
  - (* step clause *)
    intros π p' Hst; inversion Hst; subst.
    + (* session steps *)
      thread3.
      * (* the l0s thread *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           match goal with Hn : subj _ ∉ _ |- _ =>
             rewrite lC2 in Hn; simpl in Hn end.
           set_solver.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* the l1k thread: beta labels or a value, never a session *)
        exfalso.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * (* the l2m thread *)
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia.
        -- match goal with Hs : tstep (l2m 3 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 4 true) _ _ |- _ =>
             apply tstep_letu_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           destruct Hsm as [[-> _]|[_ ?]]; [|lia].
           match goal with Hn : subj _ ∉ _ |- _ =>
             rewrite lC2 in Hn; simpl in Hn end.
           set_solver.
        -- match goal with Hs : tstep (l2m 5 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 6 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 7 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- (* m = 8: the external send on c *)
           match goal with Hs : tstep (l2m 8 true) _ _ |- _ =>
             apply tstep_selR_inv in Hs as [Hα ->] end.
           simplify_eq.
           hnf.
           exists ∅, ∅, TBool, SEnd, ∅, ∅, (lC s),
             ({[+ l0s s +]} ⊎ {[+ l1k k false +]}
                ⊎ {[+ App EClos (Chan "c") +]}), ∅, ∅, TUnit, TUnit.
           split_and!.
           ++ done.
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
           ++ intros n. rewrite fmap_empty. rewrite (left_id ∅ (∪)).
              exact (Vrel_bv n false).
           ++ apply (LI3b k 9 s);
                [lia|lia|destruct Hsm as [[_ ?]|[-> _]];
                         [lia|right; split; lia]].
           ++ exact (Powners_nil _).
           ++ left; done.
        -- (* m = 9: the external close on c *)
           match goal with Hs : tstep (l2m 9 true) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα ->] end.
           simplify_eq.
           hnf. exists ∅.
           split_and!.
           ++ done.
           ++ set_solver.
           ++ replace (lC s ∖ sentc (SClos "c")) with (lC s)
                by (simpl; set_solver).
              apply (LI3b k 10 s);
                [lia|lia|destruct Hsm as [[_ ?]|[-> _]];
                         [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 10 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
    + (* beta steps *)
      thread3.
      * (* l0s: no beta *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end; simplify_eq.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l1k: beta at k ∈ {3,4,5} *)
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia.
        -- match goal with Hs : tstep (l1k 3 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m true +]}
                      ⊎ {[+ eif (bv false) selL EUnit +]})
             with ({[+ l0s s +]} ⊎ {[+ eif (bv false) selL EUnit +]}
                     ⊎ {[+ l2m m true +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3b 4 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 4 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m true +]}
                      ⊎ {[+ LetU EUnit (if false then selL else EUnit) +]})
             with ({[+ l0s s +]}
                     ⊎ {[+ LetU EUnit (if false then selL else EUnit) +]}
                     ⊎ {[+ l2m m true +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3b 5 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 5 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           replace ({[+ l0s s +]} ⊎ {[+ l2m m true +]}
                      ⊎ {[+ if false then selL else EUnit +]})
             with ({[+ l0s s +]} ⊎ {[+ if false then selL else EUnit +]}
                     ⊎ {[+ l2m m true +]} : gmultiset expr)
             by multiset_solver.
           apply (LI3b 6 m s); [lia|lia|exact Hsm].
        -- match goal with Hs : tstep (l1k 6 false) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
      * (* l2m: beta at m ∈ {3,5,6,7} *)
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia.
        -- match goal with Hs : tstep (l2m 3 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3b k 4 s);
             [lia|lia|destruct Hsm as [[-> _]|[_ ?]]; [left; split; lia|lia]].
        -- match goal with Hs : tstep (l2m 4 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 5 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3b k 6 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 6 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3b k 7 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 7 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
           apply inv_case_tau; intros _.
           apply (LI3b k 8 s);
             [lia|lia|destruct Hsm as [[_ ?]|[-> _]]; [lia|right; split; lia]].
        -- match goal with Hs : tstep (l2m 8 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 9 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l2m 10 true) _ _ |- _ =>
             stage_inv Hs end; simplify_eq.
    + (* fork steps: no fork labels anywhere *)
      exfalso. thread3.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
    + (* msg steps: no receives at these stages — refute via the receiver *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hsf : tstep ?f (LSess (SRecv _ _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&_)|[(->&->&_)
               |[(->&->&_)|[(->&->&_)|(->&->&_)]]]]]
      end.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * destruct Hsm as [[-> _]|[-> _]];
          match goal with Hs : tstep (l0s _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SRecv _ _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
    + (* close steps: only the joint d-close of l0s 2 and l2m 4 *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_triple_inv2 in Heq
            as [(->&->&_)|[(->&->&->)|[(->&->&_)
               |[(->&->&_)|[(->&->&->)|(->&->&_)]]]]]
      end.
      * (* l0s with l1k: l1k never closes *)
        exfalso. destruct Hsm as [[-> _]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα _] end.
           simplify_eq.
           assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
             match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
               stage_inv Hs end; simplify_eq.
        -- match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l0s with l2m: the genuine d-close at s = 2, m = 4 *)
        destruct Hsm as [[-> Hm4]|[-> _]].
        -- match goal with Hs : tstep (l0s 2) _ _ |- _ =>
             apply tstep_clos_inv in Hs as [Hα ->] end.
           simplify_eq.
           assert (m = 3 ∨ m = 4) as [->| ->] by lia.
           ++ exfalso.
              match goal with Hs : tstep (l2m 3 true) _ _ |- _ =>
                stage_inv Hs end; simplify_eq.
           ++ match goal with Hs : tstep (l2m 4 true) _ _ |- _ =>
                apply tstep_letu_clos_inv in Hs as [Hα2 ->] end.
              simplify_eq.
              apply inv_case_tau; intros _.
              replace (lC 2 ∖ {["d"]}) with (∅ : gset chan)
                by (rewrite lC2; set_solver).
              replace ({[+ l1k k false +]} ⊎ {[+ EUnit +]}
                         ⊎ {[+ LetU EUnit (eif (bv true) selR EUnit) +]})
                with ({[+ EUnit +]} ⊎ {[+ l1k k false +]}
                        ⊎ {[+ LetU EUnit (eif (bv true) selR EUnit) +]}
                      : gmultiset expr)
                by multiset_solver.
              apply (LI3b k 5 3); [lia|lia|right; split; lia].
        -- exfalso.
           match goal with Hs : tstep (l0s 3) _ _ |- _ =>
             eapply val_no_tstep; [exact Hs|done] end.
      * (* l1k with l0s: l1k never closes *)
        exfalso.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * (* l1k with l2m: l1k never closes *)
        exfalso.
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq.
      * (* l2m with l0s: the genuine d-close, mirrored *)
        destruct Hsm as [[-> Hm4]|[-> Hm5]].
        -- assert (m = 3 ∨ m = 4) as [->| ->] by lia.
           ++ exfalso.
              match goal with Hs : tstep (l2m 3 true) _ _ |- _ =>
                stage_inv Hs end; simplify_eq.
           ++ match goal with Hs : tstep (l2m 4 true) _ _ |- _ =>
                apply tstep_letu_clos_inv in Hs as [Hα ->] end.
              simplify_eq.
              match goal with Hs : tstep (l0s 2) _ _ |- _ =>
                apply tstep_clos_inv in Hs as [Hα2 ->] end.
              apply inv_case_tau; intros _.
              replace (lC 2 ∖ {["d"]}) with (∅ : gset chan)
                by (rewrite lC2; set_solver).
              replace ({[+ l1k k false +]}
                         ⊎ {[+ LetU EUnit (eif (bv true) selR EUnit) +]}
                         ⊎ {[+ EUnit +]})
                with ({[+ EUnit +]} ⊎ {[+ l1k k false +]}
                        ⊎ {[+ LetU EUnit (eif (bv true) selR EUnit) +]}
                      : gmultiset expr)
                by multiset_solver.
              apply (LI3b k 5 3); [lia|lia|right; split; lia].
        -- exfalso.
           assert (m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10)
             as [->|[->|[->|[->|[->| ->]]]]] by lia;
             match goal with Hs : tstep (l2m _ _) (LSess (SClos _)) _ |- _ =>
               stage_inv Hs end; simplify_eq;
             match goal with Hc : "c" ∈ lC _ |- _ =>
               exact (c_not_lC _ Hc) end.
      * (* l2m with l1k: l1k cannot be the close partner *)
        exfalso.
        assert (m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9
                ∨ m = 10)
          as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia;
          match goal with Hs : tstep (l2m _ _) (LSess (SClos _)) _ |- _ =>
            stage_inv Hs end; simplify_eq;
          try (match goal with Hc : "c" ∈ lC _ |- _ =>
            exact (c_not_lC _ Hc) end).
        assert (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) as [->|[->|[->| ->]]] by lia;
          match goal with Hs : tstep (l1k _ _) _ _ |- _ =>
            stage_inv Hs end; simplify_eq.
Qed.

(** ** Assembly: the invariant rule and the semantic judgment *)

Lemma leadI_invariant : proc_invariant leadI.
Proof.
  intros Σ T p HI. destruct HI.
  - exact leadI_case_0.
  - by apply leadI_case_1a.
  - by apply leadI_case_1b.
  - by apply leadI_case_2.
  - by apply leadI_case_3a.
  - by apply leadI_case_3b.
Qed.

(** The election process inhabits the logical relation at the
    interface c : Close ⊕ Close, at every step index. *)
Theorem leader_sem_ptyped :
  sem_ptyped {["c" := Slead]} leader_proc TUnit.
Proof.
  intro n. eapply Prel_by_invariant; [exact leadI_invariant|apply LI0].
Qed.

(** ** The environment-side client, syntactically typed

    q receives the leader's token on c, closes c, and discards the
    token — a well-typed use of the dual interface ?(∗+∗).Close,
    exercising the E-Case rule. *)

Definition qbody : expr :=
  LetU (App EClos (Var 0))
    (Case (Var 1) (LetU (Var 0) EUnit) (LetU (Var 0) EUnit)).
Definition qclient : expr := LetP (App ERecv (Chan "c")) qbody.

Lemma lenv_only_30 T : lenv_only [Some T; None; None] 0 T.
Proof.
  split; [done|]. intros [|[|[|y]]] T' H; simplify_eq/=; auto.
Qed.

Lemma qclient_typed :
  ptyped {["c" := SRcv TBool SEnd]} (∅, {[+ qclient +]}) TUnit.
Proof.
  apply ptyped_term; [constructor|].
  eapply (typed_letp _ {["c" := SRcv TBool SEnd]} ∅ _ [] [] _ _
            TBool (TSess SEnd));
    [apply senv_split_comm, senv_split_empty_l|constructor| |].
  - (* recv c : Bool ⊗ Close *)
    eapply (typed_app _ ∅ {["c" := SRcv TBool SEnd]} _ [] []
              _ _ (TSess (SRcv TBool SEnd)));
      [apply senv_split_empty_l|constructor| |].
    + apply typed_konst; [apply lenv_empty_nil|]. apply (KTRecv TBool SEnd).
    + apply typed_chan, lenv_empty_nil.
  - (* body: token b at index 1, continuation channel at index 0 *)
    eapply (typed_letu _ ∅ ∅ _ [Some (TSess SEnd); None]
              [None; Some TBool]);
      [apply senv_split_empty_l|repeat constructor| |].
    + (* clos c' *)
      eapply (typed_app _ ∅ ∅ _ [None; None] [Some (TSess SEnd); None]
                _ _ (TSess SEnd));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_konst; [auto using lenv_empty_nil, lenv_empty_cons|].
        apply KTClos.
      * apply typed_var, lenv_only_20.
    + (* case b (a. let ∗ = a in ∗)(a. let ∗ = a in ∗) *)
      eapply (typed_case _ ∅ ∅ _ [None; Some TBool] [None; None]
                _ _ _ TUnit TUnit);
        [apply senv_split_empty_l|repeat constructor|..].
      * apply typed_var, lenv_only_21.
      * eapply (typed_letu _ ∅ ∅ _ [Some TUnit; None; None]
                  [None; None; None]);
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_var, lenv_only_30. }
        { apply typed_unit. auto using lenv_empty_nil, lenv_empty_cons. }
      * eapply (typed_letu _ ∅ ∅ _ [Some TUnit; None; None]
                  [None; None; None]);
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_var, lenv_only_30. }
        { apply typed_unit. auto using lenv_empty_nil, lenv_empty_cons. }
Qed.

(** ** Deadlock freedom of the closed composite (the paper's p0)

    P-Connect (semantic form) plugs the untypable election process and
    the typed client together on c; adequacy then yields deadlock
    freedom of the fully closed process. *)

Theorem leader_election_deadlock_free :
  deadlock_free
    ({["cs"; "d"]} ∪ ∅ ∪ {["c"]},
     ({[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]}) ⊎ {[+ qclient +]}).
Proof.
  apply adequacy with (T := TUnit).
  apply (sem_ptyped_connect ∅ ∅ ∅ "c" Slead
           {["cs"; "d"]} ({[+ ld0 +]} ⊎ {[+ ld1 +]} ⊎ {[+ ld2 +]})
           ∅ {[+ qclient +]} TUnit);
    [constructor|apply senv_split_empty_l
    |set_solver|set_solver|set_solver|set_solver|set_solver
    |set_solver|set_solver|set_solver|set_solver| |].
  - rewrite insert_empty. exact leader_sem_ptyped.
  - rewrite insert_empty. exact (fundamental_proc _ _ _ qclient_typed).
Qed.
