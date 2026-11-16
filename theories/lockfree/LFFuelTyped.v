(** * The typed fuel interpretation (lock-freedom plan §17.6, stage L6)

    Stage L6 asks that every thread of a program in the static
    lock-free fragment satisfy [fsem] at the budgets of [src_world].
    The lemmas of stage L6a on the old link rule are gone with that
    rule, and the counterexamples to option 2 with link tickets (plan
    §18, decision 2026-11-16). This file keeps the tactics that step a
    thread under FuelE, the fragment facts of the scheduler and of sync,
    and their budgets. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import lockfree.LFFuel lockfree.Fragment.
From LRGV Require examples.Sync examples.Scheduler examples.Forwarder.

Set Default Proof Using "All".

(** ** Stepping a thread under FuelE *)

Lemma fstep_beta n W π φ tk e e' :
  FuelE (S n) W π φ tk e → tstep e LBeta e' → FuelE n W π φ tk e'.
Proof. intros H Hs. exact (fuel_obl _ _ _ _ _ _ H _ _ Hs). Qed.

Lemma fstep_new n W π φ tk e e' c x :
  FuelE (S n) W π φ tk e → tstep e (LNew c x) e' →
  FuelE n W (<[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π))
    (<[(c, pt_pol x) := w_bud W x]> (<[(c, negb (pt_pol x)) := w_bud W (pt_dual x)]> φ)) tk e'.
Proof. intros H Hs. exact (fuel_obl _ _ _ _ _ _ H _ _ Hs). Qed.

Ltac tsolve :=
  first
    [ apply TStepHead; econstructor; reflexivity
    | apply TStepHead; constructor; reflexivity
    | apply TStepLetP; tsolve
    | apply TStepLetU; tsolve
    | apply TStepPairL; tsolve
    | apply TStepAppL; tsolve
    | apply TStepAppR; [reflexivity|tsolve]
    | apply TStepPairR; [reflexivity|tsolve] ].

(** The term of H in normal form. The maps keep their shape: [simpl]
    or [cbn] on them, or on FuelE, runs out of stack. *)
Ltac fnorm H := match type of H with FuelE ?n ?W ?π ?φ ?tk ?e =>
  let e2 := eval vm_compute in e in change (FuelE n W π φ tk e2) in H end.

Ltac fbeta H := match type of H with FuelE (S ?n) ?W ?π ?φ ?tk ?e =>
  let Hs := fresh in eassert (Hs : tstep e LBeta _) by tsolve;
  apply (fstep_beta n W π φ tk e _ H) in Hs; clear H; rename Hs into H; fnorm H end.

Ltac fnew H c x := match type of H with FuelE (S ?n) ?W ?π ?φ ?tk ?e =>
  let Hs := fresh in eassert (Hs : tstep e (LNew c x) _) by tsolve;
  apply (fstep_new n W π φ tk e _ c x H) in Hs; clear H; rename Hs into H; fnorm H end.

(** ** The scheduler is in the fragment *)

(** Rank for the scheduler's world. Its facts are γ ≺ γ̄, γ+1 ≺ ε and
    γ̄+1 ≺ ε̄, with γ the constant 1 and ε the constant 0. *)
Definition sched_rank (x : point) : nat :=
  (if bool_decide (pt_name x = NConst 0) then 4 else 0) + 2 * pt_off x + (if pt_pol x then 0 else 1).

Lemma sched_wf : wf_world (cworld Scheduler.sched_Ψ).
Proof.
  apply (cworld_rank_wf lt _ sched_rank Wf_nat.lt_wf); [intros a b c; lia| | |].
  - intros x y (C & xs & Hin & g0 & (f & Hf & Hs & ->) & E).
    unfold Scheduler.sched_Ψ in Hin. rewrite !elem_of_app, !list_elem_of_singleton in Hin.
    destruct Hin as [[Hin|Hin]|Hin]; [by apply elem_of_nil in Hin| |].
    + injection Hin as -> ->. cbn in Hf. unfold FreshTools.ccd_P in Hf. subst f.
      cbn in E. injection E as -> ->. vm_compute. lia.
    + injection Hin as -> ->. cbn in Hf. unfold FreshTools.freshp_facts in Hf.
      destruct Hf as [(i & l & b & Hl & ->)|(j & h & b & Hl & _)]; [|by rewrite lookup_nil in Hl].
      destruct i as [|[|i]]; cbn in Hl; [..|discriminate]; injection Hl as <- <-;
        cbn in E; injection E as -> ->; vm_compute; lia.
  - intros x. unfold sched_rank, pt_shift. cbn. lia.
  - intros x. unfold sched_rank, pt_shift, pt_dual. cbn. destruct (pt_pol x); cbn; lia.
Qed.

(** The scheduler has no box, so R1, R2-recv and the hand-off graph
    hold trivially. *)
Theorem sched_lfsource : lfsource Scheduler.sched_Ψ Scheduler.sched_main TUnit.
Proof.
  split_and!.
  - apply Scheduler.sched_created.
  - constructor.
  - split; [apply Scheduler.sched_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply sched_wf.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

(** ** Budgets of sync and of the scheduler

    Stage L6a found that sync, which has no box, got L = 0 and budget 0
    at every point, and that its spawn, which hands c on, then fails.
    The stretch bound now counts the code of every thread (Fragment.v,
    [stretch_len]). sync has 5 units (spawn, send, close, receive,
    close), so L = 10, every end gets 2L = 20 and every floor is L. The
    scheduler has 11 units, the spawns and the link included, so
    L = 22. Neither has a root edge. *)

Theorem sync_lfsource : lfsource Sync.sync_Ψ Sync.sync_main TUnit.
Proof.
  split_and!.
  - apply Sync.sync_created.
  - constructor.
  - split; [apply Sync.sync_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply cworld_depth_wf. intros x y (C & xs & Hin & g0 & (f & Hf & Hs & ->) & E).
    unfold Sync.sync_Ψ in Hin. rewrite elem_of_app, list_elem_of_singleton in Hin.
    destruct Hin as [Hin|Hin]; [by apply elem_of_nil in Hin|]. injection Hin as -> ->.
    destruct Hf as [(i & Hi & _)|(j & Hj & _)]; cbn in *; lia.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

Definition sync_W : world := src_world Sync.sync_Ψ Sync.sync_main.

Theorem sync_budgets :
  strict sync_W ∧ lfptyped sync_W ∅ (∅, {[+ Sync.sync_main +]}) TUnit ∧
  stretch_len Sync.sync_main = 10 ∧ ∀ x, w_bud sync_W x = Some 20 ∧ w_pay sync_W x = 10.
Proof.
  destruct (lfsource_budgets _ _ _ sync_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 10 x); vm_compute; reflexivity.
Qed.

Definition sched_W : world := src_world Scheduler.sched_Ψ Scheduler.sched_main.

Theorem sched_budgets :
  strict sched_W ∧ lfptyped sched_W ∅ (∅, {[+ Scheduler.sched_main +]}) TUnit ∧
  stretch_len Scheduler.sched_main = 22 ∧ ∀ x, w_bud sched_W x = Some 44 ∧ w_pay sched_W x = 22.
Proof.
  destruct (lfsource_budgets _ _ _ sched_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 22 x); vm_compute; reflexivity.
Qed.
