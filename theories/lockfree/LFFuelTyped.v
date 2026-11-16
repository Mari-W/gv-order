(** * The typed fuel interpretation (lock-freedom plan §17.6, stage L6a)

    Stage L6a asks that every thread of a program in the static
    lock-free fragment satisfy [fsem] at the budgets that
    [with_budgets] computes. The statement is false, for two
    reasons, and this file proves both.

    - [lf_fuel_fundamental_false]. No world at all gives a program
      of the fragment [fsem]. The scheduler of examples/Scheduler.v
      is in the fragment ([sched_lfsource]) and links two ends.
      KTLink types link ⟨u, v⟩ at u : S@k and v : S̄@k̄, so the
      partner of v sits at k, the point of u. The link clause of
      FuelE asks the budget of that partner to lie below the counter
      of u, and F-Cap bounds the counter by the same budget, so only
      ∞ passes ([fuel_link_inf]). The scheduler also sends on the
      partner of v, and F-Wait asks a finite budget at k̄ for that
      ([sched_not_fsem]). The hand-off graph rejects every link
      inside a box (its edge from the type of u to the type of the
      partner of v is a self-loop), and it does not look at links
      outside boxes.
    - [sync_not_fsem]. [round_len] counts channel steps inside box
      bodies only. A program without boxes gets L = 0 and budget 0
      at every point, and sync (examples/Sync.v), which is in the
      fragment ([sync_lfsource]), spawns a thread with an end, which
      needs a counter of at least 1. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import lockfree.LFFuel lockfree.Fragment.
From LRGV Require examples.Sync examples.Scheduler.

Set Default Proof Using "All".

(** ** Stepping a thread under FuelE *)

Lemma fstep_beta n W π φ e e' :
  FuelE (S n) W π φ e → tstep e LBeta e' → FuelE n W π φ e'.
Proof. intros H Hs. exact (fuel_obl _ _ _ _ _ H _ _ Hs). Qed.

Lemma fstep_new n W π φ e e' c x :
  FuelE (S n) W π φ e → tstep e (LNew c x) e' →
  FuelE n W (<[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π))
    (<[(c, pt_pol x) := w_bud W x]> (<[(c, negb (pt_pol x)) := w_bud W (pt_dual x)]> φ)) e'.
Proof. intros H Hs. exact (fuel_obl _ _ _ _ _ H _ _ Hs). Qed.

Ltac tsolve :=
  first
    [ apply TStepHead; econstructor; reflexivity
    | apply TStepHead; constructor
    | apply TStepLetP; tsolve
    | apply TStepLetU; tsolve
    | apply TStepPairL; tsolve
    | apply TStepAppL; tsolve
    | apply TStepAppR; [reflexivity|tsolve]
    | apply TStepPairR; [reflexivity|tsolve] ].

(** The term of H in normal form. The maps keep their shape: [simpl]
    or [cbn] on them, or on FuelE, runs out of stack. *)
Ltac fnorm H := match type of H with FuelE ?n ?W ?π ?φ ?e =>
  let e2 := eval vm_compute in e in change (FuelE n W π φ e2) in H end.

Ltac fbeta H := match type of H with FuelE (S ?n) ?W ?π ?φ ?e =>
  let Hs := fresh in eassert (Hs : tstep e LBeta _) by tsolve;
  apply (fstep_beta n W π φ e _ H) in Hs; clear H; rename Hs into H; fnorm H end.

Ltac fnew H c x := match type of H with FuelE (S ?n) ?W ?π ?φ ?e =>
  let Hs := fresh in eassert (Hs : tstep e (LNew c x) _) by tsolve;
  apply (fstep_new n W π φ e _ c x H) in Hs; clear H; rename Hs into H; fnorm H end.

(** ** A typed link needs budget ∞ at both of its points

    KTLink types link ⟨u, v⟩ with u : S@k and v : S̄@k̄, so the partner
    of v sits at k, the point of u. The link clause of FuelE asks the
    budget of the partner of v to lie below the counter of u, and F-Cap
    bounds that counter by the budget at k, the same budget. Only ∞
    passes. *)
Lemma fuel_link_inf n W π φ e e' o1 o2 k :
  FuelE (S n) W π φ e → tstep e (LSess (SLink {[o1; o2]})) e' → o1 ≠ o2 →
  π !! o1 = Some k → π !! o2 = Some (pt_dual k) → is_Some (φ !! o1) →
  w_bud W k = None.
Proof.
  intros H Hs Hne H1 H2 [f Hf].
  destruct (fuel_cap _ _ _ _ _ H o1 f Hf) as (k' & Hk' & Hle).
  rewrite H1 in Hk'. injection Hk' as <-.
  destruct f as [m|]; [|by destruct (w_bud W k)].
  destruct (fuel_link _ _ _ _ _ H _ _ Hs o1 o2 eq_refl Hne m Hf) as (k2 & m' & Hk2 & Hb & Hlt).
  rewrite H2 in Hk2. injection Hk2 as <-. rewrite pt_dual_dual in Hb.
  rewrite Hb in Hle. simpl in Hle. lia.
Qed.

(** ** The scheduler: in the fragment, and in fsem at no world *)

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
Qed.

(** main creates a and b at γ and c at ε, spawns ag₁ = link ⟨b, ā⟩ and
    ag₂, and sends on a. ag₁ forces budget ∞ at γ̄, the point of ā,
    and F-Wait at the send on a asks a finite budget there. *)
Theorem sched_not_fsem W : ¬ fsem W ∅ Scheduler.sched_main.
Proof.
  intros Hf. pose proof (Hf 40) as H. rewrite fmap_empty in H. fnorm H.
  fnew H "a"%string (pconst 1). fbeta H. fbeta H. fbeta H.
  fnew H "b"%string (pconst 1). fbeta H. fbeta H. fbeta H.
  fnew H "c"%string (pconst 0). fbeta H. fbeta H. fbeta H.
  match type of H with FuelE _ _ ?π ?φ _ => set (P := π) in H; set (F := φ) in H end.
  match type of H with FuelE _ _ _ _ ?e => eassert (Hs : tstep e (LSpawn _) _) by tsolve end.
  destruct (fuel_obl _ _ _ _ _ H _ _ Hs) as (_ & Hc & Hp). clear Hs.
  (* ag₁ links b with ā *)
  fbeta Hc. fbeta Hc.
  match type of Hc with FuelE _ _ _ _ ?e =>
    eassert (Hl : tstep e (LSess (SLink _)) _) by tsolve end.
  rewrite upair_comm in Hl.
  assert (Hinf : w_bud W (pt_dual (pconst 1)) = None).
  { eapply (fuel_link_inf _ _ _ _ _ _ ("a", false) ("b", true) (pt_dual (pconst 1)) Hc Hl);
      [done|vm_compute; reflexivity|rewrite pt_dual_dual; vm_compute; reflexivity|].
    vm_compute. eexists. reflexivity. }
  (* main spawns ag₂ and sends on a at γ *)
  clear Hc. fbeta Hp.
  match type of Hp with FuelE _ _ ?π ?φ _ => set (P2 := π) in Hp; set (F2 := φ) in Hp end.
  match type of Hp with FuelE _ _ _ _ ?e => eassert (Hs : tstep e (LSpawn _) _) by tsolve end.
  destruct (fuel_obl _ _ _ _ _ Hp _ _ Hs) as (_ & _ & H2). clear Hs. fbeta H2.
  match type of H2 with FuelE _ _ _ _ ?e =>
    eassert (Hs : tstep e (LSess (SSend ("a", true) EUnit)) _) by tsolve end.
  destruct (fuel_wait _ _ _ _ _ H2 _ _ _ Hs eq_refl) as (k & m & Hk & Hb).
  vm_compute in Hk. injection Hk as <-. unfold pconst in Hinf. congruence.
Qed.

(** Stage L6a as stated has no proof: a program of the fragment whose
    single thread meets fuel in no world. *)
Theorem lf_fuel_fundamental_false : ¬ ∀ Ψ t T, lfsource Ψ t T → ∃ W, fsem W ∅ t.
Proof.
  intros H. destruct (H _ _ _ sched_lfsource) as [W HW]. exact (sched_not_fsem W HW).
Qed.

(** ** sync: budgets 0 without boxes *)

Lemma sync_round_len : round_len Sync.sync_main = 0.
Proof. vm_compute. reflexivity. Qed.

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
Qed.

(** sync creates c and d at ι and spawns a thread with c. At budget 0
    the spawn cannot hand c on, whatever graph and session types the
    budgets read. *)
Theorem sync_not_fsem E ty_of :
  ¬ fsem (with_budgets (cworld Sync.sync_Ψ) E (round_len Sync.sync_main) ty_of) ∅ Sync.sync_main.
Proof.
  set (W := with_budgets _ _ _ _). intros Hf. pose proof (Hf 10) as H. rewrite fmap_empty in H.
  fnorm H. fnew H "a"%string (pconst 0). fbeta H. fbeta H. fbeta H.
  match type of H with FuelE _ _ _ _ ?e => eassert (Hs : tstep e (LSpawn _) _) by tsolve end.
  destruct (fuel_obl _ _ _ _ _ H _ _ Hs) as (Hh & _ & _).
  specialize (Hh ("a", true)%string ((gdepth E - sdep E (ty_of (pconst 0)) + 1) * (2 * round_len Sync.sync_main))).
  rewrite sync_round_len in Hh.
  assert (0 + 1 ≤ (gdepth E - sdep E (ty_of (pconst 0)) + 1) * (2 * 0)) as Hc
    by (apply Hh; [vm_compute; set_solver|unfold W; vm_compute; reflexivity]).
  lia.
Qed.
