(** * The typed fuel interpretation (lock-freedom plan §17.6, stage L6)

    Stage L6 asks that every thread of a program in the static
    lock-free fragment satisfy [fsem] at the budgets of [src_world].
    The lemmas of stage L6a on the old link rule are gone with that
    rule, and the counterexamples to option 2 with link tickets (plan
    §18, decision 2026-11-16). This file keeps the tactics that step a
    thread under FuelE, the fragment facts of the scheduler and of sync,
    and their budgets.

    Stage L6 as stated is false at the budgets of [src_world]
    ([lf_fuel_fundamental_fails]). sync is in the fragment, and its
    thread fails [fsem] there ([sync_not_fsem]), because an end may
    arrive at a point outside the support of the world, and FuelE,
    closed under extension of the budgets, then asks its counter to be
    0 ([fuel_recv_unknown]). *)

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

(** The scheduler has no box, so R1, R2-recv and the box check hold
    trivially. *)
Theorem sched_lfsource : lfsource Scheduler.sched_Ψ Scheduler.sched_main TUnit.
Proof.
  split_and!.
  - apply Scheduler.sched_created.
  - constructor.
  - split; [apply Scheduler.sched_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - apply sched_wf.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

(** ** Budgets of sync and of the scheduler

    Stage L6a found that sync, which has no box, got L = 0 and budget 0
    at every point, and that its spawn, which hands c on, then fails.
    The stretch bound now counts the code of every thread (Fragment.v,
    [stretch_len]). sync has 5 units (spawn, send, close, receive,
    close), so L = 10, every end gets 2L = 20 and every floor is L. The
    scheduler has 10 units, the spawns included. Its link costs none
    under link tickets (plan §18), so L = 20. Neither has a root
    edge. *)

Theorem sync_lfsource : lfsource Sync.sync_Ψ Sync.sync_main TUnit.
Proof.
  split_and!.
  - apply Sync.sync_created.
  - constructor.
  - split; [apply Sync.sync_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
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
  stretch_len Scheduler.sched_main = 20 ∧ ∀ x, w_bud sched_W x = Some 40 ∧ w_pay sched_W x = 20.
Proof.
  destruct (lfsource_budgets _ _ _ sched_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 20 x); vm_compute; reflexivity.
Qed.

(** ** Stage L6 fails at ends received from outside the support

    FuelE is closed under every extension of the budgets ([wbext],
    decision 2026-11-16, under delegation), and an extension keeps the
    budgets only at the points the smaller world knows ([wext_bud]).
    Receive is universal over the incoming ends ([fin_ok]), which may
    sit at any point whose budget admits the floor of the carrier. An
    end received at a point outside the support with a positive counter
    then fails F-Cap in the extension that sets the budget there to 0
    ([fuel_recv_unknown]). [src_world] gives every point the budget
    (d + 2)·L, the unknown ones included, and every floor is at least
    L, so every thread of the fragment that receives fails [fsem] at
    the budgets of [src_world]. sync is the smallest instance
    ([sync_not_fsem]). *)

(** W with the budget b at the point k. *)
Definition wbud_set (W : world) (k : point) (b : option nat) : world :=
  World (w_names W) (w_lt W) (λ x, if decide (x = k) then b else w_bud W x) (w_pay W).

(** Outside the support, that is an extension. *)
Lemma wbud_set_ext W k b : ¬ pt_known W k → wbext W (wbud_set W k b).
Proof.
  intros Hk. split; [done|]. intros x Hx. simpl.
  destruct (decide (x = k)) as [->|]; [contradiction|done].
Qed.

(** A counter at a point outside the support is 0 at every index
    above 0. *)
Lemma fuel_unknown_zero n W π φ tk e o k m :
  FuelE (S n) W π φ tk e → π !! o = Some k → φ !! o = Some (Some m) → ¬ pt_known W k → m = 0.
Proof.
  intros HF Hk Hm Hu.
  apply (FuelE_wbext _ _ (wbud_set W k (Some 0))) in HF; [|by apply wbud_set_ext].
  destruct (fuel_cap _ _ _ _ _ _ HF o _ Hm) as (k' & Hk' & Hle).
  rewrite Hk in Hk'. simplify_eq. simpl in Hle. rewrite decide_True in Hle by done. simpl in Hle. lia.
Qed.

(** A receive adds no end to the receiver's maps before the incoming
    ones join. *)
Lemma fupd_recv_dom W π φ o w x :
  x ∈ dom (fupd W π φ (LSess (SRecv o w))).1 ∨ x ∈ dom (fupd W π φ (LSess (SRecv o w))).2 →
  x ∈ dom π ∨ x ∈ dom φ.
Proof.
  cbn [fupd sl_out]. unfold LFFuel.fact. cbn [sl_end sl_next].
  destruct (mrem ∅ π !! o) as [κ|] eqn:E; simpl.
  - apply lookup_mrem_Some in E as [E _].
    assert (o ∈ dom π) by (apply elem_of_dom; eauto).
    rewrite !dom_insert_L, dom_delete_L, dom_fmap_L, dom_delete_L, !dom_mrem. set_solver.
  - rewrite !dom_mrem. set_solver.
Qed.

(** A receive admits an end at a point outside the support of the world
    with a positive counter, and an extension of the world sets the
    budget there to 0. *)
Lemma fuel_recv_unknown n W π φ tk e o c2 b2 e' κ k b :
  FuelE (S (S n)) W π φ tk e →
  tstep e (LSess (SRecv o (Chan c2 b2))) e' →
  π !! o = Some κ →
  (c2, b2) ∉ dom π → (c2, b2) ∉ dom φ →
  ¬ pt_known W k → w_bud W k = Some b → w_pay W (pt_dual κ) ≤ b → 1 ≤ b →
  w_bud W (pt_dual k) ≠ None → False.
Proof.
  intros HF Hst Ho Hπ Hφ Hu Hb Hfl Hb1 Hd.
  set (α := LSess (SRecv o (Chan c2 b2))).
  set (πi := {[(c2, b2) := k]} : gmap cend point).
  set (φi := {[(c2, b2) := Some b]} : gmap cend fuel).
  assert (Hπ' : (fupd W π φ α).1 !! (c2, b2) = None).
  { apply not_elem_of_dom. intros H. destruct (fupd_recv_dom W π φ o _ (c2, b2) (or_introl H)); done. }
  assert (Hφ' : (fupd W π φ α).2 !! (c2, b2) = None).
  { apply not_elem_of_dom. intros H. destruct (fupd_recv_dom W π φ o _ (c2, b2) (or_intror H)); done. }
  assert (Hdj : dom πi ## dom (fupd W π φ α).1).
  { unfold πi. rewrite dom_singleton_L. apply disjoint_singleton_l, not_elem_of_dom, Hπ'. }
  assert (Hin : fin_ok W (w_pay W (pt_dual κ)) (Chan c2 b2) πi φi).
  { unfold πi, φi. split_and!.
    - by rewrite dom_singleton_L.
    - by rewrite dom_singleton_L.
    - intros o' f Hf. apply lookup_singleton_Some in Hf as [<- <-]. exists k.
      rewrite lookup_singleton_eq, Hb. simpl. split; [done|lia].
    - intros o' f Hf. apply lookup_singleton_Some in Hf as [<- <-]. simpl. lia.
    - intros o' k' Hk'. apply lookup_singleton_Some in Hk' as [<- <-]. done. }
  assert (Hv : Vfuel (S n) W πi φi 0 (Chan c2 b2)) by (by rewrite Vfuel_eq).
  pose proof (lffuel_recv _ _ _ _ _ _ HF _ _ _ _ _ _ _ Hst Ho (le_n _) Hdj Hin Hv) as H.
  eapply (fuel_unknown_zero _ _ _ _ _ _ (c2, b2) k b H) in Hu.
  - lia.
  - fold α. rewrite lookup_union, Hπ'. unfold πi. by rewrite lookup_singleton_eq.
  - fold α. rewrite lookup_union, Hφ'. unfold φi. by rewrite lookup_singleton_eq.
Qed.
(** sync receives on d right after its spawn. *)
Theorem sync_not_fsem : ¬ fsem sync_W ∅ Sync.sync_main.
Proof.
  intros [tk Hf]. pose proof (Hf 40) as H. rewrite fmap_empty in H. fnorm H.
  fnew H "c"%string (pconst 0). fbeta H. fbeta H. fbeta H.
  match type of H with FuelE _ _ _ _ _ ?e => eassert (Hs : tstep e (LSpawn _) _) by tsolve end.
  destruct (lffuel_spawn _ _ _ _ _ _ H _ _ Hs) as [_ Hp]. clear H Hs.
  fnorm Hp. fbeta Hp.
  match type of Hp with FuelE _ _ ?π ?φ _ _ => set (P := π) in Hp; set (F := φ) in Hp end.
  match type of Hp with FuelE _ _ _ _ _ ?e =>
    eassert (Hs : tstep e (LSess (SRecv ("c", false)%string (Chan "z" true))) _) by tsolve end.
  destruct sync_budgets as (_ & _ & _ & Hb).
  eapply (fuel_recv_unknown _ _ _ _ _ _ _ _ _ _ _ (pconst 1) 20 Hp Hs).
  - vm_compute. reflexivity.
  - apply not_elem_of_dom. vm_compute. reflexivity.
  - apply not_elem_of_dom. vm_compute. reflexivity.
  - unfold pt_known. change (w_names sync_W) with (hroots Sync.sync_Ψ). rewrite hroots_elem.
    intros (C & xs & y & Hin & Hy & E). unfold Sync.sync_Ψ in Hin.
    rewrite elem_of_app, list_elem_of_singleton in Hin.
    destruct Hin as [Hin|Hin]; [by apply elem_of_nil in Hin|]. injection Hin as -> ->.
    apply list_elem_of_singleton in Hy as ->. discriminate E.
  - apply Hb.
  - match goal with |- w_pay _ ?x ≤ _ => destruct (Hb x) as [_ ->] end. lia.
  - lia.
  - by rewrite (proj1 (Hb _)).
Qed.

(** Stage L6 as stated has no proof: sync is in the fragment and its
    thread has no fuel at the budgets of [src_world]. *)
Theorem lf_fuel_fundamental_fails : ¬ ∀ Ψ t T, lfsource Ψ t T → fsem (src_world Ψ t) ∅ t.
Proof. intros H. exact (sync_not_fsem (H _ _ _ sync_lfsource)). Qed.
