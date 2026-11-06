(** * Kobayashi's server τ-diverges (liveness.md §6, sharp edges 157)

    examples/KobForwarder.v types Kobayashi's recursive forwarder
    server statically ([fw_typed]) and proves it deadlock free. Every
    call creates a reply channel, spawns the next call and blocks, and
    the spawned call does the same before any channel step. From the
    first spawned call on, new, spawn and β alone continue forever
    ([kob_tau_diverges]).

    So the program is not in the live relation ([kob_not_live]), and
    the live fundamental theorem fails for the present static system
    ([live_fundamental_false]): typed programs may τ-diverge. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveAdequacy examples.KobForwarder.

Local Set Warnings "-register-all".

(** A pending call of the server on channel c. *)
Definition kob_call (c : chan) : expr :=
  App (Lam (LetU (Var 0) (App (App EForce fwsrv) (Chan c)))) EUnit.

Definition tbeta (e e' : expr) : Prop := tstep e LBeta e'.

Lemma rtc_tbeta_padmin C E e e' :
  rtc tbeta e e' → rtc padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]}).
Proof.
  induction 1 as [|e1 e2 e3 H _ IH]; [done|].
  eapply rtc_l; [|exact IH]. by constructor.
Qed.

(** One step of evaluation, found by search. *)
Ltac tstep_search :=
  first [ apply TStepHead; econstructor; simpl; done
        | apply TStepAppL; tstep_search
        | apply TStepAppR; [simpl; done|tstep_search]
        | apply TStepLetU; tstep_search
        | apply TStepLetP; tstep_search
        | apply TStepPairL; tstep_search
        | apply TStepPairR; [simpl; done|tstep_search]
        | apply TStepCase; tstep_search ].

Ltac tbeta_run := repeat (eapply rtc_l; [unfold tbeta; tstep_search|]; cbn); apply rtc_refl.

(** One round: from a pending call on c to a pending call on d, through
    β, a new of d and a spawn, without a channel step. *)
Lemma kob_round_thread c d :
  ∃ e1 e2 e3 e4,
    rtc tbeta (kob_call c) e1 ∧ tstep e1 (LNew d) e2 ∧ fchans e1 ⊆ {[c]} ∧
    rtc tbeta e2 e3 ∧ tstep e3 (LSpawn (Lam (LetU (Var 0) (App (App EForce fwsrv) (Chan d))))) e4.
Proof.
  eexists _, _, _, _. split_and!.
  - unfold kob_call, fwsrv. tbeta_run.
  - cbn. tstep_search.
  - cbn. set_solver.
  - cbn. tbeta_run.
  - cbn. tstep_search.
Qed.

Lemma kob_round C E c d :
  d ∉ C → d ∉ echans E → d ≠ c →
  ∃ E', tc padmin (C, E ⊎ {[+ kob_call c +]}) (C ∪ {[d]}, E' ⊎ {[+ kob_call d +]}).
Proof.
  intros HC HE Hd.
  destruct (kob_round_thread c d) as (e1 & e2 & e3 & e4 & H1 & H2 & Hf & H3 & H4).
  exists (E ⊎ {[+ e4 +]}).
  eapply tc_rtc_l; [apply rtc_tbeta_padmin, H1|].
  eapply tc_l; [apply PANew; [exact H2|done|done|set_solver]|].
  eapply tc_rtc_l; [apply rtc_tbeta_padmin, H3|].
  apply tc_once. apply PASpawn. exact H4.
Qed.

(** The main thread reaches the first pending call by β, new and spawn. *)
Lemma kob_start_thread c :
  ∃ e1 e2 e3 e4,
    rtc tbeta fw_main e1 ∧ tstep e1 (LNew c) e2 ∧ fchans e1 = ∅ ∧
    rtc tbeta e2 e3 ∧ tstep e3 (LSpawn (Lam (LetU (Var 0) (App (App EForce fwsrv) (Chan c))))) e4.
Proof.
  eexists _, _, _, _. split_and!.
  - unfold fw_main, fwsrv. tbeta_run.
  - cbn. tstep_search.
  - cbn. set_solver.
  - cbn. tbeta_run.
  - cbn. tstep_search.
Qed.

Lemma kob_start c :
  ∃ E, rtc padmin (∅, {[+ fw_main +]}) (∅ ∪ {[c]}, E ⊎ {[+ kob_call c +]}).
Proof.
  destruct (kob_start_thread c) as (e1 & e2 & e3 & e4 & H1 & H2 & Hf & H3 & H4).
  exists (∅ ⊎ {[+ e4 +]}). rewrite <-(gmultiset_disj_union_left_id {[+ fw_main +]}).
  etrans; [apply rtc_tbeta_padmin, H1|].
  eapply rtc_l; [apply PANew; [exact H2|set_solver|rewrite echans_empty; set_solver|rewrite Hf; set_solver]|].
  etrans; [apply rtc_tbeta_padmin, H3|].
  apply rtc_once. apply PASpawn. exact H4.
Qed.

(** ** No accessibility from a pending call *)

Lemma kob_not_acc q :
  Acc (λ y x, padmin x y) q →
  ∀ C E c, rtc padmin q (C, E ⊎ {[+ kob_call c +]}) → False.
Proof.
  induction 1 as [q _ IH]. intros C E c Hq.
  inversion Hq as [? Heq|? q1 ? Hq1 Hrest]; subst.
  - set (d := fresh (C ∪ echans E ∪ {[c]})).
    pose proof (is_fresh (C ∪ echans E ∪ {[c]})) as Hd. fold d in Hd.
    destruct (kob_round C E c d) as (E' & Hr); [set_solver|set_solver|set_solver|].
    inversion Hr as [? ? Hone|? q1 ? Hq1 Hrest]; subst.
    + by apply (IH _ Hone (C ∪ {[d]}) E' d).
    + apply (IH _ Hq1 (C ∪ {[d]}) E' d). by apply tc_rtc.
  - by apply (IH q1 Hq1 C E c).
Qed.

Theorem kob_tau_diverges : ¬ no_tau_divergence (∅, {[+ fw_main +]}).
Proof.
  intros Hnd. set (c := "kob"%string).
  destruct (kob_start c) as (E & Hs).
  apply (kob_not_acc (∅, {[+ fw_main +]})) with (∅ ∪ {[c]}) E c; [|exact Hs].
  apply Hnd. apply rtc_refl.
Qed.

Corollary kob_not_live W : ¬ ∀ n, LPrel n W ∅ TUnit (∅, {[+ fw_main +]}).
Proof. intros HP. by apply kob_tau_diverges, (live_no_tau_divergence W TUnit). Qed.

(** The live fundamental theorem fails for the present static system. *)
Theorem live_fundamental_false :
  ¬ (∀ W p T, strict W → ptyped W ∅ p T → ∀ n, LPrel n W ∅ T p).
Proof.
  intros H. apply (kob_not_live (Wpo [])).
  apply H; [apply Wpo_strict|]. apply ptyped_closed_s; [constructor|apply fw_typed].
Qed.
