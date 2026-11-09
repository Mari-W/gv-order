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

(** A pending call of the server on channel c, with the point value
    v (syntactic points, sharp edges 173). The server takes the point
    of r as its first argument, so a call names it. The main thread
    passes the literal of the constant 0, and every call the server
    spawns passes [KPay 0] applied to the point of its own call. *)
Definition kob_thunk (v : expr) (c : chan) : expr :=
  Lam (LetU (Var 0) (App (App (App EForce fwsrv) v) (Chan c true))).
Definition kob_call (v : expr) (c : chan) : expr := App (kob_thunk v c) EUnit.
Abbreviation kob_callp x c := (kob_call (App (Konst (KPay 0)) (EPt x)) c).

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

(** One round of a thread s: from s to a spawned pending call on d,
    through β, a new of d and a spawn, without a channel step. *)
Definition kob_round_of (s : expr) (c d : chan) (v' : expr) : Prop :=
  ∃ z e1 e2 e3 e4,
    rtc tbeta s e1 ∧ tstep e1 (LNew d z) e2 ∧ fchans e1 ⊆ {[c]} ∧
    rtc tbeta e2 e3 ∧ tstep e3 (LSpawn (kob_thunk v' d)) e4.

(** The first call, at the literal x. *)
Lemma kob_round_thread_pt x c d :
  kob_round_of (kob_call (EPt x) c) c d (App (Konst (KPay 0)) (EPt x)).
Proof.
  eexists _, _, _, _, _. split_and!.
  - unfold kob_call, kob_thunk, fwsrv. tbeta_run.
  - cbn. tstep_search.
  - cbn. set_solver.
  - cbn. tbeta_run.
  - cbn. tstep_search.
Qed.

(** A spawned call, at x[0]. *)
Lemma kob_round_thread x c d :
  kob_round_of (kob_callp x c) c d (App (Konst (KPay 0)) (EPt (pt_payload x 0))).
Proof.
  eexists _, _, _, _, _. split_and!.
  - unfold kob_call, kob_thunk, fwsrv. tbeta_run.
  - cbn. tstep_search.
  - cbn. set_solver.
  - cbn. tbeta_run.
  - cbn. tstep_search.
Qed.

Lemma kob_round_proc C E s c d v' :
  d ∉ C → d ∉ echans E → d ≠ c → kob_round_of s c d v' →
  ∃ E', tc padmin (C, E ⊎ {[+ s +]}) (C ∪ {[d]}, E' ⊎ {[+ kob_call v' d +]}).
Proof.
  intros HC HE Hd (z & e1 & e2 & e3 & e4 & H1 & H2 & Hf & H3 & H4).
  exists (E ⊎ {[+ e4 +]}).
  eapply tc_rtc_l; [apply rtc_tbeta_padmin, H1|].
  eapply tc_l; [eapply PANew; [exact H2|done|done|set_solver]|].
  eapply tc_rtc_l; [apply rtc_tbeta_padmin, H3|].
  apply tc_once. apply PASpawn. exact H4.
Qed.

Lemma kob_round C E x c d :
  d ∉ C → d ∉ echans E → d ≠ c →
  ∃ E', tc padmin (C, E ⊎ {[+ kob_callp x c +]}) (C ∪ {[d]}, E' ⊎ {[+ kob_callp (pt_payload x 0) d +]}).
Proof. intros HC HE Hd. apply (kob_round_proc C E _ c d); [done|done|done|apply kob_round_thread]. Qed.

(** The main thread reaches the first pending call by β, new and spawn. *)
Lemma kob_start_thread c :
  ∃ e1 e2 e3 e4,
    rtc tbeta fw_main e1 ∧ tstep e1 (LNew c (pconst 0)) e2 ∧ fchans e1 = ∅ ∧
    rtc tbeta e2 e3 ∧ tstep e3 (LSpawn (kob_thunk (EPt (pconst 0)) c)) e4.
Proof.
  eexists _, _, _, _. split_and!.
  - unfold fw_main, fwsrv. tbeta_run.
  - cbn. tstep_search.
  - cbn. set_solver.
  - cbn. tbeta_run.
  - cbn. tstep_search.
Qed.

Lemma kob_start c :
  ∃ E, rtc padmin (∅, {[+ fw_main +]}) (∅ ∪ {[c]}, E ⊎ {[+ kob_call (EPt (pconst 0)) c +]}).
Proof.
  destruct (kob_start_thread c) as (e1 & e2 & e3 & e4 & H1 & H2 & Hf & H3 & H4).
  exists (∅ ⊎ {[+ e4 +]}). rewrite <-(gmultiset_disj_union_left_id {[+ fw_main +]}).
  etrans; [apply rtc_tbeta_padmin, H1|].
  eapply rtc_l; [eapply PANew; [exact H2|set_solver|rewrite echans_empty; set_solver|rewrite Hf; set_solver]|].
  etrans; [apply rtc_tbeta_padmin, H3|].
  apply rtc_once. apply PASpawn. exact H4.
Qed.

(** ** No accessibility from a pending call *)

Lemma kob_not_acc q :
  Acc (λ y x, padmin x y) q →
  ∀ C E x c, rtc padmin q (C, E ⊎ {[+ kob_callp x c +]}) → False.
Proof.
  induction 1 as [q _ IH]. intros C E x c Hq.
  inversion Hq as [? Heq|? q1 ? Hq1 Hrest]; subst.
  - set (d := fresh (C ∪ echans E ∪ {[c]})).
    pose proof (is_fresh (C ∪ echans E ∪ {[c]})) as Hd. fold d in Hd.
    destruct (kob_round C E x c d) as (E' & Hr); [set_solver|set_solver|set_solver|].
    inversion Hr as [? ? Hone|? q1 ? Hq1 Hrest]; subst.
    + by apply (IH _ Hone (C ∪ {[d]}) E' (pt_payload x 0) d).
    + apply (IH _ Hq1 (C ∪ {[d]}) E' (pt_payload x 0) d). by apply tc_rtc.
  - by apply (IH q1 Hq1 C E x c).
Qed.

Theorem kob_tau_diverges : ¬ no_tau_divergence (∅, {[+ fw_main +]}).
Proof.
  intros Hnd. set (c := "kob"%string).
  destruct (kob_start c) as (E & Hs).
  destruct (exist_fresh ((∅ ∪ {[c]}) ∪ echans E ∪ {[c]})) as [d Hd].
  destruct (kob_round_proc ((∅ : gset chan) ∪ {[c]}) E (kob_call (EPt (pconst 0)) c) c d (App (Konst (KPay 0)) (EPt (pconst 0))))
    as (E' & Hr); [set_solver|set_solver|set_solver|apply kob_round_thread_pt|].
  apply (kob_not_acc (∅, {[+ fw_main +]}) (Hnd _ (rtc_refl _ _)) (((∅ : gset chan) ∪ {[c]}) ∪ {[d]}) E' (pconst 0) d).
  etrans; [exact Hs|]. apply tc_rtc, Hr.
Qed.

Corollary kob_not_live W : ¬ ∀ n, LPrel n W ∅ TUnit (∅, {[+ fw_main +]}).
Proof. intros HP. by apply kob_tau_diverges, (live_no_tau_divergence W TUnit). Qed.

(** The live fundamental theorem fails for the present static system. *)
Theorem live_fundamental_false :
  ¬ (∀ W p T, strict W → ptyped W ∅ p T → ∀ n, LPrel n W ∅ T p).
Proof.
  intros H.
  destruct (created_ptyped kfw_Ψ fw_main TUnit kfw_created ltac:(constructor) fw_typed)
    as (W1 & σ & HW1 & Hp).
  apply (kob_not_live W1). by apply H.
Qed.
