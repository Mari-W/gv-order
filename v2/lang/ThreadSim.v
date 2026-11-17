(** * Threads related one to one, for simulations (stage S1)

    The tools that simulations share (the translations of PN, PGV and MP
    in the old development use them). [bstar] is a run of β steps of one
    thread, [ectx] an evaluation context, [mrel P] relates two
    multisets of threads one to one by P, and [msb] is a β step of one
    thread of a multiset. *)

From stdpp Require Import relations.
From GV Require Export lang.Safety.

Set Default Proof Using "All".

Abbreviation bstar := (rtc (λ x y, tstep x LBeta y)).

Lemma bstar_val t t' : is_val t → bstar t t' → t' = t.
Proof. intros Hv H. inversion H; subst; [done|]. exfalso. eauto using val_no_tstep. Qed.

(** An evaluation context as a function: it lifts every step. *)
Definition ectx (K : expr → expr) : Prop := ∀ e α e', tstep e α e' → tstep (K e) α (K e').

Lemma ectx_frame f : frame_val f → ectx (fill_frame f).
Proof. intros Hf ???. by apply t_act_ctx. Qed.
Lemma ectx_appl e2 : ectx (λ x, App x e2).
Proof. exact (ectx_frame (FAppL e2) I). Qed.
Lemma ectx_appr v : is_val v → ectx (λ x, App v x).
Proof. intros Hv. exact (ectx_frame (FAppR v) Hv). Qed.
Lemma ectx_case e1 e2 : ectx (λ x, Case x e1 e2).
Proof. exact (ectx_frame (FCase e1 e2) I). Qed.
Lemma ectx_op k : ectx (λ x, Op k x).
Proof. exact (ectx_frame (FOp k) I). Qed.
Lemma ectx_comp K1 K2 : ectx K1 → ectx K2 → ectx (λ x, K1 (K2 x)).
Proof. intros H1 H2 ???. auto. Qed.
Lemma ectx_id : ectx (λ x, x).
Proof. by intros ???. Qed.

Lemma bstar_ectx K e e' : ectx K → bstar e e' → bstar (K e) (K e').
Proof. intros HK. apply rtc_congruence. intros. by apply HK. Qed.

(** Multisets of threads related one to one. *)
Inductive mrel (P : expr → expr → Prop) : gmultiset expr → gmultiset expr → Prop :=
  | mrel_nil : mrel P ∅ ∅
  | mrel_cons s t Es Et : P s t → mrel P Es Et → mrel P ({[+ s +]} ⊎ Es) ({[+ t +]} ⊎ Et).

Lemma mrel_flip P Es Et : mrel P Es Et → mrel (flip P) Et Es.
Proof. induction 1; by constructor. Qed.

Lemma mrel_extract P Es Et0 t :
  mrel P Es (Et0 ⊎ {[+ t +]}) → ∃ Es0 s, Es = Es0 ⊎ {[+ s +]} ∧ P s t ∧ mrel P Es0 Et0.
Proof.
  intros H. remember (Et0 ⊎ {[+ t +]}) as Et eqn:HEt. revert Et0 HEt.
  induction H as [|s1 t1 Es1 Et1 HP Hm IH]; intros Et0 HEt.
  - exfalso. multiset_solver.
  - destruct (decide (t1 = t)) as [->|Hne].
    + exists Es1, s1. split_and!; [multiset_solver|done|].
      assert (Et1 = Et0) as -> by multiset_solver. done.
    + assert (t ∈ Et1) as Ht by multiset_solver.
      destruct (gmultiset_split1 _ _ Ht) as [Et2 ->].
      destruct (IH Et2 eq_refl) as (Es2 & s & -> & HPs & Hm2).
      exists ({[+ s1 +]} ⊎ Es2), s. split_and!; [multiset_solver|done|].
      assert (Et0 = {[+ t1 +]} ⊎ Et2) as -> by multiset_solver. by constructor.
Qed.

Lemma mrel_extract_l P Es0 s Et :
  mrel P (Es0 ⊎ {[+ s +]}) Et → ∃ Et0 t, Et = Et0 ⊎ {[+ t +]} ∧ P s t ∧ mrel P Es0 Et0.
Proof.
  intros H. apply mrel_flip in H. destruct (mrel_extract _ _ _ _ H) as (Et0 & t & -> & Hp & Hm).
  exists Et0, t. split_and!; [done|done|]. apply mrel_flip in Hm.
  by induction Hm; constructor.
Qed.

Lemma mrel_snoc P s t Es Et : P s t → mrel P Es Et → mrel P (Es ⊎ {[+ s +]}) (Et ⊎ {[+ t +]}).
Proof.
  intros. rewrite (comm_L (⊎) Es), (comm_L (⊎) Et). by constructor.
Qed.

Lemma mrel_impl P P' Es Et : (∀ s t, s ∈ Es → P s t → P' s t) → mrel P Es Et → mrel P' Es Et.
Proof.
  intros HP H. induction H; constructor.
  - apply HP; [multiset_solver|done].
  - apply IHmrel. intros. apply HP; [multiset_solver|done].
Qed.

Lemma mrel_elem_l P Es Et s : mrel P Es Et → s ∈ Es → ∃ t, t ∈ Et ∧ P s t.
Proof.
  induction 1 as [|s1 t1 Es Et HP Hm IH]; [multiset_solver|].
  rewrite gmultiset_elem_of_disj_union, gmultiset_elem_of_singleton.
  intros [->|Hs]; [exists t1; split; [multiset_solver|done]|].
  destruct (IH Hs) as (t & ? & ?). exists t. split; [multiset_solver|done].
Qed.

Lemma mrel_elem_r P Es Et t : mrel P Es Et → t ∈ Et → ∃ s, s ∈ Es ∧ P s t.
Proof.
  induction 1 as [|s1 t1 Es Et HP Hm IH]; [multiset_solver|].
  rewrite gmultiset_elem_of_disj_union, gmultiset_elem_of_singleton.
  intros [->|Ht]; [exists s1; split; [multiset_solver|done]|].
  destruct (IH Ht) as (s & ? & ?). exists s. split; [multiset_solver|done].
Qed.

Lemma mrel_echans P Es Et :
  (∀ s t, P s t → fchans t ⊆ fchans s) → mrel P Es Et → echans Et ⊆ echans Es.
Proof.
  intros HP Hm c. rewrite !elem_of_echans. intros (t & Ht & Hc).
  destruct (mrel_elem_r _ _ _ _ Hm Ht) as (s & Hs & Hst). exists s. split; [done|].
  by apply (HP _ _ Hst).
Qed.

Lemma bstar_fchans t t' : bstar t t' → fchans t' ⊆ fchans t.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|]. apply tstep_fchans in Hxy. simpl in Hxy. set_solver.
Qed.

(** β steps of single threads. *)
Definition msb (E E' : gmultiset expr) : Prop :=
  ∃ E0 e e', tstep e LBeta e' ∧ E = E0 ⊎ {[+ e +]} ∧ E' = E0 ⊎ {[+ e' +]}.

Lemma msb_bstar E t t' : bstar t t' → rtc msb (E ⊎ {[+ t +]}) (E ⊎ {[+ t' +]}).
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|]. eapply rtc_l; [|exact IH]. by exists E, x, y.
Qed.

Lemma msb_frame F E E' : rtc msb E E' → rtc msb (F ⊎ E) (F ⊎ E').
Proof.
  induction 1 as [|x y z (E0 & e & e' & Hst & -> & ->) _ IH]; [done|].
  eapply rtc_l; [|exact IH]. exists (F ⊎ E0), e, e'. split_and!; [done|multiset_solver..].
Qed.

Lemma msb_pred C E E' : rtc msb E E' → pred_star (C, E) (C, E').
Proof.
  induction 1 as [|x y z (E0 & e & e' & Hst & -> & ->) _ IH]; [done|].
  eapply rtc_l; [|exact IH]. unfold preduction. rewrite pstep_iff. by apply ps_beta.
Qed.

Lemma bstar_proc C E t t' : bstar t t' → pred_star (C, E ⊎ {[+ t +]}) (C, E ⊎ {[+ t' +]}).
Proof. intros. by apply msb_pred, msb_bstar. Qed.

Lemma bstar_proc2 C E F t t' :
  bstar t t' → pred_star (C, E ⊎ {[+ t +]} ⊎ F) (C, E ⊎ {[+ t' +]} ⊎ F).
Proof.
  intros H. assert (∀ x, E ⊎ {[+ x +]} ⊎ F = (E ⊎ F) ⊎ {[+ x +]}) as HE by (intros; multiset_solver).
  rewrite !HE. by apply bstar_proc.
Qed.

Lemma normalize P P' Es Et :
  mrel P Es Et → (∀ s t, s ∈ Es → P s t → ∃ t', bstar t t' ∧ P' s t') →
  ∃ Et', rtc msb Et Et' ∧ mrel P' Es Et'.
Proof.
  induction 1 as [|s t Es Et HP Hm IH]; intros HPP.
  - exists ∅. split; [done|constructor].
  - destruct (HPP s t) as (t' & Hs & HP'); [multiset_solver|done|].
    destruct IH as (Et' & Hst & Hm').
    { intros s0 t0 Hin. apply HPP. multiset_solver. }
    exists ({[+ t' +]} ⊎ Et'). split; [|by constructor].
    apply (rtc_trans _ ({[+ t' +]} ⊎ Et)).
    + rewrite (comm_L (⊎) {[+ t +]}), (comm_L (⊎) {[+ t' +]}). by apply msb_bstar.
    + by apply msb_frame.
Qed.

(** [mrel] under a map of every thread, such as the substitution of a
    channel by a link. *)
Lemma mrel_map P f g Es Et :
  (∀ s t, P s t → P (f s) (g t)) → mrel P Es Et → mrel P (gmultiset_map f Es) (gmultiset_map g Et).
Proof.
  intros Hfg. induction 1 as [|s t Es Et HP Hm IH].
  - rewrite !gmultiset_map_empty. constructor.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton. constructor; [by apply Hfg|done].
Qed.
