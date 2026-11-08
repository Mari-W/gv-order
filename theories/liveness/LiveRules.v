(** * Fundamental cases of the live relation that the costs change

    β is free and the arrow is read at the current level, so applying a
    closure stays at the index (Tait, liveness.md §5). Forcing a box
    unrolls the recursion at the index. The recursion is therefore paid
    by a later self (Löb, §6): the body needs the box only at the levels
    strictly below. Spawn is a τ, and the spawned closure is V at ∗ ⊸ ∗
    at the same level (§7). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveAdequacy rules.TermRules.

Local Set Warnings "-register-all".

(** ** A deterministic β costs nothing *)

Lemma LErel_det_beta n W Θ T F e e' :
  tstep e LBeta e' → (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') →
  LErel n W Θ T F e' → LErel n W Θ T F e.
Proof.
  intros Hst Hdet HE. destruct n as [|n']; [apply LErel_0|].
  apply LErel_S_iff. intros W1 HW1. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst).
  - intros e'' Hst'. destruct (Hdet _ _ Hst') as [_ ->]. by eapply LErel_mono.
  - intros c e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros w e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros σ e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros cd e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
Qed.

(** ** E-App for a closure, at the same index (Tait) *)

Lemma LErel_app_lam n W Θ Θ1 Θ2 ub lb T U F eb v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  LVrel n W Θ1 (TLolli ub lb T U) (Lam eb) → LVrel n W Θ2 T v2 → ub_below W ub F →
  LErel n W Θ U F (App (Lam eb) v2).
Proof.
  intros HW Hc HV1 HV2 Hub. pose proof (LVrel_val _ _ _ _ _ HV2) as Hv2.
  apply LVrel_lolli_iff in HV1 as [(eb' & Heq & _ & _ & HL)|(k & _ & Heq & _)]; [|done].
  injection Heq as <-.
  apply (LErel_det_beta _ _ _ _ _ _ (subst1 v2 eb)).
  - by apply TStepHead, HeadApp.
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply (HL W n Θ2 Θ v2 F); [by apply wext_refl|lia|done|done|done].
Qed.

(** ** Forcing a box unrolls it at the same index *)

Lemma LErel_force n W m k C ub T F eb xs ss :
  strict W → LVrel n W ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox eb) →
  length xs = m → length ss = k → Forall hcontractive ss →
  bcs_hold (w_eq W) (w_lt W) C xs → Forall (pt_known W) xs →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  LErel n W ∅ (sinst_ty (slist ss) (ty_inst xs T)) F (App EForce (EBox eb)).
Proof.
  intros HW HV Hxs Hss Hsc HC HK Hub.
  apply LVrel_box_iff in HV as (_ & eb' & Heq & Hfc & HB). injection Heq as <-.
  specialize (HB W xs ss (wext_refl _ HW) Hxs Hss Hsc HC HK).
  unfold ty_inst in HB |- *. cbn [pinst_ty sinst_ty fmap option_fmap option_map] in HB.
  apply LVrel_lolli_iff in HB as [(eb' & Heq & _ & _ & HL)|(kc & _ & Heq & _)]; [|done].
  unfold thunk in Heq. injection Heq as <-.
  apply (LErel_det_beta _ _ _ _ _ _ (subst1 (EBox eb) eb)).
  - by apply TStepHead, HeadForce.
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - rewrite <-(thunk_app EUnit eb).
    apply (HL W n ∅ ∅ EUnit F); [by apply wext_refl|lia|apply tenv_comp_empty_r|done|].
    by apply LVrel_unit_iff.
Qed.

(** ** E-Exp-Live: recursion through a later self (Löb)

    The body, at an instance and under a future above the instantiated
    upper point, is in E at level n whenever the box itself is in V at
    every level below n. A channel step of the body lowers the index
    and thereby discharges the hypothesis. *)

Lemma tenv_heads_empty' : tenv_heads ∅ = ∅.
Proof. unfold tenv_heads. by rewrite map_fold_empty. Qed.

Lemma LVrel_box_lob W m k C ub T eb :
  fchans eb = ∅ →
  (∀ n W1 xs ss F, wext W W1 → length xs = m → length ss = k → Forall hcontractive ss →
     bcs_hold (w_eq W1) (w_lt W1) C xs → Forall (pt_known W1) xs →
     ub_below W1 (pt_inst (plist xs) <$> ub) F →
     (∀ j W2, j < n → wext W1 W2 →
        LVrel j W2 ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox eb)) →
     LErel n W1 ∅ (sinst_ty (slist ss) (ty_inst xs T)) F (subst1 (EBox eb) eb)) →
  ∀ n W', wext W W' → LVrel n W' ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox eb).
Proof.
  intros Hfc Hbody n. induction n as [n IH] using lt_wf_ind. intros W' HW'.
  apply LVrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
  intros W'' xs ss HW'' Hxs Hss Hsc HC HK.
  unfold ty_inst. cbn [pinst_ty sinst_ty fmap option_fmap option_map].
  apply LVrel_lolli_iff. left. exists (rename S (subst1 (EBox eb) eb)). split_and!.
  - done.
  - rewrite fchans_rename, dom_empty_L. apply set_eq. intros c. split; [|set_solver].
    intros Hc%fchans_subst1_sub. simpl in Hc. rewrite Hfc in Hc. set_solver.
  - simpl. by rewrite tenv_heads_empty'.
  - intros W3 j Θ' Θ'' w F HW3 Hj Hc Hub HVw.
    apply LVrel_unit_iff in HVw as [-> ->]. apply tenv_comp_empty_inv in Hc as ->.
    rewrite thunk_app.
    assert (wext W W3) as HWW3 by (eapply wext_trans; [exact HW'|]; by eapply wext_trans).
    apply (Hbody j W3 xs ss F); [done|done|done|done| | |exact Hub|].
    + destruct HW3 as (_ & He3 & Hl3 & _). eapply bcs_hold_mono; [exact He3|exact Hl3|exact HC].
    + eapply Forall_impl; [exact HK|]. destruct HW3 as (Hn & _). unfold pt_known.
      intros x Hx. by apply Hn.
    + intros i W4 Hi HW4. apply IH; [lia|]. by eapply wext_trans.
Qed.

(** ** E-Spawn: the spawn obligation is V at ∗ ⊸ ∗ at the same level *)

Lemma LErel_spawn n W Θ ub lb F w :
  LVrel n W Θ (TLolli ub lb TUnit TUnit) w → LErel n W Θ TUnit F (App ESpawn w).
Proof.
  intros HV. pose proof (LVrel_val _ _ _ _ _ HV) as Hw.
  assert (∀ α e', tstep (App ESpawn w) α e' → α = LSpawn w ∧ e' = EUnit) as Hdet.
  { intros α e' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst. }
  assert (tstep (App ESpawn w) (LSpawn w) EUnit) as Hst by by apply TStepHead, HeadSpawn.
  destruct n as [|n']; [apply LErel_0|].
  apply LErel_S_iff. intros W1 HW1. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst).
  - intros e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros c e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros w' e'' Hst'. destruct (Hdet _ _ Hst') as [[= <-] ->].
    exists Θ, ∅, ub, lb. split_and!.
    + apply tenv_comp_empty_r.
    + apply Vspawn_LVrel. by eapply LVrel_mono_r.
    + apply LVrel_LErel. by apply LVrel_unit_iff.
  - intros σ e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
  - intros cd e'' Hst'. destruct (Hdet _ _ Hst') as [Hα _]. discriminate Hα.
Qed.
