(** * Characteristic equations of the live relation

    Encoding-free unfoldings, as [Vrel_*_iff], [Erel_S_iff] and
    [Erel_S_ind] for the relation of LogicalRelation.v. Later proofs use
    only these. [LEstep X n] is one unfolding of E at level S n with X
    for E at S n itself, [LPstep X n] the same for P. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveRelation.

Local Set Warnings "-register-all".

(** ** Unfolding the levels *)

Lemma LVrel_eq n W Θ T v : LVrel n W Θ T v ↔ lVtop (llevels n) n T W Θ v.
Proof. unfold LVrel. by rewrite llevel_at_eq. Qed.

Lemma LErel_S_eq n W Θ T F e :
  LErel (S n) W Θ T F e ↔ Eind (llevels (S n)) (S n) (lVtop (llevels (S n)) (S n) T) T W Θ F e.
Proof. unfold LErel. by rewrite llevel_at_eq. Qed.

Lemma LPrel_S_eq n W Σ T p :
  LPrel (S n) W Σ T p ↔ Pind (llevels (S n)) (S n) (lVtop (llevels (S n)) (S n) T) T W Σ p.
Proof. unfold LPrel. by rewrite llevel_at_eq. Qed.

Lemma LErel_eq n W Θ T F e :
  LErel n W Θ T F e ↔ Etop (llevels n) n (lVtop (llevels n) n T) T W Θ F e.
Proof. unfold LErel. by rewrite llevel_at_eq. Qed.

Lemma lvV_llevels n j W Θ T v : j < n → lvV (llevels n j) W Θ T v ↔ LVrel j W Θ T v.
Proof. intros Hj. by rewrite llevels_at. Qed.

Lemma lvE_llevels n j W Θ T F e : j < n → lvE (llevels n j) W Θ T F e ↔ LErel j W Θ T F e.
Proof. intros Hj. by rewrite llevels_at. Qed.

Lemma lvP_llevels n j W Σ T p : j < n → lvP (llevels n j) W Σ T p ↔ LPrel j W Σ T p.
Proof. intros Hj. by rewrite llevels_at. Qed.

(** ** V *)

(** One step of [LVdef], per type constructor, without unfolding the
    fuel of the recursive calls. *)
Lemma LVdef_S_lolli below n k W Θ ub lb T1 U v :
  LVdef below n (S k) W Θ (TLolli ub lb T1 U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W lb (tenv_heads Θ) ∧
     ∀ W' j Θ' Θ'' w F, wext W W' → j ≤ n →
       tenv_comp (w_eq W') Θ'' Θ Θ' → ub_below W' ub F →
       (j < n → lvV (below j) W' Θ' T1 w → lvE (below j) W' Θ'' U F (subst1 w eb)) ∧
       (j = n → LVdef below n k W' Θ' T1 w →
          Etop below n (λ W Θ v, LVdef below n k W Θ U v) U W' Θ'' F (subst1 w eb)))
  ∨ (∃ kc T0, v = Konst kc ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) kc T0 ∧
       teqW W T0 (TLolli ub lb T1 U)).
Proof. done. Qed.

Lemma LVdef_S_prod below n k W Θ T1 U v :
  LVdef below n (S k) W Θ (TProd T1 U) v ↔
  ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
    LVdef below n k W Θ1 T1 v1 ∧ LVdef below n k W Θ2 U v2.
Proof. done. Qed.

Lemma LVdef_S_sum below n k W Θ T1 U v :
  LVdef below n (S k) W Θ (TSum T1 U) v ↔
  (∃ v', v = Inj1 v' ∧ LVdef below n k W Θ T1 v') ∨ (∃ v', v = Inj2 v' ∧ LVdef below n k W Θ U v').
Proof. done. Qed.

Lemma LVdef_S_box below n k W Θ m kk C T1 v :
  LVdef below n (S k) W Θ (TBox m kk C T1) v ↔
  Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ W' xs ss, wext W W' → length xs = m → length ss = kk → Forall hcontractive ss →
      bcs_hold (w_eq W') (w_lt W') C xs → Forall (pt_known W') xs →
      LVdef below n k W' ∅ (sinst_ty (slist ss) (ty_inst xs T1)) (thunk eb).
Proof. done. Qed.

Lemma LVdef_S_ex below n k W Θ lb m C T1 v :
  LVdef below n (S k) W Θ (TEx lb m C T1) v ↔
  lbx_below W lb (tenv_heads Θ) false ∧
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    LVdef below n k W Θ (ty_inst xs T1) v.
Proof. done. Qed.

Lemma LVdef_fuel_l below n k1 k2 W Θ T v :
  LVdef below n k1 W Θ T v → tsize T < k1 → tsize T < k2 → LVdef below n k2 W Θ T v.
Proof. intros H H1 H2. exact (proj1 (LVdef_fuel below n k1 k2 W Θ T v H1 H2) H). Qed.

Lemma LVrel_unit_iff n W Θ v : LVrel n W Θ TUnit v ↔ Θ = ∅ ∧ v = EUnit.
Proof. by rewrite LVrel_eq. Qed.

Lemma LVrel_sess_iff n W Θ s x v :
  LVrel n W Θ (TSess s x) v ↔
  ∃ c s0 k, v = Chan c ∧ Θ = {[c := One (s0, k)]} ∧ seq s0 s ∧ w_eq W k x.
Proof. by rewrite LVrel_eq. Qed.

Lemma LVrel_prod_iff n W Θ T U v :
  LVrel n W Θ (TProd T U) v ↔
  ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
    LVrel n W Θ1 T v1 ∧ LVrel n W Θ2 U v2.
Proof.
  rewrite LVrel_eq. unfold lVtop. cbn [tsize]. rewrite LVdef_S_prod.
  setoid_rewrite LVrel_eq. unfold lVtop.
  split; intros (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2); exists v1, v2, Θ1, Θ2;
    (split_and!; [done|done| |]); (eapply LVdef_fuel_l; [eassumption|..]); lia.
Qed.

Lemma LVrel_sum_iff n W Θ T U v :
  LVrel n W Θ (TSum T U) v ↔
  (∃ v', v = Inj1 v' ∧ LVrel n W Θ T v') ∨ (∃ v', v = Inj2 v' ∧ LVrel n W Θ U v').
Proof.
  rewrite LVrel_eq. unfold lVtop. cbn [tsize]. rewrite LVdef_S_sum.
  setoid_rewrite LVrel_eq. unfold lVtop.
  split; (intros [(v' & -> & H)|(v' & -> & H)]; [left|right]); exists v'; (split; [done|]);
    (eapply LVdef_fuel_l; [eassumption|..]); lia.
Qed.

Lemma LVrel_box_iff n W Θ m k C T v :
  LVrel n W Θ (TBox m k C T) v ↔
  Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ W' xs ss, wext W W' → length xs = m → length ss = k → Forall hcontractive ss →
      bcs_hold (w_eq W') (w_lt W') C xs → Forall (pt_known W') xs →
      LVrel n W' ∅ (sinst_ty (slist ss) (ty_inst xs T)) (thunk eb).
Proof.
  rewrite LVrel_eq. unfold lVtop. cbn [tsize]. rewrite LVdef_S_box.
  setoid_rewrite LVrel_eq. unfold lVtop.
  assert (∀ xs ss, tsize (sinst_ty (slist ss) (ty_inst xs T)) = tsize T) as Hts.
  { intros xs ss. unfold ty_inst. by rewrite tsize_sinst, tsize_pinst. }
  apply and_iff_compat_l. f_equiv. intros eb. do 2 apply and_iff_compat_l.
  split; intros H W' xs ss ? ? ? ? ? ?; (eapply LVdef_fuel_l; [by apply H|..]); rewrite Hts; lia.
Qed.

Lemma LVrel_ex_iff n W Θ lb m C T v :
  LVrel n W Θ (TEx lb m C T) v ↔
  lbx_below W lb (tenv_heads Θ) false ∧
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    LVrel n W Θ (ty_inst xs T) v.
Proof.
  rewrite LVrel_eq. unfold lVtop. cbn [tsize]. rewrite LVdef_S_ex.
  setoid_rewrite LVrel_eq. unfold lVtop.
  assert (∀ xs, tsize (ty_inst xs T) = tsize T) as Hts.
  { intros xs. unfold ty_inst. by rewrite tsize_pinst. }
  apply and_iff_compat_l. f_equiv. intros xs. do 3 apply and_iff_compat_l.
  split; intros H; (eapply LVdef_fuel_l; [exact H|..]); rewrite Hts; lia.
Qed.

(** The arrow reads argument and body at every j ≤ n. *)
Lemma LVrel_lolli_iff n W Θ ub lb T U v :
  LVrel n W Θ (TLolli ub lb T U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W lb (tenv_heads Θ) ∧
     ∀ W' j Θ' Θ'' w F, wext W W' → j ≤ n →
       tenv_comp (w_eq W') Θ'' Θ Θ' → ub_below W' ub F →
       LVrel j W' Θ' T w → LErel j W' Θ'' U F (subst1 w eb))
  ∨ (∃ k T0, v = Konst k ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) k T0 ∧
       teqW W T0 (TLolli ub lb T U)).
Proof.
  rewrite LVrel_eq. unfold lVtop. cbn [tsize]. rewrite LVdef_S_lolli.
  apply or_iff_compat_r.
  split; intros (eb & -> & Hfc & Hlb & H); exists eb; (split_and!; [done..|]).
  - intros W' j Θ' Θ'' w F HW Hj Hc Hub HV.
    destruct (H W' j Θ' Θ'' w F HW Hj Hc Hub) as [K1 K2].
    destruct (decide (j < n)) as [Hlt|Hge].
    + apply (lvE_llevels n); [done|]. apply K1; [done|]. by apply (lvV_llevels n).
    + assert (j = n) as -> by lia. apply LErel_eq.
      eapply Etop_VT_iff; [|apply K2; [done|]].
      * intros. unfold lVtop. apply LVdef_fuel; lia.
      * apply LVrel_eq in HV. unfold lVtop in HV. eapply LVdef_fuel_l; [exact HV|..]; lia.
  - intros W' j Θ' Θ'' w F HW Hj Hc Hub. split.
    + intros Hlt HV. apply (lvE_llevels n); [done|].
      apply (H W' j Θ' Θ'' w F HW Hj Hc Hub). by apply (lvV_llevels n).
    + intros -> HV. specialize (H W' n Θ' Θ'' w F HW Hj Hc Hub).
      apply LErel_eq in H.
      * eapply Etop_VT_iff; [|exact H].
        intros. unfold lVtop. apply LVdef_fuel; lia.
      * apply LVrel_eq. unfold lVtop. eapply LVdef_fuel_l; [exact HV|..]; lia.
Qed.

(** ** E

    [Vsp] is V at ∗ ⊸ ∗, read through the spawn obligation. *)
Lemma Vspawn_ext Vl1 Vl2 El1 El2 (E1 E2 : world → tenv → gset point → expr → Prop) n W Θ ub lb w :
  (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
  (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e → El2 j W Θ T F e) →
  (∀ W Θ F e, E1 W Θ F e → E2 W Θ F e) →
  Vspawn Vl1 El1 E1 n W Θ ub lb w → Vspawn Vl2 El2 E2 n W Θ ub lb w.
Proof.
  intros HV HEl HE [(eb & -> & Hfc & Hlb & H)|Hk]; [left|by right].
  exists eb. split_and!; [done..|]. intros W' j Θ' Θ'' w' F HW Hj Hc Hub.
  destruct (H W' j Θ' Θ'' w' F HW Hj Hc Hub) as [H1 H2]. split.
  - intros Hlt HV'. apply HEl; [done|]. apply H1; [done|]. by apply HV.
  - intros ? ? ?. apply HE. auto.
Qed.

Lemma Vspawn_LVrel n W Θ ub lb w :
  Vspawn LVrel LErel (λ W Θ F e, LErel n W Θ TUnit F e) n W Θ ub lb w ↔
  LVrel n W Θ (TLolli ub lb TUnit TUnit) w.
Proof.
  rewrite LVrel_lolli_iff. unfold Vspawn. apply or_iff_compat_r.
  split; intros (eb & -> & Hfc & Hlb & H); exists eb; (split_and!; [done..|]).
  - intros W' j Θ' Θ'' w' F HW Hj Hc Hub HV.
    destruct (H W' j Θ' Θ'' w' F HW Hj Hc Hub) as [K1 K2].
    destruct (decide (j < n)) as [Hlt|Hge]; [by apply K1|].
    assert (j = n) as -> by lia. apply LVrel_unit_iff in HV as [-> ->]. by apply K2.
  - intros W' j Θ' Θ'' w' F HW Hj Hc Hub. split.
    + intros _ HV. by apply (H W' j Θ' Θ'' w' F).
    + intros -> -> ->. apply (H W' n ∅ Θ'' EUnit F); [done..|]. by apply LVrel_unit_iff.
Qed.

Definition LEstep (X : world → tenv → ty → gset point → expr → Prop) (n : nat)
    (W : world) (Θ : tenv) (T : ty) (F : gset point) (e : expr) : Prop :=
  ∀ W1, wext_r W W1 →
    (irred e → LVrel (S n) W1 Θ T e) ∧
    (¬ irred e → ready_t W1 Θ F e) ∧
    (∀ e', tstep e LBeta e' → X W1 Θ T F e') ∧
    (∀ c e', tstep e (LNew c) e' → c ∉ dom Θ →
       ∃ a s s' W', NConst a ∉ tenv_roots Θ ∪ ty_roots T ∪ future_roots F ∧
         sdual s s' ∧ wext_fresh W1 {[NConst a]} W' ∧
         X W' (<[c := Both (s, pconst a) (s', pt_dual (pconst a))]> Θ) T F e') ∧
    (∀ w e', tstep e (LSpawn w) e' →
       ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W1) Θ Θ1 Θ2 ∧
         Vspawn LVrel LErel (λ W Θ F e, X W Θ TUnit F e) (S n) W1 Θ1 ub lb w ∧
         X W1 Θ2 T F e') ∧
    (∀ σ e', tstep e (LSess σ) e' → LEobl LVrel LErel (S n) W1 Θ T F σ e').

Lemma LEstep_mono (X Y : world → tenv → ty → gset point → expr → Prop) n W Θ T F e :
  (∀ W Θ T F e, X W Θ T F e → Y W Θ T F e) →
  LEstep X n W Θ T F e → LEstep Y n W Θ T F e.
Proof.
  intros HXY H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ).
  split_and!; [done|done| | | |done].
  - intros e' Hst. auto.
  - intros c e' Hst Hc. destruct (Hn c e' Hst Hc) as (a & s & s' & W' & ? & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_mono; [|exact Hv]. auto.
Qed.

(** One unfolding of the inductive layer, read at the levels. *)
Lemma Ebody_LEstep n (X : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop)
    (Y : world → tenv → ty → gset point → expr → Prop) VT T W Θ F e :
  (∀ W Θ v, VT W Θ v → LVrel (S n) W Θ T v) →
  (∀ W Θ F e, X VT T W Θ F e → Y W Θ T F e) →
  (∀ W Θ F e, X Vunit_top TUnit W Θ F e → Y W Θ TUnit F e) →
  Ebody (llevels (S n)) (S n) X VT T W Θ F e →
  LEstep Y n W Θ T F e.
Proof.
  intros HV HX HXu H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ).
  split_and!; [|done| | | |].
  - intros Hirr. auto.
  - intros e' Hst. auto.
  - intros c e' Hst Hc. destruct (Hn c e' Hst Hc) as (a & s & s' & W' & ? & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_ext; [..|exact Hv]; [| |auto].
    + intros j Hj ? ? ? ?. by apply lvV_llevels.
    + intros j Hj ? ? ? ? ?. by apply lvE_llevels.
  - intros σ e' Hst. eapply LEobl_mono; [..|exact (Hσ σ e' Hst)].
    + intros j Hj ? ? ? ?. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvE_llevels. simpl in Hj. lia.
Qed.

Lemma LEstep_Ebody n (X : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop)
    (Y : world → tenv → ty → gset point → expr → Prop) T W Θ F e :
  (∀ T W Θ F e, Y W Θ T F e → X (lVtop (llevels (S n)) (S n) T) T W Θ F e) →
  (∀ W Θ F e, Y W Θ TUnit F e → X Vunit_top TUnit W Θ F e) →
  LEstep Y n W Θ T F e →
  Ebody (llevels (S n)) (S n) X (lVtop (llevels (S n)) (S n) T) T W Θ F e.
Proof.
  intros HX HXu H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ).
  split_and!; [|done| | | |].
  - intros Hirr. apply LVrel_eq. auto.
  - intros e' Hst. auto.
  - intros c e' Hst Hc. destruct (Hn c e' Hst Hc) as (a & s & s' & W' & ? & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_ext; [..|exact Hv]; [| |auto].
    + intros j Hj ? ? ? ?. symmetry. by apply lvV_llevels.
    + intros j Hj ? ? ? ? ?. by apply lvE_llevels.
  - intros σ e' Hst. eapply LEobl_mono; [..|exact (Hσ σ e' Hst)].
    + intros j Hj ? ? ? ?. symmetry. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvE_llevels. simpl in Hj. lia.
Qed.

Lemma LErel_S_unit n W Θ F e :
  LErel (S n) W Θ TUnit F e ↔ Eind (llevels (S n)) (S n) Vunit_top TUnit W Θ F e.
Proof. rewrite LErel_S_eq. by apply Eind_VT_iff. Qed.

Lemma LErel_S_iff n W Θ T F e : LErel (S n) W Θ T F e ↔ LEstep (LErel (S n)) n W Θ T F e.
Proof.
  rewrite LErel_S_eq. split.
  - intros H%Eind_inv. eapply Ebody_LEstep; [..|exact H].
    + intros. by apply LVrel_eq.
    + intros. by apply LErel_S_eq.
    + intros. by apply LErel_S_unit.
  - intros H. constructor. eapply LEstep_Ebody; [..|exact H].
    + intros. by apply LErel_S_eq.
    + intros. by apply LErel_S_unit.
Qed.

(** Induction over the τ steps at a fixed level S n. *)
Lemma LErel_S_ind n (Φ : world → tenv → ty → gset point → expr → Prop) :
  (∀ W Θ T F e,
     LEstep (λ W Θ T F e, LErel (S n) W Θ T F e ∧ Φ W Θ T F e) n W Θ T F e →
     Φ W Θ T F e) →
  ∀ W Θ T F e, LErel (S n) W Θ T F e → Φ W Θ T F e.
Proof.
  intros Hind W Θ T F e HE. apply LErel_S_eq in HE.
  cut (∀ VT T W Θ F e, Eind (llevels (S n)) (S n) VT T W Θ F e →
         (∀ W Θ v, VT W Θ v ↔ lVtop (llevels (S n)) (S n) T W Θ v) → Φ W Θ T F e).
  { intros H. by apply (H _ _ _ _ _ _ HE). }
  clear W Θ T F e HE. intros VT T W Θ F e HE.
  induction HE as [VT T W Θ F e H] using Eind_ind'. intros HVT.
  apply Hind. eapply (Ebody_LEstep n _ _ VT); [| | |exact H].
  - intros. apply LVrel_eq. by apply HVT.
  - intros W' Θ' F' e' [H1 H2]. split.
    + apply LErel_S_eq. eapply Eind_VT_mono; [|exact H1]. intros. by apply HVT.
    + by apply H2.
  - intros W' Θ' F' e' [H1 H2]. split.
    + by apply LErel_S_unit.
    + apply H2. intros. done.
Qed.
