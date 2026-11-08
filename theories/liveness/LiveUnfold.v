(** * Characteristic equations of the live relation

    Encoding-free unfoldings, as [Vrel_*_iff], [Erel_S_iff] and
    [Erel_S_ind] for the relation of LogicalRelation.v. Later proofs use
    only these. [LEstep X n] is one unfolding of E at level S n with X
    for E at S n itself, [LPstep X n] the same for P. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveRelation invariance.Monotonicity.

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
       ∀ L : gset pname, ∃ x s s' W', new_place W1 (L ∪ tenv_roots Θ ∪ ty_roots T ∪ future_roots F) x W' ∧
         sdual s s' ∧
         X W' (<[c := Both (s, x) (s', pt_dual x)]> Θ) T F e') ∧
    (∀ w e', tstep e (LSpawn w) e' →
       ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W1) Θ Θ1 Θ2 ∧
         Vspawn LVrel LErel (λ W Θ F e, X W Θ TUnit F e) (S n) W1 Θ1 ub lb w ∧
         X W1 Θ2 T F e') ∧
    (∀ σ e', tstep e (LSess σ) e' → LEobl LVrel LErel (S n) W1 Θ T F σ e') ∧
    (∀ cd e', tstep e (LSess (SLink cd)) e' → LElink (λ W Θ F e, X W Θ T F e) W1 Θ F cd e').

Lemma LEstep_mono (X Y : world → tenv → ty → gset point → expr → Prop) n W Θ T F e :
  (∀ W Θ T F e, X W Θ T F e → Y W Θ T F e) →
  LEstep X n W Θ T F e → LEstep Y n W Θ T F e.
Proof.
  intros HXY H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split_and!; [done|done| | | |done|].
  - intros e' Hst. auto.
  - intros c e' Hst Hc L. destruct (Hn c e' Hst Hc L) as (a & s & s' & W' & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_mono; [|exact Hv]. auto.
  - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)]. auto.
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
  intros HV HX HXu H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split_and!; [|done| | | | |].
  - intros Hirr. auto.
  - intros e' Hst. auto.
  - intros c e' Hst Hc L. destruct (Hn c e' Hst Hc L) as (a & s & s' & W' & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_ext; [..|exact Hv]; [| |auto].
    + intros j Hj ? ? ? ?. by apply lvV_llevels.
    + intros j Hj ? ? ? ? ?. by apply lvE_llevels.
  - intros σ e' Hst. eapply LEobl_mono; [..|exact (Hσ σ e' Hst)].
    + intros j Hj ? ? ? ?. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvE_llevels. simpl in Hj. lia.
  - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)]. auto.
Qed.

Lemma LEstep_Ebody n (X : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop)
    (Y : world → tenv → ty → gset point → expr → Prop) T W Θ F e :
  (∀ T W Θ F e, Y W Θ T F e → X (lVtop (llevels (S n)) (S n) T) T W Θ F e) →
  (∀ W Θ F e, Y W Θ TUnit F e → X Vunit_top TUnit W Θ F e) →
  LEstep Y n W Θ T F e →
  Ebody (llevels (S n)) (S n) X (lVtop (llevels (S n)) (S n) T) T W Θ F e.
Proof.
  intros HX HXu H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split_and!; [|done| | | | |].
  - intros Hirr. apply LVrel_eq. auto.
  - intros e' Hst. auto.
  - intros c e' Hst Hc L. destruct (Hn c e' Hst Hc L) as (a & s & s' & W' & ? & ? & ?).
    exists a, s, s', W'. auto.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |auto].
    eapply Vspawn_ext; [..|exact Hv]; [| |auto].
    + intros j Hj ? ? ? ?. symmetry. by apply lvV_llevels.
    + intros j Hj ? ? ? ? ?. by apply lvE_llevels.
  - intros σ e' Hst. eapply LEobl_mono; [..|exact (Hσ σ e' Hst)].
    + intros j Hj ? ? ? ?. symmetry. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvE_llevels. simpl in Hj. lia.
  - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)]. auto.
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

(** ** P *)

Definition LPstep (X : world → senv → ty → proc → Prop) (n : nat)
    (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  ∀ W1, wext_r W W1 →
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ LVrel (S n) W1 (tenv_of Σ) T v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (¬ pirred p → ready_p W1 Σ p) ∧
    (∀ p', padmin p p' → p'.1 ## dom Σ →
       ∀ L : gset pname, ∃ N W', N ## L ∪ senv_roots Σ ∪ ty_roots T ∧ wext_fresh W1 N W' ∧ X W' Σ T p') ∧
    (∀ p', pcomm p p' → LPtau_case (LPrel (pred n)) W1 Σ T p') ∧
    (∀ cd p', proc_step p (PSess (SLink cd)) p' → Plink_case X W1 Σ T cd p') ∧
    (∀ σ p', proc_step p (PSess σ) p' → LPobl LVrel LPrel (S n) W1 Σ T p σ p').

Lemma Pbody_LPstep n VT T (X : world → senv → proc → Prop)
    (Y : world → senv → ty → proc → Prop) W Σ p :
  (∀ W Θ v, VT W Θ v → LVrel (S n) W Θ T v) →
  (∀ W Σ p, X W Σ p → Y W Σ T p) →
  Pbody (llevels (S n)) (S n) VT T X W Σ p → LPstep Y n W Σ T p.
Proof.
  intros HV HX H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [| done | | | | ].
  - intros Hirr. destruct (Hs Hirr) as (v & E & ? & ? & ? & ?). exists v, E. split_and!; auto.
  - intros p' Hst Hd L. destruct (Ha p' Hst Hd L) as (N & W' & ? & ? & ?). exists N, W'. split_and!; auto.
  - intros p' Hst. eapply LPtau_case_mono; [|by apply Hc].
    intros ? ? ? Hx. apply (lvP_llevels (S n)) in Hx; [done|simpl; lia].
  - intros cd p' Hst. eapply Plink_case_mono; [|by apply Hl]. auto.
  - intros σ p' Hst. eapply LPobl_mono; [..|exact (Hσ σ p' Hst)].
    + intros j Hj ? ? ? ?. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvP_llevels. simpl in Hj. lia.
Qed.

Lemma LPstep_Pbody n VT T (X : world → senv → proc → Prop)
    (Y : world → senv → ty → proc → Prop) W Σ p :
  (∀ W Θ v, LVrel (S n) W Θ T v → VT W Θ v) →
  (∀ W Σ p, Y W Σ T p → X W Σ p) →
  LPstep Y n W Σ T p → Pbody (llevels (S n)) (S n) VT T X W Σ p.
Proof.
  intros HV HX H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [| done | | | | ].
  - intros Hirr. destruct (Hs Hirr) as (v & E & ? & ? & ? & ?). exists v, E. split_and!; auto.
  - intros p' Hst Hd L. destruct (Ha p' Hst Hd L) as (N & W' & ? & ? & ?). exists N, W'. split_and!; auto.
  - intros p' Hst. eapply LPtau_case_mono; [|by apply Hc].
    intros ? ? ? Hx. apply (lvP_llevels (S n)); [simpl; lia|done].
  - intros cd p' Hst. eapply Plink_case_mono; [|by apply Hl]. auto.
  - intros σ p' Hst. eapply LPobl_mono; [..|exact (Hσ σ p' Hst)].
    + intros j Hj ? ? ? ?. symmetry. apply lvV_llevels. simpl in Hj. lia.
    + intros j Hj ? ? ? ?. apply lvP_llevels. simpl in Hj. lia.
Qed.

Lemma LPrel_S_iff n W Σ T p : LPrel (S n) W Σ T p ↔ LPstep (LPrel (S n)) n W Σ T p.
Proof.
  rewrite LPrel_S_eq. split.
  - intros H%Pind_inv. eapply Pbody_LPstep; [..|exact H].
    + intros. by apply LVrel_eq.
    + intros. by apply LPrel_S_eq.
  - intros H. constructor. eapply LPstep_Pbody; [..|exact H].
    + intros. by apply LVrel_eq.
    + intros. by apply LPrel_S_eq.
Qed.

Lemma LPrel_S_ind n (Φ : world → senv → ty → proc → Prop) :
  (∀ W Σ T p, LPstep (λ W Σ T p, LPrel (S n) W Σ T p ∧ Φ W Σ T p) n W Σ T p → Φ W Σ T p) →
  ∀ W Σ T p, LPrel (S n) W Σ T p → Φ W Σ T p.
Proof.
  intros Hind W Σ T p HP. apply LPrel_S_eq in HP.
  induction HP as [W Σ p H] using Pind_ind'.
  apply Hind. eapply Pbody_LPstep; [..|exact H].
  - intros. by apply LVrel_eq.
  - intros W' Σ' p' [H1 H2]. split; [by apply LPrel_S_eq|done].
Qed.

(** ** Downward closure *)

Lemma LVrel_down n m W Θ T v : m ≤ n → LVrel n W Θ T v → LVrel m W Θ T v.
Proof.
  intros Hmn. destruct (decide (m = n)) as [->|Hne]; [done|].
  rewrite !LVrel_eq. unfold lVtop.
  assert (∀ k W Θ T v, tsize T < k →
            LVdef (llevels n) n k W Θ T v → LVdef (llevels m) m k W Θ T v) as Hk.
  { induction k as [|k IH]; intros W0 Θ0 T0 v0 Hk H; [done|].
    destruct T0 as [|ub lb T1 U|T1 U|T1 U|mm kk C T1|s x|lb mm C T1]; cbn [tsize] in Hk.
    - done.
    - apply LVdef_S_lolli in H. apply LVdef_S_lolli.
      destruct H as [(eb & -> & Hfc & Hlb & H)|Hkc]; [left|by right].
      exists eb. split_and!; [done..|]. intros W' j Θ' Θ'' w F HW Hj Hc Hub.
      split.
      + intros Hjm HV.
        apply (lvE_llevels m); [done|]. apply (lvE_llevels n); [lia|].
        apply (H W' j Θ' Θ'' w F HW ltac:(lia) Hc Hub); [lia|].
        apply (lvV_llevels n); [lia|]. by apply (lvV_llevels m) in HV.
      + intros -> HV. destruct (H W' m Θ' Θ'' w F HW ltac:(lia) Hc Hub) as [K1 _].
        assert (LVrel m W' Θ' T1 w) as HV1.
        { apply LVrel_eq. unfold lVtop. eapply LVdef_fuel_l; [exact HV|..]; lia. }
        specialize (K1 ltac:(lia) (proj2 (lvV_llevels n m _ _ _ _ ltac:(lia)) HV1)).
        apply (lvE_llevels n) in K1; [|lia]. apply LErel_eq in K1.
        eapply Etop_VT_iff; [|exact K1]. intros. unfold lVtop. apply LVdef_fuel; lia.
    - apply LVdef_S_prod in H as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2). apply LVdef_S_prod.
      exists v1, v2, Θ1, Θ2. split_and!; [done|done|apply IH; [lia|done]|apply IH; [lia|done]].
    - apply LVdef_S_sum in H. apply LVdef_S_sum.
      destruct H as [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists v'; split; [done|apply IH; [lia|done]|done|apply IH; [lia|done]].
    - apply LVdef_S_box in H as (-> & eb & -> & Hfc & H). apply LVdef_S_box.
      split; [done|]. exists eb. split_and!; [done..|]. intros W' xs ss ? ? ? ? ? ?.
      apply IH; [unfold ty_inst; rewrite tsize_sinst, tsize_pinst; lia|]. auto.
    - done.
    - apply LVdef_S_ex in H as (Hlb & xs & ? & ? & ? & H). apply LVdef_S_ex.
      split; [done|]. exists xs. split_and!; [done..|].
      apply IH; [unfold ty_inst; rewrite tsize_pinst; lia|done]. }
  apply Hk. lia.
Qed.

Lemma LEobl_lower Vl El n m W Θ T F σ e' :
  m ≤ n →
  (∀ W Θ T v, Vl (pred n) W Θ T v → Vl (pred m) W Θ T v) →
  (∀ W Θ T F, El (pred n) W Θ T F e' → El (pred m) W Θ T F e') →
  LEobl Vl El n W Θ T F σ e' → LEobl Vl El m W Θ T F σ e'.
Proof.
  intros Hmn HV HE. destruct σ as [c w|c w|c|cd|c b|c b]; cbn [LEobl].
  - intros (Θ1 & mm & U & s & k & Hhd & H). exists Θ1, mm, U, s, k. split; [done|].
    intros W' j Θ2 Θ1c Θ' HW Hj. apply H; [done|lia].
  - intros (Θr&Θ1&Θ2&mm&U&s&k&Θ'&?&?&Hp&?&HX). exists Θr, Θ1, Θ2, mm, U, s, k, Θ'.
    split_and!; auto.
  - intros (Θ1&k&?&HX). exists Θ1, k. auto.
  - done.
  - intros (Θr&s1&s2&k&Θ'&?&?&HX). exists Θr, s1, s2, k, Θ'. split_and!; auto.
  - intros (Θr&s1&s2&k&Θ'&?&?&HX). exists Θr, s1, s2, k, Θ'. split_and!; auto.
Qed.

Lemma Psend_case_mono (V1 V2 : world → tenv → ty → expr → Prop) (X Y : world → senv → ty → proc → Prop)
    W Σ T p c w p' :
  (∀ W Θ T v, V1 W Θ T v → V2 W Θ T v) → (∀ W Σ T, X W Σ T p' → Y W Σ T p') →
  Psend_case V1 X W Σ T p c w p' → Psend_case V2 Y W Σ T p c w p'.
Proof.
  intros HV HX (Σ0&Σv&m&U&s&k&Σe&Θe&?&?&?&?&?&?&?&Hp&HP).
  exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; auto.
Qed.

Lemma LPobl_lower Vl Pl n m W Σ T p σ p' :
  m ≤ n →
  (∀ W Θ T v, Vl (pred n) W Θ T v → Vl (pred m) W Θ T v) →
  (∀ W Σ T, Pl (pred n) W Σ T p' → Pl (pred m) W Σ T p') →
  LPobl Vl Pl n W Σ T p σ p' → LPobl Vl Pl m W Σ T p σ p'.
Proof.
  intros Hmn HV HP. destruct σ as [c w|c w|c|cd|c b|c b]; cbn [LPobl].
  - intros (Σ1 & mm & U & s & k & Hhd & Hc & H). exists Σ1, mm, U, s, k.
    split_and!; [done|done|]. intros W' j Θ2 HW Hj. apply H; [done|lia].
  - by apply Psend_case_mono.
  - intros (Σ1&k&?&?&HX). exists Σ1, k. split_and!; auto.
  - done.
  - intros (Σ1&s1&s2&k&?&?&HX). exists Σ1, s1, s2, k. split_and!; auto.
  - intros (Σ1&s1&s2&k&?&?&HX). exists Σ1, s1, s2, k. split_and!; auto.
Qed.

Lemma LErel_down n : ∀ m W Θ T F e, m ≤ n → LErel n W Θ T F e → LErel m W Θ T F e.
Proof.
  induction n as [n IHn] using lt_wf_ind. intros m W Θ T F e Hmn HE.
  destruct m as [|m']; [apply LErel_0|].
  destruct n as [|n']; [lia|].
  destruct (decide (m' = n')) as [->|Hne]; [done|].
  revert W Θ T F e HE. apply (LErel_S_ind n'). intros W Θ T F e H.
  apply LErel_S_iff. intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split_and!; [| done | | | | | ].
  - intros Hirr. eapply LVrel_down; [|by apply Hs]. lia.
  - intros e' Hst. by apply (Hb e' Hst).
  - intros c e' Hst Hc L. destruct (Hn c e' Hst Hc L) as (a & s & s' & W' & ? & ? & _ & HX).
    exists a, s, s', W'. by split_and!.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & _ & HX).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |done].
    destruct Hv as [(eb & -> & ? & ? & Hv)|Hk]; [left|by right]. exists eb.
    split_and!; [done..|]. intros W' j Θ' Θ'' w' F' HW Hj Hc Hub. split.
    + intros Hjm HV. destruct (Hv W' j Θ' Θ'' w' F') as [K1 _]; [done|lia|done|done|].
      apply K1; [lia|done].
    + intros -> -> ->. destruct (Hv W' (S m') ∅ Θ'' EUnit F') as [K1 _]; [done|lia|done|done|].
      apply K1; [lia|]. by apply LVrel_unit_iff.
  - intros σ e' Hst. eapply LEobl_lower; [..|exact (Hσ σ e' Hst)]; [lia| |].
    + intros. eapply LVrel_down; [|done]. simpl. lia.
    + intros ? ? ? ? Hx. apply (IHn n'); [lia|simpl; lia|exact Hx].
  - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)]. by intros ? [_ ?].
Qed.

Lemma LPrel_down n : ∀ m W Σ T p, m ≤ n → LPrel n W Σ T p → LPrel m W Σ T p.
Proof.
  induction n as [n IHn] using lt_wf_ind. intros m W Σ T p Hmn HP.
  destruct m as [|m']; [apply LPrel_0|].
  destruct n as [|n']; [lia|].
  destruct (decide (m' = n')) as [->|Hne]; [done|].
  revert W Σ T p HP. apply (LPrel_S_ind n'). intros W Σ T p H.
  apply LPrel_S_iff. intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [| done | | | | ].
  - intros Hirr. destruct (Hs Hirr) as (v & E & ? & ? & HV & ?). exists v, E.
    split_and!; [done|done| |done]. eapply LVrel_down; [|exact HV]. lia.
  - intros p' Hst Hd L. destruct (Ha p' Hst Hd L) as (N & W' & ? & ? & _ & HX). eauto.
  - intros p' Hst. eapply LPtau_case_mono; [|by apply Hc].
    intros ? ? ? Hx. apply (IHn (pred n')); [lia|lia|exact Hx].
  - intros cd p' Hst. eapply Plink_case_mono; [|by apply Hl]. by intros ? [_ ?].
  - intros σ p' Hst. eapply LPobl_lower; [..|exact (Hσ σ p' Hst)]; [lia| |].
    + intros. eapply LVrel_down; [|done]. simpl. lia.
    + intros ? ? ? Hx. apply (IHn n'); [lia|simpl; lia|exact Hx].
Qed.

(** ** Values and monotonicity of V in the world *)

Lemma LVdef_val below n k W Θ T v : LVdef below n k W Θ T v → is_val v.
Proof.
  revert W Θ T v. induction k as [|k IH]; intros W Θ T v H; [done|].
  destruct T as [|ub lb T1 U|T1 U|T1 U|m kk C T1|s x|lb m C T1].
  - by destruct H as [_ ->].
  - apply LVdef_S_lolli in H. by destruct H as [(eb & -> & _)|(kc & T0 & -> & _)].
  - apply LVdef_S_prod in H as (v1 & v2 & Θ1 & Θ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - apply LVdef_S_sum in H as [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - apply LVdef_S_box in H as (_ & eb & -> & _). done.
  - by destruct H as (c & s0 & kk & -> & _).
  - apply LVdef_S_ex in H as (_ & xs & _ & _ & _ & H). eauto.
Qed.

Lemma LVrel_val n W Θ T v : LVrel n W Θ T v → is_val v.
Proof. rewrite LVrel_eq. apply LVdef_val. Qed.

Lemma LVdef_mono below n k W W' Θ T v :
  wext W W' → LVdef below n k W Θ T v → LVdef below n k W' Θ T v.
Proof.
  intros HWW'. revert W' HWW' Θ T v. induction k as [|k IH]; intros W' HWW' Θ T v H; [done|].
  destruct T as [|ub lb T1 U|T1 U|T1 U|m kk C T1|s x|lb m C T1].
  - done.
  - apply LVdef_S_lolli in H. apply LVdef_S_lolli.
    destruct H as [(eb & -> & Hfc & Hlb & H)|(kc & T0 & -> & -> & Hk & Ht)].
    + left. exists eb. split_and!; [done|done|by eapply lb_below_mono|].
      intros W'' j Θ' Θ'' w F HW Hj Hc Hub. apply H; [by eapply wext_trans|done..].
    + right. exists kc, T0. destruct HWW' as (Hn & He & Hl & _). split_and!; [done|done| |].
      * eapply konst_ty_mono; [| | |exact Hk]; auto. unfold pt_known. intros x Hx. by apply Hn.
      * by eapply teqW_mono.
  - apply LVdef_S_prod in H as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2). apply LVdef_S_prod.
    exists v1, v2, Θ1, Θ2. split_and!; [done| |by apply IH|by apply IH].
    eapply tenv_comp_mono; [|exact Hc]. by destruct HWW' as (_ & ? & _).
  - apply LVdef_S_sum in H. apply LVdef_S_sum.
    destruct H as [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists v'; split; auto.
  - apply LVdef_S_box in H as (-> & eb & -> & Hfc & H). apply LVdef_S_box.
    split; [done|]. exists eb. split_and!; [done|done|].
    intros W'' xs ss HW. apply H. by eapply wext_trans.
  - destruct H as (c & s0 & kk & -> & -> & Hs & Hx). exists c, s0, kk. split_and!; [done..|].
    destruct HWW' as (_ & He & _). auto.
  - apply LVdef_S_ex in H as (Hlb & xs & Hxs & HK & HC & H). apply LVdef_S_ex.
    split; [by eapply lbx_below_mono|]. exists xs. split_and!; [done| | |by apply IH].
    + eapply Forall_impl; [exact HK|]. destruct HWW' as (Hn & _). unfold pt_known.
      intros x Hx. by apply Hn.
    + eapply bcs_hold_mono; [| |exact HC]; by destruct HWW' as (_ & ? & ? & _).
Qed.

Lemma LVrel_mono n W W' Θ T v : wext W W' → LVrel n W Θ T v → LVrel n W' Θ T v.
Proof. rewrite !LVrel_eq. apply LVdef_mono. Qed.

Lemma LVrel_mono_r n W W' Θ T v : wext_r W W' → LVrel n W Θ T v → LVrel n W' Θ T v.
Proof. intros [->|HW]; [done|]. by apply LVrel_mono. Qed.

Lemma LErel_mono n W W' Θ T F e : wext_r W W' → LErel n W Θ T F e → LErel n W' Θ T F e.
Proof.
  intros HW. rewrite !LErel_eq. destruct n; [done|]. by apply Eind_mono_world.
Qed.

Lemma LPrel_mono n W W' Σ T p : wext_r W W' → LPrel n W Σ T p → LPrel n W' Σ T p.
Proof.
  intros HW. destruct n as [|n]; [intros; apply LPrel_0|]. rewrite !LPrel_S_eq.
  by apply Pind_mono_world.
Qed.

(** E at level n holds the values of V at level n. *)
Lemma LVrel_LErel n W Θ T F v : LVrel n W Θ T v → LErel n W Θ T F v.
Proof.
  intros HV. assert (is_val v) as Hv by by eapply LVrel_val.
  destruct n as [|n']; [apply LErel_0|].
  apply LErel_S_iff. intros W1 HW1. split_and!.
  - intros _. by eapply LVrel_mono_r.
  - intros Hirr. exfalso. by apply Hirr, val_irred.
  - intros e' Hst. exfalso. eauto using val_no_tstep.
  - intros c e' Hst. exfalso. eauto using val_no_tstep.
  - intros w e' Hst. exfalso. eauto using val_no_tstep.
  - intros σ e' Hst. exfalso. eauto using val_no_tstep.
  - intros cd e' Hst. exfalso. eauto using val_no_tstep.
Qed.
