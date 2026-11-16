(** * The constants in the live relation (TermRules.v)

    The application of every constant but force, at the live costs.
    Every proof first moves to a later world W1 ([lmove]), because the
    premises of E hold in every later world, and then reads the step at
    W1 alone ([LEnow]). Channel steps continue one level down. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveConv.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

(** One unfolding of E at level S n in one world. *)
Definition LEcase (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point)
    (α : tlabel) (e' : expr) : Prop :=
  match α with
  | LBeta => LErel (S n) W Θ T F e'
  | LNew c x => c ∉ dom Θ →
      pt_known W x ∧ ∃ s s',
        sdual s s' ∧
        LErel (S n) W (<[c := Both (s, x) (s', pt_dual x)]> Θ) T F e'
  | LSpawn w => ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
      LVrel (S n) W Θ1 (TLolli ub lb TUnit TUnit) w ∧ LErel (S n) W Θ2 T F e'
  | LSess (SLink cd) => LElink (λ W Θ F e, LErel (S n) W Θ T F e) W Θ F cd e'
  | LSess σ => LEobl LVrel LErel (S n) W Θ T F σ e'
  end.

Definition LEnow (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point) (e : expr) : Prop :=
  (irred e → LVrel (S n) W Θ T e) ∧ (¬ irred e → ready_t W Θ F e) ∧
  ∀ α e', tstep e α e' → LEcase n W Θ T F α e'.

Lemma LErel_intro n W Θ T F e :
  (∀ W1, wext_r W W1 → match n with 0 => True | S n' => LEnow n' W1 Θ T F e end) →
  LErel n W Θ T F e.
Proof.
  destruct n as [|n']; intros H; [apply LErel_0|]. apply LErel_S_iff. intros W1 HW1.
  destruct (H W1 HW1) as (Hs & Hr & Hst). split_and!; [done|done| | | | |].
  - intros e' He. exact (Hst _ _ He).
  - intros c x e' He. exact (Hst _ _ He).
  - intros w e' He. destruct (Hst _ _ He) as (Θ1 & Θ2 & ub & lb & ? & ? & ?).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |done]. by apply Vspawn_LVrel.
  - intros σ e' He. destruct σ as [| | |cd| |]; try exact (Hst _ _ He). done.
  - intros cd e' He. exact (Hst _ _ He).
Qed.

Lemma ub_below_mono_r W W1 ub F : wext_r W W1 → ub_below W ub F → ub_below W1 ub F.
Proof. intros [->|HW] H; [done|by eapply ub_below_mono]. Qed.

Lemma LVrel_teq n W Θ T T' v : world_wf W → teq T T' → LVrel n W Θ T v → LVrel n W Θ T' v.
Proof. intros HW Ht. apply LVrel_tconv; [done|by apply teq_teqW]. Qed.

Lemma LVrel_box_empty n W Θ m k C T v : LVrel n W Θ (TBox m k C T) v → Θ = ∅.
Proof. intros [-> _]%LVrel_box_iff. done. Qed.

Lemma LVrel_konst_inv n W Θ ub lb T U k :
  LVrel n W Θ (TLolli ub lb T U) (Konst k) →
  ∃ ub0 lb0 A B, konst_ty (w_eq W) (w_lt W) (pt_known W) k (TLolli ub0 lb0 A B) ∧
    opt_rel (pteqW W) ub0 ub ∧ opt_rel (pteqW W) lb0 lb ∧
    teqW W A T ∧ teqW W B U ∧ Θ = ∅.
Proof.
  intros HV. apply LVrel_lolli_iff in HV
    as [(eb & ? & _)|(k' & T0 & Hk' & -> & Hk & Ht)]; [done|simplify_eq].
  destruct T0; try done. destruct Ht as (? & ? & Ht1 & Ht2). eauto 10.
Qed.

(** Move a constant's application to a later world W1, renamed W. *)
Ltac lmove :=
  match goal with
  | HW : strict ?W, HV1 : LVrel _ ?W _ _ _, HV2 : LVrel _ ?W _ _ _ |- LErel _ ?W _ _ _ _ =>
    apply LErel_intro;
    let W1 := fresh "W1" in let HW1 := fresh "HW1" in intros W1 HW1;
    let HV1' := fresh in let HV2' := fresh in let HW' := fresh in
    pose proof (LVrel_mono_r _ _ _ _ _ _ HW1 HV1) as HV1';
    pose proof (LVrel_mono_r _ _ _ _ _ _ HW1 HV2) as HV2';
    pose proof (wext_r_strict _ _ HW HW1) as HW';
    try (match goal with Hub0 : ub_below W _ _ |- _ =>
           let Hu := fresh in pose proof (ub_below_mono_r _ _ _ _ HW1 Hub0) as Hu;
           clear Hub0; rename Hu into Hub0 end);
    clear HV1 HV2 HW HW1; clear W; rename W1 into W;
    rename HV1' into HV1; rename HV2' into HV2; rename HW' into HW
  end.

Lemma LVrel_heads_above n W Θ T v :
  world_wf W → hbot T = false → LVrel n W Θ T v → heads_above W (heads T) Θ.
Proof.
  intros HW. revert Θ v.
  induction T as [|ub lb T1 IH1 T2 IH2|T1 IH1 T2 IH2|T1 IH1 T2 IH2|m kk C T1 IH1|s x|lb m C T1 IH1|x];
    intros Θ v Hb HV; simpl; simpl in Hb; try apply orb_false_iff in Hb as [Hb1 Hb2].
  - apply LVrel_unit_iff in HV as [-> _]. apply heads_above_empty.
  - apply LVrel_lolli_iff in HV as [(eb & _ & _ & Hlb & _)|(k & T0 & _ & -> & _)];
      [|apply heads_above_empty].
    intros k e He. destruct lb as [l|]; simpl in Hlb.
    + exists l. split; [set_solver|]. apply Hlb. apply elem_of_tenv_heads_entry. eauto.
    + exfalso. assert (pt_dual e.2 ∈ tenv_heads Θ) as Hin by (apply elem_of_tenv_heads_entry; eauto).
      rewrite Hlb in Hin. set_solver.
  - apply LVrel_prod_iff in HV as (v1 & v2 & Θ1 & Θ2 & _ & Hc & H1 & H2).
    eapply heads_above_comp; [exact Hc|eauto|eauto].
  - apply LVrel_sum_iff in HV as [(v' & _ & H)|(v' & _ & H)].
    + eapply heads_above_sub; [|by eapply IH1]. set_solver.
    + eapply heads_above_sub; [|by eapply IH2]. set_solver.
  - apply LVrel_box_empty in HV as ->. apply heads_above_empty.
  - apply LVrel_sess_iff in HV as (c & bb & s0 & k & _ & -> & _ & Hk & _).
    intros [c' b] e He. unfold tenv_entry in He. simpl in He.
    destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_singleton_eq in He. destruct b; simplify_eq.
      exists (pt_dual x). split; [set_solver|]. left. apply (wf_eq_dual _ HW). by apply (wf_eq_sym _ HW).
    + rewrite lookup_singleton_ne in He by done. done.
  - apply LVrel_ex_iff in HV as [Hlb _].
    intros k e He. destruct lb as [| |l]; simpl in Hlb, Hb; [|done|].
    + exfalso. assert (pt_dual e.2 ∈ tenv_heads Θ) as Hin by (apply elem_of_tenv_heads_entry; eauto).
      rewrite (proj1 Hlb) in Hin. set_solver.
    + exists l. split; [set_solver|]. apply Hlb. apply elem_of_tenv_heads_entry. eauto.
  - apply LVrel_pt_iff in HV as [-> _]. apply heads_above_empty.
Qed.

Lemma Lkonst_app_inv n W Θ1 Θ2 ub lb T U k v2 :
  world_wf W → LVrel n W Θ1 (TLolli ub lb T U) (Konst k) → LVrel n W Θ2 T v2 →
  Θ1 = ∅ ∧ ∃ ub0 lb0 A B, konst_ty (w_eq W) (w_lt W) (pt_known W) k (TLolli ub0 lb0 A B) ∧
    opt_rel (pteqW W) ub0 ub ∧ teqW W B U ∧ LVrel n W Θ2 A v2.
Proof.
  intros HW HV1 HV2.
  destruct (LVrel_konst_inv _ _ _ _ _ _ _ _ HV1) as (ub0 & lb0 & A & B & Hk & Hub & _ & HA & HB & ->).
  split; [done|]. exists ub0, lb0, A, B. split_and!; [done|done|done|].
  eapply LVrel_tconv; [done| |exact HV2]. by apply teqW_sym.
Qed.

Lemma LErel_app_new n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) ENew → LVrel n W Θ T v2 →
  LErel n W Θ U F (App ENew v2).
Proof.
  intros HW HV1 HV2. lmove.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| S x Hx| |]; subst; [inversion Hsig|].
  (* new@x (§16.1): the argument is the point value x, the label carries x *)
  apply LVrel_pt_iff in HV as (-> & -> & Hkx). destruct n as [|n']; [exact I|].
  assert (tstep (App ENew (EPt x)) (LNew "c" x)
            (Pair (Chan "c" (pt_pol x)) (Chan "c" (negb (pt_pol x))))) as Hst0
    by apply TStepHead, HeadNew.
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst0).
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | |c x0| | | | | | | | | | | | |]; subst. simpl. intros _.
    split; [done|]. exists S, (dual S). split_and!.
    + apply sdual_dual.
    + apply LVrel_LErel. eapply LVrel_tconv; [exact (proj1 HW)|exact HB|].
      apply LVrel_prod_iff. exists (Chan c (pt_pol x)), (Chan c (negb (pt_pol x))), {[c := One (S, x)]},
        {[c := One (dual S, pt_dual x)]}. split_and!.
      * done.
      * split.
        -- intros c'. rewrite insert_empty. destruct (decide (c' = c)) as [->|Hne].
           ++ rewrite !lookup_singleton_eq. constructor.
           ++ rewrite !lookup_singleton_ne by done. constructor.
        -- intros c' e1 e2 H1 H2. destruct (decide (c' = c)) as [->|Hne];
             [|by rewrite lookup_singleton_ne in H1].
           rewrite lookup_singleton_eq in H1, H2. simplify_eq. simpl.
           rewrite pt_dual_dual. split; [done|apply sdual_dual].
      * apply LVrel_sess_iff. exists c, (pt_pol x), S, x. split_and!; [done|done|apply seq_refl|done|done].
      * apply LVrel_sess_iff. exists c, (negb (pt_pol x)), (dual S), (pt_dual x).
        split_and!; [done|done|apply seq_refl|done|done].
Qed.

(** x[i] and x+1 on point values (§16.1): one β step each. *)
Lemma LErel_app_pay n W Θ ub lb T U F i v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) (Konst (KPay i)) → LVrel n W Θ T v2 →
  LErel n W Θ U F (App (Konst (KPay i)) v2).
Proof.
  intros HW HV1 HV2.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| |i0 x Hx|]; subst; [inversion Hsig|].
  apply LVrel_pt_iff in HV as (-> & -> & Hkx).
  eapply LErel_det_beta; [by apply TStepHead, HeadPay| |].
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply LVrel_LErel. eapply LVrel_tconv; [exact (proj1 HW)|exact HB|].
    apply LVrel_pt_iff. split_and!; [done|done|]. exact Hx.
Qed.

Lemma LErel_app_succ n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) (Konst KSucc) → LVrel n W Θ T v2 →
  LErel n W Θ U F (App (Konst KSucc) v2).
Proof.
  intros HW HV1 HV2.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| | |x Hx]; subst; [inversion Hsig|].
  apply LVrel_pt_iff in HV as (-> & -> & Hkx).
  eapply LErel_det_beta; [by apply TStepHead, HeadSucc| |].
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply LVrel_LErel. eapply LVrel_tconv; [exact (proj1 HW)|exact HB|].
    apply LVrel_pt_iff. split_and!; [done|done|]. exact Hx.
Qed.

Lemma LErel_app_spawn n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) ESpawn → LVrel n W Θ T v2 →
  LErel n W Θ U F (App ESpawn v2).
Proof.
  intros HW HV1 HV2. lmove.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [ub1 lb1| | | | | | | |]; subst.
  pose proof (LVrel_val _ _ _ _ _ HV) as Hv.
  destruct n as [|n']; [exact I|].
  assert (tstep (App ESpawn v2) (LSpawn v2) EUnit) as Hst0 by by apply TStepHead, HeadSpawn.
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst0).
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst; subst. simpl.
    exists Θ, ∅, ub1, lb1. split_and!; [apply tenv_comp_empty_r|done|].
    apply LVrel_LErel. eapply LVrel_tconv; [apply HW|exact HB|]. by apply LVrel_unit_iff.
Qed.

(** Readiness and future of a term holding one end, which it offers. *)








Lemma LErel_app_recv n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) ERecv → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App ERecv v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [|m T0 S x| | | | | | |]; subst.
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply LVrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_rcv_inv _ _ _ _ _ Hs0 (unfoldS_rcv _ _ _))
    as (U0 & s' & Hu0 & HU0 & Hs').
  destruct n as [|n']; [exact I|].
  assert (∀ w, is_val w → tstep (App ERecv (Chan c (pt_pol k)))
            (LSess (SRecv (c, pt_pol k) w)) (Pair w (Chan c (pt_pol k))))
    as Hst0 by (intros; by apply TStepHead, HeadRecv).
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ (Hst0 EUnit I)).
  - intros _. apply ready_single.
    + exists (SRecv (c, pt_pol k) EUnit), (Pair EUnit (Chan c (pt_pol k))). split; [by apply Hst0|].
      split; [done|]. exists (s0, k), m, U0, s'. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | | | | | |c' β' w Hw| | | | | | | | |]; subst. simpl.
    exists ∅, m, U0, s', k. split.
    { split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty]. }
    intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hcomp HVw.
    apply tenv_ext_empty in Hext as ->.
    pose proof (wext_wf _ _ HW') as HWf'.
    apply LVrel_LErel. eapply LVrel_tconv; [done|eapply teqW_mono; [apply HW'|exact HB]|].
    apply LVrel_prod_iff. exists w, (Chan c (pt_pol k)), Θ2, {[c := One (s', pt_shift 1 k)]}. split_and!.
    + done.
    + apply comp_comm; [exact (wf_rdsym _ HWf')|exact Hcomp].
    + eapply LVrel_teq; [done|apply teq_ty_inst, HU0|].
      eapply LVrel_payload; [done| |exact HVw]. by apply (proj1 (proj2 HW')).
    + apply LVrel_sess_iff. exists c, (pt_pol k), s', (pt_shift 1 k). split_and!; [done|done|done| |done].
      apply (wf_eq_shift _ HWf'). by apply (proj1 (proj2 HW')).
Qed.

Lemma LErel_app_close n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) EClos → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App EClos v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [| | |x| | | | |]; subst.
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply LVrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  pose proof (seq_end_inv _ _ Hs0 eq_refl) as Hu0.
  destruct n as [|n']; [exact I|].
  assert (tstep (App EClos (Chan c (pt_pol k))) (LSess (SClos (c, pt_pol k))) EUnit) as Hst0
    by apply TStepHead, HeadClos.
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _. apply ready_single.
    + exists (SClos (c, pt_pol k)), EUnit. split; [done|].
      split; [done|]. exists (s0, k). split_and!; [|done|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst; subst. simpl.
    exists ∅, k. split.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + apply LVrel_LErel. eapply LVrel_tconv; [done|exact HB|]. by apply LVrel_unit_iff.
Qed.

(** select₁ and select₂ (K4): a giving step like send, at cost 0. *)
Lemma LErel_app_sel n W Θ ub lb T U F v2 (b : bool) :
  strict W → LVrel n W ∅ (TLolli ub lb T U) (Konst (ksel b)) → LVrel n W Θ T v2 →
  ub_below W ub F → LErel n W Θ U F (App (Konst (ksel b)) v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  assert (∃ S1 S2 x, ub0 = Some x ∧ A = TSess (SPlus S1 S2) x ∧
            B = TSess (sbranch b S1 S2) (sel_pt x b)) as (S1 & S2 & x & -> & -> & ->).
  { destruct b; simpl in Hk; inversion Hk as [kq Tq Gq xq Hsig| | |]; subst; inversion Hsig; subst; eauto 10. }
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply LVrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_plus_inv _ _ _ _ Hs0 (unfoldS_plus _ _)) as (s1 & s2 & Hu0 & Hs1 & Hs2).
  destruct n as [|n']; [exact I|].
  assert (tstep (App (Konst (ksel b)) (Chan c (pt_pol k))) (LSess (SSel (c, pt_pol k) b))
            (Chan c false)) as Hst0
    by (destruct b; apply TStepHead; constructor).
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _. apply ready_single.
    + exists (SSel (c, pt_pol k) b), (Chan c false). split; [done|]. split; [done|].
      exists (s0, k), s1, s2. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|by destruct b|done].
    assert (α = LSess (SSel (c, pt_pol k) b) ∧ e' = Chan c false) as [-> ->]
      by (destruct b; inversion Hst; subst; done).
    simpl. exists ∅, s1, s2, k, {[c := One (sbranch b s1 s2, sel_pt k b)]}. split_and!.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + left. split; [done|by rewrite insert_empty].
    + apply LVrel_LErel. eapply LVrel_tconv; [done|exact HB|].
      apply LVrel_sess_iff. exists c, false, (sbranch b s1 s2), (sel_pt k b).
      split_and!; [done|done|by destruct b|by apply (wf_eq_dual _ HWf), (wf_eq_payload _ HWf)|done].
Qed.

(** branch (K4): it waits like receive, at cost 1, and returns the
    channel in the injection of the branch taken. *)
Lemma LErel_app_bra n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) EBra → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App EBra v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  assert (∃ S1 S2 x, ub0 = Some x ∧ A = TSess (SWith S1 S2) x ∧
            B = TSum (TSess S1 (pt_payload x (bidx false))) (TSess S2 (pt_payload x (bidx true))))
    as (S1 & S2 & x & -> & -> & ->)
    by (inversion Hk as [kq Tq Gq xq Hsig| | |]; subst; inversion Hsig; subst; eauto 10).
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply LVrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_with_inv _ _ _ _ Hs0 (unfoldS_with _ _)) as (s1 & s2 & Hu0 & Hs1 & Hs2).
  destruct n as [|n']; [exact I|].
  assert (∀ b, tstep (App EBra (Chan c (pt_pol k))) (LSess (SBra (c, pt_pol k) b))
                 (inj_of b (Chan c true))) as Hst0
    by (intros; apply TStepHead, HeadBra).
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ (Hst0 false)).
  - intros _. apply ready_single.
    + exists (SBra (c, pt_pol k) false), (inj_of false (Chan c true)). split; [done|]. split; [done|].
      exists (s0, k), s1, s2. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | | | | | | | | | | |c' β' b'| | | |]; subst. simpl.
    exists ∅, s1, s2, k, {[c := One (sbranch b' s1 s2, pt_payload k (bidx b'))]}. split_and!.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + left. split; [done|by rewrite insert_empty].
    + apply LVrel_LErel. eapply LVrel_tconv; [done|eapply teqW_mono; [|exact HB]; done|].
      apply LVrel_sum_iff. destruct b'; [right|left]; eexists; (split; [done|]);
        apply LVrel_sess_iff; eexists _, true, _, (pt_payload k (bidx _));
        (split_and!; [done|done|done|by apply (wf_eq_payload _ HWf)|done]).
Qed.

(** Θ = Θ1, c : e as a composition with a singleton. *)


Lemma LErel_app_send n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) ESend → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App ESend v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig HG _| | |]; subst.
  inversion Hsig as [|m T0 S x Hpb| | | | | | |]; subst.
  assert (∀ h, h ∈ heads (payload_at m T0 x) → w_lt W x h) as Hpay
    by (intros h Hh; apply (HG (FLt x h)); by exists h).
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply LVrel_prod_iff in HV as (w & vc & Θw & Θc & -> & Hc & HVw & HVc).
  apply LVrel_sess_iff in HVc as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  pose proof (LVrel_val _ _ _ _ _ HVw) as Hw.
  destruct (seq_snd_inv _ _ _ _ _ Hs0 (unfoldS_snd _ _ _))
    as (U0 & s' & Hu0 & HU0 & Hs').
  pose proof (comp_single_ext _ _ _ _ _ Hc) as Hext.
  (* the payload's entries lie above x *)
  assert (∀ k' e', tenv_entry Θw k' = Some e' → w_lt W k (pt_dual e'.2)) as Habove.
  { intros k' e' He'.
    assert (hbot (payload_at m T0 k) = false) as Hpb' by (unfold payload_at, ty_inst; by rewrite hbot_pinst).
    destruct (LVrel_heads_above _ _ _ _ _ HWf Hpb' HVw _ _ He') as (h & Hh & Hle).
    eapply (wf_lt_eq _ HWf); [reflexivity|eapply lt_le_W; [done|by apply Hpay|exact Hle]|reflexivity]. }
  (* the key of the sending end *)
  assert (∃ kc, tenv_entry Θ kc = Some (s0, k) ∧ kc.1 = c ∧
            ∀ k' e', k' ≠ kc → tenv_entry Θ k' = Some e' → ∃ k'', tenv_entry Θw k'' = Some e')
    as (kc & Hkc & Hkc1 & Hrest).
  { assert (∀ c' b e', c' ≠ c → tenv_entry Θ (c', b) = Some e' → tenv_entry Θw (c', b) = Some e')
      as Hne.
    { intros c' b e' Hne He'. unfold tenv_entry in *. simpl in *.
      destruct Hext as [[_ ->]|(f & _ & [->| ->])]; by rewrite lookup_insert_ne in He'. }
    destruct Hext as [[H1 ->]|(f & H1 & [->| ->])].
    - exists (c, false). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [done|congruence].
      + exists (c', b). apply Hne; [done|]. done.
    - exists (c, false). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [|congruence]. injection He' as <-. exists (c, false).
        unfold tenv_entry. simpl. by rewrite H1.
      + exists (c', b). by apply Hne.
    - exists (c, true). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [congruence|]. injection He' as <-. exists (c, false).
        unfold tenv_entry. simpl. by rewrite H1.
      + exists (c', b). by apply Hne. }
  destruct n as [|n']; [exact I|].
  assert (tstep (App ESend (Pair w (Chan c (pt_pol k)))) (LSess (SSend (c, pt_pol k) w))
            (Chan c (pt_pol k))) as Hst0
    by by apply TStepHead, HeadSend.
  assert (offered_t Θ (App ESend (Pair w (Chan c (pt_pol k)))) kc) as Hoff.
  { exists (SSend (c, pt_pol k) w), (Chan c (pt_pol k)). split; [done|]. split; [done|].
    exists (s0, k), m, U0, s'. done. }
  (* only the sending end is offered: the other end of c, if Θw holds it, is dual *)
  assert (∀ k' e', offered_t Θ (App ESend (Pair w (Chan c (pt_pol k)))) k' → tenv_entry Θ k' = Some e' →
            e' = (s0, k)) as Honly.
  { intros k' e' (σ & t' & Hst & Hsel) He'.
    apply app_val_step in Hst; [|done|simpl; by apply andb_True].
    assert (σ = SSend (c, pt_pol k) w) as -> by (inversion Hst; done).
    destruct Hsel as (Hk1 & e'' & m' & T' & s'' & He'' & _ & Hu''). rewrite He' in He''.
    injection He'' as <-. destruct k' as [c' b]. simpl in Hk1. subst c'.
    assert (∀ f, Θw !! c = Some (One f) → unfoldS f.1 = SSeq (SSnd m' T') s'' → False) as Hno.
    { intros f Hf Hfu. destruct Hc as [_ Hd].
      destruct (Hd c f (s0, k) Hf (lookup_singleton_eq _ _)) as [_ Hdu].
      destruct (sdual_snd _ _ _ _ _ Hdu Hfu) as (U1 & r1 & Hr1). simpl in Hr1.
      by rewrite Hu0 in Hr1. }
    unfold tenv_entry in He'. simpl in He'.
    destruct Hext as [[H1 ->]|(f & H1 & [->| ->])]; rewrite lookup_insert_eq in He';
      destruct b; simplify_eq; try done; exfalso; by apply (Hno e'). }
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. split; [intros H; exfalso; exact (H _ Hoff)|].
    right. intros k0 e0 Hoff0 He0. rewrite (Honly k0 e0 Hoff0 He0). split.
    + intros k' e' He' Hn.
      destruct (decide (k' = kc)) as [->|Hne]; [by exfalso|].
      destruct (Hrest k' e' Hne He') as (k'' & Hk'').
      unfold entry_head. simpl. by apply (Habove k'').
    + intros y Hy. unfold entry_head. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|simpl; by apply andb_True].
    assert (α = LSess (SSend (c, pt_pol k) w) ∧ e' = Chan c (pt_pol k)) as [-> ->]
      by (inversion Hst; done). simpl.
    exists Θw, ∅, Θw, m, U0, s', k, {[c := One (s', pt_shift 1 k)]}. split_and!.
    + split; [by exists s0|done].
    + apply tenv_comp_empty_l. exact (wf_rdsym _ HWf).
    + eapply LVrel_payload; [done|reflexivity|].
      eapply LVrel_teq; [done|apply teq_ty_inst, teq_sym, HU0|]. eapply LVrel_down; [|exact HVw]. lia.
    + left. split; [done|by rewrite insert_empty].
    + apply LVrel_LErel. eapply LVrel_tconv; [done|exact HB|].
      apply LVrel_sess_iff. exists c, (pt_pol k), s', (pt_shift 1 k). split_and!; [done|done|done| |done].
      by apply (wf_eq_shift _ HWf).
Qed.

Lemma LErel_app_link n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) ELink → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App ELink v2).
Proof.
  intros HW HV1 HV2 Hub0. lmove. pose proof (proj1 HW) as HWf.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig HG _| | |]; subst.
  inversion Hsig as [| | | | | | |S x|]; subst.
  assert (w_eq W x (pt_dual (pt_dual x))) as Hxx' by (rewrite pt_dual_dual; apply (wf_eq_refl _ HWf)).

  apply LVrel_prod_iff in HV as (vc & vd & Θc & Θd & -> & Hc & HVc & HVd).
  apply LVrel_sess_iff in HVc as (c & bc & sc & kc & -> & -> & Hsc & Hkc & <-).
  apply LVrel_sess_iff in HVd as (d & bd & sd & kd & -> & -> & Hsd & Hkd & <-).
  set (cd := ({[(c, pt_pol kc); (d, pt_pol kd)]} : gset cend)).
  destruct n as [|n']; [exact I|].
  assert (tstep (App ELink (Pair (Chan c (pt_pol kc)) (Chan d (pt_pol kd)))) (LSess (SLink cd)) EUnit)
    as Hst0 by apply TStepHead, HeadLink.
  assert (∀ k', is_Some (tenv_entry Θ k') →
            offered_t Θ (App ELink (Pair (Chan c (pt_pol kc)) (Chan d (pt_pol kd)))) k')
    as Hoff.
  { intros k' [e' He']. exists (SLink cd), EUnit. split; [done|].
    exists e'. split; [done|].
    assert ((k'.1, pt_pol e'.2) ∈ tenv_ends Θ) as Hin
      by (apply elem_of_tenv_ends_entry; eauto).
    rewrite (tenv_join_ends _ _ _ (proj1 Hc)), !tenv_ends_singleton_one in Hin. exact Hin. }
  unfold LEnow. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. split.
    + intros H. exfalso. apply (H (c, false)), Hoff.
      destruct Hc as [Hj _]. specialize (Hj c). rewrite lookup_singleton_eq in Hj.
      unfold tenv_entry. simpl. inversion Hj; by eexists.
    + (* a link compares nothing (sharp edges 68) *)
      left. by exists cd, EUnit.
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    assert (α = LSess (SLink cd) ∧ e' = EUnit) as [-> ->] by (inversion Hst; done). simpl.
    exists c, d, ∅, {[d := One (sd, kd)]}, sc, sd, kc, kd. split_and!.
    + done.
    + left. split; [done|by rewrite insert_empty].
    + apply (comp_single_ext (w_eq W)). apply comp_comm; [exact (wf_rdsym _ HWf)|exact Hc].
    + apply sdual_seq_dual. eapply seq_trans; [exact Hsd|]. apply seq_dual, seq_sym, Hsc.
    + eapply (wf_eq_trans _ HWf); [exact Hkc|].
      eapply (wf_eq_trans _ HWf); [exact Hxx'|exact (wf_eq_dual _ HWf _ _ (wf_eq_sym _ HWf _ _ Hkd))].
    + apply LVrel_LErel. eapply LVrel_tconv; [done|exact HB|]. by apply LVrel_unit_iff.
Qed.

(** Every function value but force (sharp edges 51). *)
Lemma LErel_app_noforce n W Θ Θ1 Θ2 ub lb T U F v1 v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → v1 ≠ EForce →
  LVrel n W Θ1 (TLolli ub lb T U) v1 → LVrel n W Θ2 T v2 → ub_below W ub F →
  LErel n W Θ U F (App v1 v2).
Proof.
  intros HW Hc Hnf HV1 HV2 Hub.
  pose proof (wf_rdsym _ (proj1 HW)) as Hs.
  destruct (proj1 (LVrel_lolli_iff _ _ _ _ _ _ _ _) HV1) as [(eb & -> & _)|(k & T0 & -> & -> & _)].
  - by eapply LErel_app_lam.
  - apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
    destruct k; [eapply LErel_app_new|eapply LErel_app_spawn|eapply LErel_app_recv|eapply LErel_app_send
                |eapply LErel_app_close|eapply LErel_app_link|done
                |eapply (LErel_app_sel _ _ _ _ _ _ _ _ _ false)
                |eapply (LErel_app_sel _ _ _ _ _ _ _ _ _ true)|eapply LErel_app_bra
                |eapply LErel_app_pay|eapply LErel_app_succ]; eauto.
Qed.

