(** * P-Connect, the τ steps of the composite (stage S4)

    Every τ step of the composite is one of the cases of
    compat/ConnectSteps.v, compat/ConnectCross.v and compat/ConnectLink.v,
    or contradicts the clauses of a component. *)

From GV Require Export compat.ConnectCross compat.ConnectLink.
From GV Require Import fuel.FuelMono.

Section tau.
  Context (κ : ctable) (n : nat) (W1 : world) (T : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (CC : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Let HS := cc_HS CC. Let HT := cc_HT CC. Let Hc := cc_Hc CC.
  Let H1 := cc_H1 CC. Let H2 := cc_H2 CC. Let L := cc_L CC.
  Let X1P := cc_X1P CC. Let X2P := cc_X2P CC. Let HP1 := cc_HP1 CC. Let HP2 := cc_HP2 CC.
  Let G1 := cc_G1 CC. Let G2 := cc_G2 CC.
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma Hq1e M1 : soup M1 = q1.2 → erase (q1.1, M1) = q1.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q1. Qed.
  Local Lemma Hq2e M2 : soup M2 = q2.2 → erase (q2.1, M2) = q2.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q2. Qed.

  Local Lemma side (M1 M2 : gmap nat expr) i e : (M1 ∪ M2) !! i = Some e → M1 !! i = Some e ∨ M2 !! i = Some e.
  Proof. intros [H|[_ H]]%lookup_union_Some_raw; auto. Qed.

  (** Two threads of p1 close the two ends of a channel p1 does not
      restrict: both ends would be in Σ1 ∪ ΣC. *)
  Local Lemma close_same1 M1 i j o e e' f f' :
    soup M1 = q1.2 → M1 !! i = Some e → M1 !! j = Some f →
    tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose (edual o))) f' → ech o ∉ q1.1 → False.
  Proof.
    intros HM1 Hi Hj He Hf Hn. destruct H1 as (_ & _ & HP).
    destruct (Psteps_head _ _ _ _ _ _ _ _ _ _ HP (q1.1, M1) i (SClose o) (q1.1 ∖ ∅, <[i := e']> M1) o (Hq1e M1 HM1))
      as (S0 & x & La & _); [by eapply p_act_session; [eassumption|eassumption|simpl; cc_set_solver]|done|].
    destruct (Psteps_head _ _ _ _ _ _ _ _ _ _ HP (q1.1, M1) j (SClose (edual o)) (q1.1 ∖ ∅, <[j := f']> M1) (edual o) (Hq1e M1 HM1))
      as (S0' & x' & La' & _); [by eapply p_act_session; [eassumption|eassumption|simpl; rewrite ech_edual; cc_set_solver]|done|].
    apply (pfree_1C _ _ _ _ _ _ Hc o); by eapply elem_of_dom_2.
  Qed.

  Local Lemma close_same2 M2 i j o e e' f f' :
    soup M2 = q2.2 → M2 !! i = Some e → M2 !! j = Some f →
    tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose (edual o))) f' → ech o ∉ q2.1 → False.
  Proof.
    intros HM2 Hi Hj He Hf Hn. destruct H2 as (_ & _ & HP).
    destruct (Psteps_head _ _ _ _ _ _ _ _ _ _ HP (q2.1, M2) i (SClose o) (q2.1 ∖ ∅, <[i := e']> M2) o (Hq2e M2 HM2))
      as (S0 & x & La & _); [by eapply p_act_session; [eassumption|eassumption|simpl; cc_set_solver]|done|].
    destruct (Psteps_head _ _ _ _ _ _ _ _ _ _ HP (q2.1, M2) j (SClose (edual o)) (q2.1 ∖ ∅, <[j := f']> M2) (edual o) (Hq2e M2 HM2))
      as (S0' & x' & La' & _); [by eapply p_act_session; [eassumption|eassumption|simpl; rewrite ech_edual; cc_set_solver]|done|].
    apply (pfree_1C _ _ _ _ _ _ (conn_sym _ _ _ _ _ _ Hc) o); by eapply elem_of_dom_2.
  Qed.

  Local Ltac side1 i Hi := match goal with H : (_ ∪ _) !! i = Some _ |- _ => destruct (side _ _ _ _ H) as [Hi|Hi] end.

  (** Every τ step of the composite. *)
  Lemma tau_all q ev q' : erase q = pc → istep q ev q' → ev_tau ev → (erase q').1 ## chans_of (Σ1 ∪ Σ2) →
    at_cost_P (S n) (ev_cost κ ev) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T (erase q').
  Proof.
    intros Hq Hst Hτ Hfr. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
    assert (q1.1 ## q2.1) as HCC by (by destruct Hc).
    assert (∀ i e, M1 !! i = Some e → i ∈ dom M1) as D1 by (intros; by eapply elem_of_dom_2).
    assert (∀ i e, M2 !! i = Some e → i ∈ dom M2) as D2 by (intros; by eapply elem_of_dom_2).
    pose proof Hst as Hst0.
    Local Ltac loc1 := eapply tau_l1; try eassumption; split; simpl; [cc_set_solver|try done].
    Local Ltac loc2 := eapply tau_l2; try eassumption; split; simpl; [cc_set_solver|try done].
    inversion Hst0; subst; try (by unfold ev_tau in Hτ).
    - side1 i Hi; [loc1|loc2]; eauto.
    - side1 i Hi; [loc1|loc2]; eauto.
    - side1 i Hi; [loc1|loc2]; eauto.
    - side1 i Hi; [loc1|loc2]; eauto.
    - (* message *)
      side1 i Hi; side1 j Hj.
      + loc1; apply D1 in Hi, Hj; cc_set_solver.
      + simpl. eapply tau_msg12; eassumption.
      + simpl. eapply tau_msg21; eassumption.
      + loc2; apply D2 in Hi, Hj; cc_set_solver.
    - (* close *)
      side1 i Hi; side1 j Hj.
      + destruct (decide (ech o ∈ q1.1)) as [Ho|Ho]; [|exfalso; by eapply (close_same1 M1 i j o)].
        loc1; apply D1 in Hi, Hj; cc_set_solver.
      + simpl. eapply tau_close; eassumption.
      + simpl. replace (ech o) with (ech (edual o)) by apply ech_edual.
        rewrite insert_insert_ne by (intros ->; eapply (disj_lookup_n M1 M2); eassumption).
        eapply tau_close; try eassumption; [rewrite edual_edual; eassumption|by rewrite ech_edual].
      + destruct (decide (ech o ∈ q2.1)) as [Ho|Ho]; [|exfalso; by eapply (close_same2 M2 i j o)].
        loc2; apply D2 in Hi, Hj; cc_set_solver.
    - (* choice *)
      side1 i Hi; side1 j Hj.
      + loc1; apply D1 in Hi, Hj; cc_set_solver.
      + simpl. eapply tau_choice12; eassumption.
      + simpl. eapply tau_choice21; eassumption.
      + loc2; apply D2 in Hi, Hj; cc_set_solver.
    - (* link *)
      side1 i Hi.
      + destruct (decide (ech o1 ∈ q1.1)) as [Ho1|Ho1]; [loc1; eauto|].
        destruct (decide (ech o2 ∈ q1.1)) as [Ho2|Ho2].
        * simpl. eapply tau_link_own1; try eassumption. match goal with H : ech o1 ∈ _ ∪ _ ∪ _ |- _ => clear -H Ho1; cc_set_solver end.
        * simpl. eapply tau_link_ext1; eassumption.
      + destruct (decide (ech o1 ∈ q2.1)) as [Ho1|Ho1]; [loc2; eauto|].
        destruct (decide (ech o2 ∈ q2.1)) as [Ho2|Ho2].
        * simpl. eapply tau_link_own2; try eassumption. match goal with H : ech o1 ∈ _ ∪ _ ∪ _ |- _ => clear -H Ho1; cc_set_solver end.
        * simpl. eapply tau_link_ext2; eassumption.
  Qed.
End tau.
