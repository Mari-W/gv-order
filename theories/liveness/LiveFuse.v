(** * The move lemma for the live relation (invariance/JunkRenaming.v, [rel_fuse])

    Moving the ends of c to d inside a related value or term: junk
    collapse, renaming and fusion. As in LiveConv.v, V and E are moved
    together inside one level by induction on [tsize]. New stays at the
    index. When the image creates c itself, the original creates a
    fresh c0, and a swap of c0 and c finishes, because c is absent from
    the image. Every other name the image creates is created by the
    original as well, so the τ layer needs no second move. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveJunk.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

(** ** Steps and environments *)

Lemma tstep_chsubst_new_same x b e c y f' :
  tstep (chsubst x b e) (LNew c y) f' → c ≠ x → ∃ f, tstep e (LNew c y) f ∧ f' = chsubst x b f.
Proof.
  intros Hst Hcx.
  destruct (exist_fresh (fchans e ∪ {[x; b; c]})) as [c0 Hc0].
  destruct (tstep_chsubst_new_inv x b e c y f' Hst c0) as (f0 & Hf0 & ->); [set_solver..|].
  exists (chsubst c0 c f0). split.
  - apply (tstep_chsubst c0 c) in Hf0. simpl in Hf0.
    rewrite (chsubst_id c0 c e), csub_hit in Hf0 by set_solver. exact Hf0.
  - apply chsubst_comm; set_solver.
Qed.

Lemma move_none_d W c d Θ Θ' :
  tenv_move W c d Θ Θ' → Θ' !! d = None → Θ !! c = None ∧ Θ !! d = None.
Proof. intros (_ & _ & Hj & _) H. rewrite H in Hj. by inversion Hj. Qed.

Lemma move_insert_d W c d Θ Θ' o :
  c ≠ d → Θ !! c = None → Θ !! d = None → tenv_move W c d Θ Θ' →
  tenv_move W c d (<[d := o]> Θ) (<[d := o]> Θ').
Proof.
  intros Hcd Hc Hd (Hc' & Ho & Hj & Hdd). split_and!.
  - by rewrite lookup_insert_ne.
  - intros k Hkc Hkd. rewrite !lookup_insert_ne by done. by apply Ho.
  - rewrite lookup_insert_ne by done. rewrite !lookup_insert_eq, Hc. constructor.
  - intros e1 e2 H1 _. rewrite lookup_insert_ne in H1 by done. congruence.
Qed.

(** A move keeps the fit of a term (E-Fit). *)
Lemma tenv_bipol_move W c d Θ Θ' :
  c ≠ d → tenv_move W c d Θ Θ' → tenv_bipol Θ → tenv_bipol Θ'.
Proof.
  intros Hcd (Hc' & Ho & Hj & Hdd) HB y e1 e2 Hy.
  destruct (decide (y = c)) as [->|Hyc]; [by rewrite Hc' in Hy|].
  destruct (decide (y = d)) as [->|Hyd].
  - rewrite Hy in Hj.
    destruct (Θ !! c) as [oc|] eqn:Ec, (Θ !! d) as [od|] eqn:Ed; inversion Hj; subst.
    all: first [by apply (HB c)|by apply (HB d)|
      (destruct (Hdd _ _ eq_refl eq_refl) as [Hx _]; rewrite Hx, pt_pol_dual;
       first [by destruct (pt_pol e2.2)|by destruct (pt_pol e1.2)])].
  - rewrite Ho in Hy by done. by apply (HB y).
Qed.

Lemma tenv_fit_move W c d Θ Θ' e :
  c ≠ d → tenv_move W c d Θ Θ' → tenv_fit Θ e → tenv_fit Θ' (chsubst c d e).
Proof.
  intros Hcd Hm [Hf HB]. split; [|by eapply tenv_bipol_move].
  symmetry. apply (fends_move W c d Θ Θ' e Hcd Hm). by symmetry.
Qed.

Lemma LVrel_move_empty n W Θ' T v c d :
  tenv_move W c d ∅ Θ' → LVrel n W ∅ T v → LVrel n W Θ' T (chsubst c d v).
Proof.
  intros Hm HV. rewrite (move_empty W c d Θ' Hm), chsubst_id; [done|].
  rewrite (LVrel_fchans _ _ _ _ _ HV), dom_empty_L. set_solver.
Qed.

Lemma LVrel_rename n W Θ T v c d :
  d ∉ dom Θ → LVrel n W Θ T v → LVrel n W (tenvswap c d Θ) T (chsubst c d v).
Proof.
  intros Hd HV. rewrite <-eswap_chsubst_absent.
  - by apply LVrel_swap.
  - by rewrite (LVrel_fchans _ _ _ _ _ HV).
Qed.

(** A stable, ready term holding one end each of two dual channels acts
    on neither, unless by a link. *)
Lemma LErel_fusion_exclusion n W Θ T F e c d e1 e2 σ e' :
  strict W → LErel (S n) W Θ T F e → Θ !! c = Some (One e1) → Θ !! d = Some (One e2) →
  w_eq W e1.2 (pt_dual e2.2) → c ≠ d → tstep e (LSess σ) e' →
  (c ∈ subjs σ ∨ d ∈ subjs σ) → ∃ cd, σ = SLink cd.
Proof.
  intros [HWf Hirr] HE Hc Hd Hx Hcd Hst Hsub.
  destruct σ as [[c0 β0] w|[c0 β0] w|[c0 β0]|cd|[c0 β0] i|[c0 β0] i];
    [exfalso|exfalso|exfalso|by eexists|exfalso|exfalso].
  all: assert (stable_t e) as Hs by (intros α f Hf;
         destruct (tstep_same_act _ _ _ _ _ Hst Hf) as (a & Ha & Ha');
         destruct a, α; simpl in *; done).
  all: assert (¬ irred e) as Hni by (intros Hi; by apply (Hi _ _ Hst)).
  all: destruct (Loffered_some _ _ _ _ _ _ _ _ HE Hst) as [k0 Hk0].
  all: pose proof (LErel_S_ready _ _ _ _ _ _ HE Hni) as Hrdy.
  all: destruct (Hrdy Hs) as [_ Ha].
  all: destruct Ha as [Hl|Ha]; [by destruct (link_t_only _ _ _ Hl Hst)|].
  all: assert (∀ k, offered_t Θ e k → k.1 = c0) as Hsame
         by (intros k (σ' & f & Hf & Hsel); apply selects_subj in Hsel;
             destruct (tstep_same_act _ _ _ _ _ Hst Hf) as (a & Ha1 & Ha2);
             destruct a, σ'; simpl in *; try done; destruct_and?; simplify_eq; set_solver).
  all: simpl in Hsub; assert (c0 = c ∨ c0 = d) as [->| ->] by set_solver.
  all: pose proof (Hsame _ Hk0) as Hk0c; destruct k0 as [k1 b0]; simpl in Hk0c; subst k1.
  all: pose proof Hk0 as (σ1 & t1 & _ & Hsel1); destruct (selects_entry _ _ _ Hsel1) as [f Hf].
  all: destruct b0; unfold tenv_entry in Hf; simpl in Hf; rewrite ?Hc, ?Hd in Hf; try done.
  all: injection Hf as <-.
  all: first
    [ (pose proof (proj1 (Ha _ _ Hk0 ltac:(unfold tenv_entry; simpl; by rewrite Hc)) (d, false) e2
         ltac:(unfold tenv_entry; simpl; by rewrite Hd)
         ltac:(intros Ho; apply Hsame in Ho; simpl in Ho; congruence)) as Hlt;
       unfold entry_head in Hlt; simpl in Hlt;
       apply (Hirr e1.2); eapply (wf_lt_eq _ HWf); [reflexivity|exact Hlt|by apply (wf_eq_sym _ HWf)])
    | (pose proof (proj1 (Ha _ _ Hk0 ltac:(unfold tenv_entry; simpl; by rewrite Hd)) (c, false) e1
         ltac:(unfold tenv_entry; simpl; by rewrite Hc)
         ltac:(intros Ho; apply Hsame in Ho; simpl in Ho; congruence)) as Hlt;
       unfold entry_head in Hlt; simpl in Hlt;
       apply (Hirr e2.2); eapply (wf_lt_eq _ HWf);
         [reflexivity|exact Hlt|apply (wf_eq_sym _ HWf); by apply eq_dual_sym]) ].
Qed.

(** ** Moving the body of a λ

    The body of a λ is read at a fresh argument environment. The
    argument may hold c, so c is first swapped with a fresh z. V and the
    two E's are parameters, so that the arrow and the spawned closure
    share the proof. *)
Lemma lam_move (V : nat → world → tenv → expr → Prop)
    (Es Et : nat → world → tenv → gset point → expr → Prop) N W Θ Θ' eb c d ub :
  c ≠ d → strict W → tenv_move W c d Θ Θ' →
  (∀ j a b W Θ w, V j W Θ w → V j W (tenvswap a b Θ) (eswap a b w)) →
  (∀ j a b W Θ F e, Et j W Θ F e → Et j W (tenvswap a b Θ) F (eswap a b e)) →
  (∀ j W Θ0 Θ0' F e, j ≤ N → strict W → tenv_move W c d Θ0 Θ0' →
     Es j W Θ0 F e → Et j W Θ0' F (chsubst c d e)) →
  (∀ W' j Θa Θ'' w F, wext W W' → j ≤ N → tenv_comp (w_eq W') Θ'' Θ Θa →
     ub_below W' ub F → V j W' Θa w → Es j W' Θ'' F (subst1 w eb)) →
  ∀ W' j Θa Θ'' w F, wext W W' → j ≤ N → tenv_comp (w_eq W') Θ'' Θ' Θa →
    ub_below W' ub F → V j W' Θa w → Et j W' Θ'' F (subst1 w (chsubst c d eb)).
Proof.
  intros Hcd HW Hm HVs HEs HEm HL W' j Θa Θ'' w F Hx Hj Hcomp Hub HVw.
  assert (strict W') as HW' by (by destruct Hx as (_ & _ & _ & ?)).
  destruct (exist_fresh (dom Θ ∪ dom Θa ∪ fchans eb ∪ fchans w ∪ {[c; d]})) as [z Hz].
  assert (c ∉ dom Θ') as Hc' by (pose proof Hm as (Hc0 & _); by apply not_elem_of_dom).
  assert (z ∉ dom Θ') as Hz'.
  { rewrite (move_dom W c d Θ Θ' z Hm). set_solver. }
  apply (tenv_comp_swap c z) in Hcomp.
  rewrite (tenvswap_fix c z Θ') in Hcomp by done.
  assert (tenv_move W' c d Θ Θ') as HmW'.
  { eapply (move_mono W c d W'); [|exact Hm]. intros ? ? ?. by apply (proj1 (proj2 Hx)). }
  destruct (move_comp_join W' (proj1 HW') c d Hcd Θ Θ' (tenvswap c z Θa)
              (tenvswap c z Θ'') HmW' Hcomp) as (Θ0 & Hc0 & Hm0).
  { rewrite lookup_tenvswap', cswap_l. apply not_elem_of_dom. set_solver. }
  pose proof (HL W' j (tenvswap c z Θa) Θ0 (eswap c z w) F Hx Hj Hc0 Hub
                (HVs _ c z _ _ _ HVw)) as HE1.
  apply (HEm j W' _ _ _ _ Hj HW' Hm0) in HE1.
  rewrite chsubst_subst1 in HE1.
  rewrite (chsubst_id c d (eswap c z w)) in HE1.
  2: { rewrite fchans_eswap, elem_of_gswap', cswap_l. set_solver. }
  apply (HEs _ c z) in HE1. rewrite tenvswap_involutive, eswap_subst1,
    eswap_involutive in HE1.
  rewrite (eswap_fresh c z (chsubst c d eb)) in HE1; [done| |].
  - by apply fchans_chsubst_notin.
  - intros Hz2. apply fchans_chsubst in Hz2. set_solver.
Qed.

(** The spawned closure read uniformly in j ≤ N. *)
Definition Vsp_u (N : nat) : nat → world → tenv → expr → Prop :=
  λ j W Θ w, (j < N ∧ LVrel j W Θ TUnit w) ∨ (j = N ∧ Θ = ∅ ∧ w = EUnit).

Definition Esp_u (N : nat) (X : world → tenv → gset point → expr → Prop) :
    nat → world → tenv → gset point → expr → Prop :=
  λ j W Θ F e, (j < N → LErel j W Θ TUnit F e) ∧ (j = N → X W Θ F e).

(** ** The move lemma *)

Section fuse.
  Context (c d : chan) (Hcd : c ≠ d) (n : nat).
  Context (IHn : ∀ j, j < n →
    (∀ W Θ Θ' T v, strict W → tenv_move W c d Θ Θ' →
       LVrel j W Θ T v → LVrel j W Θ' T (chsubst c d v)) ∧
    (∀ W Θ Θ' T F e, strict W → tenv_move W c d Θ Θ' →
       LErel j W Θ T F e → LErel j W Θ' T F (chsubst c d e))).

  Lemma LErel_fuse_at T :
    (∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
       LVrel n W Θ T v → LVrel n W Θ' T (chsubst c d v)) →
    ∀ W Θ Θ' F e, strict W → tenv_move W c d Θ Θ' →
      LErel n W Θ T F e → LErel n W Θ' T F (chsubst c d e).
  Proof.
    intros HVT W Θ Θ' F e HW Hm HE.
    destruct n as [|n']; [apply LErel_0|].
    assert (IHE : ∀ j, j < S n' → ∀ W Θ Θ' T F e, strict W → tenv_move W c d Θ Θ' →
              LErel j W Θ T F e → LErel j W Θ' T F (chsubst c d e)).
    { intros j Hj. apply (IHn j Hj). }
    assert (IHV : ∀ j, j < S n' → ∀ W Θ Θ' T v, strict W → tenv_move W c d Θ Θ' →
              LVrel j W Θ T v → LVrel j W Θ' T (chsubst c d v)).
    { intros j Hj. apply (IHn j Hj). }
    clear IHn.
    revert W Θ T F e HE HVT Θ' HW Hm.
    refine (LErel_S_ind n' (λ W Θ T F e,
      (∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
         LVrel (S n') W Θ T v → LVrel (S n') W Θ' T (chsubst c d v)) →
      ∀ Θ', strict W → tenv_move W c d Θ Θ' → LErel (S n') W Θ' T F (chsubst c d e)) _).
    intros W0 Θ T F e H HVT Θ' HW0 Hm0.
    apply LErel_S_iff. split; [exact (tenv_fit_move _ _ _ _ _ _ Hcd Hm0 (proj1 H))|].
    intros W HW1.
    assert (strict W) as HW.
    { destruct HW1 as [->|HW1]; [done|by destruct HW1 as (_ & _ & _ & ?)]. }
    assert (tenv_move W c d Θ Θ') as Hm.
    { eapply (move_mono W0 c d W); [|exact Hm0]. intros ? ? ?.
      destruct HW1 as [->|HW1]; [done|by apply (proj1 (proj2 HW1))]. }
    assert (HE0 : LErel (S n') W Θ T F e).
    { eapply LErel_mono; [exact HW1|]. apply LErel_S_iff.
      eapply LEstep_mono; [|exact H]. by intros ? ? ? ? ? [? _]. }
    destruct (proj2 H W HW1) as (Hval & Hrdy & Hb & Hnew & Hsp & Hσ & Hlk).
    clear H HW0 Hm0 HW1.
    pose proof (proj1 HW) as HWf.
    assert (Hexcl : fused c d Θ → ∀ σ f, tstep e (LSess σ) f → (c ∈ subjs σ ∨ d ∈ subjs σ) →
                      ∃ cd, σ = SLink cd).
    { intros (e1 & e2 & Hc & Hd) σ f Hf Ht.
      assert (w_eq W e1.2 (pt_dual e2.2)) as Hx by (pose proof Hm as (_ & _ & _ & H); by apply H).
      exact (LErel_fusion_exclusion n' W Θ T F e c d e1 e2 σ f HW HE0 Hc Hd Hx Hcd Hf Ht). }
    assert (Hsub : ∀ σ f, tstep e (LSess σ) f → subjs σ ⊆ dom Θ)
      by (intros σ f Hf; exact (LErel_subjs _ _ _ _ _ _ _ _ HE0 Hf)).
    assert (Hok : ∀ σ f c0, tstep e (LSess σ) f → (∀ cd, σ ≠ SLink cd) → c0 ∈ subjs σ →
                    move_ok c d Θ c0)
      by (intros; eapply step_move_ok; eassumption).
    assert (Hlnk : ∀ cd f, tstep e (LSess (SLink cd)) f → ∀ y b, (y, b) ∈ cd →
                 ∃ k e0, k.1 = y ∧ tenv_entry Θ k = Some e0 ∧ pt_pol e0.2 = b)
      by (intros cd f Hf; exact (LErel_link_ends _ _ _ _ _ _ _ _ HE0 Hf)).
    destruct (move_keys_csub W c d Hcd Θ Θ' Hm) as (κ & Hκ1 & Hκ2 & Hκ3 & Hκ4 & Hκ5).
    assert (Hfwd : ∀ k, offered_t Θ e k → offered_t Θ' (chsubst c d e) (κ k))
      by (intros; eapply fused_offer_fwd; eassumption).
    assert (Hback : ∀ k' e', offered_t Θ' (chsubst c d e) k' → tenv_entry Θ' k' = Some e' →
              below_rest W Θ (offered_t Θ e) F →
              ∃ k e0, offered_t Θ e k ∧ tenv_entry Θ k = Some e0 ∧ w_eq W e0.2 e'.2)
      by (intros; eapply fused_offer_back; try eassumption; exact (proj2 HW)).
    assert (HVu : ∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
              LVrel (S n') W Θ TUnit v → LVrel (S n') W Θ' TUnit (chsubst c d v)).
    { intros W2 Θ2 Θ2' v HW2 Hm2 [-> ->]%LVrel_unit_iff.
      rewrite (move_empty W2 c d Θ2' Hm2). by apply LVrel_unit_iff. }
    split_and!.
    - intros Hirr. apply irred_chsubst in Hirr as Hirr0.
      exact (HVT W Θ Θ' e HW Hm (Hval Hirr0)).
    - intros Hni. assert (¬ irred e) as Hni0.
      { intros Hi. apply Hni. by apply irred_chsubst_back. }
      intros Hs. apply stable_chsubst in Hs as Hs0. destruct (Hrdy Hni0 Hs0) as [Hv Ha]. split.
      + intros Hno. rewrite is_val_chsubst. apply Hv. intros k Hk. apply (Hno (κ k)).
        by apply Hfwd.
      + destruct Ha as [(cd & f & Hf)|Ha].
        { left. exists (gosub c d cd), (chsubst c d f). by apply (tstep_chsubst c d) in Hf. }
        right. intros k' e' Ho He'.
        destruct (Hback k' e' Ho He' Ha) as (k & e0 & Ho0 & He0 & Heq).
        destruct (Ha k e0 Ho0 He0) as [H1 H2]. split.
        * intros k2 e2 He2 Hn2. destruct (Hκ4 k2 e2 He2) as (k3 & <- & He3).
          assert (¬ offered_t Θ e k3) as Hn3 by (intros Ho3; apply Hn2; by apply Hfwd).
          pose proof (H1 k3 e2 He3 Hn3) as Hlt. unfold entry_head in *.
          eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|reflexivity].
        * intros y Hy. pose proof (H2 y Hy) as Hlt. unfold entry_head in *.
          eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|reflexivity].
    - (* β *)
      intros f' Hst.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      apply eq_sym, lsub_beta in Hα as ->.
      destruct (Hb _ Hf) as [_ HΦ]. by apply HΦ.
    - (* new *)
      intros c' y' f' Hst Hc'.
      assert (c ∉ dom Θ') as HcΘ' by (pose proof Hm as (Hc0 & _); by apply not_elem_of_dom).
      destruct (decide (c' = c)) as [->|Hc'c].
      + destruct (exist_fresh (fchans e ∪ dom Θ ∪ dom Θ' ∪ {[c; d]})) as [c0 Hc0].
        destruct (tstep_chsubst_new_inv c d e c y' f' Hst c0) as (f & Hf & ->); [set_solver..|].
        destruct (Hnew _ _ _ Hf ltac:(set_solver)) as (Hpl & s & s' & Hdu & _ & HΦ).
        split; [done|]. exists s, s'. split; [done|].
        pose proof (HΦ HVT (<[c0 := Both (s, y') (s', pt_dual y')]> Θ') HW) as HE1.
        assert (LErel (S n') W (<[c0 := Both (s, y') (s', pt_dual y')]> Θ') T F (chsubst c d f))
          as HE2.
        { apply HE1. apply move_insert; [set_solver|set_solver|done]. }
        apply (LErel_swap c0 c) in HE2.
        rewrite tenvswap_insert, cswap_l, tenvswap_fix in HE2 by set_solver.
        rewrite eswap_chsubst_absent in HE2; [done|].
        by apply fchans_chsubst_notin.
      + destruct (tstep_chsubst_new_same c d e c' y' f' Hst Hc'c) as (f & Hf & ->).
        assert (c' ∉ dom Θ) as Hc'0.
        { destruct (decide (c' = d)) as [->|Hc'd].
          - apply not_elem_of_dom. apply not_elem_of_dom in Hc'.
            exact (proj2 (move_none_d W c d Θ Θ' Hm Hc')).
          - pose proof Hm as (_ & Ho & _). apply not_elem_of_dom. apply not_elem_of_dom in Hc'.
            by rewrite <-(Ho c' Hc'c Hc'd). }
        destruct (Hnew _ _ _ Hf Hc'0) as (Hpl & s & s' & Hdu & _ & HΦ).
        split; [done|]. exists s, s'. split; [done|].
        apply (HΦ HVT); [done|].
        destruct (decide (c' = d)) as [->|Hc'd].
        * apply not_elem_of_dom in Hc'.
          destruct (move_none_d W c d Θ Θ' Hm Hc') as [Hc1 Hd1].
          by apply move_insert_d.
        * by apply move_insert.
    - (* spawn *)
      intros w' f' Hst.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
      destruct (Hsp _ _ Hf) as (Θ1 & Θ2 & ub & lb & Hc & Hv & _ & HΦ).
      destruct (move_comp_split W HWf c d Hcd Θ Θ' Θ1 Θ2 Hm Hc)
        as (Θ1' & Θ2' & Hm1 & Hm2 & Hc').
      exists Θ1', Θ2', ub, lb. split_and!; [done| |by apply HΦ].
      destruct Hv as [(eb & -> & Hfc & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + left. exists (chsubst c d eb). split_and!; [done|exact (tenv_fit_move W c d Θ1 Θ1' eb Hcd Hm1 Hfc)
          |by rewrite (move_heads W c d Hcd Θ1 Θ1' Hm1)|].
        pose proof (lam_move (Vsp_u (S n'))
                      (Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e ∧
                         ((∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
                            LVrel (S n') W Θ TUnit v → LVrel (S n') W Θ' TUnit (chsubst c d v)) →
                          ∀ Θ', strict W → tenv_move W c d Θ Θ' →
                            LErel (S n') W Θ' TUnit F (chsubst c d e))))
                      (Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e))
                      (S n') W Θ1 Θ1' eb c d ub Hcd HW Hm1) as K.
        assert (Hvs : ∀ j a b W Θ w, Vsp_u (S n') j W Θ w →
                  Vsp_u (S n') j W (tenvswap a b Θ) (eswap a b w)).
        { intros j a b W5 Θ5 w5 [[Hlt HV2]|(Hjn & -> & ->)].
          - left. split; [done|by apply LVrel_swap].
          - right. by rewrite tenvswap_empty. }
        assert (Hes : ∀ j a b W Θ F e, Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e) j W Θ F e →
                  Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e) j W (tenvswap a b Θ) F
                    (eswap a b e)).
        { intros j a b W5 Θ5 F5 e5 [K1 K2]. split.
          - intros Hlt. by apply LErel_swap, K1.
          - intros Hjn. by apply LErel_swap, K2. }
        specialize (K Hvs Hes).
        assert (Hem : ∀ j W Θ0 Θ0' F e, j ≤ S n' → strict W → tenv_move W c d Θ0 Θ0' →
                  Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e ∧
                         ((∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
                            LVrel (S n') W Θ TUnit v → LVrel (S n') W Θ' TUnit (chsubst c d v)) →
                          ∀ Θ', strict W → tenv_move W c d Θ Θ' →
                            LErel (S n') W Θ' TUnit F (chsubst c d e))) j W Θ0 F e →
                  Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e) j W Θ0' F (chsubst c d e)).
        { intros j W5 Θ0 Θ0' F5 e5 Hj HW5 Hm3 [K1 K2]. split.
          - intros Hlt. eapply IHE; [done|done|exact Hm3|by apply K1].
          - intros Hjn. destruct (K2 Hjn) as [_ HΦ2]. by apply HΦ2. }
        specialize (K Hem).
        assert (HL' : ∀ W' j Θa Θ'' w F, wext W W' → j ≤ S n' → tenv_comp (w_eq W') Θ'' Θ1 Θa →
                  ub_below W' ub F → Vsp_u (S n') j W' Θa w →
                  Esp_u (S n') (λ W Θ F e, LErel (S n') W Θ TUnit F e ∧
                         ((∀ W Θ Θ' v, strict W → tenv_move W c d Θ Θ' →
                            LVrel (S n') W Θ TUnit v → LVrel (S n') W Θ' TUnit (chsubst c d v)) →
                          ∀ Θ', strict W → tenv_move W c d Θ Θ' →
                            LErel (S n') W Θ' TUnit F (chsubst c d e))) j W' Θ'' F (subst1 w eb)).
        { intros W' j Θa Θ'' w F2 HW' Hj Hca Hub HVw.
          destruct (HL W' j Θa Θ'' w F2 HW' Hj Hca Hub) as [K1 K2]. split.
          - intros Hlt. destruct HVw as [[_ HVw]|(Hjn & _ & _)]; [by apply K1|lia].
          - intros Hjn. destruct HVw as [[Hlt _]|(_ & -> & ->)]; [lia|]. by apply K2. }
        specialize (K HL').
        intros W' j Θa Θ'' w F2 HW' Hj Hca Hub. split.
        * intros Hlt HVw.
          exact (proj1 (K W' j Θa Θ'' w F2 HW' Hj Hca Hub (or_introl (conj Hlt HVw))) Hlt).
        * intros Hjn -> ->.
          exact (proj2 (K W' j ∅ Θ'' EUnit F2 HW' Hj Hca Hub
                          (or_intror (conj Hjn (conj eq_refl eq_refl)))) Hjn).
      + right. exists k, T0. rewrite (move_empty W c d Θ1' Hm1). split_and!; done.
    - (* session steps *)
      intros σ' f' Hst. destruct σ' as [[c' β'] w'|[c' β'] w'|[c' β']|cd'|[c' β'] i'|[c' β'] i'].
      + (* receive: freshen the payload's c through z *)
        destruct (exist_fresh (fchans w' ∪ fchans e ∪ dom Θ ∪ dom Θ' ∪ {[c; d]})) as [z Hz].
        destruct (tstep_chsubst_recv_inv_swap c d z e (c', β') w' f')
          as ([c0 β0] & f & Hc0 & Hf & ->); [done|set_solver|set_solver|set_solver|done|set_solver|].
        unfold osub in Hc0; simpl in Hc0. injection Hc0 as Hc0 <-.
        assert (Hok0 : move_ok c d Θ c0)
          by (eapply Hok; [exact Hf|intros ? [=]|simpl; by apply elem_of_singleton]).
        pose proof (Hσ _ _ Hf) as Hc1. cbn [LEobl pred] in Hc1 |- *.
        destruct Hc1 as (Θ1 & m & U & s & k & [Hhd Hp] & H).
        assert (Hok1 : move_ok c d Θ1 c0)
          by (destruct Hhd as (? & Hx0 & _); exact (move_ok_ext c d Θ1 c0 _ Θ Hcd Hx0 Hok0)).
        destruct (move_hd W c d Hcd Θ Θ' c0 _ k Θ1 Hm Hhd Hok0) as (Θ1' & Hhd' & Hm1).
        rewrite Hc0 in Hhd'.
        exists Θ1', m, U, s, k. split; [by split|].
        intros W' j Θ2 Θ1c' Θ'' HW' Hj Hext Hcomp HVw.
        assert (strict W') as HW'' by (by destruct HW' as (_ & _ & _ & ?)).
        destruct (move_ext_given_ok W c d Θ1 Θ1' c0 _ Θ1c' Hcd Hm1 Hok1
                    ltac:(by rewrite Hc0)) as (Θ1c & Hext1 & Hm1c).
        assert (z ∉ dom Θ2) as HzΘ2 by (rewrite <-(LVrel_fchans _ _ _ _ _ HVw); set_solver).
        assert (c ∉ dom Θ1c' ∧ z ∉ dom Θ1c') as [HcΘ1 HzΘ1].
        { assert (dom Θ1' ⊆ dom Θ' ∧ c' ∈ dom Θ') as [Hs1 Hs2].
          { destruct Hhd' as (s0 & Hx0 & _).
            destruct Hx0 as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver. }
          assert (c ∉ dom Θ') as Hc'' by (pose proof Hm as (Hc0' & _); by apply not_elem_of_dom).
          assert (dom Θ1c' ⊆ dom Θ1' ∪ {[c']}) as Hs3.
          { destruct Hext as [[_ ->]|(g & _ & [-> | ->])]; rewrite dom_insert_L; set_solver. }
          split; clear -Hs1 Hs2 Hs3 Hc'' Hz; set_solver. }
        apply (tenv_comp_swap c z) in Hcomp.
        rewrite (tenvswap_fix c z Θ1c') in Hcomp by done.
        assert (tenv_move W' c d Θ1c Θ1c') as Hm1c'.
        { eapply (move_mono W c d W'); [|exact Hm1c]. intros ? ? ?. by apply (proj1 (proj2 HW')). }
        destruct (move_comp_join W' (proj1 HW'') c d Hcd Θ1c Θ1c' (tenvswap c z Θ2)
                    (tenvswap c z Θ'') Hm1c' Hcomp) as (Θ0 & Hcj & Hm0).
        { rewrite lookup_tenvswap', cswap_l. by apply not_elem_of_dom. }
        pose proof (H W' j (tenvswap c z Θ2) Θ1c Θ0 HW' Hj Hext1 Hcj
                      (LVrel_swap c z _ _ _ _ _ HVw)) as HE1.
        apply (IHE j ltac:(lia) W' _ _ T F f HW'' Hm0) in HE1.
        apply (LErel_swap c z) in HE1. rewrite tenvswap_involutive in HE1. exact HE1.
      + (* send *)
        apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[[c0 β0] w0|[c0 β0] w0|[c0 β0]|cd0|[c0 β0] i0|[c0 β0] i0]| |]; cbn [lsub ssub] in Hα; try discriminate.
        injection Hα as Hc0 Hb0 Hw0. subst c' β' w'.
        assert (Hok0 : move_ok c d Θ c0)
          by (eapply Hok; [exact Hf|intros ? [=]|simpl; by apply elem_of_singleton]).
        pose proof (Hσ _ _ Hf) as Hc1. cbn [LEobl pred] in Hc1 |- *.
        destruct Hc1 as (Θr & Θ1 & Θ2 & m & U & s & k & Θ'' & [Hhd Hp] & Hsp' & HVw & Hext & HE').
        assert (Hokr : move_ok c d Θr c0)
          by (destruct Hhd as (? & Hx0 & _); exact (move_ok_ext c d Θr c0 _ Θ Hcd Hx0 Hok0)).
        destruct (move_hd W c d Hcd Θ Θ' c0 _ k Θr Hm Hhd Hok0) as (Θr' & Hhd' & Hmr).
        destruct (move_comp_split W HWf c d Hcd Θr Θr' Θ1 Θ2 Hmr Hsp')
          as (Θ1' & Θ2' & Hm1 & Hm2 & Hsp'').
        destruct (move_ext W c d Hcd Θ1 Θ1' c0 _ Θ'' Hm1 Hext
                    (move_ok_comp c d _ Θr Θ1 Θ2 c0 Hsp' Hokr)) as (Θ3 & Hext' & Hm3).
        exists Θr', Θ1', Θ2', m, U, s, k, Θ3. split_and!; [by split|done| |done|].
        * exact (IHV n' ltac:(lia) W Θ2 Θ2' _ w0 HW Hm2 HVw).
        * exact (IHE n' ltac:(lia) W _ _ T F f HW Hm3 HE').
      + (* close *)
        apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[[c0 β0] w0|[c0 β0] w0|[c0 β0]|cd0|[c0 β0] i0|[c0 β0] i0]| |]; cbn [lsub ssub] in Hα; try discriminate.
        injection Hα as Hc0 Hb0. subst c' β'.
        assert (Hok0 : move_ok c d Θ c0)
          by (eapply Hok; [exact Hf|intros ? [=]|simpl; by apply elem_of_singleton]).
        pose proof (Hσ _ _ Hf) as Hc1. cbn [LEobl pred] in Hc1 |- *.
        destruct Hc1 as (Θ1 & k & [Hhd Hp] & HE').
        destruct (move_hd W c d Hcd Θ Θ' c0 _ k Θ1 Hm Hhd Hok0) as (Θ1' & Hhd' & Hm1).
        exists Θ1', k. split; [by split|]. exact (IHE n' ltac:(lia) W _ _ T F f HW Hm1 HE').
      + (* link: O-Link below *)
        exact I.
      + (* select *)
        apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[[c0 β0] w0|[c0 β0] w0|[c0 β0]|cd0|[c0 β0] i0|[c0 β0] i0]| |]; cbn [lsub ssub] in Hα; try discriminate.
        injection Hα as Hc0 Hb0 Hi0. subst c' β' i'.
        assert (Hok0 : move_ok c d Θ c0)
          by (eapply Hok; [exact Hf|intros ? [=]|simpl; by apply elem_of_singleton]).
        pose proof (Hσ _ _ Hf) as Hc1. cbn [LEobl pred] in Hc1 |- *.
        destruct Hc1 as (Θr & s1 & s2 & k & Θ'' & [Hhd Hp] & Hext & HE').
        assert (Hokr : move_ok c d Θr c0)
          by (destruct Hhd as (? & Hx0 & _); exact (move_ok_ext c d Θr c0 _ Θ Hcd Hx0 Hok0)).
        destruct (move_hd W c d Hcd Θ Θ' c0 _ k Θr Hm Hhd Hok0) as (Θr' & Hhd' & Hmr).
        destruct (move_ext W c d Hcd Θr Θr' c0 _ Θ'' Hmr Hext Hokr) as (Θ3 & Hext' & Hm3).
        exists Θr', s1, s2, k, Θ3. split_and!; [by split|done|].
        exact (IHE n' ltac:(lia) W _ _ T F f HW Hm3 HE').
      + (* branch *)
        apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
        destruct α as [|[[c0 β0] w0|[c0 β0] w0|[c0 β0]|cd0|[c0 β0] i0|[c0 β0] i0]| |]; cbn [lsub ssub] in Hα; try discriminate.
        injection Hα as Hc0 Hb0 Hi0. subst c' β' i'.
        assert (Hok0 : move_ok c d Θ c0)
          by (eapply Hok; [exact Hf|intros ? [=]|simpl; by apply elem_of_singleton]).
        pose proof (Hσ _ _ Hf) as Hc1. cbn [LEobl pred] in Hc1 |- *.
        destruct Hc1 as (Θr & s1 & s2 & k & Θ'' & [Hhd Hp] & Hext & HE').
        assert (Hokr : move_ok c d Θr c0)
          by (destruct Hhd as (? & Hx0 & _); exact (move_ok_ext c d Θr c0 _ Θ Hcd Hx0 Hok0)).
        destruct (move_hd W c d Hcd Θ Θ' c0 _ k Θr Hm Hhd Hok0) as (Θr' & Hhd' & Hmr).
        destruct (move_ext W c d Hcd Θr Θr' c0 _ Θ'' Hmr Hext Hokr) as (Θ3 & Hext' & Hm3).
        exists Θr', s1, s2, k, Θ3. split_and!; [by split|done|].
        exact (IHE n' ltac:(lia) W _ _ T F f HW Hm3 HE').
    - (* O-Link, at the index *)
      intros cd' f' Hst.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; cbn [lsub ssub] in Hα; try discriminate.
      injection Hα as Hcd'. subst cd'.
      destruct (Hlk _ _ Hf) as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & Hdu & Hal & [_ HΦ]).
      destruct (move_unext_any W c d Θ Θ' c1 _ Θm Hcd Hm H2) as (Θm' & H2' & Hmm).
      destruct (move_unext_any W c d Θm Θm' d1 _ Θ1 Hcd Hmm H1) as (Θ1' & H1' & Hm1).
      exists (csub c d c1), (csub c d d1), Θ1', Θm', sc, sd, kc, kd. split_and!; [|done..|].
      * apply gosub_upair.
      * exact (HΦ HVT Θ1' HW Hm1).
  Qed.

  Lemma LVrel_fuse_size k :
    ∀ W Θ Θ' T v, tsize T ≤ k → strict W → tenv_move W c d Θ Θ' →
      LVrel n W Θ T v → LVrel n W Θ' T (chsubst c d v).
  Proof.
    induction k as [k IHk] using lt_wf_ind.
    intros W Θ Θ' T v Hk HW Hm HVv.
    assert (∀ W Θ Θ' T F e, tsize T < k → strict W → tenv_move W c d Θ Θ' →
              LErel n W Θ T F e → LErel n W Θ' T F (chsubst c d e)) as HE.
    { intros W0 Θ0 Θ0' T0 F e Hs. apply LErel_fuse_at.
      intros W1 Θ1 Θ1' v1. apply (IHk (tsize T0)); [lia|lia]. }
    destruct T as [|ub lb T1 U|T1 U|T1 U|m kk C0 T1|s x|lb m C0 T1|x]; simpl in Hk.
    - pose proof HVv as [-> _]%LVrel_unit_iff. by apply (LVrel_move_empty n W Θ').
    - pose proof HVv as [(eb & -> & Hfc & Hlb & HL)|(kc & T0 & -> & -> & _)]%LVrel_lolli_iff;
        [|by apply (LVrel_move_empty n W Θ')].
      apply LVrel_lolli_iff. left. exists (chsubst c d eb). split_and!.
      + done.
      + exact (tenv_fit_move W c d Θ Θ' eb Hcd Hm Hfc).
      + by rewrite (move_heads W c d Hcd Θ Θ' Hm).
      + apply (lam_move (λ j W Θ w, LVrel j W Θ T1 w) (λ j W Θ F e, LErel j W Θ U F e)
                 (λ j W Θ F e, LErel j W Θ U F e) n W Θ Θ' eb c d ub Hcd HW Hm).
        * intros j a b W0 Θ0 w0. apply LVrel_swap.
        * intros j a b W0 Θ0 F0 e0. apply LErel_swap.
        * intros j W0 Θ0 Θ0' F0 e0 Hj HW0 Hm0.
          destruct (decide (j < n)) as [Hlt|Hge].
          -- by apply (proj2 (IHn j Hlt)).
          -- assert (j = n) as -> by lia. apply (HE _ _ _ U); [lia|done|done].
        * done.
    - apply LVrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      destruct (move_comp_split W (proj1 HW) c d Hcd Θ Θ' Θ1 Θ2 Hm Hsp)
        as (Θ1' & Θ2' & Hm1 & Hm2 & Hsp').
      apply LVrel_prod_iff. exists (chsubst c d v1), (chsubst c d v2), Θ1', Θ2'.
      split_and!; [done|done|eapply (IHk (tsize T1)); [lia|lia|done|exact Hm1|exact H1]
                  |eapply (IHk (tsize U)); [lia|lia|done|exact Hm2|exact H2]].
    - apply LVrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply LVrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + eapply (IHk (tsize T1)); [lia|lia|done|exact Hm|exact H].
      + eapply (IHk (tsize U)); [lia|lia|done|exact Hm|exact H].
    - pose proof HVv as [-> _]%LVrel_box_iff. by apply (LVrel_move_empty n W Θ').
    - apply LVrel_sess_iff in HVv as (c0 & bb & s0 & kk & -> & -> & Hs & Hkk & Hp).
      rewrite chsubst_chan. apply LVrel_sess_iff. exists (csub c d c0), bb, s0, kk.
      split_and!; [done| |done|done|done].
      destruct (move_singleton W c d Hcd c0 _ Θ' Hm) as [[-> ->]|[Hne ->]];
        [by rewrite csub_hit|by rewrite csub_ne].
    - apply LVrel_ex_iff in HVv as [Hlb (xs & Hxs & HK & HC & H)].
      apply LVrel_ex_iff. split; [by rewrite (move_heads W c d Hcd Θ Θ' Hm)|].
      exists xs. split_and!; [done..|].
      eapply (IHk (tsize T1)); [lia|unfold ty_inst; rewrite tsize_pinst; lia|done|exact Hm|exact H].
    - pose proof HVv as [-> _]%LVrel_pt_iff. by apply (LVrel_move_empty n W Θ').
  Qed.
End fuse.

Lemma lrel_fuse c d n : c ≠ d →
  (∀ W Θ Θ' T v, strict W → tenv_move W c d Θ Θ' →
     LVrel n W Θ T v → LVrel n W Θ' T (chsubst c d v)) ∧
  (∀ W Θ Θ' T F e, strict W → tenv_move W c d Θ Θ' →
     LErel n W Θ T F e → LErel n W Θ' T F (chsubst c d e)).
Proof.
  intros Hcd. induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ Θ' T v, strict W → tenv_move W c d Θ Θ' →
            LVrel n W Θ T v → LVrel n W Θ' T (chsubst c d v)) as HV.
  { intros W Θ Θ' T v. by apply (LVrel_fuse_size c d Hcd n IHn (tsize T)). }
  split; [exact HV|].
  intros W Θ Θ' T F e. apply (LErel_fuse_at c d Hcd n IHn). intros. by eapply HV.
Qed.

Lemma LVrel_fuse n W Θ Θ' T v c d :
  strict W → c ≠ d → tenv_move W c d Θ Θ' → LVrel n W Θ T v → LVrel n W Θ' T (chsubst c d v).
Proof. intros HW Hcd. by apply (lrel_fuse c d n Hcd). Qed.

Lemma LErel_fuse n W Θ Θ' T F e c d :
  strict W → c ≠ d → tenv_move W c d Θ Θ' → LErel n W Θ T F e → LErel n W Θ' T F (chsubst c d e).
Proof. intros HW Hcd. by apply (lrel_fuse c d n Hcd). Qed.

(** Junk collapse and renaming are the moves that fuse nothing. *)
Lemma LErel_junk n W Θ T F e x b :
  strict W → x ∉ dom Θ → x ≠ b → LErel n W Θ T F e → LErel n W Θ T F (chsubst x b e).
Proof.
  intros HW Hx Hxb HE. apply (LErel_fuse n W Θ Θ T F e x b); [done|done|by apply move_id|done].
Qed.

Lemma LErel_rename n W Θ T F e c d :
  strict W → d ∉ dom Θ → c ≠ d → LErel n W Θ T F e →
  LErel n W (tenvswap c d Θ) T F (chsubst c d e).
Proof.
  intros HW Hd Hcd HE. apply (LErel_fuse n W Θ _ T F e c d HW Hcd); [|done].
  apply move_swap; [done|]. by apply not_elem_of_dom.
Qed.
