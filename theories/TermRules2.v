(** * Compositionality of the term rules, part 2 (spec §11)

    The rules that need the box (sharp edges 52): the application of
    force, hence E-App for every function value, E-Force, E-Exp, and
    E-Contract. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export TermRules.

Set Default Proof Using "All".

(** ** Applying force

    force : □(∀ιs. C. ∗ ⊸^u_⊤ T) ⊸^{u[xs/ιs]}_⊤ T[xs/ιs], at an instance xs
    with C[xs/ιs] in W (sharp edges 58). Its upper point is the box's,
    instantiated, so the frame of the application is one V-Box
    accepts, and the instance meets the box's constraint. *)

Lemma Erel_app_force n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) EForce → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App EForce v2).
Proof.
  intros HW HV1 HV2 Hub.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hu & HB & HV).
  inversion Hk as [| | | | | |m C1 ub1 T1 xs Hxs HC1 HK1]; subst.
  apply Vrel_box_thunk_iff in HV as (-> & eb & -> & Hfc & HK).
  destruct n as [|n']; [apply Erel_0|].
  apply (Erel_det_beta_S _ _ _ _ _ _ (subst1 (EBox eb) eb)).
  - by apply TStepHead, HeadForce.
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - eapply Erel_tconv; [apply HW|exact HB|].
    apply (HK W n' xs F); [by apply wext_refl|lia|done|done|done|].
    eapply ub_below_conv; [apply HW| |exact Hub]. by apply opt_rel_sym; [apply HW|].
Qed.

(** Every function value. *)
Lemma Erel_app n W Θ Θ1 Θ2 ub lb T U F v1 v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  Vrel n W Θ1 (TLolli ub lb T U) v1 → Vrel n W Θ2 T v2 → ub_below W ub F →
  Erel n W Θ U F (App v1 v2).
Proof.
  intros HW Hc HV1 HV2 Hub.
  destruct (decide (v1 = EForce)) as [->|Hnf]; [|by eapply Erel_app_noforce].
  pose proof (wf_eq_sym _ (proj1 HW)) as Hs.
  destruct (proj1 (Vrel_lolli_iff _ _ _ _ _ _ _ _) HV1) as [(eb & ? & _)|(k & T0 & _ & -> & _)];
    [done|].
  apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->. by eapply Erel_app_force.
Qed.

Lemma app_good_all ub lb T U : app_good ub lb T U.
Proof. intros n W Θ Θ1 Θ2 F v1 v2 HW Hc HV1 HV2 Hub. by eapply Erel_app. Qed.

(** ** E-App *)

Lemma sem_typed_app W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
  sem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  sem_typed W Θ Δ F (App e1 e2) U.
Proof. apply sem_typed_app_gen, app_good_all. Qed.

(** ** E-Force: force applied to a box, at an instance xs whose upper
    point lies below the frame. *)

Definition lenv_nones (Δ : lenv) : lenv := (λ _, None) <$> Δ.

Lemma lenv_empty_nones Δ : lenv_empty (lenv_nones Δ).
Proof. intros o (?&->&?)%list_elem_of_fmap. done. Qed.

Lemma lenv_split_nones_l Δ : lenv_split Δ (lenv_nones Δ) Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; unfold lenv_nones; simpl; constructor; auto.
Qed.

Lemma sem_typed_force W Θ Δ F e m C ub T xs :
  world_wf W → length xs = m → bcs_hold (w_lt W) C xs → Forall (pt_known W) xs →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  sem_typed W Θ Δ F e (TBox m C (TLolli ub None TUnit T)) →
  sem_typed W Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs HC HK Hub He.
  eapply (sem_typed_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply sem_typed_konst; [apply lenv_empty_nones|]. by constructor.
  - simpl. by rewrite union_empty_r_L.
Qed.

(** ** E-Contract: two copies of an unlimited hypothesis merge
    (t[x/y] = rename pred t). *)

Lemma grounding_contract n W Θ Δ U γ :
  world_wf W → unlimited U → grounding n W Θ (Some U :: Δ) γ →
  grounding n W Θ (Some U :: Some U :: Δ) (λ x, γ (pred x)).
Proof.
  intros HW Hu Hg. pose proof Hg as Hg0. simpl in Hg.
  destruct Hg as (Θ1 & Θ2 & Hc & HV & _).
  pose proof (Vrel_unl_empty _ _ _ _ _ Hu HV) as ->.
  exists ∅, Θ. split_and!.
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - exact HV.
  - eapply grounding_ext; [|exact Hg0]. by intros [|i].
Qed.

Lemma sem_typed_contract W Θ Δ U F e T :
  unlimited U →
  sem_typed W Θ (Some U :: Some U :: Δ) F e T →
  sem_typed W Θ (Some U :: Δ) F (rename pred e) T.
Proof.
  intros Hu He n W' Θ' Θ'' γ HW Hc Hg. rewrite subst_rename.
  apply (He n W' Θ' Θ'' (λ x, γ (pred x))); [done|done|].
  apply grounding_contract; [exact (wext_wf _ _ HW)|done|done].
Qed.

(** ** E-Exp

    The body is good, in every later world, at every instance xs of the
    box's point variables that meets its constraint C (sharp edges 58),
    and under every frame above the instantiated upper point (sharp
    edges 52). The box is then a value at every
    index, by induction on the index (the recursive occurrence is the
    box itself, one level down). *)

Lemma grounding_unl n W Θ Δ γ : world_wf W → lenv_unl Δ → grounding n W Θ Δ γ → Θ = ∅.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hu Hg; simpl in *.
  - done.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    destruct (Hu (Some T)) as [?|(U & [= <-] & HU)]; [by left|done|].
    rewrite (Vrel_unl_empty _ _ _ _ _ HU HV) in Hc.
    apply (tenv_comp_empty_l_inv _ _ _ (wf_eq_sym _ HW)) in Hc as ->.
    apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply Hu. by right.
  - apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply Hu. by right.
Qed.

Lemma sem_typed_box W Δ F e m C ub T :
  lenv_unl Δ → term_wf ∅ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ) e →
  (∀ W1 xs F', wext W W1 → length xs = m → bcs_hold (w_lt W1) C xs →
     Forall (pt_known W1) xs → ub_below W1 (pt_inst (plist xs) <$> ub) F' →
     sem_typed W1 ∅ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ) F' e (ty_inst xs T)) →
  sem_typed W ∅ Δ F (EBox e) (TBox m C (TLolli ub None TUnit T)).
Proof.
  intros Hu (Hfc & Hfv & _) He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wext_wf _ _ HW) as HW'.
  pose proof (grounding_unl _ _ _ _ _ HW' Hu Hg) as ->.
  apply tenv_comp_empty_inv in Hc as ->.
  apply Vrel_Erel.
  assert (fchans (subst (up γ) e) = ∅) as Hfc'.
  { assert (fchans (subst (up γ) e) ⊆ fchans e ∪ dom (∅ : tenv)) as Hsub.
    { apply fchans_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      - intros _. set_solver.
      - intros (T' & Hx). unfold compose. rewrite fchans_rename. by eapply grounding_fchans. }
    rewrite Hfc, dom_empty_L in Hsub. set_solver. }
  assert (∀ j W2, j ≤ n → wext W' W2 →
            Vrel j W2 ∅ (TBox m C (TLolli ub None TUnit T)) (EBox (subst (up γ) e))) as Hbox.
  { induction j as [j IHj] using lt_wf_ind. intros W2 Hj HW2.
    apply Vrel_box_thunk_iff. split; [done|]. exists (subst (up γ) e). split_and!; [done|done|].
    intros W3 k xs F' HW3 Hk Hxs HC HKn Hub. rewrite subst1_subst.
    pose proof (wext_trans _ _ _ HW2 HW3) as HW23.
    pose proof (wext_trans _ _ _ HW HW23) as HWW3.
    apply (He W3 xs F' HWW3 Hxs HC HKn Hub k W3 ∅ ∅).
    - apply wext_refl, HWW3.
    - apply tenv_comp_empty_r.
    - exists ∅, ∅. split_and!.
      + apply tenv_comp_empty_r.
      + apply (IHj k Hk W3); [lia|exact HW23].
      + eapply grounding_ext;
          [|eapply grounding_down; [|eapply grounding_mono; [exact HW'|exact HW23|exact Hg]]];
          [done|lia]. }
  apply Hbox; [done|]. apply wext_refl, HW.
Qed.
