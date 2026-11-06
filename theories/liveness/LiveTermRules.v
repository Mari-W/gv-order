(** * The term rules for the live relation (liveness.md §10, step 1)

    The live semantic judgment [lsem_typed] and one lemma per typing
    rule of rules/TermRules.v, on top of the live bind lemma
    [LErel_bind]. The proofs follow TermRules.v. Every step at cost 0
    stays at the index, so the continuation of an elimination rule is
    read at every j ≤ n, the current index included. E-Exp is not here:
    its live form needs a guarded body (§6). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveConsts rules.BoxRules.

Set Default Proof Using "All".
Local Set Warnings "-register-all".

(** ** Values: channels and unlimited types *)

Lemma LVdef_fchans below n k W Θ T v : LVdef below n k W Θ T v → fchans v = dom Θ.
Proof.
  revert W Θ T v. induction k as [|k IH]; intros W Θ T v; [done|].
  destruct T; cbn [LVdef].
  - intros [-> ->]. simpl. by rewrite dom_empty_L.
  - intros [(eb & -> & Hsup & _)|(kc & T0 & -> & -> & _)]; simpl; [done|by rewrite dom_empty_L].
  - intros (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & H1 & H2). simpl.
    rewrite (IH _ _ _ _ H1), (IH _ _ _ _ H2). by rewrite (tenv_join_dom _ _ _ Hj).
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - intros (-> & eb & -> & Hfc & _). simpl. rewrite Hfc. by rewrite dom_empty_L.
  - intros (c & s0 & kk & -> & -> & _). simpl. by rewrite dom_singleton_L.
  - intros (_ & xs & _ & _ & _ & H). eauto.
Qed.

Lemma LVrel_fchans n W Θ T v : LVrel n W Θ T v → fchans v = dom Θ.
Proof. intros H%LVrel_eq. exact (LVdef_fchans _ _ _ _ _ _ _ H). Qed.

Lemma LVrel_unl_empty n W Θ T v : unlimited T → LVrel n W Θ T v → Θ = ∅.
Proof. destruct T; try done. intros _. apply LVrel_box_empty. Qed.

(** ** Grounding substitutions *)

Fixpoint lgrounding (n : nat) (W : world) (Θ : tenv) (Δ : lenv) (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => lgrounding n W Θ Δ' (γ ∘ S)
  | Some T :: Δ' =>
      ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ LVrel n W Θ1 T (γ 0) ∧
               lgrounding n W Θ2 Δ' (γ ∘ S)
  end.

(** Θ; Δ ⊨ˡ^F_W e : T *)
Definition lsem_typed (W : world) (Θ : tenv) (Δ : lenv) (F : gset point)
    (e : expr) (T : ty) : Prop :=
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' →
    lgrounding n W' Θ' Δ γ → LErel n W' Θ'' T F (subst γ e).

Lemma lgrounding_heads n W Θ Δ γ :
  world_wf W → lenv_bot Δ = false → lgrounding n W Θ Δ γ → heads_above W (lenv_heads Δ) Θ.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hb Hg; simpl in *.
  - subst. apply heads_above_empty.
  - apply orb_false_iff in Hb as [Hb1 Hb2]. destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    eapply heads_above_comp; [exact Hc|by eapply LVrel_heads_above|by eapply IH].
  - by eapply IH.
Qed.

Lemma lgrounding_mono n W W' Θ Δ γ :
  wext W W' → lgrounding n W Θ Δ γ → lgrounding n W' Θ Δ γ.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hg; simpl in *; [done| |exact (IH _ _ Hg)].
  destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!.
  - exact Hc.
  - by eapply LVrel_mono.
  - exact (IH _ _ Hg).
Qed.

Lemma lgrounding_down n m W Θ Δ γ :
  m ≤ n → lgrounding n W Θ Δ γ → lgrounding m W Θ Δ γ.
Proof.
  intros Hle. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hg; simpl in *; [done| |exact (IH _ _ Hg)].
  destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2.
  split_and!; [done|by eapply LVrel_down|exact (IH _ _ Hg)].
Qed.

Lemma lgrounding_ext n W Θ Δ γ γ' :
  (∀ i, γ i = γ' i) → lgrounding n W Θ Δ γ → lgrounding n W Θ Δ γ'.
Proof.
  revert Θ γ γ'. induction Δ as [|[T|] Δ IH]; intros Θ γ γ' Hγ Hg; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|by rewrite <-Hγ|].
    eapply IH; [|exact Hg]. intros i. apply Hγ.
  - eapply IH; [|exact Hg]. intros i. apply Hγ.
Qed.

Lemma lgrounding_split n W Θ Δ Δ1 Δ2 γ :
  lenv_split Δ Δ1 Δ2 → lgrounding n W Θ Δ γ →
  ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ lgrounding n W Θ1 Δ1 γ ∧ lgrounding n W Θ2 Δ2 γ.
Proof.
  intros Hsp. pose proof eq_rdsym as Hs.
  revert Θ γ. induction Hsp as [|Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|U Δ Δ1 Δ2 HU Hsp IH];
    intros Θ γ Hg; simpl in *.
  - subst. exists ∅, ∅. split_and!; [apply tenv_comp_empty_r|done|done].
  - by apply IH.
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) Hc') as [HX HY].
    eexists _, Θ2. split_and!; [exact HY| |done].
    exists Θa, Θ1. split_and!; [by apply comp_comm|done|done].
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) (comp_comm _ _ _ _ Hs Hc'))
      as [HX HY].
    eexists Θ1, _. split_and!; [by apply comp_comm|done|].
    exists Θa, Θ2. split_and!; [by apply comp_comm|done|done].
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    pose proof (LVrel_unl_empty _ _ _ _ _ HU HV) as ->.
    apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    exists Θ1, Θ2. split_and!; [done| |].
    + exists ∅, Θ1. split_and!; [by apply tenv_comp_empty_l|done|done].
    + exists ∅, Θ2. split_and!; [by apply tenv_comp_empty_l|done|done].
Qed.

(** ** The elimination skeleton *)

Lemma lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 Th T (f : (nat → expr) → frame) :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → (∀ γ, frame_val (f γ)) →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 Th →
  (∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' → lgrounding n W' Θ' Δ2 γ →
     ∀ W'' j Θ1' Θ3 v, wext W' W'' → j ≤ n → tenv_comp (w_eq W'') Θ3 Θ1' Θ'' →
       LVrel j W'' Θ1' Th v → LErel j W'' Θ3 T F (fill_frame (f γ) v)) →
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' → lgrounding n W' Θ' Δ γ →
    LErel n W' Θ'' T F (fill_frame (f γ) (subst γ e1)).
Proof.
  intros Hc Hsp Hf He1 HK n W' Θ' Θ'' γ HW Hc'' Hg.
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgrounding_split _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  eapply (LErel_bind n (f γ) W' Θ'' A B Th T F (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))).
  - apply Hf.
  - apply HW.
  - done.
  - apply heads_above_x_bot. intros Hb.
    eapply heads_above_comp; [exact HB|by apply heads_above_self|by eapply lgrounding_heads].
  - by apply (He1 n W' Θ'1 A γ).
  - intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. by eapply (HK n W' Θ'2 B γ).
Qed.

(** ** E-Inj *)

Lemma lsem_typed_inj1 W Θ Δ F e T U :
  lsem_typed W Θ Δ F e T → lsem_typed W Θ Δ F (Inj1 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj1 (subst γ e)) with (fill_frame FInj1 (subst γ e)).
  eapply (LErel_bind n FInj1 W' Θ'' Θ'' ∅ T _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply LVrel_LErel. simpl.
  apply LVrel_sum_iff. left. eauto.
Qed.

Lemma lsem_typed_inj2 W Θ Δ F e T U :
  lsem_typed W Θ Δ F e U → lsem_typed W Θ Δ F (Inj2 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj2 (subst γ e)) with (fill_frame FInj2 (subst γ e)).
  eapply (LErel_bind n FInj2 W' Θ'' Θ'' ∅ U _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply LVrel_LErel. simpl.
  apply LVrel_sum_iff. right. eauto.
Qed.

Lemma lsem_typed_later W Θ2 Δ2 F e T n W' Θ' Θ'' γ W'' j :
  lsem_typed W Θ2 Δ2 F e T → wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' →
  lgrounding n W' Θ' Δ2 γ → wext W' W'' → j ≤ n →
  LErel j W'' Θ'' T F (subst γ e).
Proof.
  intros He HW Hc Hg HW'' Hj. apply (He j W'' Θ' Θ'' γ).
  - by eapply wext_trans.
  - exact Hc.
  - eapply lgrounding_down; [exact Hj|]. by eapply lgrounding_mono.
Qed.

(** ** E-Let* *)

Lemma lsem_typed_letu W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 TUnit →
  lsem_typed W Θ2 Δ2 F e2 T →
  lsem_typed W Θ Δ F (LetU e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetU (subst γ e1) (subst γ e2)) with (fill_frame (FLetU (subst γ e2)) (subst γ e1)).
  eapply (lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 TUnit T (λ γ, FLetU (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  apply LVrel_unit_iff in HV as [-> ->].
  apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc3 as ->.
  apply (LErel_det_beta _ _ _ _ _ _ (subst γ e2)).
  - apply TStepHead, HeadLetU.
  - intros α e'' Hst. apply tstep_letu_inv in Hst as [(e1' & Hst & _)|(_ & -> & ->)]; [|done].
    exfalso. by eapply val_no_tstep.
  - by eapply lsem_typed_later.
Qed.

(** ** E-LetPair *)

Lemma lsem_typed_letp W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TProd T1 T2) →
  lsem_typed W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
  lsem_typed W Θ Δ F (LetP e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetP (subst γ e1) (subst (up (up γ)) e2))
    with (fill_frame (FLetP (subst (up (up γ)) e2)) (subst γ e1)).
  eapply (lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 (TProd T1 T2) T (λ γ, FLetP (subst (up (up γ)) e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2.
  apply LVrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hcab & HV1 & HV2).
  pose proof (LVrel_val _ _ _ _ _ HV1) as Hv1. pose proof (LVrel_val _ _ _ _ _ HV2) as Hv2.
  destruct (comp_bind2 _ _ _ _ _ _ _ _ eq_rdsym Hc3 Hcab Hc') as (X & A & HX & HXA & HA).
  apply (LErel_det_beta _ _ _ _ _ _ (subst2 v1 v2 (subst (up (up γ)) e2))).
  - by apply TStepHead, HeadLetP.
  - intros α e'' Hst. apply tstep_letp_inv in Hst as [(e1' & Hst & _)|(u & w & Heq & _ & _ & -> & ->)].
    + exfalso. eapply val_no_tstep; [exact Hst|]. simpl. by apply andb_True.
    + by injection Heq as -> ->.
  - rewrite subst2_subst. apply (He2 j W'' X Θ3); [done|done|].
    exists Θb, A. split_and!; [done|done|].
    exists Θa, Θ'. split_and!; [done|done|].
    eapply lgrounding_ext; [|eapply lgrounding_down; [exact Hj|]].
    { intros i. done. }
    eapply lgrounding_mono; [exact HW''|exact Hg].
Qed.

(** ** E-Case *)

Lemma lsem_typed_case W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e (TSum T1 T2) →
  lsem_typed W Θ2 (Some T1 :: Δ2) F e1 T →
  lsem_typed W Θ2 (Some T2 :: Δ2) F e2 T →
  lsem_typed W Θ Δ F (Case e e1 e2) T.
Proof.
  intros Hc Hsp He He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Case (subst γ e) (subst (up γ) e1) (subst (up γ) e2))
    with (fill_frame (FCase (subst (up γ) e1) (subst (up γ) e2)) (subst γ e)).
  eapply (lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e (TSum T1 T2) T
            (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc3) (comp_comm _ _ _ _ Hs Hc'))
    as [HX HY].
  assert (lgrounding j W'' Θ' Δ2 γ) as Hg'.
  { eapply lgrounding_down; [exact Hj|]. eapply lgrounding_mono; [exact HW''|exact Hg]. }
  apply LVrel_sum_iff in HV as [(w & -> & HVw)|(w & -> & HVw)];
    pose proof (LVrel_val _ _ _ _ _ HVw) as Hw.
  - apply (LErel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e1))).
    + by apply TStepHead, HeadCase1.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _ & -> & ->)|(u & Heq & _)]]; [|by injection Heq as ->|done].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He1 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgrounding_ext; [|exact Hg']. done.
  - apply (LErel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e2))).
    + by apply TStepHead, HeadCase2.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _)|(u & Heq & _ & -> & ->)]]; [|done|by injection Heq as ->].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He2 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgrounding_ext; [|exact Hg']. done.
Qed.

(** ** E-Pair *)

Lemma lsem_typed_pair W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 T →
  lsem_typed W Θ2 Δ2 (F ∪ (heads T ∪ bot_pts (hbot T))) e2 U →
  lsem_typed W Θ Δ F (Pair e1 e2) (TProd T U).
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Pair (subst γ e1) (subst γ e2)) with (fill_frame (FPairL (subst γ e2)) (subst γ e1)).
  eapply (lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 T (TProd T U) (λ γ, FPairL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  pose proof (LVrel_val _ _ _ _ _ HV1) as Hv1.
  change (Pair v1 (subst γ e2)) with (fill_frame (FPairR v1) (subst γ e2)).
  eapply (LErel_bind j (FPairR v1) W'' Θ3 Θ'' Θ1' U (TProd T U) F (heads T ∪ bot_pts (hbot T))).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - apply heads_above_x_bot. intros Hb. eapply LVrel_heads_above; [exact (wext_wf _ _ HW2)|exact Hb|exact HV1].
  - exact (lsem_typed_later _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2. apply LVrel_LErel. simpl.
    apply LVrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; [done| | |done].
    { apply comp_comm; [exact Hs|exact Hc4]. }
    eapply LVrel_down; [exact Hj'|]. exact (LVrel_mono _ _ _ _ _ _ HW3 HV1).
Qed.

(** ** Channels of a grounding *)

Lemma lgrounding_fchans n W Θ Δ γ x T :
  lgrounding n W Θ Δ γ → Δ !! x = Some (Some T) → fchans (γ x) ⊆ dom Θ.
Proof.
  revert Θ γ x. induction Δ as [|[T0|] Δ IH]; intros Θ γ x Hg Hx; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_dom _ _ _ Hj).
    destruct x as [|x]; simpl in Hx.
    + rewrite (LVrel_fchans _ _ _ _ _ HV). set_solver.
    + pose proof (IH _ _ _ Hg Hx). set_solver.
  - destruct x as [|x]; simpl in Hx; [done|]. exact (IH _ _ _ Hg Hx).
Qed.

Lemma lgrounding_dom n W Θ Δ γ ch :
  lgrounding n W Θ Δ γ → ch ∈ dom Θ →
  ∃ x T, Δ !! x = Some (Some T) ∧ ¬ unlimited T ∧ ch ∈ fchans (γ x).
Proof.
  revert Θ γ. induction Δ as [|[T0|] Δ IH]; intros Θ γ Hg Hch; simpl in *.
  - subst. rewrite dom_empty_L in Hch. set_solver.
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_dom _ _ _ Hj) in Hch.
    apply elem_of_union in Hch as [Hch|Hch].
    + exists 0, T0. split_and!; [done| |].
      * intros Hu. rewrite (LVrel_unl_empty _ _ _ _ _ Hu HV), dom_empty_L in Hch. set_solver.
      * by rewrite (LVrel_fchans _ _ _ _ _ HV).
    + destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
  - destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
Qed.

(** ** E-Abs

    The arrow reads the body at every j ≤ n, the current index
    included, so the body is read at j itself. *)

Lemma lsem_typed_lam W Θ Δ F e T U ub lb :
  term_wf Θ (Some T :: Δ) e →
  lenv_bot Δ = false →
  lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
  (∀ W1 F', wext W W1 → ub_below W1 ub F' → lsem_typed W1 Θ (Some T :: Δ) F' e U) →
  lsem_typed W Θ Δ F (Lam e) (TLolli ub lb T U).
Proof.
  intros (Hfc & Hfv & Hrel) Hbot Hlb He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  apply LVrel_LErel, LVrel_lolli_iff. left. exists (subst (up γ) e). split_and!; [done| | |].
  - rewrite (tenv_join_dom _ _ _ (proj1 Hc)). apply set_eq. intros ch. split.
    + intros Hch.
      assert (fchans (subst (up γ) e) ⊆ fchans e ∪ dom Θ') as Hsub.
      { apply fchans_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
        - intros _. set_solver.
        - intros (T' & Hx). unfold compose. rewrite fchans_rename. by eapply lgrounding_fchans. }
      rewrite <-Hfc. set_solver.
    + intros [Hch|Hch]%elem_of_union.
      * apply fchans_subst_super. by rewrite Hfc.
      * destruct (lgrounding_dom _ _ _ _ _ _ Hg Hch) as (x & T' & Hx & Hu & Hin).
        assert (freevar (S x) e) as Hfree by (apply Hrel; by exists T').
        pose proof (fchans_subst_free e (S x) (up γ) Hfree) as Hsub. simpl in Hsub.
        unfold compose in Hsub. rewrite fchans_rename in Hsub. set_solver.
  - assert (∀ h, h ∈ tenv_heads Θ'' → (h ∈ tenv_heads Θ ∨ ∃ h', h' ∈ lenv_heads Δ ∧ w_le W' h' h))
      as Hh.
    { intros h (k & e0 & He0 & ->)%elem_of_tenv_heads_entry.
      destruct (comp_entry _ _ _ _ _ _ Hc He0) as [[k' Hk]|[k' Hk]].
      - left. apply elem_of_tenv_heads_entry. eauto.
      - right. exact (lgrounding_heads _ _ _ _ _ HW' Hbot Hg _ _ Hk). }
    pose proof (lb_below_mono _ _ _ _ HW Hlb) as Hlb'.
    destruct lb as [l|]; simpl in *.
    + intros h Hin. destruct (Hh h Hin) as [Hin'|(h' & Hh' & Hle)].
      * apply Hlb'. set_solver.
      * eapply le_le_W; [exact HW'| |exact Hle]. apply Hlb'. set_solver.
    + apply set_eq. intros h. split; [|set_solver]. intros Hin.
      destruct (Hh h Hin) as [Hin'|(h' & Hh' & _)]; set_solver.
  - intros W2 j Θa Θb w F' HW2 Hj Hcb Hub HVw. rewrite subst1_subst.
    pose proof (wext_trans _ _ _ HW HW2) as HWW2.
    destruct (comp_assoc _ _ _ _ _ _ Hs Hcb (comp_comm _ _ _ _ Hs Hc)) as [HX HY].
    apply (He W2 F' HWW2 Hub j W2 (tjoin_as Θb Θ' Θa) Θb).
    + by apply wext_refl, HWW2.
    + by apply comp_comm.
    + exists Θa, Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgrounding_ext; [|eapply lgrounding_down; [|eapply lgrounding_mono; [exact HW2|exact Hg]]].
      * done.
      * lia.
Qed.

(** ** Applying a value to a value *)

Lemma LErel_app_force n W Θ ub lb T U F v2 :
  strict W → LVrel n W ∅ (TLolli ub lb T U) EForce → LVrel n W Θ T v2 → ub_below W ub F →
  LErel n W Θ U F (App EForce v2).
Proof.
  intros HW HV1 HV2 Hub.
  destruct (Lkonst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hu & HB & HV).
  inversion Hk as [kq Tq Gq xs Hsig HC1 HK1| |]; subst.
  inversion Hsig as [| | | | | | | |m kk C1 ub1 T1 ? ss Hxs Hss Hsc]; subst.
  apply facts_hold_bcs_at in HC1.
  pose proof HV as HV'. apply LVrel_box_iff in HV as (-> & eb & -> & _).
  eapply LErel_tconv; [apply HW|exact HB|].
  apply (LErel_force _ _ _ _ _ _ _ _ _ xs ss HW HV'); [done|done|done|done|done|].
  eapply ub_below_conv; [apply HW| |exact Hub]. by apply opt_rel_sym; [apply HW|].
Qed.

Lemma LErel_app n W Θ Θ1 Θ2 ub lb T U F v1 v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  LVrel n W Θ1 (TLolli ub lb T U) v1 → LVrel n W Θ2 T v2 → ub_below W ub F →
  LErel n W Θ U F (App v1 v2).
Proof.
  intros HW Hc HV1 HV2 Hub.
  destruct (decide (v1 = EForce)) as [->|Hnf]; [|by eapply LErel_app_noforce].
  destruct (proj1 (LVrel_lolli_iff _ _ _ _ _ _ _ _) HV1) as [(eb & ? & _)|(k & T0 & _ & -> & _)];
    [done|].
  apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->. by eapply LErel_app_force.
Qed.

(** ** E-App *)

Lemma lsem_typed_app W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TLolli ub lb T U) →
  lsem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  lsem_typed W Θ Δ F (App e1 e2) U.
Proof.
  intros Hc Hsp Hub He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (App (subst γ e1) (subst γ e2)) with (fill_frame (FAppL (subst γ e2)) (subst γ e1)).
  eapply (lsem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 (TLolli ub lb T U) U (λ γ, FAppL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  pose proof (LVrel_val _ _ _ _ _ HV1) as Hv1.
  change (App v1 (subst γ e2)) with (fill_frame (FAppR v1) (subst γ e2)).
  eapply (LErel_bind j (FAppR v1) W'' Θ3 Θ'' Θ1' T U F (opt_heads lb)).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - left. eapply (LVrel_heads_above _ _ _ (TLolli ub lb T U)); [exact (wext_wf _ _ HW2)|done|exact HV1].
  - exact (lsem_typed_later _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2.
    pose proof (wext_trans _ _ _ HW2 HW3) as HW4.
    apply (LErel_app j' W3 Θ4 Θ1' Θ2' ub lb T U); [apply HW4| | |done|].
    + apply comp_comm; [exact Hs|exact Hc4].
    + eapply LVrel_down; [exact Hj'|]. exact (LVrel_mono _ _ _ _ _ _ HW3 HV1).
    + eapply ub_below_mono; [exact HW4|exact Hub].
Qed.

(** ** The rules without elimination of a function *)

Lemma lgrounding_lenv_empty n W Θ Δ γ : lenv_empty Δ → lgrounding n W Θ Δ γ → Θ = ∅.
Proof.
  revert Θ γ. induction Δ as [|o Δ IH]; intros Θ γ He Hg; simpl in *; [done|].
  destruct o as [T|].
  - exfalso. assert (Some T = None) by (apply He; set_solver). done.
  - apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply He. set_solver.
Qed.

Lemma lgrounding_only n W Θ Δ γ x T :
  lenv_only Δ x T → lgrounding n W Θ Δ γ → LVrel n W Θ T (γ x).
Proof.
  revert Θ γ x. induction Δ as [|o Δ IH]; intros Θ γ x [Hx Honly] Hg; simpl in *.
  - done.
  - destruct x as [|x]; simpl in Hx.
    + injection Hx as ->. destruct Hg as (Θa & Θr & Hc & HV & Hg).
      assert (lenv_empty Δ) as He.
      { intros o Ho. destruct o as [U|]; [|done]. exfalso.
        apply list_elem_of_lookup in Ho as [i Hi].
        destruct (Honly (S i) U Hi) as [? _]. done. }
      rewrite (lgrounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
      by apply tenv_comp_empty_r_inv in Hc as ->.
    + destruct o as [U|].
      * exfalso. by destruct (Honly 0 U eq_refl).
      * apply (IH Θ (γ ∘ S) x); [|done]. split; [done|].
        intros y T' Hy. destruct (Honly (S y) T' Hy) as [Hy' ->]. split; [congruence|done].
Qed.

Lemma lsem_typed_unit W Δ F : lenv_empty Δ → lsem_typed W ∅ Δ F EUnit TUnit.
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. rewrite (lgrounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_inv in Hc as ->. apply LVrel_LErel. by apply LVrel_unit_iff.
Qed.

Lemma lsem_typed_konst W Δ F k T :
  lenv_empty Δ → konst_ty (w_eq W) (w_lt W) (pt_known W) k T →
  lsem_typed W ∅ Δ F (Konst k) T.
Proof.
  intros He Hk n W' Θ' Θ'' γ HW Hc Hg. rewrite (lgrounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_inv in Hc as ->. apply LVrel_LErel. simpl.
  destruct HW as (Hn & Heq & Hlt & _).
  assert (konst_ty (w_eq W') (w_lt W') (pt_known W') k T) as Hk'.
  { eapply konst_ty_mono; [| | |exact Hk]; [done|done|]. unfold pt_known. intros x Hx. by apply Hn. }
  assert (∃ ub lb A B, T = TLolli ub lb A B) as (ub & lb & A & B & ->)
    by (destruct Hk' as [? ? ? ? Hs ? ?| |]; [destruct Hs| |]; eauto).
  apply LVrel_lolli_iff; right; eexists _, _; split_and!; [done|done|exact Hk'|apply teqW_refl].
Qed.

Lemma lsem_typed_var W Δ F x T : lenv_only Δ x T → lsem_typed W ∅ Δ F (Var x) T.
Proof.
  intros Ho n W' Θ' Θ'' γ HW Hc Hg. simpl.
  apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->.
  apply LVrel_LErel. by eapply lgrounding_only.
Qed.

Lemma lsem_typed_chan W Δ F c s k s' y :
  lenv_empty Δ → seq s s' → w_eq W k y →
  lsem_typed W {[c := One (s, k)]} Δ F (Chan c) (TSess s' y).
Proof.
  intros He Hs Hk n W' Θ' Θ'' γ HW Hc Hg. rewrite (lgrounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_r_inv in Hc as ->. apply LVrel_LErel. simpl.
  apply LVrel_sess_iff. exists c, s, k. by split_and!.
Qed.

(** ** E-Weak, E-Conv, E-Contract *)

Lemma lgrounding_wk n W Θ Δ' Δ γ :
  lenv_wk Δ' Δ → lgrounding n W Θ Δ γ → lgrounding n W Θ Δ' γ.
Proof.
  intros Hwk. revert Θ γ.
  induction Hwk as [|[T|] Δ' Δ Hwk IH|U Δ' Δ HU Hwk IH]; intros Θ γ Hg; simpl in *.
  - done.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|done|by apply IH].
  - by apply IH.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    rewrite (LVrel_unl_empty _ _ _ _ _ HU HV) in Hc.
    apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->. by apply IH.
Qed.

Lemma lsem_typed_wk W Θ Δ' Δ F e T :
  lenv_wk Δ' Δ → lsem_typed W Θ Δ' F e T → lsem_typed W Θ Δ F e T.
Proof.
  intros Hwk He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc). by eapply lgrounding_wk.
Qed.

Lemma lsem_typed_conv W Θ Δ F e T T' :
  teqW W T T' → lsem_typed W Θ Δ F e T → lsem_typed W Θ Δ F e T'.
Proof.
  intros Ht He n W' Θ' Θ'' γ HW Hc Hg. eapply LErel_tconv; [exact (wext_wf _ _ HW)| |by apply (He n W' Θ')].
  eapply teqW_mono; [|exact Ht]. intros x y H. exact H.
Qed.

Lemma lgrounding_contract n W Θ Δ U γ :
  unlimited U → lgrounding n W Θ (Some U :: Δ) γ →
  lgrounding n W Θ (Some U :: Some U :: Δ) (λ x, γ (pred x)).
Proof.
  intros Hu Hg. pose proof Hg as Hg0. simpl in Hg.
  destruct Hg as (Θ1 & Θ2 & Hc & HV & _).
  pose proof (LVrel_unl_empty _ _ _ _ _ Hu HV) as ->.
  exists ∅, Θ. split_and!.
  - apply tenv_comp_empty_l, eq_rdsym.
  - exact HV.
  - eapply lgrounding_ext; [|exact Hg0]. by intros [|i].
Qed.

Lemma lsem_typed_contract W Θ Δ U F e T :
  unlimited U →
  lsem_typed W Θ (Some U :: Some U :: Δ) F e T →
  lsem_typed W Θ (Some U :: Δ) F (rename pred e) T.
Proof.
  intros Hu He n W' Θ' Θ'' γ HW Hc Hg. rewrite subst_rename.
  apply (He n W' Θ' Θ'' (λ x, γ (pred x))); [done|done|]. by apply lgrounding_contract.
Qed.

(** ** E-Force *)

Lemma lsem_typed_force W Θ Δ F e m k C ub T xs ss :
  world_wf W → length xs = m → bcs_hold (w_eq W) (w_lt W) C xs → Forall (pt_known W) xs →
  length ss = k → Forall hcontractive ss →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  lsem_typed W Θ Δ F e (TBox m k C (TLolli ub None TUnit T)) →
  lsem_typed W Θ Δ F (App EForce e) (sinst_ty (slist ss) (ty_inst xs T)).
Proof.
  intros HW Hxs HC HK Hss Hsc Hub He.
  eapply (lsem_typed_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, eq_rdsym.
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply lsem_typed_konst; [apply lenv_empty_nones|]. by apply KTForce.
  - simpl. by rewrite union_empty_r_L.
Qed.

(** ** E-Pack and E-Open *)

Lemma new_place_wext_r W N x W' : new_place W N x W' → wext_r W W'.
Proof. intros [(a & _ & _ & Hfr)|(_ & ->)]; [right; apply Hfr|left; done]. Qed.

(** E at T' from E at T, when V at T is contained in V at T' at every
    level up to n and in every later world. *)
Lemma LErel_Vsub n : ∀ W Θ T T' F e,
  (∀ j W' Θ' v, j ≤ n → wext_r W W' → LVrel j W' Θ' T v → LVrel j W' Θ' T' v) →
  LErel n W Θ T F e → LErel n W Θ T' F e.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  destruct n as [|n']; [intros; apply LErel_0|].
  intros W Θ T T' F e HV HE. revert T' HV.
  revert W Θ T F e HE.
  refine (LErel_S_ind n' (λ W Θ T F e, ∀ T',
            (∀ j W' Θ' v, j ≤ S n' → wext_r W W' → LVrel j W' Θ' T v → LVrel j W' Θ' T' v) →
            LErel (S n') W Θ T' F e) _).
  intros W Θ T F e H T' HV. apply LErel_S_iff. intros W1 HW1.
  assert (∀ W2, wext_r W1 W2 →
            ∀ j W' Θ' v, j ≤ S n' → wext_r W2 W' → LVrel j W' Θ' T v → LVrel j W' Θ' T' v) as HV2.
  { intros W2 HW2 j W' Θ' v Hj HW' HVv. apply HV; [done| |done].
    eapply wext_r_trans; [exact HW1|]. by eapply wext_r_trans. }
  assert (∀ j W0 Θ0 F0 e0, j ≤ n' → wext_r W1 W0 →
            LErel j W0 Θ0 T F0 e0 → LErel j W0 Θ0 T' F0 e0) as HEj.
  { intros j W0 Θ0 F0 e0 Hj HW0. apply (IHn j ltac:(lia)).
    intros i W' Θ' v Hi HW'. apply (HV2 W0 HW0); [lia|done]. }
  destruct (H W1 HW1) as (Hs & Hr & Hb & Hnew & Hsp & Hσ).
  split_and!.
  - intros Hirr. apply (HV2 W1 (wext_r_refl _)); [lia|apply wext_r_refl|by apply Hs].
  - done.
  - intros e' Hst. destruct (Hb e' Hst) as [_ HΦ]. apply HΦ.
    intros j W' Θ' v Hj HW' HVv. apply (HV2 W1 (wext_r_refl _)); [done|done|done].
  - intros c e' Hst Hc L.
    destruct (Hnew c e' Hst Hc (L ∪ ty_roots T')) as (x & s & s' & W' & Hpl & Hdu & _ & HΦ).
    exists x, s, s', W'. split_and!; [eapply new_place_sub; [|exact Hpl]; set_solver|done|].
    apply HΦ. intros j W'' Θ' v Hj HW'' HVv.
    apply (HV2 W' (new_place_wext_r _ _ _ _ Hpl)); [done|done|done].
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & _ & HΦ).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |].
    + eapply Vspawn_mono; [|exact Hv]. by intros ? ? ? ? [? _].
    + apply HΦ. intros j W' Θ' v Hj HW' HVv. apply (HV2 W1 (wext_r_refl _)); [done|done|done].
  - intros σ e' Hst. pose proof (Hσ σ e' Hst) as Hc.
    destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LEobl pred] in Hc |- *.
    + destruct Hc as (Θ1 & m & U & s & k & Hhd & H').
      exists Θ1, m, U, s, k. split; [done|].
      intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hc HVw.
      eapply HEj; [lia|by right|by apply (H' W' j Θ2 Θ1c Θ')].
    + destruct Hc as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & ? & ? & ? & ? & HE').
      exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done.
      eapply HEj; [lia|apply wext_r_refl|exact HE'].
    + destruct Hc as (Θ1 & k & ? & HE'). exists Θ1, k. split; [done|].
      eapply HEj; [lia|apply wext_r_refl|exact HE'].
    + destruct Hc as (c & d & Θ1 & Θm & sc & sd & kc & kd & -> & ? & ? & ? & ? & HE').
      exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; try done.
      eapply HEj; [lia|apply wext_r_refl|exact HE'].
    + destruct Hc as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
      exists Θr, s1, s2, k, Θ'. split_and!; try done.
      eapply HEj; [lia|apply wext_r_refl|exact HE'].
    + destruct Hc as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
      exists Θr, s1, s2, k, Θ'. split_and!; try done.
      eapply HEj; [lia|apply wext_r_refl|exact HE'].
Qed.

Lemma lsem_typed_pack W Θ Δ F e lb m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  lbx_below W lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  lsem_typed W Θ Δ F e (ty_inst xs T) → lsem_typed W Θ Δ F e (TEx lb m C T).
Proof.
  intros Hxs HK HC Hlb He n W' Θ' Θ'' γ HW Hc Hg.
  eapply LErel_Vsub; [|by apply (He n W' Θ' Θ'' γ)].
  intros j W2 Θ2 v Hj HW2 HV.
  assert (wext W W2) as HWW2 by (destruct HW2 as [->|HW2]; [done|by eapply wext_trans]).
  pose proof (wext_wf _ _ HWW2) as HW2f.
  apply LVrel_ex_iff. split; [|exists xs; split_and!; [done| | |done]].
  - pose proof (lbx_below_mono _ _ _ _ _ HWW2 Hlb) as Hlb2.
    destruct lb as [| |x]; simpl in *; [|done|].
    + destruct Hlb2 as [Hlb2 Hb]. pose proof (LVrel_heads_above _ _ _ _ _ HW2f Hb HV) as Hab.
      split; [|done]. apply set_eq. intros y. split; [|set_solver].
      intros (k & e0 & Hk & ->)%elem_of_tenv_heads_entry.
      destruct (Hab k e0 Hk) as (h & Hh & _). set_solver.
    + destruct Hlb2 as [Hlb2 Hb]. pose proof (LVrel_heads_above _ _ _ _ _ HW2f Hb HV) as Hab.
      split; [|done]. intros y (k & e0 & Hk & ->)%elem_of_tenv_heads_entry.
      destruct (Hab k e0 Hk) as (h & Hh & Hle). eapply le_le_W; [done| |exact Hle]. by apply Hlb2.
  - eapply Forall_impl; [exact HK|]. intros x. unfold pt_known. destruct HWW2 as (? & _). set_solver.
  - destruct HWW2 as (_ & He2 & Hl2 & _). eapply bcs_hold_mono; [exact He2|exact Hl2|exact HC].
Qed.

Lemma lgrounding_open n W Θ Δ γ i lb m C T :
  Δ !! i = Some (Some (TEx lb m C T)) → lgrounding n W Θ Δ γ →
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    lgrounding n W Θ (<[i := Some (ty_inst xs T)]> Δ) γ.
Proof.
  revert i Θ γ. induction Δ as [|o Δ IH]; intros i Θ γ Hi Hg; [done|].
  destruct i as [|i]; simpl in Hi.
  - injection Hi as ->. simpl in Hg. destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    apply LVrel_ex_iff in HV as [_ (xs & Hxs & HK & HC & HV)].
    exists xs. split_and!; [done..|]. simpl. by exists Θ1, Θ2.
  - destruct o as [U|]; simpl in Hg.
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
      destruct (IH i Θ2 (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
      exists xs. split_and!; [done..|]. simpl. by exists Θ1, Θ2.
    + destruct (IH i Θ (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
      exists xs. by split_and!.
Qed.

Lemma lsem_typed_open W Θ Δ F e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     lsem_typed W1 Θ (<[i := Some (ty_inst xs T)]> Δ) F e U) →
  lsem_typed W Θ Δ F e U.
Proof.
  intros Hi He n W' Θ' Θ'' γ HW Hc Hg.
  destruct (lgrounding_open _ _ _ _ _ _ _ _ _ _ Hi Hg) as (xs & Hxs & HK & HC & Hg').
  apply (He W' xs HW Hxs HK HC n W' Θ' Θ'' γ); [|done|done].
  apply wext_refl. by destruct HW as (_&_&_&?).
Qed.
