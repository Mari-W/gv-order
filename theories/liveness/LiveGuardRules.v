(** * The rules of the later judgment (liveness.md §10)

    One lemma per clause of the guard [ok] (Guard.v). A variable marked
    later in Δ is in V only below the current index. A form whose parts
    all carry the mark binds at the current index, as in LiveTermRules.v.
    A guarded hole ([gd]) binds with a continuation below the index, so
    the continuation reads every variable now, one level down. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveGuard.

Set Default Proof Using "All".
Local Set Warnings "-register-all".

(** ** Groundings with marks *)

Lemma lsem_later_extL W Θ Δ Lm Lm' F e T :
  (∀ i, Lm i = Lm' i) → lsem_later W Θ Δ Lm F e T → lsem_later W Θ Δ Lm' F e T.
Proof.
  intros HL He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc).
  eapply lgroundingL_extL; [|exact Hg]. intros i. by rewrite HL.
Qed.

Lemma lsem_later_of_typed W Θ Δ Lm F e T :
  (∀ i, Lm i = None) → lsem_typed W Θ Δ F e T → lsem_later W Θ Δ Lm F e T.
Proof.
  intros HL He. apply (lsem_later_extL _ _ _ noL); [done|]. by apply lsem_later_now.
Qed.

(** No marked variable is available in Δ. *)
Definition lfree (Δ : lenv) (Lm : lmark) : Prop :=
  ∀ i T, Δ !! i = Some (Some T) → Lm i = None.

Lemma lgroundingL_free n W Θ Δ Lm γ :
  lfree Δ Lm → lgroundingL n W Θ Δ Lm γ → lgrounding n W Θ Δ γ.
Proof.
  revert Θ Lm γ. induction Δ as [|[T|] Δ IH]; intros Θ Lm γ Hf Hg; simpl in *; [done| |].
  - rewrite (Hf 0 T eq_refl) in Hg. destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    exists Θ1, Θ2. split_and!; [done|done|]. apply (IH _ (Lm ∘ S)); [|done].
    intros i T' Hi. apply (Hf (S i) T' Hi).
  - apply (IH _ (Lm ∘ S)); [|done]. intros i T' Hi. apply (Hf (S i) T' Hi).
Qed.

Lemma lsem_later_free W Θ Δ Lm F e T :
  lfree Δ Lm → lsem_typed W Θ Δ F e T → lsem_later W Θ Δ Lm F e T.
Proof.
  intros Hf He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc). by eapply lgroundingL_free.
Qed.

Lemma lfree_empty Δ Lm : lenv_empty Δ → lfree Δ Lm.
Proof. intros He i T Hi. exfalso. assert (Some T = None) by (apply He; by eapply list_elem_of_lookup_2). done. Qed.

Lemma lfree_only Δ Lm x T : lenv_only Δ x T → Lm x = None → lfree Δ Lm.
Proof. intros [_ Ho] Hx i T' Hi. by destruct (Ho i T' Hi) as [-> _]. Qed.

(** The resources of a grounding come from the linear variables read now. *)
Lemma lgroundingL_empty n W Θ Δ Lm γ :
  (∀ x T, Δ !! x = Some (Some T) → ¬ unlimited T → Lm x ≠ None) →
  lgroundingL n W Θ Δ Lm γ → Θ = ∅.
Proof.
  revert Θ Lm γ. induction Δ as [|[T|] Δ IH]; intros Θ Lm γ Hl Hg; simpl in *; [done| |].
  - destruct (Lm 0) as [lam|] eqn:HL0.
    + destruct Hg as (_ & _ & Hg). apply (IH _ (Lm ∘ S) (γ ∘ S)); [|done].
      intros x T' Hx. apply (Hl (S x) T' Hx).
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
      assert (unlimited T) as Hu.
      { destruct T; simpl; try done; exfalso; (apply (Hl 0 _ eq_refl); [intros []|exact HL0]). }
      rewrite (LVrel_unl_empty _ _ _ _ _ Hu HV) in Hc.
      apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->.
      apply (IH _ (Lm ∘ S) (γ ∘ S)); [|done]. intros x T' Hx. apply (Hl (S x) T' Hx).
  - apply (IH _ (Lm ∘ S) (γ ∘ S)); [|done]. intros x T' Hx. apply (Hl (S x) T' Hx).
Qed.

Lemma lgroundingL_later n W Θ Δ Lm γ x T lam :
  Δ !! x = Some (Some T) → Lm x = Some lam → lgroundingL n W Θ Δ Lm γ →
  later_val n W lam T (γ x).
Proof.
  revert Θ Lm γ x. induction Δ as [|[T0|] Δ IH]; intros Θ Lm γ x Hx HL Hg; simpl in *; [done| |].
  - destruct x as [|x]; simpl in Hx.
    + injection Hx as ->. rewrite HL in Hg. by destruct Hg as (_ & ? & _).
    + destruct (Lm 0); [destruct Hg as (_ & _ & Hg)|destruct Hg as (? & ? & _ & _ & Hg)];
        exact (IH _ (Lm ∘ S) (γ ∘ S) x Hx HL Hg).
  - destruct x as [|x]; simpl in Hx; [done|]. exact (IH _ (Lm ∘ S) (γ ∘ S) x Hx HL Hg).
Qed.

(** ** E-Weak, E-Contract, E-Open, E-Conv, E-Pack with marks *)

Lemma lgroundingL_wk n W Θ Δ' Δ Lm γ :
  lenv_wk Δ' Δ → lgroundingL n W Θ Δ Lm γ → lgroundingL n W Θ Δ' Lm γ.
Proof.
  intros Hwk. revert Θ Lm γ.
  induction Hwk as [|[T|] Δ' Δ Hwk IH|U Δ' Δ HU Hwk IH]; intros Θ Lm γ Hg; simpl in *.
  - done.
  - destruct (Lm 0).
    + destruct Hg as (? & ? & Hg). split_and!; [done|done|by apply IH].
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|done|by apply IH].
  - by apply IH.
  - destruct (Lm 0).
    + destruct Hg as (_ & _ & Hg). by apply IH.
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
      rewrite (LVrel_unl_empty _ _ _ _ _ HU HV) in Hc.
      apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->. by apply IH.
Qed.

Lemma lsem_later_wk W Θ Δ' Δ Lm F e T :
  lenv_wk Δ' Δ → lsem_later W Θ Δ' Lm F e T → lsem_later W Θ Δ Lm F e T.
Proof.
  intros Hwk He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc). by eapply lgroundingL_wk.
Qed.

Lemma lsem_later_conv W Θ Δ Lm F e T T' :
  teqW W T T' → lsem_later W Θ Δ Lm F e T → lsem_later W Θ Δ Lm F e T'.
Proof.
  intros Ht He n W' Θ' Θ'' γ HW Hc Hg. eapply LErel_tconv; [exact (wext_wf _ _ HW)| |by apply (He n W' Θ')].
  eapply teqW_mono; [|exact Ht]. intros x y H. exact H.
Qed.

Lemma lgroundingL_contract n W Θ Δ U Lm γ :
  unlimited U → lgroundingL n W Θ (Some U :: Δ) Lm γ →
  lgroundingL n W Θ (Some U :: Some U :: Δ) (λ x, Lm (pred x)) (λ x, γ (pred x)).
Proof.
  intros Hu Hg. pose proof Hg as Hg0. simpl in Hg |- *.
  destruct (Lm 0) as [lam|].
  - destruct Hg as (_ & Hv & Hg). split_and!; [done|done|done|done|].
    eapply lgroundingL_ext; [|eapply lgroundingL_extL; [|exact Hg]]; done.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    pose proof (LVrel_unl_empty _ _ _ _ _ Hu HV) as ->.
    apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->.
    exists ∅, Θ2. split_and!; [apply tenv_comp_empty_l, eq_rdsym|done|].
    exists ∅, Θ2. split_and!; [apply tenv_comp_empty_l, eq_rdsym|done|].
    eapply lgroundingL_ext; [|eapply lgroundingL_extL; [|exact Hg]]; done.
Qed.

Lemma lsem_later_contract W Θ Δ U Lm F e T :
  unlimited U →
  lsem_later W Θ (Some U :: Some U :: Δ) (λ x, Lm (pred x)) F e T →
  lsem_later W Θ (Some U :: Δ) Lm F (rename pred e) T.
Proof.
  intros Hu He n W' Θ' Θ'' γ HW Hc Hg. rewrite subst_rename.
  apply (He n W' Θ' Θ'' (λ x, γ (pred x))); [done|done|]. by apply lgroundingL_contract.
Qed.

Lemma lgroundingL_open n W Θ Δ Lm γ i lb m C T :
  Δ !! i = Some (Some (TEx lb m C T)) → lgroundingL n W Θ Δ Lm γ →
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    lgroundingL n W Θ (<[i := Some (ty_inst xs T)]> Δ) Lm γ.
Proof.
  revert i Θ Lm γ. induction Δ as [|o Δ IH]; intros i Θ Lm γ Hi Hg; [done|].
  destruct i as [|i]; simpl in Hi.
  - injection Hi as ->. simpl in Hg |- *. destruct (Lm 0); [by destruct Hg as ([] & _)|].
    destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    apply LVrel_ex_iff in HV as [_ (xs & Hxs & HK & HC & HV)].
    exists xs. split_and!; [done..|]. by exists Θ1, Θ2.
  - destruct o as [U|]; simpl in Hg |- *.
    + destruct (Lm 0).
      * destruct Hg as (Hu & Hv & Hg).
        destruct (IH i Θ (Lm ∘ S) (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
        exists xs. by split_and!.
      * destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
        destruct (IH i Θ2 (Lm ∘ S) (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
        exists xs. split_and!; [done..|]. by exists Θ1, Θ2.
    + destruct (IH i Θ (Lm ∘ S) (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
      exists xs. by split_and!.
Qed.

Lemma lsem_later_open W Θ Δ Lm F e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     lsem_later W1 Θ (<[i := Some (ty_inst xs T)]> Δ) Lm F e U) →
  lsem_later W Θ Δ Lm F e U.
Proof.
  intros Hi He n W' Θ' Θ'' γ HW Hc Hg.
  destruct (lgroundingL_open _ _ _ _ _ _ _ _ _ _ _ Hi Hg) as (xs & Hxs & HK & HC & Hg').
  apply (He W' xs HW Hxs HK HC n W' Θ' Θ'' γ); [|done|done].
  apply wext_refl. by destruct HW as (_&_&_&?).
Qed.

(** V at T is contained in V at the packed type, at every level. *)
Lemma LVrel_pack W lb m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  lbx_below W lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  ∀ j W2 Θ2 v, wext W W2 → LVrel j W2 Θ2 (ty_inst xs T) v → LVrel j W2 Θ2 (TEx lb m C T) v.
Proof.
  intros Hxs HK HC Hlb j W2 Θ2 v HWW2 HV.
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

(** ** The elimination skeletons *)

Lemma lsem_later_at W Θ2 Δ2 Lm F e T n W' Θ' Θ'' γ W'' j :
  lsem_later W Θ2 Δ2 Lm F e T → wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' →
  lgroundingL n W' Θ' Δ2 Lm γ → wext W' W'' → j ≤ n →
  LErel j W'' Θ'' T F (subst γ e).
Proof.
  intros He HW Hc Hg HW'' Hj. apply (He j W'' Θ' Θ'' γ).
  - by eapply wext_trans.
  - exact Hc.
  - eapply lgroundingL_down; [exact Hj|]. by eapply lgroundingL_mono.
Qed.

Definition lcont (W : world) (Θ2 : tenv) (Δ2 : lenv) (Lm : lmark) (Th T : ty) (F : gset point)
    (f : (nat → expr) → frame) : Prop :=
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' → lgroundingL n W' Θ' Δ2 Lm γ →
    ∀ W'' j Θ1' Θ3 v, wext W' W'' → j ≤ n → tenv_comp (w_eq W'') Θ3 Θ1' Θ'' →
      LVrel j W'' Θ1' Th v → LErel j W'' Θ3 T F (fill_frame (f γ) v).

Lemma lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 Th T (f : (nat → expr) → frame) :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → (∀ γ, frame_val (f γ)) →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 Th →
  lcont W Θ2 Δ2 Lm Th T F f →
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' → lgroundingL n W' Θ' Δ Lm γ →
    LErel n W' Θ'' T F (fill_frame (f γ) (subst γ e1)).
Proof.
  intros Hc Hsp Hf He1 HK n W' Θ' Θ'' γ HW Hc'' Hg.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgroundingL_split _ _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  eapply (LErel_bind (S n') (f γ) W' Θ'' A B Th T F (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))).
  - apply Hf.
  - apply HW.
  - done.
  - apply heads_above_x_bot. intros Hb.
    eapply heads_above_comp; [exact HB|by apply heads_above_self|].
    eapply lgrounding_heads; [exact HW'|exact Hb|]. apply (lgroundingL_lower (S n') n' _ _ _ _ _ ltac:(lia) Hg2).
  - by apply (He1 (S n') W' Θ'1 A γ).
  - intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. by eapply (HK (S n') W' Θ'2 B γ).
Qed.

(** A guarded hole: the continuation reads every variable now. *)
Lemma lsem_later_elim_guarded W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 Th T (f : (nat → expr) → frame) :
  gd e1 = true →
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → (∀ γ, frame_val (f γ)) →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 Th →
  lcont W Θ2 Δ2 noL Th T F f →
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' → lgroundingL n W' Θ' Δ Lm γ →
    LErel n W' Θ'' T F (fill_frame (f γ) (subst γ e1)).
Proof.
  intros Hgd Hc Hsp Hf He1 HK n W' Θ' Θ'' γ HW Hc'' Hg.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgroundingL_split _ _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  eapply (LErel_bind_guarded (S n') (f γ) W' Θ'' A B Th T F
            (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))).
  - apply gd_noret, gd_subst, Hgd.
  - apply Hf.
  - apply HW.
  - done.
  - apply heads_above_x_bot. intros Hb.
    eapply heads_above_comp; [exact HB|by apply heads_above_self|].
    eapply lgrounding_heads; [exact HW'|exact Hb|]. apply (lgroundingL_lower (S n') n' _ _ _ _ _ ltac:(lia) Hg2).
  - by apply (He1 (S n') W' Θ'1 A γ).
  - intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
    refine (HK j W' Θ'2 B γ HW HB _ W'' j Θ1' Θ3 v HW'' ltac:(lia) Hc3 HV).
    apply lgroundingL_none. exact (lgroundingL_lower (S n') j _ _ _ _ _ Hj Hg2).
Qed.

(** ** The continuations *)

Lemma lcont_letu W Θ2 Δ2 Lm F e2 T :
  lsem_later W Θ2 Δ2 Lm F e2 T → lcont W Θ2 Δ2 Lm TUnit T F (λ γ, FLetU (subst γ e2)).
Proof.
  intros He2 n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  destruct (decide (j = 0)) as [->|Hj0]; [apply LErel_0|].
  apply LVrel_unit_iff in HV as [-> ->].
  apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc3 as ->.
  apply (LErel_det_beta _ _ _ _ _ _ (subst γ e2)).
  - apply TStepHead, HeadLetU.
  - intros α e'' Hst. apply tstep_letu_inv in Hst as [(e1' & Hst & _)|(_ & -> & ->)]; [|done].
    exfalso. by eapply val_no_tstep.
  - by eapply lsem_later_at.
Qed.

Lemma lcont_letp W Θ2 Δ2 Lm F e2 T1 T2 T :
  lsem_later W Θ2 (Some T2 :: Some T1 :: Δ2) (None .: None .: Lm) F e2 T →
  lcont W Θ2 Δ2 Lm (TProd T1 T2) T F (λ γ, FLetP (subst (up (up γ)) e2)).
Proof.
  intros He2 n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  destruct (decide (j = 0)) as [->|Hj0]; [apply LErel_0|].
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
    simpl. exists Θb, A. split_and!; [done|done|].
    exists Θa, Θ'. split_and!; [done|done|].
    eapply lgroundingL_ext; [|eapply lgroundingL_down; [exact Hj|]].
    { intros i. done. }
    eapply lgroundingL_mono; [exact HW''|exact Hg].
Qed.

Lemma lcont_case W Θ2 Δ2 Lm F e1 e2 T1 T2 T :
  lsem_later W Θ2 (Some T1 :: Δ2) (None .: Lm) F e1 T →
  lsem_later W Θ2 (Some T2 :: Δ2) (None .: Lm) F e2 T →
  lcont W Θ2 Δ2 Lm (TSum T1 T2) T F (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)).
Proof.
  intros He1 He2 n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  destruct (decide (j = 0)) as [->|Hj0]; [apply LErel_0|].
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc3) (comp_comm _ _ _ _ Hs Hc'))
    as [HX HY].
  assert (lgroundingL j W'' Θ' Δ2 Lm γ) as Hg'.
  { eapply lgroundingL_down; [exact Hj|]. eapply lgroundingL_mono; [exact HW''|exact Hg]. }
  apply LVrel_sum_iff in HV as [(w & -> & HVw)|(w & -> & HVw)];
    pose proof (LVrel_val _ _ _ _ _ HVw) as Hw.
  - apply (LErel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e1))).
    + by apply TStepHead, HeadCase1.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _ & -> & ->)|(u & Heq & _)]]; [|by injection Heq as ->|done].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He1 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      simpl. exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgroundingL_ext; [|exact Hg']. done.
  - apply (LErel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e2))).
    + by apply TStepHead, HeadCase2.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _)|(u & Heq & _ & -> & ->)]]; [|done|by injection Heq as ->].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He2 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      simpl. exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgroundingL_ext; [|exact Hg']. done.
Qed.

Lemma lcont_pair W Θ2 Δ2 Lm F e2 T U :
  lsem_later W Θ2 Δ2 Lm (F ∪ (heads T ∪ bot_pts (hbot T))) e2 U →
  lcont W Θ2 Δ2 Lm T (TProd T U) F (λ γ, FPairL (subst γ e2)).
Proof.
  intros He2 n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  pose proof (LVrel_val _ _ _ _ _ HV1) as Hv1.
  change (Pair v1 (subst γ e2)) with (fill_frame (FPairR v1) (subst γ e2)).
  eapply (LErel_bind j (FPairR v1) W'' Θ3 Θ'' Θ1' U (TProd T U) F (heads T ∪ bot_pts (hbot T))).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - apply heads_above_x_bot. intros Hb. eapply LVrel_heads_above; [exact (wext_wf _ _ HW2)|exact Hb|exact HV1].
  - exact (lsem_later_at _ _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2. apply LVrel_LErel. simpl.
    apply LVrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; [done| | |done].
    { apply comp_comm; [exact Hs|exact Hc4]. }
    eapply LVrel_down; [exact Hj'|]. exact (LVrel_mono _ _ _ _ _ _ HW3 HV1).
Qed.

Lemma lcont_app W Θ2 Δ2 Lm F e2 ub lb T U :
  ub_below W ub F →
  lsem_later W Θ2 Δ2 Lm (F ∪ opt_heads lb) e2 T →
  lcont W Θ2 Δ2 Lm (TLolli ub lb T U) U F (λ γ, FAppL (subst γ e2)).
Proof.
  intros Hub He2 n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof eq_rdsym as Hs.
  pose proof (LVrel_val _ _ _ _ _ HV1) as Hv1.
  change (App v1 (subst γ e2)) with (fill_frame (FAppR v1) (subst γ e2)).
  eapply (LErel_bind j (FAppR v1) W'' Θ3 Θ'' Θ1' T U F (opt_heads lb)).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - left. eapply (LVrel_heads_above _ _ _ (TLolli ub lb T U)); [exact (wext_wf _ _ HW2)|done|exact HV1].
  - exact (lsem_later_at _ _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2.
    pose proof (wext_trans _ _ _ HW2 HW3) as HW4.
    apply (LErel_app j' W3 Θ4 Θ1' Θ2' ub lb T U); [apply HW4| | |done|].
    + apply comp_comm; [exact Hs|exact Hc4].
    + eapply LVrel_down; [exact Hj'|]. exact (LVrel_mono _ _ _ _ _ _ HW3 HV1).
    + eapply ub_below_mono; [exact HW4|exact Hub].
Qed.

(** ** Let, let-pair, case, pair and application with marks

    Each form has two rules: the parts all carry the marks, or the first
    part is guarded and the rest is judged without marks. *)

Lemma lsem_later_letu W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 TUnit →
  lsem_later W Θ2 Δ2 Lm F e2 T →
  lsem_later W Θ Δ Lm F (LetU e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetU (subst γ e1) (subst γ e2)) with (fill_frame (FLetU (subst γ e2)) (subst γ e1)).
  eapply (lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 TUnit T (λ γ, FLetU (subst γ e2)));
    [done|done|done|done| |done|done|done].
  by apply lcont_letu.
Qed.

Lemma lsem_later_letp W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TProd T1 T2) →
  lsem_later W Θ2 (Some T2 :: Some T1 :: Δ2) (None .: None .: Lm) F e2 T →
  lsem_later W Θ Δ Lm F (LetP e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetP (subst γ e1) (subst (up (up γ)) e2))
    with (fill_frame (FLetP (subst (up (up γ)) e2)) (subst γ e1)).
  eapply (lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 (TProd T1 T2) T (λ γ, FLetP (subst (up (up γ)) e2)));
    [done|done|done|done| |done|done|done].
  by apply lcont_letp.
Qed.

Lemma lsem_later_case W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e (TSum T1 T2) →
  lsem_later W Θ2 (Some T1 :: Δ2) (None .: Lm) F e1 T →
  lsem_later W Θ2 (Some T2 :: Δ2) (None .: Lm) F e2 T →
  lsem_later W Θ Δ Lm F (Case e e1 e2) T.
Proof.
  intros Hc Hsp He He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Case (subst γ e) (subst (up γ) e1) (subst (up γ) e2))
    with (fill_frame (FCase (subst (up γ) e1) (subst (up γ) e2)) (subst γ e)).
  eapply (lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e (TSum T1 T2) T
            (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)));
    [done|done|done|done| |done|done|done].
  by apply lcont_case.
Qed.

Lemma lsem_later_pair W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 T →
  lsem_later W Θ2 Δ2 Lm (F ∪ (heads T ∪ bot_pts (hbot T))) e2 U →
  lsem_later W Θ Δ Lm F (Pair e1 e2) (TProd T U).
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Pair (subst γ e1) (subst γ e2)) with (fill_frame (FPairL (subst γ e2)) (subst γ e1)).
  eapply (lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 T (TProd T U) (λ γ, FPairL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  by apply lcont_pair.
Qed.

Lemma lsem_later_app W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 ub lb T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TLolli ub lb T U) →
  lsem_later W Θ2 Δ2 Lm (F ∪ opt_heads lb) e2 T →
  lsem_later W Θ Δ Lm F (App e1 e2) U.
Proof.
  intros Hc Hsp Hub He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (App (subst γ e1) (subst γ e2)) with (fill_frame (FAppL (subst γ e2)) (subst γ e1)).
  eapply (lsem_later_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 (TLolli ub lb T U) U (λ γ, FAppL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  by apply lcont_app.
Qed.

Lemma noL_cons1 i : (None .: noL) i = None.
Proof. by destruct i. Qed.

Lemma noL_cons2 i : (None .: None .: noL) i = None.
Proof. by destruct i as [|[|i]]. Qed.

Lemma lsem_later_letu_g W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T :
  gd e1 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 TUnit →
  lsem_typed W Θ2 Δ2 F e2 T →
  lsem_later W Θ Δ Lm F (LetU e1 e2) T.
Proof. apply lsem_later_letu_guard. Qed.

Lemma lsem_later_letp_g W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T1 T2 T :
  gd e1 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TProd T1 T2) →
  lsem_typed W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
  lsem_later W Θ Δ Lm F (LetP e1 e2) T.
Proof.
  intros Hgd Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetP (subst γ e1) (subst (up (up γ)) e2))
    with (fill_frame (FLetP (subst (up (up γ)) e2)) (subst γ e1)).
  eapply (lsem_later_elim_guarded W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 (TProd T1 T2) T (λ γ, FLetP (subst (up (up γ)) e2)));
    [done|done|done|done|done| |done|done|done].
  apply lcont_letp. apply lsem_later_of_typed; [apply noL_cons2|done].
Qed.

Lemma lsem_later_case_g W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e e1 e2 T1 T2 T :
  gd e = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e (TSum T1 T2) →
  lsem_typed W Θ2 (Some T1 :: Δ2) F e1 T →
  lsem_typed W Θ2 (Some T2 :: Δ2) F e2 T →
  lsem_later W Θ Δ Lm F (Case e e1 e2) T.
Proof.
  intros Hgd Hc Hsp He He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Case (subst γ e) (subst (up γ) e1) (subst (up γ) e2))
    with (fill_frame (FCase (subst (up γ) e1) (subst (up γ) e2)) (subst γ e)).
  eapply (lsem_later_elim_guarded W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e (TSum T1 T2) T
            (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)));
    [done|done|done|done|done| |done|done|done].
  apply lcont_case; apply lsem_later_of_typed; [apply noL_cons1|done|apply noL_cons1|done].
Qed.

Lemma lsem_later_pair_g W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 T U :
  gd e1 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 T →
  lsem_typed W Θ2 Δ2 (F ∪ (heads T ∪ bot_pts (hbot T))) e2 U →
  lsem_later W Θ Δ Lm F (Pair e1 e2) (TProd T U).
Proof.
  intros Hgd Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Pair (subst γ e1) (subst γ e2)) with (fill_frame (FPairL (subst γ e2)) (subst γ e1)).
  eapply (lsem_later_elim_guarded W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 T (TProd T U) (λ γ, FPairL (subst γ e2)));
    [done|done|done|done|done| |done|done|done].
  apply lcont_pair. by apply lsem_later_now.
Qed.

Lemma lsem_later_app_g W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 e2 ub lb T U :
  gd e1 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  lsem_later W Θ1 Δ1 Lm (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TLolli ub lb T U) →
  lsem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  lsem_later W Θ Δ Lm F (App e1 e2) U.
Proof.
  intros Hgd Hc Hsp Hub He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (App (subst γ e1) (subst γ e2)) with (fill_frame (FAppL (subst γ e2)) (subst γ e1)).
  eapply (lsem_later_elim_guarded W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F e1 (TLolli ub lb T U) U (λ γ, FAppL (subst γ e2)));
    [done|done|done|done|done| |done|done|done].
  apply lcont_app; [done|]. by apply lsem_later_now.
Qed.

(** ** E-Inj with marks *)

Lemma lsem_later_inj1 W Θ Δ Lm F e T U :
  lsem_later W Θ Δ Lm F e T → lsem_later W Θ Δ Lm F (Inj1 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj1 (subst γ e)) with (fill_frame FInj1 (subst γ e)).
  eapply (LErel_bind n FInj1 W' Θ'' Θ'' ∅ T _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply LVrel_LErel. simpl.
  apply LVrel_sum_iff. left. eauto.
Qed.

Lemma lsem_later_inj2 W Θ Δ Lm F e T U :
  lsem_later W Θ Δ Lm F e U → lsem_later W Θ Δ Lm F (Inj2 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj2 (subst γ e)) with (fill_frame FInj2 (subst γ e)).
  eapply (LErel_bind n FInj2 W' Θ'' Θ'' ∅ U _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply LVrel_LErel. simpl.
  apply LVrel_sum_iff. right. eauto.
Qed.

(** ** E-Abs with marks

    The arrow reads its body at every j ≤ n, the current index included,
    so the body is judged with the marks of the λ. A marked variable is
    in V one level down, which is all the channel and head conditions of
    the arrow read. *)

Lemma lsem_later_lam W Θ Δ Lm F e T U ub lb :
  term_wf Θ (Some T :: Δ) e → tenv_bipol Θ →
  lenv_bot Δ = false →
  lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
  (∀ W1 F', wext W W1 → ub_below W1 ub F' → lsem_later W1 Θ (Some T :: Δ) (None .: Lm) F' e U) →
  lsem_later W Θ Δ Lm F (Lam e) (TLolli ub lb T U).
Proof.
  intros Hwf HBΘ Hbot Hlb He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (lgroundingL_lower (S n') n' _ _ _ _ _ ltac:(lia) Hg) as Hgl.
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  apply LVrel_LErel, LVrel_lolli_iff. left. exists (subst (up γ) e). split_and!; [done| | |].
  - eapply lsubst_fit_g; [exact Hwf|exact HBΘ|by eapply lgrounding_bipol|exact Hc|].
    apply gends_up. by eapply lgrounding_gends.
  - assert (∀ h, h ∈ tenv_heads Θ'' → (h ∈ tenv_heads Θ ∨ ∃ h', h' ∈ lenv_heads Δ ∧ w_le W' h' h))
      as Hh.
    { intros h (k & e0 & He0 & ->)%elem_of_tenv_heads_entry.
      destruct (comp_entry _ _ _ _ _ _ Hc He0) as [[k' Hk]|[k' Hk]].
      - left. apply elem_of_tenv_heads_entry. eauto.
      - right. exact (lgrounding_heads _ _ _ _ _ HW' Hbot Hgl _ _ Hk). }
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
    + simpl. exists Θa, Θ'. split_and!; [by apply comp_comm|done|].
      eapply lgroundingL_ext; [|eapply lgroundingL_down; [|eapply lgroundingL_mono; [exact HW2|exact Hg]]].
      * done.
      * lia.
Qed.

(** ** The closure at level 0

    A closure is in V at level 0 by its channels and heads alone, so the
    rules of E-Abs without the body give it. An applied λ whose argument
    is guarded needs no more of its function now (a closure built before
    the guard). *)

Definition lsem_v0 (W : world) (Θ : tenv) (Δ : lenv) (Lm : lmark) (e : expr) (T : ty) : Prop :=
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' → lgroundingL (S n) W' Θ' Δ Lm γ →
    LVrel 0 W' Θ'' T (subst γ e).

Lemma lsem_v0_lam W Θ Δ Lm e T U ub lb :
  term_wf Θ (Some T :: Δ) e → tenv_bipol Θ → lenv_bot Δ = false →
  lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
  lsem_v0 W Θ Δ Lm (Lam e) (TLolli ub lb T U).
Proof.
  intros Hwf HBΘ Hbot Hlb n' W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (lgroundingL_lower (S n') n' _ _ _ _ _ ltac:(lia) Hg) as Hgl.
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  apply LVrel_lolli_iff. left. exists (subst (up γ) e). split_and!; [done| | |].
  - eapply lsubst_fit_g; [exact Hwf|exact HBΘ|by eapply lgrounding_bipol|exact Hc|].
    apply gends_up. by eapply lgrounding_gends.
  - assert (∀ h, h ∈ tenv_heads Θ'' → (h ∈ tenv_heads Θ ∨ ∃ h', h' ∈ lenv_heads Δ ∧ w_le W' h' h))
      as Hh.
    { intros h (k & e0 & He0 & ->)%elem_of_tenv_heads_entry.
      destruct (comp_entry _ _ _ _ _ _ Hc He0) as [[k' Hk]|[k' Hk]].
      - left. apply elem_of_tenv_heads_entry. eauto.
      - right. exact (lgrounding_heads _ _ _ _ _ HW' Hbot Hgl _ _ Hk). }
    pose proof (lb_below_mono _ _ _ _ HW Hlb) as Hlb'.
    destruct lb as [l|]; simpl in *.
    + intros h Hin. destruct (Hh h Hin) as [Hin'|(h' & Hh' & Hle)].
      * apply Hlb'. set_solver.
      * eapply le_le_W; [exact HW'| |exact Hle]. apply Hlb'. set_solver.
    + apply set_eq. intros h. split; [|set_solver]. intros Hin.
      destruct (Hh h Hin) as [Hin'|(h' & Hh' & _)]; set_solver.
  - intros W2 j Θa Θb w F' HW2 Hj Hcb Hub HVw. assert (j = 0) as -> by lia. apply LErel_0.
Qed.

Lemma LErel_val_inv n W Θ T F v : is_val v → LErel (S n) W Θ T F v → LVrel (S n) W Θ T v.
Proof.
  intros Hv H. apply LErel_S_iff in H. destruct (H W (wext_r_refl _)) as (Hs & _).
  apply Hs. intros α e' Hst. by eapply val_no_tstep.
Qed.

Lemma LErel_beta_inv n W Θ T F e e' : tstep e LBeta e' → LErel (S n) W Θ T F e → LErel (S n) W Θ T F e'.
Proof.
  intros Hst H. apply LErel_S_iff in H. destruct (H W (wext_r_refl _)) as (_ & _ & Hb & _). by apply Hb.
Qed.

Lemma lsem_v0_wk W Θ Δ' Δ Lm e T :
  lenv_wk Δ' Δ → lsem_v0 W Θ Δ' Lm e T → lsem_v0 W Θ Δ Lm e T.
Proof.
  intros Hwk He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc). by eapply lgroundingL_wk.
Qed.

Lemma lsem_v0_conv W Θ Δ Lm e T T' :
  teqW W T T' → lsem_v0 W Θ Δ Lm e T → lsem_v0 W Θ Δ Lm e T'.
Proof.
  intros Ht He n W' Θ' Θ'' γ HW Hc Hg. eapply LVrel_tconv; [exact (wext_wf _ _ HW)| |by apply (He n W' Θ')].
  eapply teqW_mono; [|exact Ht]. intros x y H. exact H.
Qed.

Lemma lsem_v0_contract W Θ Δ U Lm e T :
  unlimited U →
  lsem_v0 W Θ (Some U :: Some U :: Δ) (λ x, Lm (pred x)) e T →
  lsem_v0 W Θ (Some U :: Δ) Lm (rename pred e) T.
Proof.
  intros Hu He n W' Θ' Θ'' γ HW Hc Hg. rewrite subst_rename.
  apply (He n W' Θ' Θ'' (λ x, γ (pred x))); [done|done|]. by apply lgroundingL_contract.
Qed.

Lemma lsem_v0_open W Θ Δ Lm e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     lsem_v0 W1 Θ (<[i := Some (ty_inst xs T)]> Δ) Lm e U) →
  lsem_v0 W Θ Δ Lm e U.
Proof.
  intros Hi He n W' Θ' Θ'' γ HW Hc Hg.
  destruct (lgroundingL_open _ _ _ _ _ _ _ _ _ _ _ Hi Hg) as (xs & Hxs & HK & HC & Hg').
  apply (He W' xs HW Hxs HK HC n W' Θ' Θ'' γ); [|done|done].
  apply wext_refl. by destruct HW as (_&_&_&?).
Qed.

Lemma lsem_v0_pack W Θ Δ Lm e lb m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  lbx_below W lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  lsem_v0 W Θ Δ Lm e (ty_inst xs T) → lsem_v0 W Θ Δ Lm e (TEx lb m C T).
Proof.
  intros Hxs HK HC Hlb He n W' Θ' Θ'' γ HW Hc Hg.
  eapply LVrel_pack; [done..|exact HW|by apply (He n W' Θ')].
Qed.

Lemma lsem_later_pack W Θ Δ Lm F e lb m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  lbx_below W lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  lsem_later W Θ Δ Lm F e (ty_inst xs T) → lsem_later W Θ Δ Lm F e (TEx lb m C T).
Proof.
  intros Hxs HK HC Hlb He n W' Θ' Θ'' γ HW Hc Hg.
  eapply LErel_Vsub; [|by apply (He n W' Θ' Θ'' γ)].
  intros j W2 Θ2 v Hj HW2 HV. eapply LVrel_pack; [done..| |exact HV].
  destruct HW2 as [->|HW2]; [done|by eapply wext_trans].
Qed.

(** ** The applied λ whose argument is guarded

    The closure is a value at once. The argument acts before it returns,
    so the closure is applied below the index, where its free variables
    are read now. Its heads are read at level 0. *)

Lemma lsem_later_app_lam W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F b e2 ub lb T U :
  gd e2 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) (Lam b) (TLolli ub lb T U) →
  lsem_v0 W Θ1 Δ1 Lm (Lam b) (TLolli ub lb T U) →
  lsem_later W Θ2 Δ2 Lm (F ∪ opt_heads lb) e2 T →
  lsem_later W Θ Δ Lm F (App (Lam b) e2) U.
Proof.
  intros Hgd Hc Hsp Hub He1 Hv1 He2 n W' Θ' Θ'' γ HW Hc'' Hg.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgroundingL_split _ _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  change (subst γ (App (Lam b) e2)) with (fill_frame (FAppR (subst γ (Lam b))) (subst γ e2)).
  eapply (LErel_bind_guarded (S n') _ W' Θ'' B A T U F (opt_heads lb)).
  - apply gd_noret, gd_subst, Hgd.
  - done.
  - apply HW.
  - by apply comp_comm.
  - left. eapply (LVrel_heads_above _ _ _ (TLolli ub lb T U)); [exact HW'|done|].
    exact (Hv1 n' W' Θ'1 A γ HW HA Hg1).
  - by apply (He2 (S n') W' Θ'2 B γ).
  - intros W'' j Θ2' Θ4 v2 HW'' Hj Hc4 HV2.
    destruct j as [|j']; [apply LErel_0|].
    pose proof (wext_trans _ _ _ HW HW'') as HWW''.
    assert (LVrel (S j') W'' A (TLolli ub lb T U) (subst γ (Lam b))) as HV1.
    { apply (LErel_val_inv _ _ _ _ (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2)))); [done|].
      apply (He1 (S j') W'' Θ'1 A γ HWW''); [exact HA|].
      eapply lgrounding_mono; [exact HW''|]. exact (lgroundingL_lower (S n') (S j') _ _ _ _ _ Hj Hg1). }
    apply (LErel_app (S j') W'' Θ4 A Θ2' ub lb T U); [apply HWW''| |done|done|].
    + apply comp_comm; [exact Hs|exact Hc4].
    + eapply ub_below_mono; [exact HWW''|exact Hub].
Qed.

(** ** Force of the self applied to a guarded argument (sharp edges 161)

    The self is later and a box around a λ, so forcing it is one β to a
    closure without channels. The argument acts before it returns, and
    the closure is applied below the index. *)

Lemma lsem_later_app_force W Θ Θ1 Θ2 Δ Δ1 Δ2 Lm F y T0 e2 ub lb T U :
  gd e2 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  Δ1 !! y = Some (Some T0) → Lm y = Some true →
  term_wf Θ1 Δ1 (App EForce (Var y)) →
  lsem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) (App EForce (Var y))
    (TLolli ub lb T U) →
  lsem_later W Θ2 Δ2 Lm (F ∪ opt_heads lb) e2 T →
  lsem_later W Θ Δ Lm F (App (App EForce (Var y)) e2) U.
Proof.
  intros Hgd Hc Hsp Hub Hy HLy (Hfc & _ & Hrel) He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgroundingL_split _ _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  pose proof (lgroundingL_later _ _ _ _ _ _ _ _ _ Hy HLy Hg1) as [Hlv Hlam].
  destruct (Hlam eq_refl) as [b0 Hb0].
  assert (fends (γ y) = ∅) as Hfy.
  { destruct (LVrel_fit _ _ _ _ _ (Hlv 0 W' ltac:(lia) (wext_r_refl _))) as [Hf _].
    by rewrite <-Hf, tenv_ends_empty. }
  assert (Θ1 = ∅) as ->.
  { apply dom_empty_inv_L. rewrite <-tenv_ends_dom, <-Hfc. simpl. set_solver. }
  assert (Θ'1 = ∅) as ->.
  { refine (lgroundingL_empty _ _ _ _ _ _ _ Hg1). intros x T' Hx Hu.
    assert (freevar x (App EForce (Var y))) as Hfx by (apply Hrel; by exists T').
    simpl in Hfx. destruct Hfx as [[]| ->]. by rewrite HLy. }
  apply (tenv_comp_empty_inv) in HA as ->.
  apply (tenv_comp_empty_l_inv _ _ _ Hs) in HAB as <-.
  set (cl := subst1 (EBox (Lam b0)) (Lam b0)).
  assert (is_val cl) as Hcl by done.
  simpl. rewrite Hb0 in Hfy |- *.
  pose proof (He2 (S n') W' Θ'2 Θ'' γ HW HB Hg2) as HE2.
  assert (fends cl = ∅) as Hfcl.
  { apply set_eq. intros o. split; [|set_solver]. intros Ho%fends_subst1_sub. simpl in Ho, Hfy. set_solver. }
  apply (LErel_det_beta _ _ _ _ _ _ (App cl (subst γ e2))).
  { apply TStepAppL, TStepHead, HeadForce. }
  { intros α e'' Hst.
    apply tstep_app_inv in Hst as [(e1' & Hst & ->)|[(Hv & _)|(Hv & _)]]; [|done|done].
    apply app_val_step in Hst; [|done|done]. by inversion Hst. }
  change (App cl (subst γ e2)) with (fill_frame (FAppR cl) (subst γ e2)).
  eapply (LErel_bind_guarded (S n') _ W' Θ'' Θ'' ∅ T U F (opt_heads lb)).
  - apply gd_noret, gd_subst, Hgd.
  - done.
  - apply HW.
  - apply tenv_comp_empty_r.
  - left. apply heads_above_empty.
  - exact HE2.
  - intros W'' j Θ2' Θ4 v2 HW'' Hj Hc4 HV2.
    destruct j as [|j']; [apply LErel_0|].
    pose proof (wext_trans _ _ _ HW HW'') as HWW''.
    assert (LVrel (S j') W'' ∅ (TLolli ub lb T U) cl) as HV1.
    { apply (LErel_val_inv _ _ _ _ (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2)))); [done|].
      apply (LErel_beta_inv _ _ _ _ _ (App EForce (EBox (Lam b0)))); [by apply TStepHead, HeadForce|].
      rewrite <-Hb0. change (App EForce (γ y)) with (subst γ (App EForce (Var y))).
      apply (He1 (S j') W'' ∅ ∅ γ HWW''); [apply tenv_comp_empty_r|].
      eapply lgrounding_mono; [exact HW''|]. exact (lgroundingL_lower (S n') (S j') _ _ _ _ _ Hj Hg1). }
    apply tenv_comp_empty_r_inv in Hc4 as ->.
    apply (LErel_app (S j') W'' Θ2' ∅ Θ2' ub lb T U); [apply HWW''| |done|done|].
    + apply tenv_comp_empty_l, eq_rdsym.
    + eapply ub_below_mono; [exact HWW''|exact Hub].
Qed.
