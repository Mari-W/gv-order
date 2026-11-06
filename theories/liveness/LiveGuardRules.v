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
