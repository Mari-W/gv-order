(** * The guard in the semantics (liveness.md §6, §10 step 2)

    A term with [gd] performs a session primitive before it returns:
    no sequence of β, new and spawn steps reaches a value ([gd_noret]).
    This is purely operational, so a guarded hole meets the condition of
    [LErel_bind_R] with [R := noret], and its continuation is needed
    below the current index only ([LErel_bind_guarded]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveTermRules liveness.Guard.

Set Default Proof Using "All".
Local Set Warnings "-register-all".

(** ** [gd] is syntactic *)

Lemma gd_val v : is_val v → gd v = false.
Proof.
  induction v; simpl; try done; try (intros; by apply IHv).
  intros [H1 H2]%andb_True. by rewrite IHv1, IHv2.
Qed.

(** An application is guarded when its function or its argument is. *)
Lemma gd_app_ge e1 e2 : gd e1 || gd e2 = true → gd (App e1 e2) = true.
Proof.
  intros H. destruct e1; simpl in *; rewrite ?orb_true_iff in *; tauto.
Qed.

Lemma gd_app_inv e1 e2 :
  gd (App e1 e2) = true →
  gd e1 || gd e2 = true ∨ (∃ k, e1 = Konst k ∧ prim_konst k = true) ∨ (∃ b, e1 = Lam b ∧ gd b = true).
Proof.
  destruct e1; simpl; try (intros H; by left).
  - intros [H|H]%orb_true_iff; [right; left; eauto|left; by rewrite H].
  - intros [H|H]%orb_true_iff; [left; by rewrite H|right; right; eauto].
Qed.

Lemma gd_subst_aux e : ∀ σ, (gd e = true → gd (subst σ e) = true) ∧
  (∀ b, e = Lam b → gd b = true → gd (subst (up σ) b) = true).
Proof.
  induction e as [x| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros σ;
    (split; [intros H|intros b' Hb'; try discriminate Hb']); simpl in *; try done.
  - injection Hb' as <-. intros Hg. by apply (proj1 (IH _)).
  - destruct (gd_app_inv _ _ H) as [H'|[(k & -> & Hk)|(b & -> & Hb)]].
    + apply gd_app_ge. apply orb_true_iff in H' as [H'|H']; apply orb_true_iff;
        [left; by apply (proj1 (IH1 _))|right; by apply (proj1 (IH2 _))].
    + simpl. by rewrite Hk.
    + simpl. apply orb_true_iff. right. by apply (proj2 (IH1 σ) b).
  - apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left; by apply (proj1 (IH1 _))|right; by apply (proj1 (IH2 _))].
  - apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left; by apply (proj1 (IH1 _))|right; by apply (proj1 (IH2 _))].
  - apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left; by apply (proj1 (IH1 _))|right; by apply (proj1 (IH2 _))].
  - by apply (proj1 (IH _)).
  - by apply (proj1 (IH _)).
  - apply orb_true_iff in H as [H|(H1 & H2)%andb_true_iff]; apply orb_true_iff; [left; by apply (proj1 (IH _))|right].
    apply andb_true_iff. split; [by apply (proj1 (IH1 _))|by apply (proj1 (IH2 _))].
Qed.

Lemma gd_subst e σ : gd e = true → gd (subst σ e) = true.
Proof. apply gd_subst_aux. Qed.

Lemma gd_subst1 v e : gd e = true → gd (subst1 v e) = true.
Proof. apply gd_subst. Qed.

Lemma gd_subst2 u v e : gd e = true → gd (subst2 u v e) = true.
Proof. apply gd_subst. Qed.

(** ** τ steps keep the guard *)

Definition tau_label (α : tlabel) : Prop := ∀ σ, α ≠ LSess σ.

Lemma gd_tstep e α e' : tstep e α e' → tau_label α → gd e = true → gd e' = true.
Proof.
  induction 1 as [e α e' Hh|e1 α e1' e2 Hst IH|v e2 α e2' Hv Hst IH|e1 α e1' e2 Hst IH
                 |v e2 α e2' Hv Hst IH|e1 α e1' e2 Hst IH|e1 α e1' e2 Hst IH|e α e' Hst IH
                 |e α e' Hst IH|e α e' e1 e2 Hst IH]; intros Hα Hg.
  - destruct Hh; simpl in *; try discriminate Hg; try (exfalso; exact (Hα _ eq_refl)).
    + apply orb_true_iff in Hg as [Hg|Hg]; [by rewrite gd_val in Hg|by apply gd_subst1].
    + done.
    + rewrite (gd_val u), (gd_val v) in Hg by done. simpl in Hg. by apply gd_subst2.
    + by rewrite gd_val in Hg.
    + apply orb_true_iff in Hg as [Hg|(Hg & _)%andb_true_iff]; [by rewrite gd_val in Hg|by apply gd_subst1].
    + apply orb_true_iff in Hg as [Hg|(_ & Hg)%andb_true_iff]; [by rewrite gd_val in Hg|by apply gd_subst1].
  - apply gd_app_ge. destruct (gd_app_inv _ _ Hg) as [H'|[(k & -> & _)|(b & -> & _)]];
      [|exfalso; by eapply val_no_tstep..].
    apply orb_true_iff in H' as [H'|H']; apply orb_true_iff; [left; auto|right; done].
  - destruct (gd_app_inv _ _ Hg) as [H'|[(k & -> & Hk)|(b & -> & Hb)]].
    + apply gd_app_ge. apply orb_true_iff in H' as [H'|H']; [by rewrite gd_val in H'|].
      apply orb_true_iff. right. auto.
    + simpl. by rewrite Hk.
    + simpl. by rewrite Hb, orb_true_r.
  - simpl in *. apply orb_true_iff in Hg as [H|H]; apply orb_true_iff; [left; auto|right; done].
  - simpl in *. apply orb_true_iff in Hg as [H|H]; [by rewrite gd_val in H|].
    apply orb_true_iff. right. auto.
  - simpl in *. apply orb_true_iff in Hg as [H|H]; apply orb_true_iff; [left; auto|right; done].
  - simpl in *. apply orb_true_iff in Hg as [H|H]; apply orb_true_iff; [left; auto|right; done].
  - simpl in *. auto.
  - simpl in *. auto.
  - simpl in *. apply orb_true_iff in Hg as [H|H]; apply orb_true_iff; [left; auto|right; done].
Qed.

(** ** A guarded term does not return before a channel step *)

Definition noret (e : expr) : Prop := ∀ e', rtc tadmin e e' → is_val e' = false.

Lemma tadmin_tau e e' : tadmin e e' → ∃ α, tstep e α e' ∧ tau_label α.
Proof. intros [? ? Hs|? ? ? Hs|? ? ? Hs]; eexists; (split; [exact Hs|done]). Qed.

Lemma gd_noret e : gd e = true → noret e.
Proof.
  intros Hg e' Hs. induction Hs as [e|e1 e2 e3 H12 _ IH].
  - destruct (is_val e) eqn:Hv; [|done]. by rewrite gd_val in Hg; [|by rewrite Hv].
  - apply IH. destruct (tadmin_tau _ _ H12) as (α & Hst & Hα). by eapply gd_tstep.
Qed.

Lemma noret_step e e' : noret e → tadmin e e' → noret e'.
Proof. intros H Hs e'' Hs'. apply H. by eapply rtc_l. Qed.

Lemma noret_val v : noret v → is_val v = false.
Proof. intros H. apply H, rtc_refl. Qed.

(** The bind lemma for a guarded hole: the continuation is needed below
    the current index only. *)
Lemma LErel_bind_guarded n f W Θ Θ1 Θ2 Th T F H e :
  noret e → frame_val f → strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above_x W H Θ2 →
  LErel n W Θ1 Th (F ∪ H) e →
  (∀ W' j Θ1' Θ' v, wext W W' → j < n → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
     LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) →
  LErel n W Θ T F (fill_frame f e).
Proof.
  intros Hnr Hf HW Hc Hh HE HK.
  apply (LErel_bind_R n noret f W Θ Θ1 Θ2 Th T F H e); try done.
  - intros ? ? ? ?. by eapply noret_step.
  - intros W' j Θ1' Θ' v HW' Hj HR Hc' HV.
    destruct (decide (j = n)) as [->|Hne].
    + exfalso. pose proof (noret_val _ (HR eq_refl)) as Hv.
      pose proof (LVrel_val _ _ _ _ _ HV) as Hv'. by rewrite Hv in Hv'.
    + apply (HK W' j Θ1' Θ' v); [done|lia|done|done].
Qed.

(** ** A judgment with one later variable

    [L = Some x] marks the variable x of Δ as later: its value is in V at
    every level below n and in every later world, and its environment
    is empty. With [lam], the value is moreover a box whose body is a λ,
    so forcing it is one β to a value (sharp edges 161). [L = None] is
    [lgrounding]. *)

Definition later_val (n : nat) (W : world) (lam : bool) (T : ty) (v : expr) : Prop :=
  (∀ j W2, j < n → wext_r W W2 → LVrel j W2 ∅ T v) ∧ (lam = true → ∃ b, v = EBox (Lam b)).

Definition shiftL (L : option nat) : option nat :=
  match L with Some (S x) => Some x | _ => None end.

Fixpoint lgroundingL (n : nat) (W : world) (Θ : tenv) (Δ : lenv) (L : option nat) (lam : bool)
    (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => lgroundingL n W Θ Δ' (shiftL L) lam (γ ∘ S)
  | Some T :: Δ' =>
      if decide (L = Some 0) then
        unlimited T ∧ later_val n W lam T (γ 0) ∧ lgroundingL n W Θ Δ' None lam (γ ∘ S)
      else
        ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ LVrel n W Θ1 T (γ 0) ∧
                 lgroundingL n W Θ2 Δ' (shiftL L) lam (γ ∘ S)
  end.

Definition lsem_later (W : world) (Θ : tenv) (Δ : lenv) (L : option nat) (lam : bool)
    (F : gset point) (e : expr) (T : ty) : Prop :=
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' →
    lgroundingL n W' Θ' Δ L lam γ → LErel n W' Θ'' T F (subst γ e).

Lemma shiftL_none : shiftL None = None.
Proof. done. Qed.

Lemma lgroundingL_none n W Θ Δ lam γ : lgroundingL n W Θ Δ None lam γ ↔ lgrounding n W Θ Δ γ.
Proof.
  revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ; simpl; [done| |by apply IH].
  destruct (decide (None = Some 0)) as [|_]; [done|].
  split; intros (Θ1 & Θ2 & ? & ? & Hg); exists Θ1, Θ2; split_and!; try done; by apply IH.
Qed.

(** A later variable is now one level down. *)
Lemma lgroundingL_lower n j W Θ Δ L lam γ :
  j < n → lgroundingL n W Θ Δ L lam γ → lgrounding j W Θ Δ γ.
Proof.
  intros Hj. revert Θ L γ. induction Δ as [|[T|] Δ IH]; intros Θ L γ Hg; simpl in *; [done| |by eapply IH].
  destruct (decide (L = Some 0)) as [->|HL].
  - destruct Hg as (Hu & [Hv _] & Hg). exists ∅, Θ. split_and!.
    + apply tenv_comp_empty_l, eq_rdsym.
    + apply (Hv j W Hj), wext_r_refl.
    + by eapply IH.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2.
    split_and!; [done|eapply LVrel_down; [|exact HV]; lia|by eapply IH].
Qed.

Lemma lgroundingL_mono n W W' Θ Δ L lam γ :
  wext W W' → lgroundingL n W Θ Δ L lam γ → lgroundingL n W' Θ Δ L lam γ.
Proof.
  intros HW. revert Θ L γ. induction Δ as [|[T|] Δ IH]; intros Θ L γ Hg; simpl in *; [done| |by apply IH].
  destruct (decide (L = Some 0)) as [->|HL].
  - destruct Hg as (Hu & [Hv Hl] & Hg). split_and!; [done| |by apply IH].
    split; [|done]. intros j W2 Hj HW2. apply Hv; [done|]. right.
    destruct HW2 as [->|HW2]; [done|by eapply wext_trans].
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2.
    split_and!; [done|by eapply LVrel_mono|by apply IH].
Qed.

Lemma lgroundingL_down n m W Θ Δ L lam γ :
  m ≤ n → lgroundingL n W Θ Δ L lam γ → lgroundingL m W Θ Δ L lam γ.
Proof.
  intros Hm. revert Θ L γ. induction Δ as [|[T|] Δ IH]; intros Θ L γ Hg; simpl in *; [done| |by apply IH].
  destruct (decide (L = Some 0)) as [->|HL].
  - destruct Hg as (Hu & [Hv Hl] & Hg). split_and!; [done| |by apply IH].
    split; [|done]. intros j W2 Hj HW2. apply Hv; [lia|done].
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2.
    split_and!; [done|by eapply LVrel_down|by apply IH].
Qed.

Lemma lgroundingL_ext n W Θ Δ L lam γ γ' :
  (∀ i, γ i = γ' i) → lgroundingL n W Θ Δ L lam γ → lgroundingL n W Θ Δ L lam γ'.
Proof.
  revert Θ L γ γ'. induction Δ as [|[T|] Δ IH]; intros Θ L γ γ' Hγ Hg; simpl in *; [done| |].
  - destruct (decide (L = Some 0)).
    + destruct Hg as (Hu & Hv & Hg). rewrite <-Hγ. split_and!; [done|done|].
      eapply IH; [|exact Hg]. intros i. apply Hγ.
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|by rewrite <-Hγ|].
      eapply IH; [|exact Hg]. intros i. apply Hγ.
  - eapply IH; [|exact Hg]. intros i. apply Hγ.
Qed.

Lemma lgroundingL_unl n W Θ Δ L lam γ : lenv_unl Δ → lgroundingL n W Θ Δ L lam γ → Θ = ∅.
Proof.
  revert Θ L γ. induction Δ as [|[T|] Δ IH]; intros Θ L γ Hu Hg; simpl in *.
  - done.
  - assert (lenv_unl Δ) as Hu' by (intros o Ho; apply Hu; by right).
    destruct (decide (L = Some 0)).
    + destruct Hg as (_ & _ & Hg). by eapply IH.
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
      destruct (Hu (Some T)) as [?|(U & [= <-] & HU)]; [by left|done|].
      rewrite (LVrel_unl_empty _ _ _ _ _ HU HV) in Hc.
      apply (tenv_comp_empty_l_inv _ _ _ eq_rdsym) in Hc as ->. by eapply IH.
  - apply (IH _ (shiftL L) (γ ∘ S)); [|done]. intros o Ho. apply Hu. by right.
Qed.

(** ** E-Exp-Live: the body with a later self

    The self is the variable 0 of the body. When the body is a λ, the
    later hypothesis also says that the self is a box around a λ. *)

Definition is_lam (e : expr) : bool := match e with Lam _ => true | _ => false end.

Lemma is_lam_subst σ e : is_lam e = true → ∃ b, subst σ e = Lam b.
Proof. destruct e; try done. intros _. simpl. eauto. Qed.


(** [LVrel_box_lob] up to a bound N on the index. *)
Lemma LVrel_box_lob_le N W m k C ub T eb :
  fchans eb = ∅ →
  (∀ n W1 xs ss F, n ≤ N → wext W W1 → length xs = m → length ss = k → Forall hcontractive ss →
     bcs_hold (w_eq W1) (w_lt W1) C xs → Forall (pt_known W1) xs →
     ub_below W1 (pt_inst (plist xs) <$> ub) F →
     (∀ j W2, j < n → wext W1 W2 →
        LVrel j W2 ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox eb)) →
     LErel n W1 ∅ (sinst_ty (slist ss) (ty_inst xs T)) F (subst1 (EBox eb) eb)) →
  ∀ n W', n ≤ N → wext W W' → LVrel n W' ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox eb).
Proof.
  intros Hfc Hbody n. induction n as [n IH] using lt_wf_ind. intros W' HnN HW'.
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
    apply (Hbody j W3 xs ss F); [lia|done|done|done|done| | |exact Hub|].
    + destruct HW3 as (_ & He3 & Hl3 & _). eapply bcs_hold_mono; [exact He3|exact Hl3|exact HC].
    + eapply Forall_impl; [exact HK|]. destruct HW3 as (Hn & _). unfold pt_known.
      intros x Hx. by apply Hn.
    + intros i W4 Hi HW4. apply IH; [lia|lia|]. by eapply wext_trans.
Qed.

Lemma lgrounding_unl n W Θ Δ γ : lenv_unl Δ → lgrounding n W Θ Δ γ → Θ = ∅.
Proof.
  intros Hu Hg. apply (lgroundingL_unl n W Θ Δ None false γ Hu). by apply lgroundingL_none.
Qed.

Lemma lsem_typed_box_live W Δ F e m k C ub T :
  lenv_unl Δ → term_wf ∅ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ) e →
  (∀ W1 xs ss F', wext W W1 → length xs = m → length ss = k → Forall hcontractive ss →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     Forall (pt_known W1) xs → ub_below W1 (pt_inst (plist xs) <$> ub) F' →
     lsem_later W1 ∅ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ) (Some 0) (is_lam e) F' e
       (sinst_ty (slist ss) (ty_inst xs T))) →
  lsem_typed W ∅ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T)).
Proof.
  intros Hu (Hfc & Hfv & _) He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (lgrounding_unl _ _ _ _ _ Hu Hg) as ->.
  apply tenv_comp_empty_inv in Hc as ->.
  apply LVrel_LErel.
  assert (fchans (subst (up γ) e) = ∅) as Hfc'.
  { assert (fchans (subst (up γ) e) ⊆ fchans e ∪ dom (∅ : tenv)) as Hsub.
    { apply fchans_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      - intros _. set_solver.
      - intros (T' & Hx). unfold compose. rewrite fchans_rename. by eapply lgrounding_fchans. }
    rewrite Hfc, dom_empty_L in Hsub. set_solver. }
  apply (LVrel_box_lob_le n W' m k C ub T (subst (up γ) e) Hfc'); [|done|apply wext_refl, HW].
  intros n1 W1 xs ss F1 Hn1 HW1 Hxs Hss Hsc HC HK Hub Hlob. rewrite subst1_subst.
  pose proof (wext_trans _ _ _ HW HW1) as HWW1.
  apply (He W1 xs ss F1 HWW1 Hxs Hss Hsc HC HK Hub n1 W1 ∅ ∅).
  - apply wext_refl, HWW1.
  - apply tenv_comp_empty_r.
  - simpl. destruct (decide (Some 0 = Some 0)) as [_|]; [|done]. split_and!.
    + done.
    + split.
      * intros j W2 Hj [<-|HW2]; [apply Hlob; [done|apply wext_refl, HWW1]|by apply Hlob].
      * intros Hl. destruct (is_lam_subst (up γ) e Hl) as [b ->]. by exists b.
    + apply lgroundingL_none. eapply lgrounding_ext; [|eapply lgrounding_down; [exact Hn1|]].
      * done.
      * eapply lgrounding_mono; [exact HW1|exact Hg].
Qed.

(** ** The guard discharges the later variable *)

Lemma lgroundingL_split n W Θ Δ Δ1 Δ2 L lam γ :
  lenv_split Δ Δ1 Δ2 → lgroundingL n W Θ Δ L lam γ →
  ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ lgroundingL n W Θ1 Δ1 L lam γ ∧
    lgroundingL n W Θ2 Δ2 L lam γ.
Proof.
  intros Hsp. pose proof eq_rdsym as Hs.
  revert Θ L γ. induction Hsp as [|Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|U Δ Δ1 Δ2 HU Hsp IH];
    intros Θ L γ Hg; simpl in *.
  - subst. exists ∅, ∅. split_and!; [apply tenv_comp_empty_r|done|done].
  - by apply IH.
  - destruct (decide (L = Some 0)) as [->|HL].
    + destruct Hg as (Hu & Hv & Hg). destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc & Hg1 & Hg2).
      exists Θ1, Θ2. split; [done|]. split; [exact (conj Hu (conj Hv Hg1))|done].
    + destruct Hg as (Θa & Θr & Hc & HV & Hg).
      destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
      destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) Hc') as [HX HY].
      eexists _, Θ2. split_and!; [exact HY| |done].
      exists Θa, Θ1. split_and!; [by apply comp_comm|done|done].
  - destruct (decide (L = Some 0)) as [->|HL].
    + destruct Hg as (Hu & Hv & Hg). destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc & Hg1 & Hg2).
      exists Θ1, Θ2. split; [done|]. split; [done|exact (conj Hu (conj Hv Hg2))].
    + destruct Hg as (Θa & Θr & Hc & HV & Hg).
      destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
      destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) (comp_comm _ _ _ _ Hs Hc'))
        as [HX HY].
      eexists Θ1, _. split_and!; [by apply comp_comm|done|].
      exists Θa, Θ2. split_and!; [by apply comp_comm|done|done].
  - destruct (decide (L = Some 0)) as [->|HL].
    + destruct Hg as (Hu & Hv & Hg). destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc & Hg1 & Hg2).
      exists Θ1, Θ2. split; [done|]. split; [exact (conj Hu (conj Hv Hg1))|exact (conj Hu (conj Hv Hg2))].
    + destruct Hg as (Θa & Θr & Hc & HV & Hg).
      pose proof (LVrel_unl_empty _ _ _ _ _ HU HV) as ->.
      apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
      destruct (IH _ _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
      exists Θ1, Θ2. split_and!; [done| |].
      * exists ∅, Θ1. split_and!; [by apply tenv_comp_empty_l|done|done].
      * exists ∅, Θ2. split_and!; [by apply tenv_comp_empty_l|done|done].
Qed.

(** E-Guard-Let: a guarded e1 with a later variable, and a continuation
    that reads the variable now. *)
Lemma lsem_later_letu_guard W Θ Θ1 Θ2 Δ Δ1 Δ2 L lam F e1 e2 T :
  gd e1 = true → tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  lsem_later W Θ1 Δ1 L lam (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 TUnit →
  lsem_typed W Θ2 Δ2 F e2 T →
  lsem_later W Θ Δ L lam F (LetU e1 e2) T.
Proof.
  intros Hgd Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  destruct n as [|n']; [apply LErel_0|].
  pose proof (wext_wf _ _ HW) as HW'. pose proof eq_rdsym as Hs.
  destruct (lgroundingL_split _ _ _ _ _ _ _ _ _ Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' Hc Hc') as (A & B & HAB & HA & HB).
  change (LetU (subst γ e1) (subst γ e2)) with (fill_frame (FLetU (subst γ e2)) (subst γ e1)).
  eapply (LErel_bind_guarded (S n') _ W' Θ'' A B TUnit T F
            (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))).
  - apply gd_noret, gd_subst, Hgd.
  - done.
  - apply HW.
  - done.
  - apply heads_above_x_bot. intros Hb.
    eapply heads_above_comp; [exact HB|by apply heads_above_self|].
    eapply lgrounding_heads; [exact HW'|exact Hb|]. apply (lgroundingL_lower (S n') n' _ _ _ _ _ _ ltac:(lia) Hg2).
  - by apply (He1 (S n') W' Θ'1 A γ).
  - intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
    apply LVrel_unit_iff in HV as [-> ->].
    apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc3 as ->.
    apply (LErel_det_beta _ _ _ _ _ _ (subst γ e2)).
    + apply TStepHead, HeadLetU.
    + intros α e'' Hst. apply tstep_letu_inv in Hst as [(e1' & Hst & _)|(_ & -> & ->)]; [|done].
      exfalso. by eapply val_no_tstep.
    + apply (He2 j W'' Θ'2 B γ); [by eapply wext_trans|done|].
      eapply lgrounding_mono; [exact HW''|]. apply (lgroundingL_lower (S n') j _ _ _ _ _ _ Hj Hg2).
Qed.
