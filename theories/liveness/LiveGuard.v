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
