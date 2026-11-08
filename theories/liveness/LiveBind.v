(** * The bind lemma for the live relation (Bind.v)

    As [Erel_bind], with the live costs. A τ step of the hole (β, new,
    spawn, link) stays at the index and uses the induction over τ steps. A channel step lowers
    the index and uses the induction on n. New keeps the world, so no
    renaming of points is needed. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveRules rules.Bind.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

Lemma LErel_S_step n W Θ T F e σ e' :
  LErel (S n) W Θ T F e → tstep e (LSess σ) e' → LEobl LVrel LErel (S n) W Θ T F σ e'.
Proof.
  intros HE Hst. apply LErel_S_iff in HE.
  destruct (HE W (wext_r_refl W)) as (_ & _ & _ & _ & _ & Hσ & _). by apply Hσ.
Qed.

Lemma LErel_S_link n W Θ T F e cd e' :
  LErel (S n) W Θ T F e → tstep e (LSess (SLink cd)) e' → LElink (λ W Θ F e, LErel (S n) W Θ T F e) W Θ F cd e'.
Proof.
  intros HE Hst. apply LErel_S_iff in HE.
  destruct (HE W (wext_r_refl W)) as (_ & _ & _ & _ & _ & _ & Hl). by apply Hl.
Qed.

Lemma LErel_S_ready n W Θ T F e : LErel (S n) W Θ T F e → ¬ irred e → ready_t W Θ F e.
Proof.
  intros HE. apply LErel_S_iff in HE. by destruct (HE W (wext_r_refl W)) as (_ & ? & _).
Qed.

Lemma LErel_S_stop n W Θ T F e : LErel (S n) W Θ T F e → irred e → LVrel (S n) W Θ T e.
Proof.
  intros HE. apply LErel_S_iff in HE. by destruct (HE W (wext_r_refl W)) as (? & _).
Qed.

Lemma LErel_subjs n W Θ T F e σ e' :
  LErel (S n) W Θ T F e → tstep e (LSess σ) e' → subjs σ ⊆ dom Θ.
Proof.
  intros HE Hst. pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc.
  destruct σ as [c w|c w|c|cd|c i|c i]; simpl in Hc |- *;
    [| | |pose proof (LErel_S_link _ _ _ _ _ _ _ _ HE Hst) as Hc'; clear Hc; rename Hc' into Hc| |].
  5,6: destruct Hc as (Θr & s1 & s2 & k & Θ' & (s0 & Hext & _) & _);
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (Θ1 & m & U & s & k & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (Θ1 & k & (s0 & Hext & _) & _).
    destruct Hext as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L; set_solver.
  - destruct Hc as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & _).
    destruct H2 as [[_ ->]|(f & _ & [-> | ->])]; rewrite dom_insert_L;
    destruct H1 as [[_ ->]|(g & _ & [-> | ->])]; rewrite ?dom_insert_L; set_solver.
Qed.

Lemma Loffered_some n W Θ T F e σ e' :
  LErel (S n) W Θ T F e → tstep e (LSess σ) e' → ∃ k, offered_t Θ e k.
Proof.
  intros HE Hst. pose proof (LErel_subjs _ _ _ _ _ _ _ _ HE Hst) as Hsub.
  pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep.
  assert (∀ c u k Θr, tenv_hd Θ c u k Θr → ∃ b s, tenv_entry Θ (c, b) = Some (s, k) ∧ unfoldS s = u)
    as Hhd.
  { intros c u k Θr (s & [(_ & ->)|(e0 & _ & [->| ->])] & Hu).
    - exists false, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq.
    - exists false, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq.
    - exists true, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq. }
  destruct σ as [c w|c w|c|cd|c i|c i]; simpl in Hstep.
  5: { destruct Hstep as (Θr & s1 & s2 & k & Θ' & Hh & _).
       destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
       exists (c, b), (SSel c i), e'. split; [done|]. split; [done|]. eauto 10. }
  5: { destruct Hstep as (Θr & s1 & s2 & k & Θ' & Hh & _).
       destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
       exists (c, b), (SBra c i), e'. split; [done|]. split; [done|]. eauto 10. }
  - destruct Hstep as (Θ1 & m & U & s & k & Hh & _). destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    exists (c, b), (SRecv c w), e'. split; [done|]. split; [done|]. eauto 10.
  - destruct Hstep as (Θr & ? & ? & m & U & s & k & ? & Hh & _).
    destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    exists (c, b), (SSend c w), e'. split; [done|]. split; [done|]. eauto 10.
  - destruct Hstep as (Θ1 & k & Hh & _). destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    destruct b.
    + destruct (tenv_entry Θ (c, false)) as [e0|] eqn:E0.
      * assert (unfoldS e0.1 = SEnd ∨ unfoldS e0.1 ≠ SEnd) as [Hu0|Hu0]
          by (destruct (unfoldS e0.1); first [by left|by right]).
        -- exists (c, false), (SClos c), e'. split; [done|]. split; [done|].
           exists e0. split_and!; [done|done|discriminate].
        -- exists (c, true), (SClos c), e'. split; [done|]. split; [done|].
           exists (s0, k). split_and!; [done|done|]. intros _ e1 He1. congruence.
      * exists (c, true), (SClos c), e'. split; [done|]. split; [done|].
        exists (s0, k). split_and!; [done|done|]. intros _ e1 He1. congruence.
    + exists (c, false), (SClos c), e'. split; [done|]. split; [done|].
      exists (s0, k). split_and!; [done|done|discriminate].
  - destruct (set_choose_or_empty cd) as [[c Hc]|Hcd].
    + assert (c ∈ dom Θ) as HcΘ by (apply Hsub; done). apply elem_of_dom in HcΘ as [o Ho].
      exists (c, false), (SLink cd), e'. split; [done|]. split; [done|].
      unfold tenv_entry. simpl. rewrite Ho. destruct o; by eexists.
    + exfalso. destruct (LErel_S_link _ _ _ _ _ _ _ _ HE Hst) as (c & d & ? & ? & ? & ? & ? & ? & -> & _). set_solver.
Qed.

(** With the comparisons of readiness in hand, the redex acts on no
    channel of the context. *)
Lemma Lsubjs_free_br n W Θ Θ1 Θ2 Th F H e σ e' :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above_x W H Θ2 →
  LErel (S n) W Θ1 Th (F ∪ H) e → below_rest W Θ1 (offered_t Θ1 e) (F ∪ H) →
  tstep e (LSess σ) e' → subjs σ ## dom Θ2.
Proof.
  intros [HWf Hirr] [Hj Hd] Hh HE Hfr Hst c Hc1 Hc2.
  pose proof (LErel_subjs _ _ _ _ _ _ _ _ HE Hst c Hc1) as Hc1'.
  pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep.
  apply elem_of_dom in Hc1' as [o1 Ho1]. apply elem_of_dom in Hc2 as [o2 Ho2].
  pose proof (Hj c) as Jc. rewrite Ho1, Ho2 in Jc. inversion Jc as [| | |e1 e2|e1 e2]; subst.
  all: destruct (Hd c e1 e2 Ho1 Ho2) as [Hq _].
  all: assert (tenv_entry Θ1 (c, false) = Some e1) as Hen by (unfold tenv_entry; simpl; by rewrite Ho1).
  all: assert (offered_t Θ1 e (c, false)) as Hoff.
  all: try (exists σ, e'; split; [done|];
            destruct σ as [c0 w|c0 w|c0|cd|c0 i|c0 i]; simpl in Hc1, Hstep |- *;
            [apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θ1r & m & U & s & k & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & ? & ? & m & U & s & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & k & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|];
             exists e1; split_and!; [done|done|discriminate]
            |split; [done|by eexists]
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & s1 & s2 & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & s1 & s2 & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10]).
  all: pose proof (proj2 (Hfr (c, false) e1 Hoff Hen)) as Hlt.
  all: destruct Hh as [Hh|Hb]; [|by apply (no_lt_pbot W e1.2 HWf), Hlt, elem_of_union_r].
  all: assert (tenv_entry Θ2 (c, false) = Some e2) as Hen2 by (unfold tenv_entry; simpl; by rewrite Ho2).
  all: destruct (Hh _ _ Hen2) as (h & HhH & Hle).
  all: pose proof (Hlt h ltac:(set_solver)) as Hlh; unfold entry_head in Hlh; simpl in Hlh.
  all: apply (Hirr e1.2); destruct Hle as [Heq|Hlt'].
  all: try (eapply (wf_lt_eq _ HWf); [reflexivity|exact Hlh|];
            eapply (wf_eq_trans _ HWf); [exact Heq|by apply (wf_eq_sym _ HWf)]).
  all: eapply (wf_lt_eq _ HWf); [reflexivity|eapply (wf_lt_trans _ HWf); [exact Hlh|exact Hlt']|];
         by apply (wf_eq_sym _ HWf).
Qed.

(** A redex other than a link acts on no channel of the context. A link
    may act on the other end of a channel the context holds, because a
    term at a link compares nothing (sharp edges 68). *)
Lemma Lsubjs_free n W Θ Θ1 Θ2 Th F H e σ e' :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above_x W H Θ2 →
  LErel (S n) W Θ1 Th (F ∪ H) e → tstep e (LSess σ) e' → (∀ cd, σ ≠ SLink cd) →
  subjs σ ## dom Θ2.
Proof.
  intros HW Hc Hh HE Hst Hnl.
  pose proof (sess_stable _ _ _ Hst) as Hs.
  assert (¬ irred e) as Hni by (intros Hi; by apply (Hi _ _ Hst)).
  pose proof (LErel_S_ready _ _ _ _ _ _ HE) as Hrdy.
  destruct (Hrdy Hni Hs) as [_ [Hl|Hfr]].
  - destruct (link_t_only _ _ _ Hl Hst) as [cd ->]. by destruct (Hnl cd).
  - exact (Lsubjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hfr Hst).
Qed.

Section Lbind_ready.
  Context (n : nat) (W : world) (Θ Θ1 Θ2 : tenv) (Th : ty) (F H : gset point).
  Context (f : frame) (e : expr).
  Context (Hf : frame_val f) (Hv : ¬ is_val e) (HW : strict W).
  Context (Hc : tenv_comp (w_eq W) Θ Θ1 Θ2) (Hh : heads_above_x W H Θ2).
  Context (HE : LErel (S n) W Θ1 Th (F ∪ H) e).

  Section Lbind_ready_br.
  Context (Hbr : below_rest W Θ1 (offered_t Θ1 e) (F ∪ H)).

  Lemma Lbr_up k : offered_t Θ1 e k → offered_t Θ (fill_frame f e) k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & e' & Hst & Hsel).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (Lsubjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, (fill_frame f e'). split; [by apply tstep_fill|].
    eapply selects_agree; [|exact Hsel]. intros y Hy.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (Lsubjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst y Hy).
  Qed.

  Lemma Lbr_down k : offered_t Θ (fill_frame f e) k → offered_t Θ1 e k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & E' & Hst & Hsel).
    destruct (tstep_fill_inv _ _ _ _ Hf Hv Hst) as (e' & Hst' & ->).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (Lsubjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst' (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, e'. split; [done|].
    eapply selects_agree; [|exact Hsel]. intros y Hy. symmetry.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (Lsubjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst' y Hy).
  Qed.
  End Lbind_ready_br.

  Lemma Lbr_stable : stable_t (fill_frame f e) → stable_t e.
  Proof. intros Hs α e' Hst. exact (Hs _ _ (tstep_fill _ _ _ _ Hf Hst)). Qed.

  Lemma Lbind_ready : ready_t W Θ F (fill_frame f e).
  Proof.
    pose proof (LErel_S_ready _ _ _ _ _ _ HE) as Hrdy. pose proof (LErel_S_stop _ _ _ _ _ _ HE) as Hval.
    assert (¬ irred e) as Hni by (intros Hi; apply Hv; by eapply LVrel_val, Hval).
    intros Hs. pose proof (Lbr_stable Hs) as Hse. destruct (Hrdy Hni Hse) as [_ Hab].
    destruct Hab as [(cd & e1 & Hl)|Hab].
    { (* a link redex: K[e] offers its entries and compares nothing *)
      split; [|left; exists cd, (fill_frame f e1); by apply tstep_fill].
      intros Hno. exfalso.
      destruct (Loffered_some _ _ _ _ _ _ _ _ HE Hl) as [k0 (σ & e' & Hst & Hsel)].
      destruct (link_t_only e σ e' (ex_intro _ cd (ex_intro _ e1 Hl)) Hst) as [cd' ->].
      apply (Hno k0). exists (SLink cd'), (fill_frame f e'). split; [by apply tstep_fill|].
      destruct Hsel as [Hk Hent]. split; [done|]. exact (comp_entry_some _ _ _ _ _ Hc Hent). }
    split.
    - destruct (tstep_progress e) as [Hi|(α & e' & Hst)]; [by destruct Hni|].
      pose proof (Hse _ _ Hst) as Hα. destruct α as [|σ|c|w]; try done.
      destruct (Loffered_some _ _ _ _ _ _ _ _ HE Hst) as [k0 Hk0].
      destruct (Lbr_up Hab k0 Hk0) as [Hk0' _].
      intros Hno. exfalso. exact (Hno k0 Hk0').
    - right. intros k0 ent0 Hoff0 Hent0.
      destruct (Lbr_down Hab k0 Hoff0) as [Hk0 Hk0f].
      rewrite (surjective_pairing k0), (entry_agree _ _ _ _ _ _ Hc) in Hent0 by done.
      rewrite <-surjective_pairing in Hent0.
      destruct (Hab k0 ent0 Hk0 Hent0) as [H1 H2].
      destruct Hh as [Hh'|Hb];
        [|exfalso; by apply (no_lt_pbot W (entry_head k0 ent0) (proj1 HW)), H2, elem_of_union_r].
      split.
      + intros [c b] ent Hent Hnot.
        destruct (decide (c ∈ dom Θ2)) as [Hin|Hnin].
        * change (entry_head (c, b) ent) with ent.2.
          apply elem_of_dom in Hin as [o2 Ho2]. pose proof Hc as [Hj Hd].
          pose proof (Hj c) as Jc. unfold tenv_entry in Hent. simpl in Hent. rewrite Ho2 in Jc.
          assert (Hn1 : ∀ e1, Θ1 !! c = Some (One e1) → w_lt W (entry_head k0 ent0) (pt_dual e1.2)).
          { intros e1 He1. apply (H1 (c, false) e1); [unfold tenv_entry; simpl; by rewrite He1|].
            intros Ho'. apply (proj2 (Lbr_up Hab _ Ho')). simpl. by apply elem_of_dom_2 in Ho2. }
          assert (Hn2 : ∀ k' e2, tenv_entry Θ2 k' = Some e2 → w_lt W (entry_head k0 ent0) (pt_dual e2.2)).
          { intros k' e2 He2. destruct (Hh' k' e2 He2) as (h & HhH & Hle).
            eapply lt_le_W; [apply HW| |exact Hle]. apply H2. by apply elem_of_union_r. }
          destruct (Θ1 !! c) as [o1|] eqn:Ho1, (Θ !! c) as [o|] eqn:Ho;
            inversion Jc; subst; try done.
          all: first [ apply (Hn2 (c, b)); unfold tenv_entry; simpl; rewrite Ho2; done
                     | destruct b; simplify_eq;
                       first [ by apply Hn1
                             | apply (Hn2 (c, false)); unfold tenv_entry; simpl; by rewrite Ho2 ] ].
        * rewrite (entry_agree _ _ _ _ _ _ Hc) in Hent by done.
          apply (H1 (c, b) ent Hent). intros Ho'. apply Hnot. exact (proj1 (Lbr_up Hab _ Ho')).
      + intros y Hy. apply H2. by apply elem_of_union_l.
  Qed.
End Lbind_ready.

(** ** Facts of the composition in a later world *)

Lemma wext_r_strict W W1 : strict W → wext_r W W1 → strict W1.
Proof. intros HW [->|H]; [done|apply H]. Qed.

Lemma heads_above_x_mono_r W W1 H Θ2 :
  wext_r W W1 → heads_above_x W H Θ2 → heads_above_x W1 H Θ2.
Proof. intros [->|HW] Hh; [done|by eapply heads_above_x_mono]. Qed.

Lemma wext_r_wext W W1 W' : strict W → wext_r W W1 → wext W1 W' → wext W W'.
Proof. intros _ [->|HW] HW'; [done|by eapply wext_trans]. Qed.

(** ** The bind lemma *)

Lemma LErel_bind n : ∀ f W Θ Θ1 Θ2 Th T F H e,
  frame_val f → strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above_x W H Θ2 →
  LErel n W Θ1 Th (F ∪ H) e →
  (∀ W' j Θ1' Θ' v, wext W W' → j ≤ n → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
     LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) →
  LErel n W Θ T F (fill_frame f e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros f W Θ Θ1 Θ2 Th T F H e Hf HW Hc Hh HE HK.
  destruct n as [|n']; [apply LErel_0|].
  remember (F ∪ H) as FH eqn:HFH.
  revert Θ Hc HK Hh HW HFH.
  revert W Θ1 Th FH e HE.
  refine (LErel_S_ind n' (λ W Θ1 Th FH e, ∀ Θ,
            tenv_comp (w_eq W) Θ Θ1 Θ2 →
            (∀ W' j Θ1' Θ' v, wext W W' → j ≤ S n' → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
               LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) →
            heads_above_x W H Θ2 → strict W → FH = F ∪ H →
            LErel (S n') W Θ T F (fill_frame f e)) _).
  intros W Θ1 Th FH e Hstep Θ Hc HK Hh HW ->.
  assert (HE : LErel (S n') W Θ1 Th (F ∪ H) e).
  { apply LErel_S_iff. eapply LEstep_mono; [|exact Hstep]. by intros ? ? ? ? ? [? _]. }
  destruct (is_val e) eqn:Hv.
  { apply (HK W (S n') Θ1 Θ e); [by apply wext_refl|lia|done|].
    apply (LErel_S_stop _ _ _ _ _ _ HE), val_irred. by rewrite Hv. }
  assert (¬ is_val e) as Hnv by (rewrite Hv; intros []).
  apply LErel_S_iff. intros W1 HW1.
  pose proof (wext_r_strict _ _ HW HW1) as HW1s.
  assert (tenv_comp (w_eq W1) Θ Θ1 Θ2) as Hc1.
  { exact Hc. }
  pose proof (heads_above_x_mono_r _ _ _ _ HW1 Hh) as Hh1.
  pose proof (LErel_mono _ _ _ _ _ _ _ HW1 HE) as HE1.
  assert (rdsym (w_eq W1)) as Hsym by apply eq_rdsym.
  assert (∀ W' j Θ1' Θ' v, wext W1 W' → j ≤ S n' → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
            LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) as HK1.
  { intros W' j Θ1' Θ' v HW' Hj Hc' HV'. apply (HK W' j Θ1' Θ' v); [|done..].
    by eapply wext_r_wext. }
  destruct (Hstep W1 HW1) as (Hval & Hrdy & Hbeta & Hnew & Hsp & Hσ & Hlk).
  assert (∀ W' j, wext W1 W' → j ≤ n' →
            ∀ W'' j' Θ1' Θ' v, wext W' W'' → j' ≤ j → tenv_comp (w_eq W'') Θ' Θ1' Θ2 →
              LVrel j' W'' Θ1' Th v → LErel j' W'' Θ' T F (fill_frame f v)) as HKd.
  { intros W' j HW' Hj W'' j' Θ1' Θ' v HW'' Hj' Hc' HV.
    apply (HK1 W'' j' Θ1' Θ' v); [by eapply wext_trans|lia|done|done]. }
  split_and!.
  - intros Hirr. exfalso. apply Hnv. eapply LVrel_val, Hval.
    intros α e' Hst. by apply (Hirr α (fill_frame f e')), tstep_fill.
  - intros _. exact (Lbind_ready n' W1 Θ Θ1 Θ2 Th F H f e Hf Hnv HW1s Hc1 Hh1 HE1).
  - intros E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hbeta e' Hst') as [_ HΦ]. by apply HΦ.
  - intros c E' Hst HcΘ. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    assert (Θ1 !! c = None ∧ Θ2 !! c = None) as [H1c H2c].
    { rewrite (tenv_join_dom _ _ _ (proj1 Hc1)) in HcΘ.
      split; apply not_elem_of_dom; clear -HcΘ; set_solver. }
    destruct (Hnew c e' Hst' ltac:(by apply not_elem_of_dom))
      as (x & s & s' & Hx & Hdd & _ & HΦ).
    exists x, s, s'. split_and!; [done|done|].
    apply HΦ; [by apply comp_insert|exact HK1|done|done|done].
  - intros w E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hsp w e' Hst') as (Θa & Θb & ub & lb & HcAB & HV & _ & HΦ).
    destruct (comp_assoc _ _ _ _ _ _ Hsym Hc1 (comp_comm _ _ _ _ Hsym HcAB)) as [HX1 HX2].
    exists Θa, (tjoin_as Θ Θb Θ2), ub, lb. split_and!.
    + by apply comp_comm.
    + eapply Vspawn_mono; [|exact HV]. by intros ? ? ? ? [? _].
    + apply HΦ; [exact HX1|exact HK1|done|done|done].
  - intros σ E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    pose proof (Hσ σ e' Hst') as Hcase.
    assert (∀ σ', σ = σ' → (∀ cd, σ' ≠ SLink cd) → subjs σ' ## dom Θ2) as Hfree.
    { intros σ' <-. exact (Lsubjs_free _ _ _ _ _ _ _ _ _ _ _ HW1s Hc1 Hh1 HE1 Hst'). }
    destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LEobl pred] in Hcase |- *.
    + (* receive *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & m & U & s & k & (s0 & Hext & Hu) & Hcont).
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), m, U, s, k. split; [by exists s0|].
      intros W' j Θp Θrc Θ' HW' Hj Hextc Hcomp' HV.
      pose proof (proj2 (proj2 (proj2 HW'))) as HWs'.
      assert (rdsym (w_eq W')) as Hsym' by apply eq_rdsym.
      pose proof Hcr as Hcr'.
      destruct (comp_ext_back _ _ _ _ _ c _ Hcr' H2c Hextc) as [Hc1' Hext1].
      destruct (comp_assoc _ _ _ _ _ _ Hsym' Hcomp' Hc1') as [HX1 HX2].
      pose proof (Hcont W' j Θp _ _ HW' Hj Hext1 HX1 HV) as HEj.
      eapply (IHn j); [lia|done|done|exact HX2|by eapply heads_above_x_mono|exact HEj|].
      apply (HKd W' j); [done|done].
    + (* send *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & A & B & m & U & s & k & Θ1' & (s0 & Hext & Hu) & HcAB & HV & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      destruct (comp_assoc _ _ _ _ _ _ Hsym Hcr HcAB) as [HX1 HX2].
      set (X := tjoin_as (partial_alter (λ _, Θ1r !! c) c Θ) A Θ2) in *.
      exists (partial_alter (λ _, Θ1r !! c) c Θ), X, B, m, U, s, k,
        (partial_alter (λ _, Θ1' !! c) c X).
      split_and!; [by exists s0|done|done| |].
      * eapply ext_transfer; [exact Hext'|by apply (comp_lookup _ _ _ _ _ HX1)|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite lookup_partial_alter_ne.
      * pose proof (comp_set _ _ _ _ c (Θ1' !! c) HX1 H2c) as Hcs.
        rewrite (palter_eq A Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
        eapply (IHn n'); [lia|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
    + (* close *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1' & k & (s0 & Hext & Hu) & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1' !! c) c Θ), k. split; [by exists s0|].
      eapply (IHn n'); [lia|done|done|exact Hcr|done|exact HE'|].
      apply (HKd W1 n'); [by apply wext_refl|done].
    + (* link: O-Link below *)
      done.
    + (* select *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * eapply (IHn n'); [lia|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
    + (* branch *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * eapply (IHn n'); [lia|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
  - (* O-Link: a τ of the hole, at the index *)
    intros cd E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hlk cd e' Hst') as (c & d & Θ1' & Θm & sc & sd & kc & kd & -> & Hx1 & Hx2 & Hdu & Heq & [_ HΦ]).
    destruct (comp_ext_gen _ _ _ _ _ c _ Hc1 Hx2) as (Θm' & Hcm & Hextm).
    destruct (comp_ext_gen _ _ _ _ _ d _ Hcm Hx1) as (Θ1'' & Hc1'' & Hext1).
    eexists c, d, _, _, sc, sd, kc, kd. split_and!; [done|exact Hext1|exact Hextm|done|done|].
    apply HΦ; [exact Hc1''|exact HK1|done|done|done].
Qed.

(** ** Bind with a condition on the returns of the hole

    [R] holds of the hole and is closed under its τ steps. The
    continuation is needed at the current index only for values that
    satisfy [R]. With [R] false of values, the hole cannot return before
    its first channel step, and the continuation is needed below the
    index only (the guard, liveness.md §6). *)

Inductive tadmin : expr → expr → Prop :=
  | TABeta e e' : tstep e LBeta e' → tadmin e e'
  | TANew e c e' : tstep e (LNew c) e' → tadmin e e'
  | TASpawn e w e' : tstep e (LSpawn w) e' → tadmin e e'
  | TALink e cd e' : tstep e (LSess (SLink cd)) e' → tadmin e e'.

Lemma LErel_bind_R n : ∀ (R : expr → Prop) f W Θ Θ1 Θ2 Th T F H e,
  (∀ e e', R e → tadmin e e' → R e') → R e →
  frame_val f → strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above_x W H Θ2 →
  LErel n W Θ1 Th (F ∪ H) e →
  (∀ W' j Θ1' Θ' v, wext W W' → j ≤ n → (j = n → R v) → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
     LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) →
  LErel n W Θ T F (fill_frame f e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros R f W Θ Θ1 Θ2 Th T F H e HRc HRe Hf HW Hc Hh HE HK.
  destruct n as [|n']; [apply LErel_0|].
  remember (F ∪ H) as FH eqn:HFH.
  revert Θ Hc HK Hh HW HFH HRe.
  revert W Θ1 Th FH e HE.
  refine (LErel_S_ind n' (λ W Θ1 Th FH e, ∀ Θ,
            tenv_comp (w_eq W) Θ Θ1 Θ2 →
            (∀ W' j Θ1' Θ' v, wext W W' → j ≤ S n' → (j = S n' → R v) →
               tenv_comp (w_eq W') Θ' Θ1' Θ2 →
               LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) →
            heads_above_x W H Θ2 → strict W → FH = F ∪ H → R e →
            LErel (S n') W Θ T F (fill_frame f e)) _).
  intros W Θ1 Th FH e Hstep Θ Hc HK Hh HW -> HRe.
  assert (HE : LErel (S n') W Θ1 Th (F ∪ H) e).
  { apply LErel_S_iff. eapply LEstep_mono; [|exact Hstep]. by intros ? ? ? ? ? [? _]. }
  destruct (is_val e) eqn:Hv.
  { apply (HK W (S n') Θ1 Θ e); [by apply wext_refl|lia|done|done|].
    apply (LErel_S_stop _ _ _ _ _ _ HE), val_irred. by rewrite Hv. }
  assert (¬ is_val e) as Hnv by (rewrite Hv; intros []).
  apply LErel_S_iff. intros W1 HW1.
  pose proof (wext_r_strict _ _ HW HW1) as HW1s.
  assert (tenv_comp (w_eq W1) Θ Θ1 Θ2) as Hc1.
  { exact Hc. }
  pose proof (heads_above_x_mono_r _ _ _ _ HW1 Hh) as Hh1.
  pose proof (LErel_mono _ _ _ _ _ _ _ HW1 HE) as HE1.
  assert (rdsym (w_eq W1)) as Hsym by apply eq_rdsym.
  assert (∀ W' j Θ1' Θ' v, wext W1 W' → j ≤ S n' → (j = S n' → R v) →
            tenv_comp (w_eq W') Θ' Θ1' Θ2 →
            LVrel j W' Θ1' Th v → LErel j W' Θ' T F (fill_frame f v)) as HK1.
  { intros W' j Θ1' Θ' v HW' Hj HRv Hc' HV'. apply (HK W' j Θ1' Θ' v); [|done..].
    by eapply wext_r_wext. }
  destruct (Hstep W1 HW1) as (Hval & Hrdy & Hbeta & Hnew & Hsp & Hσ & Hlk).
  assert (∀ W' j, wext W1 W' → j ≤ n' →
            ∀ W'' j' Θ1' Θ' v, wext W' W'' → j' ≤ j → (j' = j → True) →
              tenv_comp (w_eq W'') Θ' Θ1' Θ2 →
              LVrel j' W'' Θ1' Th v → LErel j' W'' Θ' T F (fill_frame f v)) as HKd.
  { intros W' j HW' Hj W'' j' Θ1' Θ' v HW'' Hj' _ Hc' HV.
    apply (HK1 W'' j' Θ1' Θ' v); [by eapply wext_trans|lia|lia|done|done]. }
  split_and!.
  - intros Hirr. exfalso. apply Hnv. eapply LVrel_val, Hval.
    intros α e' Hst. by apply (Hirr α (fill_frame f e')), tstep_fill.
  - intros _. exact (Lbind_ready n' W1 Θ Θ1 Θ2 Th F H f e Hf Hnv HW1s Hc1 Hh1 HE1).
  - intros E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hbeta e' Hst') as [_ HΦ]. apply HΦ; try done. eapply HRc; [exact HRe|by econstructor].
  - intros c E' Hst HcΘ. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    assert (Θ1 !! c = None ∧ Θ2 !! c = None) as [H1c H2c].
    { rewrite (tenv_join_dom _ _ _ (proj1 Hc1)) in HcΘ.
      split; apply not_elem_of_dom; clear -HcΘ; set_solver. }
    destruct (Hnew c e' Hst' ltac:(by apply not_elem_of_dom))
      as (x & s & s' & Hx & Hdd & _ & HΦ).
    exists x, s, s'. split_and!; [done|done|].
    apply HΦ; [by apply comp_insert|exact HK1|done|done|done|eapply HRc; [exact HRe|by econstructor]].
  - intros w E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hsp w e' Hst') as (Θa & Θb & ub & lb & HcAB & HV & _ & HΦ).
    destruct (comp_assoc _ _ _ _ _ _ Hsym Hc1 (comp_comm _ _ _ _ Hsym HcAB)) as [HX1 HX2].
    exists Θa, (tjoin_as Θ Θb Θ2), ub, lb. split_and!.
    + by apply comp_comm.
    + eapply Vspawn_mono; [|exact HV]. by intros ? ? ? ? [? _].
    + apply HΦ; [exact HX1|exact HK1|done|done|done|eapply HRc; [exact HRe|by econstructor]].
  - intros σ E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    pose proof (Hσ σ e' Hst') as Hcase.
    assert (∀ σ', σ = σ' → (∀ cd, σ' ≠ SLink cd) → subjs σ' ## dom Θ2) as Hfree.
    { intros σ' <-. exact (Lsubjs_free _ _ _ _ _ _ _ _ _ _ _ HW1s Hc1 Hh1 HE1 Hst'). }
    destruct σ as [c w|c w|c|cd|c i|c i]; cbn [LEobl pred] in Hcase |- *.
    + (* receive *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & m & U & s & k & (s0 & Hext & Hu) & Hcont).
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), m, U, s, k. split; [by exists s0|].
      intros W' j Θp Θrc Θ' HW' Hj Hextc Hcomp' HV.
      pose proof (proj2 (proj2 (proj2 HW'))) as HWs'.
      assert (rdsym (w_eq W')) as Hsym' by apply eq_rdsym.
      pose proof Hcr as Hcr'.
      destruct (comp_ext_back _ _ _ _ _ c _ Hcr' H2c Hextc) as [Hc1' Hext1].
      destruct (comp_assoc _ _ _ _ _ _ Hsym' Hcomp' Hc1') as [HX1 HX2].
      pose proof (Hcont W' j Θp _ _ HW' Hj Hext1 HX1 HV) as HEj.
      eapply (IHn j ltac:(lia) (λ _, True)); [intros; done|done|done|done|exact HX2|by eapply heads_above_x_mono|exact HEj|].
      apply (HKd W' j); [done|done].
    + (* send *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & A & B & m & U & s & k & Θ1' & (s0 & Hext & Hu) & HcAB & HV & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      destruct (comp_assoc _ _ _ _ _ _ Hsym Hcr HcAB) as [HX1 HX2].
      set (X := tjoin_as (partial_alter (λ _, Θ1r !! c) c Θ) A Θ2) in *.
      exists (partial_alter (λ _, Θ1r !! c) c Θ), X, B, m, U, s, k,
        (partial_alter (λ _, Θ1' !! c) c X).
      split_and!; [by exists s0|done|done| |].
      * eapply ext_transfer; [exact Hext'|by apply (comp_lookup _ _ _ _ _ HX1)|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite lookup_partial_alter_ne.
      * pose proof (comp_set _ _ _ _ c (Θ1' !! c) HX1 H2c) as Hcs.
        rewrite (palter_eq A Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
        eapply (IHn n' ltac:(lia) (λ _, True)); [intros; done|done|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
    + (* close *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1' & k & (s0 & Hext & Hu) & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1' !! c) c Θ), k. split; [by exists s0|].
      eapply (IHn n' ltac:(lia) (λ _, True)); [intros; done|done|done|done|exact Hcr|done|exact HE'|].
      apply (HKd W1 n'); [by apply wext_refl|done].
    + (* link: O-Link below *)
      done.
    + (* select *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * eapply (IHn n' ltac:(lia) (λ _, True)); [intros; done|done|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
    + (* branch *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc1 H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * eapply (IHn n' ltac:(lia) (λ _, True)); [intros; done|done|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W1 n'); [by apply wext_refl|done].
  - (* O-Link: a τ of the hole, at the index *)
    intros cd E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    destruct (Hlk cd e' Hst') as (c & d & Θ1' & Θm & sc & sd & kc & kd & -> & Hx1 & Hx2 & Hdu & Heq & [_ HΦ]).
    destruct (comp_ext_gen _ _ _ _ _ c _ Hc1 Hx2) as (Θm' & Hcm & Hextm).
    destruct (comp_ext_gen _ _ _ _ _ d _ Hcm Hx1) as (Θ1'' & Hc1'' & Hext1).
    eexists c, d, _, _, sc, sd, kc, kd. split_and!; [done|exact Hext1|exact Hextm|done|done|].
    apply HΦ; [exact Hc1''|exact HK1|done|done|done|eapply HRc; [exact HRe|by econstructor]].
Qed.


