(** * The source rules of [styped] as lemmas, and an induction principle

    [styped] is the instance of [typed] at Θ = ∅ and [wnil]
    (static/Source.v). Its rules read off the hypotheses Ψ alone
    ([heqs], [hlt], [hyp_known]). [sderiv] is that rule set as an
    inductive, and [styped_sderiv_iff] shows it has the same
    derivations as [styped]. The lemmas [st_unit] … [st_open] are the
    rules stated for [styped]. A proof by induction on a source
    derivation converts with [styped_sderiv] and inducts on [sderiv]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Source.

Set Default Proof Using "All".

Inductive sderiv : fhyps → hyps → lenv → sfuture → expr → ty → Prop :=
  | sr_unit Φ Ψ Δ F :                                   (* E-Unit *)
      lenv_empty Δ →
      sderiv Φ Ψ Δ F EUnit TUnit
  | sr_konst Φ Ψ Δ F k T :                              (* E-Const *)
      lenv_empty Δ → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T → kscoped k T →
      sderiv Φ Ψ Δ F (Konst k) T
  | sr_var Φ Ψ Δ F x T :                                (* E-LVar *)
      lenv_only Δ x T →
      sderiv Φ Ψ Δ F (Var x) T
  | sr_lam Φ Ψ Δ F e T U ub lb φ :                      (* E-Abs *)
      φ ∉ dom Φ →
      hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
      sderiv (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
      sderiv Φ Ψ Δ F (Lam e) (TLolli ub lb T U)
  | sr_app Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U :              (* E-App *)
      lenv_split Δ Δ1 Δ2 → hub_below_s Ψ Φ ub F →
      sderiv Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
      sderiv Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 T →
      sderiv Φ Ψ Δ F (App e1 e2) U
  | sr_pair Φ Ψ Δ Δ1 Δ2 F e1 e2 T U :                   (* E-Pair *)
      lenv_split Δ Δ1 Δ2 →
      sderiv Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
      sderiv Φ Ψ Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
      sderiv Φ Ψ Δ F (Pair e1 e2) (TProd T U)
  | sr_letu Φ Ψ Δ Δ1 Δ2 F e1 e2 T :                     (* E-Let* *)
      lenv_split Δ Δ1 Δ2 →
      sderiv Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
      sderiv Φ Ψ Δ2 F e2 T →
      sderiv Φ Ψ Δ F (LetU e1 e2) T
  | sr_letp Φ Ψ Δ Δ1 Δ2 F e1 e2 T1 T2 T :               (* E-LetPair *)
      lenv_split Δ Δ1 Δ2 →
      sderiv Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
      sderiv Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T →
      sderiv Φ Ψ Δ F (LetP e1 e2) T
  | sr_inj1 Φ Ψ Δ F e T U :                             (* E-Inj *)
      sderiv Φ Ψ Δ F e T → sderiv Φ Ψ Δ F (Inj1 e) (TSum T U)
  | sr_inj2 Φ Ψ Δ F e T U :
      sderiv Φ Ψ Δ F e U → sderiv Φ Ψ Δ F (Inj2 e) (TSum T U)
  | sr_case Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :             (* E-Case *)
      lenv_split Δ Δ1 Δ2 →
      sderiv Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
      sderiv Φ Ψ (Some T1 :: Δ2) F e1 T →
      sderiv Φ Ψ (Some T2 :: Δ2) F e2 T →
      sderiv Φ Ψ Δ F (Case e e1 e2) T
  | sr_box Φ Ψ Δ F e m k C ub T φ :                     (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      (∀ ss, length ss = k → Forall hcontractive ss →
         sderiv (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
           (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
           (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ))
           (∅, Some (FVar φ)) e (sinst_ty (slist ss) T)) →
      sderiv Φ Ψ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T))
  | sr_wk Φ Ψ Δ' Δ F e T :                              (* E-Weak *)
      lenv_wk Δ' Δ → sderiv Φ Ψ Δ' F e T → sderiv Φ Ψ Δ F e T
  | sr_contract Φ Ψ Δ U F e T :                         (* E-Contract *)
      unlimited U →
      sderiv Φ Ψ (Some U :: Some U :: Δ) F e T →
      sderiv Φ Ψ (Some U :: Δ) F (rename pred e) T
  | sr_conv Φ Ψ Δ F e T T' :                            (* E-Conv *)
      hsteq Ψ T T' → sderiv Φ Ψ Δ F e T → sderiv Φ Ψ Δ F e T'
  | sr_pack Φ Ψ Δ F e lb m C T xs :                     (* E-Pack *)
      length xs = m → Forall (hyp_known Ψ) xs → bcs_hold (heqs Ψ) (hlt Ψ) C xs →
      hlbx_below_h Ψ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      sderiv Φ Ψ Δ F e (ty_inst xs T) → sderiv Φ Ψ Δ F e (TEx lb m C T)
  | sr_open Φ Ψ Δ F e i lb m C T U :                    (* E-Open *)
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      sderiv (fhyps_pinst (pshift m) Φ)
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
      sderiv Φ Ψ Δ F e U.

Lemma sderiv_styped Φ Ψ Δ F e T : sderiv Φ Ψ Δ F e T → styped Φ Ψ Δ F e T.
Proof.
  unfold styped. induction 1.
  - by apply t_unit.
  - apply t_const; [done| |done]. by apply hkonst_ty.
  - by apply t_var.
  - eapply t_abs; [done| |exact IHsderiv].
    rewrite tenv_heads_empty, (left_id_L ∅ (∪)). by apply hlb_below_hb_lb.
  - eapply t_app; [apply tenv_comp_empty_r|done|by apply hub_below_s_ub| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_pair; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_letstar; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_letpair; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - by apply t_inj1.
  - by apply t_inj2.
  - eapply t_case; [apply tenv_comp_empty_r|done| |done|done].
    by rewrite sf_unionb_tenv0.
  - eapply t_exp; [done|done|]. intros ss Hss Hsc. by apply H2.
  - by eapply t_weak.
  - by apply t_contract.
  - eapply t_conv; [by apply hsteq_steq|done].
  - eapply t_pack; [done| | | |done].
    + eapply Forall_impl; [done|]. intros x. apply hyp_known_skn.
    + eapply bcs_hold_mono; [apply heqs_seqs|apply hlt_slt|done].
    + by apply hlbx_below_h_lbx.
  - eapply t_open; [done|done|]. rewrite tenv_pinst_empty. exact IHsderiv.
Qed.

Lemma styped_sderiv Φ Ψ Δ F e T : styped Φ Ψ Δ F e T → sderiv Φ Ψ Δ F e T.
Proof.
  unfold styped. intros Ht. remember (∅ : tenv) as Θ eqn:HΘ. revert HΘ.
  assert (HW : world_wf wnil) by apply wnil_strict. pose proof wnil_names as HN.
  induction Ht; intros HΘ.
  - by apply sr_unit.
  - apply sr_konst; [done| |done]. by apply (konst_ty_h wnil HW HN).
  - by apply sr_var.
  - exfalso. apply (f_equal dom) in HΘ.
    rewrite dom_singleton_L, dom_empty_L in HΘ. set_solver.
  - subst Θ. eapply sr_lam; [done| |by apply IHHt].
    rewrite tenv_heads_empty, (left_id_L ∅ (∪)) in H0.
    by apply (lb_below_hb_hlb wnil HW HN).
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply sr_app; [done|by apply (ub_below_s_hub wnil HW HN)| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply sr_pair; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply sr_letu; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply sr_letp; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - by apply sr_inj1, IHHt.
  - by apply sr_inj2, IHHt.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply sr_case; [done| |by apply IHHt2|by apply IHHt3].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - eapply sr_box; [done|done|]. intros ss Hss Hsc. by apply H2.
  - eapply sr_wk; [done|by apply IHHt].
  - by apply sr_contract, IHHt.
  - eapply sr_conv; [by apply (steq_hsteq wnil HW HN)|by apply IHHt].
  - eapply sr_pack; [done| | | |by apply IHHt].
    + eapply Forall_impl; [done|]. intros x. by apply (skn_hyp_known wnil HW HN).
    + eapply bcs_hold_mono; [by apply (seqs_heqs wnil HW HN)|by apply (slt_hlt wnil HW HN)|done].
    + by apply (lbx_below_h_hlbx wnil HW HN).
  - subst Θ. eapply sr_open; [done|done|]. apply IHHt. apply tenv_pinst_empty.
Qed.

Corollary styped_sderiv_iff Φ Ψ Δ F e T : styped Φ Ψ Δ F e T ↔ sderiv Φ Ψ Δ F e T.
Proof. split; [apply styped_sderiv|apply sderiv_styped]. Qed.

(** ** The rules, stated for [styped] *)

Local Ltac src_rule c :=
  intros; apply sderiv_styped;
  repeat match goal with H : styped _ _ _ _ _ _ |- _ => apply styped_sderiv in H end;
  eapply c; eauto using styped_sderiv.

Lemma st_unit Φ Ψ Δ F : lenv_empty Δ → styped Φ Ψ Δ F EUnit TUnit.
Proof. src_rule sr_unit. Qed.

Lemma st_konst Φ Ψ Δ F k T :
  lenv_empty Δ → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T → kscoped k T →
  styped Φ Ψ Δ F (Konst k) T.
Proof. src_rule sr_konst. Qed.

Lemma st_var Φ Ψ Δ F x T : lenv_only Δ x T → styped Φ Ψ Δ F (Var x) T.
Proof. src_rule sr_var. Qed.

Lemma st_lam Φ Ψ Δ F e T U ub lb φ :
  φ ∉ dom Φ →
  hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
  styped (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
  styped Φ Ψ Δ F (Lam e) (TLolli ub lb T U).
Proof. src_rule sr_lam. Qed.

Lemma st_app Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U :
  lenv_split Δ Δ1 Δ2 → hub_below_s Ψ Φ ub F →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
  styped Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 T →
  styped Φ Ψ Δ F (App e1 e2) U.
Proof. src_rule sr_app. Qed.

Lemma st_pair Φ Ψ Δ Δ1 Δ2 F e1 e2 T U :
  lenv_split Δ Δ1 Δ2 →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
  styped Φ Ψ Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
  styped Φ Ψ Δ F (Pair e1 e2) (TProd T U).
Proof. src_rule sr_pair. Qed.

Lemma st_letu Φ Ψ Δ Δ1 Δ2 F e1 e2 T :
  lenv_split Δ Δ1 Δ2 →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
  styped Φ Ψ Δ2 F e2 T →
  styped Φ Ψ Δ F (LetU e1 e2) T.
Proof. src_rule sr_letu. Qed.

Lemma st_letp Φ Ψ Δ Δ1 Δ2 F e1 e2 T1 T2 T :
  lenv_split Δ Δ1 Δ2 →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
  styped Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T →
  styped Φ Ψ Δ F (LetP e1 e2) T.
Proof. src_rule sr_letp. Qed.

Lemma st_inj1 Φ Ψ Δ F e T U : styped Φ Ψ Δ F e T → styped Φ Ψ Δ F (Inj1 e) (TSum T U).
Proof. src_rule sr_inj1. Qed.

Lemma st_inj2 Φ Ψ Δ F e T U : styped Φ Ψ Δ F e U → styped Φ Ψ Δ F (Inj2 e) (TSum T U).
Proof. src_rule sr_inj2. Qed.

Lemma st_case Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
  lenv_split Δ Δ1 Δ2 →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
  styped Φ Ψ (Some T1 :: Δ2) F e1 T →
  styped Φ Ψ (Some T2 :: Δ2) F e2 T →
  styped Φ Ψ Δ F (Case e e1 e2) T.
Proof. src_rule sr_case. Qed.

Lemma st_box Φ Ψ Δ F e m k C ub T φ :
  lenv_unl Δ → φ ∉ dom Φ →
  (∀ ss, length ss = k → Forall hcontractive ss →
     styped (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
       (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
       (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ))
       (∅, Some (FVar φ)) e (sinst_ty (slist ss) T)) →
  styped Φ Ψ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T)).
Proof.
  intros HΔ Hφ H. apply sderiv_styped. eapply sr_box; [done|done|].
  intros ss Hss Hsc. by apply styped_sderiv, H.
Qed.

Lemma st_wk Φ Ψ Δ' Δ F e T : lenv_wk Δ' Δ → styped Φ Ψ Δ' F e T → styped Φ Ψ Δ F e T.
Proof. src_rule sr_wk. Qed.

Lemma st_contract Φ Ψ Δ U F e T :
  unlimited U →
  styped Φ Ψ (Some U :: Some U :: Δ) F e T →
  styped Φ Ψ (Some U :: Δ) F (rename pred e) T.
Proof. src_rule sr_contract. Qed.

Lemma st_conv Φ Ψ Δ F e T T' : hsteq Ψ T T' → styped Φ Ψ Δ F e T → styped Φ Ψ Δ F e T'.
Proof. src_rule sr_conv. Qed.

Lemma st_pack Φ Ψ Δ F e lb m C T xs :
  length xs = m → Forall (hyp_known Ψ) xs → bcs_hold (heqs Ψ) (hlt Ψ) C xs →
  hlbx_below_h Ψ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
  styped Φ Ψ Δ F e (ty_inst xs T) → styped Φ Ψ Δ F e (TEx lb m C T).
Proof. src_rule sr_pack. Qed.

Lemma st_open Φ Ψ Δ F e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
  styped (fhyps_pinst (pshift m) Φ)
    (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
    (<[i := Some T]> (lenv_pinst (pshift m) Δ))
    (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
  styped Φ Ψ Δ F e U.
Proof. src_rule sr_open. Qed.
