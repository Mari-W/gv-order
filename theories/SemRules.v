(** * The semantic rules in derivation form (sharp edges 53)

    [sem_rules] lists the compositionality lemmas of TermRules.v and
    TermRules2.v as the rules of an infinitary judgment: the bodies of
    λ and box are typed in every later world, under every frame above
    the upper point and, for a box, at every admissible instance. Its
    fundamental theorem [sem_rules_fundamental] is one rule per lemma.
    The finite static system of Static.v reaches it through
    [typed_sem_rules]. E-Abs carries the well-formedness of its body
    as a premise, which [typed_sem_rules] reads off the finite
    derivation. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export TermRules2.

Set Default Proof Using "All".

(** ** The infinitary judgment

    The reading of sharp edges 53: the bodies of λ and box are typed in
    every later world and under every frame above the upper point. *)

Inductive sem_rules (W : world) : tenv → lenv → gset point → expr → ty → Prop :=
  | sr_unit Δ F :                                        (* E-Unit *)
      lenv_empty Δ →
      sem_rules W ∅ Δ F EUnit TUnit
  | sr_konst Δ F k T :                                   (* E-Const *)
      lenv_empty Δ → konst_ty (w_eq W) (w_lt W) (pt_known W) k T →
      sem_rules W ∅ Δ F (Konst k) T
  | sr_var Δ F x T :                                     (* E-LVar *)
      lenv_only Δ x T →
      sem_rules W ∅ Δ F (Var x) T
  | sr_chan Δ F c s k s' y :                             (* E-Ch, ι′ ≡_G ι *)
      lenv_empty Δ → seq s s' → w_eq W k y →
      sem_rules W {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | sr_lam Θ Δ F e T U ub lb :                           (* E-Abs *)
      term_wf Θ (Some T :: Δ) e → lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
      (∀ W1 F', wext W W1 → ub_below W1 ub F' → sem_rules W1 Θ (Some T :: Δ) F' e U) →
      sem_rules W Θ Δ F (Lam e) (TLolli ub lb T U)
  | sr_app Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :           (* E-App *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
      sem_rules W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      sem_rules W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
      sem_rules W Θ Δ F (App e1 e2) U
  | sr_pair Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :                (* E-Pair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      sem_rules W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      sem_rules W Θ2 Δ2 (F ∪ heads T) e2 U →
      sem_rules W Θ Δ F (Pair e1 e2) (TProd T U)
  | sr_letu Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :                  (* E-Let* *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      sem_rules W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      sem_rules W Θ2 Δ2 F e2 T →
      sem_rules W Θ Δ F (LetU e1 e2) T
  | sr_letp Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :            (* E-LetPair *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      sem_rules W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      sem_rules W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      sem_rules W Θ Δ F (LetP e1 e2) T
  | sr_inj1 Θ Δ F e T U :                                (* E-Inj *)
      sem_rules W Θ Δ F e T → sem_rules W Θ Δ F (Inj1 e) (TSum T U)
  | sr_inj2 Θ Δ F e T U :
      sem_rules W Θ Δ F e U → sem_rules W Θ Δ F (Inj2 e) (TSum T U)
  | sr_case Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :          (* E-Case *)
      tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      sem_rules W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      sem_rules W Θ2 (Some T1 :: Δ2) F e1 T →
      sem_rules W Θ2 (Some T2 :: Δ2) F e2 T →
      sem_rules W Θ Δ F (Case e e1 e2) T
  | sr_box Δ F e m C ub T :                              (* E-Exp *)
      lenv_unl Δ → term_wf ∅ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ) e →
      (∀ W1 xs F', wext W W1 → length xs = m → bcs_hold (w_lt W1) C xs →
         Forall (pt_known W1) xs → ub_below W1 (pt_inst (plist xs) <$> ub) F' →
         sem_rules W1 ∅ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ) F' e (ty_inst xs T)) →
      sem_rules W ∅ Δ F (EBox e) (TBox m C (TLolli ub None TUnit T))
  | sr_wk Θ Δ' Δ F e T :                                 (* E-Weak *)
      lenv_wk Δ' Δ → sem_rules W Θ Δ' F e T → sem_rules W Θ Δ F e T
  | sr_contract Θ Δ U F e T :                            (* E-Contract *)
      unlimited U →
      sem_rules W Θ (Some U :: Some U :: Δ) F e T →
      sem_rules W Θ (Some U :: Δ) F (rename pred e) T
  | sr_conv Θ Δ F e T T' :                               (* E-Conv *)
      teq T T' → sem_rules W Θ Δ F e T → sem_rules W Θ Δ F e T'.

(** E-Force is E-App at the constant force. *)
Lemma sem_rules_force W Θ Δ F e m C ub T xs :
  world_wf W → length xs = m → bcs_hold (w_lt W) C xs → Forall (pt_known W) xs →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  sem_rules W Θ Δ F e (TBox m C (TLolli ub None TUnit T)) →
  sem_rules W Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs HC HK Hub He.
  eapply (sr_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply sr_konst; [apply lenv_empty_nones|]. by constructor.
  - simpl. by rewrite union_empty_r_L.
Qed.

(** ** The fundamental theorem for the infinitary judgment *)

Theorem sem_rules_fundamental W Θ Δ F e T : sem_rules W Θ Δ F e T → strict W → sem_typed W Θ Δ F e T.
Proof.
  intros Ht. pose proof Ht as Ht0. revert Ht0.
  induction Ht as
    [W Δ F HΔ
    |W Δ F k T HΔ Hk
    |W Δ F x T Ho
    |W Δ F c s k s' y HΔ Hs Hk
    |W Θ Δ F e T U ub lb Hwf Hlb Hb IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |W Θ Δ F e T U H IH
    |W Θ Δ F e T U H IH
    |W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |W Δ F e m C ub T HΔ Hwf Hb IH
    |W Θ Δ' Δ F e T Hwk H IH
    |W Θ Δ U F e T Hu H IH
    |W Θ Δ F e T T' Hteq H IH]; intros Ht0 HW.
  - by apply sem_typed_unit.
  - by apply sem_typed_konst.
  - by apply sem_typed_var.
  - by apply sem_typed_chan.
  - apply sem_typed_lam; [done|done|].
    + intros W1 F' HW1 Hub'. apply IH; [done|done| |apply HW1]. by apply Hb.
  - eapply sem_typed_app; [done|done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_pair; [done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_letu; [done|done|by apply IH1|by apply IH2].
  - eapply sem_typed_letp; [done|done|by apply IH1|by apply IH2].
  - apply sem_typed_inj1. by apply IH.
  - apply sem_typed_inj2. by apply IH.
  - eapply sem_typed_case; [done|done|by apply IH0|by apply IH1|by apply IH2].
  - apply sem_typed_box; [done|done|].
    intros W1 xs F' HW1 Hxs HC HK Hub'. apply IH; [done..| |apply HW1]. by apply Hb.
  - eapply sem_typed_wk; [done|by apply IH].
  - apply sem_typed_contract; [done|by apply IH].
  - eapply sem_typed_teq; [done|by apply IH].
Qed.
