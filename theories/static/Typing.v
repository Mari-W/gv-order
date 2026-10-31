(** * The static typing judgments (spec §9)

    Θ; Δ ⊢^F_G t : T ([typed]) and Σ ⊢_G p : T ([ptyped]). The facts G
    enter through the world W they generate, so both judgments are
    indexed by W. The fresh μ of E-Abs and E-Exp is a frame variable φ
    with the one hypothesis u ≺ φ (sharp edges 54, 56). E-Exp types the
    body once, with the box's ιs as point variables 0, …, m-1 (sharp
    edges 57), and at every hereditarily contractive instance of its
    session variables αs (sharp edges 73). E-Open opens an existential
    hypothesis into fresh point variables 0, …, m-1 under its
    constraint, scoped like a box body. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.PointSubst.

Set Default Proof Using "All".

Inductive typed (W : world) : fhyps → hyps → tenv → lenv → sframe → expr → ty → Prop :=
  | t_unit Φ Ψ Δ F :                                    (* E-Unit *)
      lenv_empty Δ →
      typed W Φ Ψ ∅ Δ F EUnit TUnit
  | t_konst Φ Ψ Δ F k T :                               (* E-Const *)
      lenv_empty Δ → konst_ty (seqs W Ψ) (slt W Ψ) (skn W Ψ) k T → kscoped k T →
      typed W Φ Ψ ∅ Δ F (Konst k) T
  | t_var Φ Ψ Δ F x T :                                 (* E-LVar *)
      lenv_only Δ x T →
      typed W Φ Ψ ∅ Δ F (Var x) T
  | t_chan Φ Ψ Δ F c s k s' y :                         (* E-Ch, ι′ ≡_Γ ι *)
      lenv_empty Δ → seq s s' → seqs W Ψ k y →
      typed W Φ Ψ {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | t_lam Φ Ψ Θ Δ F e T U ub lb φ :                     (* E-Abs *)
      φ ∉ dom Φ →
      lb_below_h W Ψ lb (tenv_heads Θ ∪ lenv_heads Δ) →
      typed W (<[φ := ub]> Φ) Ψ Θ (Some T :: Δ) (∅, Some φ) e U →
      typed W Φ Ψ Θ Δ F (Lam e) (TLolli ub lb T U)
  | t_app Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :       (* E-App *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_s W Ψ Φ ub F →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (opt_heads lb)) e2 T →
      typed W Φ Ψ Θ Δ F (App e1 e2) U
  | t_pair Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :            (* E-Pair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (heads T)) e2 U →
      typed W Φ Ψ Θ Δ F (Pair e1 e2) (TProd T U)
  | t_letu Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :              (* E-Let* *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      typed W Φ Ψ Θ2 Δ2 F e2 T →
      typed W Φ Ψ Θ Δ F (LetU e1 e2) T
  | t_letp Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :        (* E-LetPair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      typed W Φ Ψ Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (LetP e1 e2) T
  | t_inj1 Φ Ψ Θ Δ F e T U :                            (* E-Inj *)
      typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F (Inj1 e) (TSum T U)
  | t_inj2 Φ Ψ Θ Δ F e T U :
      typed W Φ Ψ Θ Δ F e U → typed W Φ Ψ Θ Δ F (Inj2 e) (TSum T U)
  | t_case Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :      (* E-Case *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      typed W Φ Ψ Θ2 (Some T1 :: Δ2) F e1 T →
      typed W Φ Ψ Θ2 (Some T2 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (Case e e1 e2) T
  | t_box Φ Ψ Δ F e m k C ub T φ :                      (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      (∀ ss, length ss = k → Forall hcontractive ss →
         typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
           (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)]) ∅
           (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) (∅, Some φ) e
           (sinst_ty (slist ss) T)) →
      typed W Φ Ψ ∅ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T))
  | t_pack Φ Ψ Θ Δ F e lb m C T xs :                    (* E-Pack *)
      length xs = m → Forall (skn W Ψ) xs → bcs_hold (seqs W Ψ) (slt W Ψ) C xs →
      lb_below_h W Ψ lb (heads (ty_inst xs T)) →
      typed W Φ Ψ Θ Δ F e (ty_inst xs T) → typed W Φ Ψ Θ Δ F e (TEx lb m C T)
  | t_open Φ Ψ Θ Δ F e i lb m C T U :                   (* E-Open *)
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      typed W (fhyps_pinst (pshift m) Φ)
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (tenv_pinst (pshift m) Θ) (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
      typed W Φ Ψ Θ Δ F e U
  | t_wk Φ Ψ Θ Δ' Δ F e T :                             (* E-Weak *)
      lenv_wk Δ' Δ → typed W Φ Ψ Θ Δ' F e T → typed W Φ Ψ Θ Δ F e T
  | t_contract Φ Ψ Θ Δ U F e T :                        (* E-Contract *)
      unlimited U →
      typed W Φ Ψ Θ (Some U :: Some U :: Δ) F e T →
      typed W Φ Ψ Θ (Some U :: Δ) F (rename pred e) T
  | t_conv Φ Ψ Θ Δ F e T T' :                           (* E-Conv, ≈ up to Γ ⊢ ≡ *)
      steq W Ψ T T' → typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F e T'.

(** E-Force is E-App at the constant force. The instance must meet the
    box's constraint, every fact read from W and the hypotheses Ψ
    (sharp edges 58, 65). *)
Lemma typed_force W Φ Ψ Θ Δ F e m k C ub T xs ss :
  world_wf W → length xs = m → bcs_hold (seqs W Ψ) (slt W Ψ) C xs → Forall (skn W Ψ) xs →
  length ss = k → Forall hcontractive ss →
  ub_below_s W Ψ Φ (pt_inst (plist xs) <$> ub) F →
  typed W Φ Ψ Θ Δ F e (TBox m k C (TLolli ub None TUnit T)) →
  typed W Φ Ψ Θ Δ F (App EForce e) (sinst_ty (slist ss) (ty_inst xs T)).
Proof.
  intros HW Hxs HC HK Hss Hsc Hub He.
  eapply (t_app W Φ Ψ Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, se_sym.
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply t_konst; [apply lenv_empty_nones| |done]. by constructor.
  - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
Qed.

(** A ≺ fact of a hypothesis without outer points. *)
Lemma sl_hyp0 W Ψ P xs x y x' y' :
  (BCs [] P, xs) ∈ Ψ → P (FLt x y) → fact_scoped (length xs) (FLt x y) →
  pt_inst (plist xs) x = x' → pt_inst (plist xs) y = y' → slt W Ψ x' y'.
Proof.
  intros Hg Hxy Hs <- <-. apply sl_h. exists (BCs [] P), xs. split; [done|].
  exists (FLt x y). split; [by apply bcs_open_nil|done].
Qed.

(** A ≡ fact of a hypothesis without outer points. *)
Lemma se_hyp0 W Ψ P xs x y x' y' :
  (BCs [] P, xs) ∈ Ψ → P (FEq x y) → fact_scoped (length xs) (FEq x y) →
  pt_inst (plist xs) x = x' → pt_inst (plist xs) y = y' → seqs W Ψ x' y'.
Proof.
  intros Hg Hxy Hs <- <-. apply se_h. exists (BCs [] P), xs. split; [done|].
  exists (FEq x y). split; [by apply bcs_open_nil|done].
Qed.

(** ** Processes

    P-Term and P-Connect of §9. The side conditions are the implicit
    well-formedness of the spec: Θ_B holds both ends, dual at aliased
    points, of exactly the channels of C₀; the unions C₁ ⊍ C₂ ⊍ C₀ and
    Σ₁, Σ₂, Σ_C are disjoint; the cut ends are dual at aliased points. *)

Inductive ptyped (W : world) : senv → proc → ty → Prop :=
  | pt_term Σ ΘB C0 t T :                               (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W ∅ [] (tenv_of Σ ∪ ΘB) [] (∅, None) t T →
      ptyped W Σ (C0, {[+ t +]}) T
  | pt_connect Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :         (* P-Connect *)
      ptyped W (Σ1 ∪ ΣC) (C1, E1) T → ptyped W (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' → w_eq W e.2 e'.2 ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      ptyped W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma ptyped_prim W Σ p T : ptyped W Σ p T → prim T.
Proof. induction 1; auto. Qed.
