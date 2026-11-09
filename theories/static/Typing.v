(** * The static typing judgments (spec §9)

    Θ; Δ ⊢^F_G t : T ([typed]) and Σ ⊢_G p : T ([ptyped]). The facts G
    enter through the world W they generate, so both judgments are
    indexed by W. The fresh μ of E-Abs and E-Exp is a future variable φ
    with the one hypothesis u ≺ φ (sharp edges 54, 56). E-Exp types the
    body once, with the box's ιs as point variables 0, …, m-1 (sharp
    edges 57), and at every hereditarily contractive instance of its
    session variables αs (sharp edges 73). E-Open opens an existential
    hypothesis into fresh point variables 0, …, m-1 under its
    constraint, scoped like a box body. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.PointSubst.

(** Branch no-eq: [w_eq W] abbreviates equality and leaves W untyped. *)
Implicit Types W : world.


Set Default Proof Using "All".

(** Two ends at dual points, read from either end, in Γ ⊢ ≡ (end points). *)
Lemma se_dsym W Ψ : rdsym (seqs W Ψ).
Proof.
  intros x y H. apply se_sym. rewrite <-(pt_dual_dual y). by apply se_dual.
Qed.

Inductive typed (W : world) : fhyps → hyps → tenv → lenv → sfuture → expr → ty → Prop :=
  | t_unit Φ Ψ Δ F :                                    (* E-Unit *)
      lenv_empty Δ →
      typed W Φ Ψ ∅ Δ F EUnit TUnit
  | t_const Φ Ψ Δ F k T :                               (* E-Const *)
      lenv_empty Δ → konst_ty (seqs W Ψ) (slt W Ψ) (skn W Ψ) k T → kscoped k T →
      typed W Φ Ψ ∅ Δ F (Konst k) T
  | t_var Φ Ψ Δ F x T :                                 (* E-LVar *)
      lenv_only Δ x T →
      typed W Φ Ψ ∅ Δ F (Var x) T
  | t_pt Φ Ψ Δ F x :                                   (* E-Pt (§16.4) *)
      lenv_empty Δ → pt_ground x → skn W Ψ x →
      typed W Φ Ψ ∅ Δ F (EPt x) (TPt x)
  | t_ch Φ Ψ Δ F c b s k s' y :                       (* E-Ch, ι′ ≡_Γ ι *)
      lenv_empty Δ → seq s s' → seqs W Ψ k y → pt_pol k = b →
      typed W Φ Ψ {[c := One (s, k)]} Δ F (Chan c b) (TSess s' y)
  | t_abs Φ Ψ Θ Δ F e T U ub lb φ :                     (* E-Abs *)
      φ ∉ dom Φ →
      lb_below_hb W Ψ lb (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) →
      typed W (<[φ := ub]> Φ) Ψ Θ (Some T :: Δ) (∅, Some (FVar φ)) e U →
      typed W Φ Ψ Θ Δ F (Lam e) (TLolli ub lb T U)
  | t_app Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :       (* E-App *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_s W Ψ Φ ub F →
      typed W Φ Ψ Θ1 Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (opt_heads lb)) e2 T →
      typed W Φ Ψ Θ Δ F (App e1 e2) U
  | t_pair Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :            (* E-Pair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
      typed W Φ Ψ Θ2 Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
      typed W Φ Ψ Θ Δ F (Pair e1 e2) (TProd T U)
  | t_letstar Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :              (* E-Let* *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
      typed W Φ Ψ Θ2 Δ2 F e2 T →
      typed W Φ Ψ Θ Δ F (LetU e1 e2) T
  | t_letpair Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :        (* E-LetPair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
      typed W Φ Ψ Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (LetP e1 e2) T
  | t_inj1 Φ Ψ Θ Δ F e T U :                            (* E-Inj *)
      typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F (Inj1 e) (TSum T U)
  | t_inj2 Φ Ψ Θ Δ F e T U :
      typed W Φ Ψ Θ Δ F e U → typed W Φ Ψ Θ Δ F (Inj2 e) (TSum T U)
  | t_case Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :      (* E-Case *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
      typed W Φ Ψ Θ2 (Some T1 :: Δ2) F e1 T →
      typed W Φ Ψ Θ2 (Some T2 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (Case e e1 e2) T
  | t_exp Φ Ψ Δ F e m k C ub T φ :                      (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      (∀ ss, length ss = k → Forall hcontractive ss →
         typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
           (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)]) ∅
           (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) (∅, Some (FVar φ)) e
           (sinst_ty (slist ss) T)) →
      typed W Φ Ψ ∅ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T))
  | t_weak Φ Ψ Θ Δ' Δ F e T :                             (* E-Weak *)
      lenv_wk Δ' Δ → typed W Φ Ψ Θ Δ' F e T → typed W Φ Ψ Θ Δ F e T
  | t_contract Φ Ψ Θ Δ U F e T :                        (* E-Contract *)
      unlimited U →
      typed W Φ Ψ Θ (Some U :: Some U :: Δ) F e T →
      typed W Φ Ψ Θ (Some U :: Δ) F (rename pred e) T
  | t_conv Φ Ψ Θ Δ F e T T' :                           (* E-Conv, ≈ up to Γ ⊢ ≡ *)
      steq W Ψ T T' → typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F e T'
  | t_pack Φ Ψ Θ Δ F e lb m C T xs :                    (* E-Pack *)
      length xs = m → Forall (skn W Ψ) xs → bcs_hold (seqs W Ψ) (slt W Ψ) C xs →
      lbx_below_h W Ψ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      typed W Φ Ψ Θ Δ F e (ty_inst xs T) → typed W Φ Ψ Θ Δ F e (TEx lb m C T)
  | t_open Φ Ψ Θ Δ F e i lb m C T U :                   (* E-Open *)
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      typed W (fhyps_pinst (pshift m) Φ)
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (tenv_pinst (pshift m) Θ) (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
      typed W Φ Ψ Θ Δ F e U.

(** The ⊥ flag (sharp edges 103). A subterm whose context holds an
    unopened existential with lower bound ⊥ is typed under a future with
    the flag set ([sf_unionb]). Under the flag no call with an upper
    point passes the gate, and E-Abs does not capture such a value.

    E-Pack and E-Open (sharp edges 97, 99). E-Open opens an
    existential hypothesis into fresh point variables 0, …, m-1 under
    its constraint, scoped like a box body. Under the constant world
    new has no existential signature, so E-NewFresh is gone (sharp
    edges 172). A channel created at the top level sits at a constant
    of the program's hypotheses ([created] below). *)

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
  - apply tenv_comp_empty_l, se_dsym.
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply t_const; [apply lenv_empty_nones| |done]. by apply KTForce.
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


(** ** Processes

    P-Term and P-Connect of §9. The side conditions are the implicit
    well-formedness of the spec: Θ_B holds both ends, dual at aliased
    points, of exactly the channels of C₀; the unions C₁ ⊍ C₂ ⊍ C₀ and
    Σ₁, Σ₂, Σ_C are disjoint; the cut ends are dual at aliased points.

    P-Join is P-Connect for two components typed at their own worlds.
    It asks the join of the two worlds to be strict, which [amalgamation]
    reduces to the names both worlds share. *)

Inductive ptyped : world → senv → proc → ty → Prop :=
  | pt_term W Σ ΘB C0 t T :                             (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W ∅ [] (tenv_of Σ ∪ ΘB) [] (∅, None) t T →
      ptyped W Σ (C0, {[+ t +]}) T
  | pt_connect W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :       (* P-Connect *)
      ptyped W (Σ1 ∪ ΣC) (C1, E1) T → ptyped W (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' → w_eq W e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      ptyped W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T
  | pt_join W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :      (* P-Join *)
      ptyped W1 (Σ1 ∪ ΣC) (C1, E1) T → ptyped W2 (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
         w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      world_wf W1 → world_wf W2 → strict (wjoin W1 W2) →
      ptyped (wjoin W1 W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma ptyped_prim W Σ p T : ptyped W Σ p T → prim T.
Proof. induction 1; auto. Qed.

(** The facts of the hypothesis of E-NewFresh. *)
Lemma slt_fresh_l W Ψ σ L H x l :
  (bcs_inst σ (fresh_bcs L H), [x]) ∈ Ψ → l ∈ L → slt W Ψ (pt_inst σ l) x.
Proof.
  intros Hg Hl. apply sl_h. exists (bcs_inst σ (fresh_bcs L H)), [x]. split; [done|].
  rewrite bcs_inst_fresh. apply fresh_open. left. exists (pt_inst σ l).
  split; [by apply list_elem_of_fmap_2|done].
Qed.

Lemma slt_fresh_r W Ψ σ L H x h :
  (bcs_inst σ (fresh_bcs L H), [x]) ∈ Ψ → h ∈ H → slt W Ψ x (pt_inst σ h).
Proof.
  intros Hg Hh. apply sl_h. exists (bcs_inst σ (fresh_bcs L H)), [x]. split; [done|].
  rewrite bcs_inst_fresh. apply fresh_open. right. exists (pt_inst σ h).
  split; [by apply list_elem_of_fmap_2|done].
Qed.

(** Splitting an environment of spent entries. *)
Lemma lenv_split_nones_nones Δ : lenv_split (lenv_nones Δ) (lenv_nones Δ) (lenv_nones Δ).
Proof. induction Δ; simpl; constructor; done. Qed.

(** [let_new_at] and [let_new_pair_at], the encoded let of new, are in
    lang/Syntax.v, because the translations of PGV and of Padovani and
    Novara produce them too. *)

(** ** Channels created at the top level (sharp edges 172)

    Under the constant world every channel is created with new@x at a
    point x the context knows. A channel that a program creates at its
    top level sits at a constant of the program's hypotheses, because a
    point literal [EPt x] is ground (§16.2). [created W Ψ] says that Ψ
    arises one channel at a time. Each step adds a constant a that
    neither W nor the earlier hypotheses know, under a creation
    constraint C over the points known so far. Nothing shifts. The run
    then starts in a world that places a at that very name
    ([soundness_created], static/Fundamental.v), so the creation facts
    are facts of the initial world. *)
Inductive created (W : world) : hyps → Prop :=
  | created_nil : created W []
  | created_snoc Ψ C a :
      created W Ψ → cc_ok (seqs W Ψ) (slt W Ψ) C → Forall (skn W Ψ) (bc_env C) →
      ¬ skn W Ψ (pconst a) →
      created W (Ψ ++ [(C, [pconst a])]).

(** The constraint of sharp edges 93 with betweenness. *)
Lemma created_fresh W Ψ C a :
  created W Ψ → fresh_lt C → Forall (skn W Ψ) (bc_env C) →
  (∀ u p q v, fresh_lo C u p → fresh_hi C q v → ple p q →
     slt W Ψ (fresh_outer C u) (fresh_outer C v)) →
  ¬ skn W Ψ (pconst a) →
  created W (Ψ ++ [(C, [pconst a])]).
Proof.
  intros HΨ HC HK Hbt Ha. apply created_snoc; [done| |done|done].
  apply cc_ok_fresh; [done|by apply fresh_between_lt].
Qed.

(** With lists, L ≺ ι ≺ H, every point of L below every point of H
    (sharp edges 90, 103). *)
Lemma created_lh W Ψ L H a :
  created W Ψ → Forall (skn W Ψ) (L ++ H) →
  (∀ l h, l ∈ L → h ∈ H → slt W Ψ l h) →
  ¬ skn W Ψ (pconst a) →
  created W (Ψ ++ [(fresh_bcs L H, [pconst a])]).
Proof.
  intros HΨ HK Hbt Ha.
  apply (created_fresh W Ψ (fresh_bcs L H)); [done| |done| |done].
  - intros f Hf Hs. destruct Hf as [(i & Hi & ->)|(j & Hj & ->)].
    + left. eexists _, _. split; [done|]. split_and!; [left; by exists i|done|done|done].
    + right. eexists _, _. split; [done|]. split_and!; [right; by exists j|done|done|done].
  - intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) _.
    destruct Hf as [(i & Hi & E)|(j & Hj & E)]; injection E as -> ->; [|done].
    destruct Hf' as [(i' & Hi' & E)|(j & Hj & E)]; injection E as -> ->; [done|].
    unfold fresh_outer. rewrite !pt_inst_pvar_at. unfold plist. simpl.
    destruct (lookup_lt_is_Some_2 L i Hi) as [l Hl].
    destruct (lookup_lt_is_Some_2 H j Hj) as [h Hh].
    rewrite (lookup_app_l_Some _ _ _ _ Hl).
    rewrite lookup_app_r by lia. replace (length L + j - length L) with j by lia. rewrite Hh.
    apply Hbt; by eapply list_elem_of_lookup_2.
Qed.

(** The point variable k of a hypothesis list whose entry has instance
    [pvar k] is known. *)
Lemma skn_hyp W Ψ C k : (C, [pvar k]) ∈ Ψ → skn W Ψ (pvar k).
Proof. intros H. right. exists C, [pvar k], (pvar k). split_and!; [done|by left|done]. Qed.

(** The constant a of a channel created at the top level is known. *)
Lemma skn_hyp_const W Ψ C a : (C, [pconst a]) ∈ Ψ → skn W Ψ (pconst a).
Proof. intros H. right. exists C, [pconst a], (pconst a). split_and!; [done|by left|done]. Qed.
