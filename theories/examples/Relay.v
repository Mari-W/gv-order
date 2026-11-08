(** * relay: typable, recursive (SHARP-EDGES 65)

      S = μX. ?(∃ι. D@ι).X      D = ?∗.Close
      C₀(x, y) = {x ≺ y, x ≺ x[0], x[0] ≺ x+1, x[0] ≺ y, y ≺ x+1, y ≺ x[0]+1}
      C = C₀(ι, ι′) ∪ {C₀(ι+k+1, (ι+k)[0]+1) ∣ k ∈ ℕ}       (positions from 0)
      relay : □(∀ι ι′. C. ∗ ⊸ (S@ι ⊗ Close@ι′ ⊸^{ι′} ∗))
      relay = !(f = λp. let (c, d) = p in let (e, c) = recv c in
                       let (v, e) = recv e in let () = v in let () = close d in
                       spawn (λw. let () = w in (force f) ⟨c, e⟩))
      prod  : the same box over S̄ ⊗ Close
      prod  = !(g = λp. let (c, d) = p in let (e, e′) = new ∗ in
                       let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in let () = u in
                       let (e′, u) = ⟨send ⟨∗, e′⟩, ∗⟩ in let () = u in let () = close d in
                       spawn (λw. let () = w in (force g) ⟨c, e′⟩))
      rel_main = let (r, g) = ⟨relay, prod⟩ in let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 let () = spawn (λw. let () = w in (force r) ⟨c, d⟩) in (force g) ⟨c′, d′⟩

    The relay is §8.2's with a spawn in place of the tail call, which
    removes the ceiling. prod creates e at ι[0], the point its payload
    must live at, so it needs new under □∀ (59) and ι ≺ ι[0] for its
    send. The call at (ι+1, ι[0]+1) asks C there, which is round 0 of
    the family and round k+1 for round k, so C[ι+1, ι[0]+1] ⊆ C
    ([rel_sub]). main forces both boxes at (γ, ε), the points of c and
    d. Round 0 is C₀(γ, ε) and round k+1 is C₀(γ+k+1, (γ+k)[0]+1).

    main types under the hypotheses of its two top-level points γ and
    ε ([rel_Ψ]). c is created with the facts of its own rounds, ordered
    by the ranks 3k+3 for γ+k and 3k+4+4o for (γ+k)[0]+o, and d with
    the four facts of round 0 that mention it (sharp edges 105, 172).

    With end points the gates compare with partner points, and the two
    boxes need different constraints: the relay's round [c0] at (ι, ι′)
    and the producer's round [c0p], which keeps e′ at ι[0]‾ and recurs
    at (ι+1, ι[0]‾+1) ([relp_C]). main forces the relay at (γ, ε) and the
    producer at (γ̄, ε̄). d is created with the twelve facts of round 0
    that mention ε or ε̄, and c with {γ, γ̄} ≺ {γ[0], γ[0]‾} ≺ γ+1, γ̄+1 and
    every later round. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Definition Dr : sty := SSeq (SRcv 0 TUnit) SEnd.
Definition Srl : sty := SMu (SSeq (SRcv 1 (TSess Dr (Pt (NVar 0) 0))) (SVar 0)).

Abbreviation sv o := (Pt (NPayload (NVar 0) 0 0) o).

(** The round of the relay, which holds c at x, d at y and receives e
    at x[0]: the gates of its recv on c, its recv on e and its close of
    d, against the partner points of the ends it still holds. *)
Definition c0 (x y : point) (g : fact) : Prop :=
  g = FLt x (pt_dual y) ∨ g = FLt x y ∨ g = FLt (pt_payload x 0) (pt_shift 1 (pt_dual x)) ∨
  g = FLt (pt_payload x 0) (pt_dual y) ∨ g = FLt (pt_payload x 0) y ∨
  g = FLt y (pt_shift 1 (pt_dual x)) ∨ g = FLt y (pt_shift 1 (pt_dual (pt_payload x 0))).

(** The round of the producer, which holds c at x, d at y, sends e at
    x[0] and keeps e′ at x[0]‾. *)
Definition c0p (x y : point) (g : fact) : Prop :=
  g = FLt x (pt_dual (pt_payload x 0)) ∨ g = FLt x (pt_payload x 0) ∨ g = FLt x (pt_dual y) ∨
  g = FLt x y ∨ g = FLt (pt_dual (pt_payload x 0)) (pt_shift 1 (pt_dual x)) ∨
  g = FLt (pt_dual (pt_payload x 0)) (pt_dual y) ∨ g = FLt (pt_dual (pt_payload x 0)) y ∨
  g = FLt y (pt_shift 1 (pt_dual x)) ∨ g = FLt y (pt_shift 1 (pt_payload x 0)).

Definition rel_P (g : fact) : Prop :=
  c0 (pv 0 0) (pv 1 0) g ∨ ∃ k, c0 (pv 0 (S k)) (Pt (NPayload (NVar 0) k 0) 1) g.

Definition rel_C : bcs := BCs [] rel_P.

Definition relp_P (g : fact) : Prop :=
  c0p (pv 0 0) (pv 1 0) g ∨ ∃ k, c0p (pv 0 (S k)) (pt_dual (Pt (NPayload (NVar 0) k 0) 1)) g.

Definition relp_C : bcs := BCs [] relp_P.

Lemma c0_inst σ x y g : c0 x y g → c0 (pt_inst σ x) (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof.
  unfold c0. intros [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; cbn [fact_map];
    repeat rewrite ?pt_inst_payload, ?pt_inst_shift, ?pt_inst_dual;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

Lemma c0p_inst σ x y g : c0p x y g → c0p (pt_inst σ x) (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof.
  unfold c0p. intros [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; cbn [fact_map];
    repeat rewrite ?pt_inst_payload, ?pt_inst_shift, ?pt_inst_dual;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

(** C[ι+1, ι[0]+1] ⊆ C: round 0 goes to round 0 of the family, round
    k+1 to round k+2. *)
Lemma rel_sub g : rel_P g → fact_scoped 2 g → rel_P (fact_map (pt_inst (plist [pv 0 1; sv 1])) g).
Proof.
  intros [Hg|(k & Hg)] _; right.
  - exists 0. exact (c0_inst _ _ _ _ Hg).
  - exists (S k). exact (c0_inst _ _ _ _ Hg).
Qed.

Lemma rel_call W Ψ :
  (rel_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pv 0 1; sv 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rel_sub]. Qed.

(** The producer recurs at (ι+1, ι[0]‾+1), the point of e′. *)
Lemma relp_sub g :
  relp_P g → fact_scoped 2 g → relp_P (fact_map (pt_inst (plist [pv 0 1; pt_dual (sv 1)])) g).
Proof.
  intros [Hg|(k & Hg)] _; right.
  - exists 0. exact (c0p_inst _ _ _ _ Hg).
  - exists (S k). exact (c0p_inst _ _ _ _ Hg).
Qed.

Lemma relp_call W Ψ :
  (relp_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) relp_C [pv 0 1; pt_dual (sv 1)].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact relp_sub]. Qed.

Definition relay_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Srl (pv 0 0)) (TSess SEnd (pv 1 0))) TUnit.
Definition prod_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess (dual Srl) (pv 0 0)) (TSess SEnd (pv 1 0))) TUnit.

Definition relay : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1)) (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (LetU (App EClos (Var 4))
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 3) (Var 1)))))))))))).

Definition prod : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetP (Pair (App ESend (Pair (Var 1) (Var 3))) EUnit) (LetU (Var 0)
      (LetP (Pair (App ESend (Pair EUnit (Var 2))) EUnit) (LetU (Var 0)
        (LetU (App EClos (Var 6))
          (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 10)) (Pair (Var 4) (Var 2)))))))))))))).

Definition rel_main : expr :=
  LetP (Pair relay prod) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

Lemma relay_typed W F : world_wf W → typed W ∅ [] ∅ [] F relay (TBox 2 0 rel_C (TLolli None None TUnit relay_body)).
Proof.
  intros HW. unfold relay.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open rel_C relay_body. cbn. unfold relay_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess Dr (Pt (NVar 0) 0))) Srl) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pt_dual (pv 1 0))|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (sv 0) (pt_dual (pv 0 1))|hyp0 (sv 0) (pt_dual (pv 1 0))]|].
    exists (pv 1 0). split; [done|]. right. hyp0 (sv 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pt_dual (pv 0 1))|hyp0 (pv 1 0) (pt_dual (sv 1))]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sv 1)) (Some (sv 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (sv 0) (pt_dual (pv 0 1))|right; apply sl_dpo]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rel_C None relay_body [pv 0 1; sv 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rel_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ rel_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sv 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma prod_typed W F : strict W → typed W ∅ [] ∅ [] F prod (TBox 2 0 relp_C (TLolli None None TUnit prod_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold prod.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open relp_C prod_body. cbn. unfold prod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Dr (sv 0) HWs); [skn_payload|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess Dr (sv 0)) (TSess (SSeq (SSnd 1 (TSess Dr (Pt (NVar 0) 0))) (dual Srl)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess Dr (Pt (NVar 0) 0)) (dual Srl) (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. hyp0 (pv 0 0) (pt_dual (sv 0)).
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 0 0) (sv 0)|hyp0 (pv 0 0) (pt_dual (pv 1 0))]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pt_dual (sv 0)))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pt_dual (sv 0))))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual (sv 0))). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy;
        first [hyp0 (pt_dual (sv 0)) (pt_dual (pv 0 1))|hyp0 (pt_dual (sv 0)) (pt_dual (pv 1 0))]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pt_dual (sv 0)) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pt_dual (pv 0 1))|hyp0 (pv 1 0) (sv 1)]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (sv 1))) (Some (pt_dual (sv 0))) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (pt_dual (sv 0)) (pt_dual (pv 0 1))|right; apply sl_dpo]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 relp_C None prod_body [pv 0 1; pt_dual (sv 1)]);
      [done|done| | |apply ubs_none|tstep].
    + apply relp_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ relp_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (sv 1)). split; [done|]. apply sle_refl, HW.
Qed.

(** Both channels come from creation constraints (sharp edges 105).
    main forces the relay at (γ, ε), the points of c and d, and the
    producer at (γ̄, ε̄), the points of c′ and d′. c is created with the
    facts that stay inside its name: {γ, γ̄} ≺ {γ[0], γ[0]‾} ≺ {γ+1, γ̄+1}
    and every later round of both boxes. The ranks [relv_rank], which
    ignore polarity, order them. d is created at a fresh point ε with
    the twelve facts of round 0 that mention ε or ε̄ ([reld_L],
    [reld_H]). *)
Definition relc_P (g : fact) : Prop :=
  (∃ b b', g = FLt (pt_polar b (pv 0 0)) (pt_polar b' (sv 0)) ∨
           g = FLt (pt_polar b (sv 0)) (pt_polar b' (pv 0 1))) ∨
  (∃ k, c0 (pv 0 (S k)) (Pt (NPayload (NVar 0) k 0) 1) g) ∨
  (∃ k, c0p (pt_dual (pv 0 (S k))) (pt_dual (Pt (NPayload (NVar 0) k 0) 1)) g).
Definition relc_C : bcs := BCs [] relc_P.

(** The constraint of d: γ and γ[0] at both polarities below ε and ε̄,
    and ε below γ̄+1, γ[0]‾+1, ε̄ below γ+1, γ[0]+1. *)
Definition reld_L : list (point * bool) :=
  [(pvar 0, false); (pvar 0, true); (sv 0, false); (sv 0, true);
   (pt_dual (pvar 0), true); (pt_dual (pvar 0), false); (pt_dual (sv 0), true); (pt_dual (sv 0), false)].
Definition reld_H : list (point * bool) :=
  [(pt_dual (pv 0 1), true); (pt_dual (sv 1), true); (pv 0 1, false); (sv 1, false)].

Definition relv_base (p : pname) : nat :=
  match p with NVar 0 => 3 | NPayload (NVar 0) k 0 => 3 * k + 4 | _ => 0 end.
Definition relv_step (p : pname) : nat :=
  match p with NVar 0 => 3 | NPayload (NVar 0) _ 0 => 4 | _ => 1 end.
Definition relv_rank (x : point) : nat := relv_base (pt_name x) + relv_step (pt_name x) * pt_off x.

Lemma relc_ok peq plt : cc_ok peq plt relc_C.
Proof.
  apply (cc_ok_inner peq plt relc_P (λ x y, relv_rank x < relv_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros x _. unfold relv_rank, pt_shift. cbn.
    assert (0 < relv_step (pt_name x)) by (unfold relv_step; repeat case_match; lia). nia.
  - intros g [(b & b' & [-> | ->]) | [(k & Hg) | (k & Hg)]] _.
    + destruct b, b'; eexists _, _; (split; [done|]); unfold relv_rank; cbn; lia.
    + destruct b, b'; eexists _, _; (split; [done|]); unfold relv_rank; cbn; lia.
    + unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst;
        eexists _, _; (split; [done|]); unfold relv_rank; cbn; lia.
    + unfold c0p in Hg. repeat destruct Hg as [->|Hg]; subst;
        eexists _, _; (split; [done|]); unfold relv_rank; cbn; lia.
  - intros x _. unfold relv_rank, pt_shift, pt_dual. cbn.
    assert (0 < relv_step (pt_name x)) by (unfold relv_step; repeat case_match; lia). nia.
Qed.

Ltac rel_in := repeat (first [apply list_elem_of_here|apply list_elem_of_further]).
Ltac rel_po := match goal with |- slt ?W _ ?x _ => apply (slt_po W _ x); assumption end.

Definition rel_Ψ : hyps :=
  hyps_inst (pshift 1) (hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) relc_C, ids 1)]) ++
    [(bcs_inst (pshift 1) (freshp_bcs reld_L reld_H), ids 1)].

Lemma rel_created : created (Wpo []) rel_Ψ.
Proof.
  pose proof (proj1 Wpo_nil_strict') as HW. set (W := Wpo []) in *.
  assert (∀ b b', slt W [(relc_C, [pvar 0])] (pt_polar b (pv 0 0)) (pt_polar b' (sv 0))) as Hc1.
  { intros b b'. eapply (sl_hyp0 _ _ _ _ (pt_polar b (pv 0 0)) (pt_polar b' (sv 0)));
      [by left|left; exists b, b'; by left|destruct b, b'; cbn; lia
      |destruct b; reflexivity|destruct b'; reflexivity]. }
  assert (∀ b b', slt W [(relc_C, [pvar 0])] (pt_polar b (sv 0)) (pt_polar b' (pv 0 1))) as Hc2.
  { intros b b'. eapply (sl_hyp0 _ _ _ _ (pt_polar b (sv 0)) (pt_polar b' (pv 0 1)));
      [by left|left; exists b, b'; by right|destruct b, b'; cbn; lia
      |destruct b; reflexivity|destruct b'; reflexivity]. }
  refine (created_p W [(relc_C, [pvar 0])] reld_L reld_H _ _ _).
  { change [(relc_C, [pvar 0])] with (hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) relc_C, ids 1)]).
    apply created_snoc; [constructor|apply relc_ok|constructor]. }
  { cbn. repeat (apply Forall_cons; split; [eapply skn_inst; [by left|by left|done]|]). by apply Forall_nil. }
  { intros l h b Hl Hh. unfold reld_L, reld_H in *.
    repeat match goal with E : _ ∈ _ :: _ |- _ => apply elem_of_cons in E as [E|E]
                         | E : _ ∈ [] |- _ => by apply elem_of_nil in E end;
      repeat match goal with E : (_, _) = (_, _) |- _ => injection E; clear E; intros; subst end; try done;
      first [apply sl_dpo|rel_po
            |exact (Hc1 true true)|exact (Hc1 true false)|exact (Hc1 false true)|exact (Hc1 false false)
            |exact (Hc2 true true)|exact (Hc2 true false)|exact (Hc2 false true)|exact (Hc2 false false)
            |eapply sl_trans; [exact (Hc1 true true)|rel_po]
            |eapply sl_trans; [exact (Hc1 true false)|rel_po]
            |eapply sl_trans; [exact (Hc1 false true)|rel_po]
            |eapply sl_trans; [exact (Hc1 false false)|rel_po]]. }
Qed.

Lemma rel_typed : styped ∅ rel_Ψ [] (∅, None) rel_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold rel_main, rel_Ψ.
  tstep.
  { tstep; (apply typed_hyps_nil; [exact HWs|]); [apply prod_typed, HWs|apply relay_typed, HW]. }
  cbn. new_top HWs Srl (pvar 1). new_top HWs SEnd (pvar 0).
  fresh_clean.
  match goal with |- typed _ _ ?Ψ0 _ _ _ _ _ => set (Ψ := Ψ0) end.
  assert (∀ l b, (l, b) ∈ reld_L → slt W Ψ (pt_inst (pshift 1) l) (pt_polar b (pvar 0))) as HdL.
  { intros l b Hl. by apply (slt_freshp_l W Ψ (pshift 1) reld_L reld_H (pvar 0)); [right; left|]. }
  assert (∀ h b, (h, b) ∈ reld_H → slt W Ψ (pt_polar b (pvar 0)) (pt_inst (pshift 1) h)) as HdH.
  { intros h b Hh. by apply (slt_freshp_r W Ψ (pshift 1) reld_L reld_H (pvar 0)); [right; left|]. }
  assert (∀ g, relc_P g → fact_scoped 1 g →
            fact_holds (seqs W Ψ) (slt W Ψ) (fact_map (pt_inst (plist [pv 1 0])) g)) as Hc.
  { intros [x y] Hg Hs; cbn.
    eapply (sl_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pv 1 0; pvar 0]) as HC.
  { apply bcs_hold_intro. intros g [Hg|(k & Hg)] Hs.
    - unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn.
      + apply (HdL (pvar 0) false). unfold reld_L. rel_in.
      + apply (HdL (pvar 0) true). unfold reld_L. rel_in.
      + apply (Hc (FLt (pt_polar true (sv 0)) (pt_polar false (pv 0 1)))); [left; exists true, false; by right|cbn; lia].
      + apply (HdL (sv 0) false). unfold reld_L. rel_in.
      + apply (HdL (sv 0) true). unfold reld_L. rel_in.
      + apply (HdH (pt_dual (pv 0 1)) true). unfold reld_H. rel_in.
      + apply (HdH (pt_dual (sv 1)) true). unfold reld_H. rel_in.
    - assert (fact_map (pt_inst (plist [pv 1 0; pvar 0])) g = fact_map (pt_inst (plist [pv 1 0])) g) as ->.
      { unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; done. }
      apply Hc; [by right; left; exists k|].
      unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn; lia. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) relp_C [pt_dual (pv 1 0); pt_dual (pvar 0)]) as HCp.
  { apply bcs_hold_intro. intros g [Hg|(k & Hg)] Hs.
    - unfold c0p in Hg. repeat destruct Hg as [->|Hg]; subst; cbn.
      + apply (Hc (FLt (pt_polar false (pv 0 0)) (pt_polar false (sv 0)))); [left; exists false, false; by left|cbn; lia].
      + apply (Hc (FLt (pt_polar false (pv 0 0)) (pt_polar true (sv 0)))); [left; exists false, true; by left|cbn; lia].
      + apply (HdL (pt_dual (pvar 0)) true). unfold reld_L. rel_in.
      + apply (HdL (pt_dual (pvar 0)) false). unfold reld_L. rel_in.
      + apply (Hc (FLt (pt_polar false (sv 0)) (pt_polar true (pv 0 1)))); [left; exists false, true; by right|cbn; lia].
      + apply (HdL (pt_dual (sv 0)) true). unfold reld_L. rel_in.
      + apply (HdL (pt_dual (sv 0)) false). unfold reld_L. rel_in.
      + apply (HdH (pv 0 1) false). unfold reld_H. rel_in.
      + apply (HdH (sv 1) false). unfold reld_H. rel_in.
    - pose proof (c0p_inst (plist [pt_dual (pvar 0)]) _ _ _ Hg) as Hg'.
      assert (fact_map (pt_inst (plist [pt_dual (pv 1 0); pt_dual (pvar 0)])) g =
              fact_map (pt_inst (plist [pv 1 0])) (fact_map (pt_inst (plist [pt_dual (pvar 0)])) g)) as ->.
      { unfold c0p in Hg. repeat destruct Hg as [->|Hg]; subst; done. }
      apply Hc; [right; right; exists k; exact Hg'|].
      unfold c0p in Hg. repeat destruct Hg as [->|Hg]; subst; cbn; lia. }
  assert (Forall (skn W Ψ) [pv 1 0; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pv 1 0); pt_dual (pvar 0)]) as HK'.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (slt W Ψ (pt_dual (pv 1 0)) (pt_dual (pvar 0))) as H1.
  { apply (HdL (pt_dual (pvar 0)) false). unfold reld_L. rel_in. }
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess (dual SEnd) (pt_dual (pvar 0))); change B with (TSess SEnd (pvar 0));
    change A' with (TSess (dual Srl) (pt_dual (pv 1 0))); change B' with (TSess Srl (pv 1 0));
    change D with (TBox 2 0 relp_C (TLolli None None TUnit prod_body));
    change E with (TBox 2 0 rel_C (TLolli None None TUnit relay_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pt_dual (pv 1 0))) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact H1]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 rel_C None relay_body [pv 1 0; pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 relp_C None prod_body [pt_dual (pv 1 0); pt_dual (pvar 0)]);
      [done|done|exact HCp|exact HK'|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rel_deadlock_free : deadlock_free (∅, {[+ rel_main +]}).
Proof.
  apply (soundness_created_s rel_Ψ _ TUnit rel_created); [constructor|apply rel_typed].
Qed.
