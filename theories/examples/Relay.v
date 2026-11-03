(** * relay: typable, recursive (SHARP-EDGES 65)

      Srl = µα. ?(Dr@self.0).α        Dr = ?∗.Close

      C₀(x, y) = {x ≺ y, x ≺ x.0, x.0 ≺ x+1, x.0 ≺ y, y ≺ x+1, y ≺ x.0+1}
      C        = C₀(ι, ι′) ∪ {C₀(ι+k+1, (ι+k).0+1) ∣ k ∈ ℕ}

      relay : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ (Srl@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗))
      relay = ! f ∀ι ι′ { C }. λ^{ι′}_⊤ p.
                  let (c : Srl@ι, d : Close@ι′) = p in
                  let (e : Dr@ι.0, c₁ : Srl@(ι+1)) = recv c in
                  let (v : ∗, e₁ : Close@(ι.0+1)) = recv e in
                  v;
                  close d;
                  spawn (λ^{ι.0+1}_{ι.0} ∗. (force f [ι+1, ι.0+1]) ⟨c₁, e₁⟩)

      prod  : the same box over S̄rl ⊗ Close
      prod  = ! g ∀ι ι′ { C }. λ^{ι′}_⊤ p.
                  let (c : S̄rl@ι, d : Close@ι′) = p in
                  let (e : Dr@ι.0, e′ : D̄r@ι.0) = new κ { κ ≡ ι.0 } ∗ in
                  let c₁ : S̄rl@(ι+1) = send ⟨e, c⟩ in
                  let e′₁ : Close@(ι.0+1) = send ⟨∗, e′⟩ in
                  close d;
                  spawn (λ^{ι.0+1}_{ι.0} ∗. (force g [ι+1, ι.0+1]) ⟨c₁, e′₁⟩)

      Cc = {γ ≺ γ.0, γ.0 ≺ γ+1} ∪ {C₀(γ+k+1, (γ+k).0+1) ∣ k ∈ ℕ}
      Cd = {γ ≺ ε, γ.0 ≺ ε, ε ≺ γ+1, ε ≺ γ.0+1}

      rel_main = let (c : Srl@γ, c′ : S̄rl@γ) = new γ { Cc } ∗ in
                 let (d : Close@ε, d′ : Close@ε) = new ε { Cd } ∗ in
                 spawn (λ^ε_γ ∗. (force relay [γ, ε]) ⟨c, d⟩);
                 (force prod [γ, ε]) ⟨c′, d′⟩

    The relay is §8.2's with a spawn in place of the tail call, which
    removes the ceiling. prod creates e at ι.0, the carried root its
    payload must live at, so it needs new under □∀ (59) and ι ≺ ι.0 for
    its send. The call at [ι+1, ι.0+1] asks C there, which is round 0 of
    the family and round k+1 for round k, so C[ι+1, ι.0+1 / ι, ι′] ⊆ C
    ([rel_sub]). rel_main forces both boxes at [γ, ε], the points of c
    and d. Round 0 is C₀(γ, ε) and round k+1 is C₀(γ+k+1, (γ+k).0+1).

    c is created with the facts of its own rounds, ordered by the ranks
    3k+3 for γ+k and 3k+4+4o for (γ+k).0+o, and d with the four facts of
    round 0 that mention it.

      ∅; · ⊢^∅ rel_main : ∗   so   thread rel_main is deadlock free

    (sharp edges 105) *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Dr : sty := SRcv TUnit SEnd.
Definition Srl : sty := SMu (SRcv (TSess Dr (Pt (NVar 0) 0)) (SVar 0)).

Abbreviation sv o := (Pt (NSlot (NVar 0) 0 0) o).

Definition c0 (x y : point) (g : fact) : Prop :=
  g = FLt x y ∨ g = FLt x (pt_slot x 0) ∨ g = FLt (pt_slot x 0) (pt_shift 1 x) ∨
  g = FLt (pt_slot x 0) y ∨ g = FLt y (pt_shift 1 x) ∨ g = FLt y (pt_shift 1 (pt_slot x 0)).

Definition rel_P (g : fact) : Prop :=
  c0 (pv 0 0) (pv 1 0) g ∨ ∃ k, c0 (pv 0 (S k)) (Pt (NSlot (NVar 0) k 0) 1) g.

Definition rel_C : bcs := BCs [] rel_P.

Lemma c0_inst σ x y g : c0 x y g → c0 (pt_inst σ x) (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof.
  unfold c0. intros [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn [fact_map];
    rewrite ?pt_inst_slot, ?pt_inst_shift, ?pt_inst_slot;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

(** C[ι+1, ι.0+1 / ι, ι′] ⊆ C. Round 0 goes to round 0 of the family and
    round k+1 to round k+2. *)
Lemma rel_sub g : rel_P g → fact_scoped 2 g → rel_P (fact_map (pt_inst (plist [pv 0 1; sv 1])) g).
Proof.
  intros [Hg|(k & Hg)] _; right.
  - exists 0. exact (c0_inst _ _ _ _ Hg).
  - exists (S k). exact (c0_inst _ _ _ _ Hg).
Qed.

Lemma rel_call W Ψ :
  (rel_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pv 0 1; sv 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rel_sub]. Qed.

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

Lemma relay_typed W F : world_wf W → typed W ∅ [] ∅ [] F relay (TBox 2 rel_C (TLolli None None TUnit relay_body)).
Proof.
  intros HW. unfold relay.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rel_C relay_body. cbn. unfold relay_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SRcv (TSess Dr (Pt (NVar 0) 0)) Srl) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (sv 0) (pv 0 1)|hyp0 (sv 0) (pv 1 0)]|].
    exists (pv 1 0). split; [done|]. right. hyp0 (sv 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pv 0 1)|hyp0 (pv 1 0) (sv 1)]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sv 1)) (Some (sv 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (sv 0) (pv 0 1)|right; apply (slt_po W _ (sv 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None relay_body [pv 0 1; sv 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rel_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ rel_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sv 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma prod_typed W F : strict W → typed W ∅ [] ∅ [] F prod (TBox 2 rel_C (TLolli None None TUnit prod_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold prod.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rel_C prod_body. cbn. unfold prod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Dr (sv 0) HWs); [skn_slot|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess Dr (sv 0)) (TSess (SSnd (TSess Dr (Pt (NVar 0) 0)) (dual Srl)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ (TSess Dr (Pt (NVar 0) 0)) (dual Srl) (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. hyp0 (pv 0 0) (sv 0).
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 0 0) (sv 0)|hyp0 (pv 0 0) (pv 1 0)]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sv 0)) (TProd TUnit (TSess (SSnd TUnit SEnd) (sv 0)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ TUnit SEnd (sv 0)). cbn. set_solver.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (sv 0) (pv 0 1)|hyp0 (sv 0) (pv 1 0)]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (sv 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pv 0 1)|hyp0 (pv 1 0) (sv 1)]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sv 1)) (Some (sv 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (sv 0) (pv 0 1)|right; apply (slt_po W _ (sv 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None prod_body [pv 0 1; sv 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rel_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ rel_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sv 1). split; [done|]. apply sle_refl, HW.
Qed.

(** Both channels come from creation constraints (sharp edges 105).
    c is created with the facts of its own rounds, which stay inside
    its name, γ ≺ γ.0, γ.0 ≺ γ+1 and every later round
    C₀(γ+k+1, (γ+k).0+1). The ranks [relv_rank] order them. d is created
    at a fresh point ε with the four facts of round 0 that mention it,

      {γ ≺ ε,  γ.0 ≺ ε,  ε ≺ γ+1,  ε ≺ γ.0+1},

    whose betweenness program order and the facts of c give. *)
Definition relc_P (g : fact) : Prop :=
  g = FLt (pv 0 0) (sv 0) ∨ g = FLt (sv 0) (pv 0 1) ∨
  ∃ k, c0 (pv 0 (S k)) (Pt (NSlot (NVar 0) k 0) 1) g.
Definition relc_C : bcs := BCs [] relc_P.

(** The constraint of d. The variable 0 is ε, 1 is γ, 2 is γ.0. *)
Definition reld_facts (g : fact) : Prop :=
  g = FLt (pvar 1) (pvar 0) ∨ g = FLt (pvar 2) (pvar 0) ∨
  g = FLt (pvar 0) (pv 1 1) ∨ g = FLt (pvar 0) (pv 2 1).
Definition reld_C : bcs := BCs [pvar 0; sv 0] reld_facts.

Definition relv_base (p : pname) : nat :=
  match p with NVar 0 => 3 | NSlot (NVar 0) k 0 => 3 * k + 4 | _ => 0 end.
Definition relv_step (p : pname) : nat :=
  match p with NVar 0 => 3 | NSlot (NVar 0) _ 0 => 4 | _ => 1 end.
Definition relv_rank (x : point) : nat := relv_base (pt_name x) + relv_step (pt_name x) * pt_off x.

Lemma relc_ok peq plt : cc_ok peq plt relc_C.
Proof.
  apply (cc_ok_inner peq plt relc_P (λ x y, relv_rank x < relv_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros x _. unfold relv_rank, pt_shift. cbn.
    assert (0 < relv_step (pt_name x)) by (unfold relv_step; repeat case_match; lia). nia.
  - intros g [-> | [-> | (k & Hg)]] _; [eexists _, _; split; [done|]; unfold relv_rank; cbn; lia..|].
    unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst;
      eexists _, _; (split; [done|]); unfold relv_rank; cbn; lia.
Qed.

Lemma rel_typed : styped ∅ [] [] (∅, None) rel_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold rel_main.
  tstep.
  { tstep; [apply prod_typed, HWs|apply relay_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ Srl relc_C); [apply relc_ok|constructor|].
  fresh_clean.
  change (bcs_inst (pshift 1) relc_C) with relc_C.
  assert (slt W [(relc_C, [pvar 0])] (pv 0 0) (sv 0)) as Hc1.
  { eapply (sl_hyp0 _ _ _ _ (pv 0 0) (sv 0)); [by left|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W [(relc_C, [pvar 0])] (sv 0) (pv 0 1)) as Hc2.
  { eapply (sl_hyp0 _ _ _ _ (sv 0) (pv 0 1)); [by left|by right; left|cbn; lia|reflexivity|reflexivity]. }
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ SEnd reld_C _ _ _ _).
  { intros f Hf Hs. destruct Hf as [-> | [-> | [-> | ->]]].
    - left. eexists _, _. split; [done|]. split_and!; [by left|done|done|done].
    - left. eexists _, _. split; [done|]. split_and!; [by right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [by right; right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [by right; right; right|done|done|done]. }
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  { intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) _.
    destruct Hf as [E|[E|[E|E]]]; injection E as -> ->; try done;
    destruct Hf' as [E|[E|[E|E]]]; injection E as -> ->; try done; unfold fresh_outer; cbn;
      first [apply (slt_po W _ (pv 0 0) HW)|apply (slt_po W _ (sv 0) HW)|exact Hc2
            |eapply sl_trans; [exact Hc1|apply (slt_po W _ (sv 0) HW)]]. }
  fresh_clean.
  match goal with |- typed _ _ ?Ψ0 _ _ _ _ _ => set (Ψ := Ψ0) end.
  assert (∀ u v, reld_facts (FLt u v) → fact_scoped 3 (FLt u v) →
            slt W Ψ (pt_inst (plist [pvar 0; pv 1 0; Pt (NSlot (NVar 1) 0 0) 0]) u)
                    (pt_inst (plist [pvar 0; pv 1 0; Pt (NSlot (NVar 1) 0 0) 0]) v)) as Hd.
  { intros u v Hf Hs. apply (slt_hyp_fresh W Ψ (bcs_inst (pshift 1) reld_C) (pvar 0) u v);
      [by right; left|done|done]. }
  assert (∀ g, relc_P g → fact_scoped 1 g →
            fact_holds (seqs W Ψ) (slt W Ψ) (fact_map (pt_inst (plist [pv 1 0])) g)) as Hc.
  { intros [x y|x y] Hg Hs; cbn.
    - eapply (sl_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity].
    - eapply (se_hyp0 _ _ _ _ x y); [by left|exact Hg|exact Hs|reflexivity|reflexivity]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pv 1 0; pvar 0]) as HC.
  { apply bcs_hold_intro. intros g [Hg|(k & Hg)] Hs.
    - unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn.
      + apply (Hd (pvar 1) (pvar 0)); [by left|cbn; lia].
      + apply (Hc (FLt (pv 0 0) (sv 0))); [by left|cbn; lia].
      + apply (Hc (FLt (sv 0) (pv 0 1))); [by right; left|cbn; lia].
      + apply (Hd (pvar 2) (pvar 0)); [by right; left|cbn; lia].
      + apply (Hd (pvar 0) (pv 1 1)); [by right; right; left|cbn; lia].
      + apply (Hd (pvar 0) (pv 2 1)); [by right; right; right|cbn; lia].
    - assert (fact_map (pt_inst (plist [pv 1 0; pvar 0])) g = fact_map (pt_inst (plist [pv 1 0])) g) as ->.
      { unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; done. }
      apply Hc; [by right; right; exists k|].
      unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn; lia. }
  assert (Forall (skn W Ψ) [pv 1 0; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by right; left|by left|done]|constructor]. }
  assert (slt W Ψ (pv 1 0) (pvar 0)) as H1 by (apply (Hd (pvar 1) (pvar 0)); [by left|cbn; lia]).
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess (dual SEnd) (pvar 0)); change B with (TSess SEnd (pvar 0));
    change A' with (TSess (dual Srl) (pv 1 0)); change B' with (TSess Srl (pv 1 0));
    change D with (TBox 2 rel_C (TLolli None None TUnit prod_body));
    change E with (TBox 2 rel_C (TLolli None None TUnit relay_body)) end.
  tstep.
  { tstep; [|apply KTSpawn|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact H1]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 rel_C None relay_body [pv 1 0; pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None prod_body [pv 1 0; pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rel_deadlock_free : deadlock_free (∅, {[+ rel_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply rel_typed].
Qed.
