(** * A message that carries a channel or nothing

      S⁰ = !∗.Close        O = !((S⁰@self[0]) ⊕ ∗).Close

      R = λ^{ι+1}_ι ∗. let (m, c₁′) = recv c′ in
                       case m { inj₁ e ⇒ close (send ⟨∗, e⟩); close c₁′
                              | inj₂ u ⇒ u; close c₁′ }

      some = let (c, c′) = new ι { ι ≺ ι[0], ι[0]+1 ≺ ι+1 } ∗ in
             let (d, d′) = new κ { κ ≡ ι[0] } ∗ in
             spawn R; let c₁ = send ⟨inj₁ d, c⟩ in
             let (x, d₁′) = recv d′ in x; close d₁′; close c₁
      some_swapped = some with spawn R before the creation of d
      none = let (c, c′) = new ι { ι ≺ ι[0], ι[0]+1 ≺ ι+1 } ∗ in
             spawn R; close (send ⟨inj₂ ∗, c⟩)

    send at ι owes ι ≺ h for every head h of the payload type, and the
    heads of a sum are the heads of both arms ([heads] in
    types/Types.v), so [none] owes ι ≺ ι[0] although it sends no channel.
    E-Case types both arms of R, so the arm inj₁ asks ι[0] ≺ ι+1 and
    ι[0]+1 ≺ ι+1 in [none] too. All three programs use the same creation
    constraint for c, d is the alias at ι[0], and each program types
    under the hypothesis of its top-level point ι ([op_Ψ], sharp edges
    172) and is deadlock free by [soundness_created].

    With end points R holds c′ at ῑ and its upper point is ῑ+1. The
    payload of a send has head ι[0]‾, so send owes ι ≺ ι[0]‾, and d′
    sits at ι[0]‾ while main holds c₁ at ι+1, whose partner point is
    ῑ+1. The creation constraint of c grows to
    {ι ≺ ι[0], ι ≺ ι[0]‾, ι[0]+1 ≺ ι+1, ι[0]+1 ≺ ῑ+1, ι[0]‾+1 ≺ ῑ+1}. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** O = !((S⁰@self[0]) ⊕ ∗).Close with S⁰ = !∗.Close. *)
Definition So : sty := SSeq (SSnd 1 (TSum (TSess Sd (pvar 0)) TUnit)) SEnd.

(** R with c′ at the index k of the thunk's context. In each arm the
    payload component is 0 and c₁′ is 1. *)
Definition op_arm1 : expr := LetU (App EClos (App ESend (Pair EUnit (Var 0)))) (App EClos (Var 1)).
Definition op_arm2 : expr := LetU (Var 0) (App EClos (Var 1)).
Definition op_R (k : nat) : expr :=
  Lam (LetU (Var 0) (LetP (App ERecv (Var k)) (Case (Var 1) op_arm1 op_arm2))).

(** main of some after both news: d′ 0, d 1, c′ 2, c 3. *)
Definition op_tail : expr :=
  LetP (Pair (App ESend (Pair (Inj1 (Var 1)) (Var 3))) EUnit)
    (LetU (Var 0)
      (LetP (App ERecv (Var 2))
        (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 3)))))).

(** Under syntactic points c sits at the constant 0 and d at its field
    point (sharp edges 173). *)
Abbreviation sdc k := (Pt (NPayload (NConst 0) 0 0) k).

Definition some_main : expr :=
  let_new_pair_at (EPt (pconst 0)) (let_new_pair_at (EPt (sdc 0)) (LetU (App ESpawn (op_R 3)) op_tail)).

Definition some_swapped_main : expr :=
  let_new_pair_at (EPt (pconst 0)) (LetU (App ESpawn (op_R 1)) (let_new_pair_at (EPt (sdc 0)) op_tail)).

Definition none_main : expr :=
  let_new_pair_at (EPt (pconst 0)) (LetU (App ESpawn (op_R 1)) (App EClos (App ESend (Pair (Inj2 EUnit) (Var 1))))).

(** The creation constraint of c (end points, see above). *)
Abbreviation sd k := (Pt (NPayload (NVar 0) 0 0) k).

Definition op_P (g : fact) : Prop :=
  g = FLt (pv 0 0) (sd 0) ∨ g = FLt (sd 1) (pv 0 1) ∨ g = FLt (pv 0 0) (pt_dual (sd 0)) ∨
  g = FLt (sd 1) (pt_dual (pv 0 1)) ∨ g = FLt (pt_dual (sd 1)) (pt_dual (pv 0 1)).
Definition op_C : bcs := BCs [] op_P.

Definition op_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 10 * pt_off x
  | NPayload (NVar 0) 0 0 => 5 + pt_off x
  | _ => pt_off x
  end.

Lemma op_ok peq plt : cc_ok peq plt op_C.
Proof.
  apply (cc_ok_inner peq plt op_P (λ x y, op_rank x < op_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold op_rank, pt_shift. simpl. repeat case_match; lia.
  - intros g [-> | [-> | [-> | [-> | ->]]]] _; eexists _, _; (split; [done|]); cbn; lia.
  - intros [n pb o] _. unfold op_rank, pt_shift, pt_dual. simpl. repeat case_match; lia.
Qed.

(** The empty top-level constraint. *)
Definition op_C0 : bcs := BCs [] (λ _, False).

Lemma op_C0_acyclic : c0_acyclic 0 op_C0.
Proof. apply (c0_acyclic_rank 0 _ (vrank 1)); [apply vrank_shift|by intros ? ? []|apply vrank_dual]. Qed.

(** The hypothesis of ι, the top-level point of c. *)
Definition op_Ψ : hyps := [] ++ [(op_C, [pconst 0])].

Lemma op_created : created (Wpo []) op_Ψ.
Proof. apply created_snoc; [constructor|apply op_ok|constructor|fresh_const]. Qed.

(** After new@ι for c: the creation constraint gives ι ≺ ι[0] and
    ι[0]+1 ≺ ι+1, and program order gives ι[0] ≺ ι+1. *)
Ltac op_facts W HW :=
  fresh_clean;
  match goal with |- typed _ _ ?Q _ _ _ _ _ =>
    assert (slt W Q (pc 0 0) (sdc 0)) as H1
      by (eapply (sl_hyp0 _ _ op_P [pconst 0] (pv 0 0) (sd 0)); [by left|by left|cbn; lia|reflexivity|reflexivity]);
    assert (slt W Q (sdc 1) (pc 0 1)) as H2
      by (eapply (sl_hyp0 _ _ op_P [pconst 0] (sd 1) (pv 0 1)); [by left|by right; left|cbn; lia|reflexivity|reflexivity]);
    assert (slt W Q (sdc 0) (pc 0 1)) as H3
      by (eapply sl_trans; [apply (slt_po W _ (sdc 0) HW)|exact H2]);
    assert (slt W Q (pc 0 0) (pt_dual (sdc 0))) as H4
      by (eapply (sl_hyp0 _ _ op_P [pconst 0] (pv 0 0) (pt_dual (sd 0)));
            [by left|by right; right; left|cbn; lia|reflexivity|reflexivity]);
    assert (slt W Q (sdc 1) (pt_dual (pc 0 1))) as H5
      by (eapply (sl_hyp0 _ _ op_P [pconst 0] (sd 1) (pt_dual (pv 0 1)));
            [by left|by right; right; right; left|cbn; lia|reflexivity|reflexivity]);
    assert (slt W Q (sdc 0) (pt_dual (pc 0 1))) as H6
      by (eapply sl_trans; [apply (slt_po W _ (sdc 0) HW)|exact H5]);
    assert (slt W Q (pt_dual (sdc 1)) (pt_dual (pc 0 1))) as H7
      by (eapply (sl_hyp0 _ _ op_P [pconst 0] (pt_dual (sd 1)) (pt_dual (pv 0 1)));
            [by left|by right; right; right; right|cbn; lia|reflexivity|reflexivity]);
    assert (slt W Q (pt_dual (sdc 0)) (pt_dual (pc 0 1))) as H8
      by (eapply sl_trans; [apply (slt_po W _ (pt_dual (sdc 0)) HW)|exact H7])
  end.

Ltac op_ub_future HW :=
  apply ubs_intro; [intros y Hy; mem_cases Hy; done|];
  exists (pt_dual (pc 0 1)); split; [done|]; first [right; done|apply sle_refl, HW].

Ltac op_arm1 W HW :=
  cbn; tstep;
  [ tstep;
    [ tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (sdc 0)); cbn; set_solver|done|];
      [ tstep; tstep | op_ub_future HW ]
    | apply KTClos | done | op_ub_future HW ]
  | tstep; [tstep|apply KTClos|done|op_ub_future HW] ].

Ltac op_arm2 W HW :=
  cbn; tstep; [tstep|]; tstep; [tstep|apply KTClos|done|op_ub_future HW].

Ltac op_R W HW :=
  tstep; [|apply KTSpawn|done|apply ubs_none];
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pc 0 1))) (Some (pc 0 0)) 0);
  [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|];
  cbn; tstep; [tstep|]; cbn; tstep;
  [ tstep; [tstep|apply (KTRecv _ _ _ 1 (TSum (TSess Sd (pvar 0)) TUnit) SEnd (pt_dual (pc 0 0)))|kscope|];
    apply ubs_intro; [intros y Hy; mem_cases Hy|];
    exists (pt_dual (pc 0 1)); split; [done|]; right; apply (slt_po W _ (pt_dual (pc 0 0)) HW)
  | cbn; eapply tv_case; [exact HW|reflexivity|tstep|op_arm1 W HW|op_arm2 W HW] ].

Ltac op_spawn_R W HW := tstep; [op_R W HW|cbn].

Lemma none_typed : styped ∅ op_Ψ [] (∅, None) none_main TUnit.
Proof.
  apply styped_wnil. pose proof wnil_strict as HWs.
  pose proof (proj1 HWs) as HW. set (W := wnil) in *. unfold none_main, let_new_pair_at, op_Ψ.
  new_top HWs So (pconst 0).
  op_facts W HW.
  op_spawn_R W HW.
  cbn. tstep; [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|apply (KTSend _ _ _ 1 (TSum (TSess Sd (pvar 0)) TUnit) SEnd (pc 0 0))| |].
  - tstep; [tstep|apply t_inj2; tstep].
  - cbn. intros h Hh. mem_cases Hh. done.
  - kscope.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** main after both news. send owes ι ≺ ι[0]‾ for the payload and
    ι ≺ ι[0] for d′ at ι[0]‾. recv d′ owes ι[0]‾ ≺ ῑ+1 and close d′
    owes ι[0]‾+1 ≺ ῑ+1, because main holds c₁ at ι+1. *)
Lemma op_tail_typed W Φ Ψ :
  world_wf W →
  slt W Ψ (pc 0 0) (sdc 0) → slt W Ψ (pc 0 0) (pt_dual (sdc 0)) →
  slt W Ψ (pt_dual (sdc 0)) (pt_dual (pc 0 1)) → slt W Ψ (pt_dual (sdc 1)) (pt_dual (pc 0 1)) →
  typed W Φ Ψ ∅
    [Some (TSess (dual Sd) (pt_dual (sdc 0))); Some (TSess Sd (sdc 0)); None; None;
     None; Some (TSess So (pc 0 0)); None; None]
    (∅, None) (rename (upren (upren (λ x, 2 + x))) op_tail) TUnit.
Proof.
  intros HW H1 H4 H8 H7. cbn. tstep.
  { tstep; [tstep|].
    tstep; [|apply (KTSend _ _ _ 1 (TSum (TSess Sd (pvar 0)) TUnit) SEnd (pc 0 0))| |].
    - tstep; [tstep|apply t_inj1; tstep].
    - cbn. intros h Hh. mem_cases Hh. done.
    - kscope.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma some_typed : styped ∅ op_Ψ [] (∅, None) some_main TUnit.
Proof.
  apply styped_wnil. pose proof wnil_strict as HWs.
  pose proof (proj1 HWs) as HW. set (W := wnil) in *. unfold some_main, let_new_pair_at, op_Ψ.
  new_top HWs So (pconst 0).
  op_facts W HW.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (sdc 0) HWs); [ground|eapply skn_inst; [by left|by left|done]|].
  cbn. op_spawn_R W HW.
  apply op_tail_typed; assumption.
Qed.

Lemma some_swapped_typed : styped ∅ op_Ψ [] (∅, None) some_swapped_main TUnit.
Proof.
  apply styped_wnil. pose proof wnil_strict as HWs.
  pose proof (proj1 HWs) as HW. set (W := wnil) in *. unfold some_swapped_main, let_new_pair_at, op_Ψ.
  new_top HWs So (pconst 0).
  op_facts W HW.
  op_spawn_R W HW.
  apply (t_new_at W _ _ _ _ _ _ _ Sd (sdc 0) HWs); [ground|eapply skn_inst; [by left|by left|done]|].
  cbn. apply op_tail_typed; assumption.
Qed.

Theorem some_deadlock_free : deadlock_free (∅, {[+ some_main +]}).
Proof. apply (soundness_created_s op_Ψ _ TUnit op_created); [constructor|apply some_typed]. Qed.

Theorem some_swapped_deadlock_free : deadlock_free (∅, {[+ some_swapped_main +]}).
Proof. apply (soundness_created_s op_Ψ _ TUnit op_created); [constructor|apply some_swapped_typed]. Qed.

Theorem none_deadlock_free : deadlock_free (∅, {[+ none_main +]}).
Proof. apply (soundness_created_s op_Ψ _ TUnit op_created); [constructor|apply none_typed]. Qed.
