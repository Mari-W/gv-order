(** * rx-chain is deadlock free (fx-final, 2026-11-24)

      grow = !(f = λw. let ⟨c, c′⟩ = new in             c at ι·0
                       let ⟨d, d′⟩ = new in             d at a fresh root π
                       let ∗ = spawn (λ_. recvclose d′) in
                       let ∗ = close (send ⟨∗, d⟩) in
                       let ∗ = spawn (λ_. (force f) c′) in
                       let ∗ = close c in close w)
      main = let ⟨w, w′⟩ = new in let ∗ = spawn (λ_. close w′) in (force grow) w

    The program of examples/Descent.v ([rc_main]), which has no typing at
    any finite bound ([rx_chain_rejected]). At N = ∞ it types, on the
    template of the recursive fork-join worker of examples/ForkJoin.v.

    The box parameter w sits at ι. The box creates c at the field ι·0
    and closes c while it holds w, so it asks ι·0 ≺ ῑ. The child forces
    the box at (ι·0)‾. The box hypothesis H(ι) is F(ι) = {ι·0 ≺ ῑ}
    together with F((ι·u)‾) for every nonempty word u of fields, so
    H((ι·0)‾) ⊆ H(ι) ([rcH_desc]). The box creates d at a fresh root π
    with the constraint C that puts π and π⁺ below the three heads it
    holds, ῑ, ι·0 and (ι·0)‾. Every fact of C leaves the tree of π, so
    C has no bridge, and program order alone is acyclic on the tree of
    π ([rc_C_acyc]). main creates w at a fresh root ρ with the laws
    H(ρ), which descend forever, ρ ≻ ρ·0 ≻ ρ·0·0 ≻ …. (acyc-new) accepts
    them ([rc_acyc]) by the order [fjr_lt] of examples/ForkJoin.v.

    - [rc_dftyped]      : main types at N = ∞ over the empty world.
    - [rc_term]         : P-Term types the closed program.
    - [rc_deadlock_free]: the program is deadlock free, without excluded
                          middle. *)

From GV Require Export examples.Descent examples.GenNew.
From GV Require Import examples.ForkJoin.

(** ** The box hypothesis *)

Definition rcF (x : point) (g : fact) : Prop := g = FLt (x·0) x‾.
Definition rcH (x : point) (g : fact) : Prop :=
  rcF x g ∨ ∃ w, w ≠ [] ∧ rcF (fpath x w)‾ g.

Lemma rcF_inst σ y g : rcF y g → rcF (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof. intros ->. cbn [fact_map]. by rewrite pt_inst_dual, pt_inst_field. Qed.

Lemma rcH_inst σ x g : rcH x g → rcH (pt_inst σ x) (fact_map (pt_inst σ) g).
Proof.
  intros [H|(w & Hw & H)]; [left; by apply rcF_inst|right].
  exists w. split; [done|]. rewrite <-fpath_inst, <-pt_inst_dual. by apply rcF_inst.
Qed.

(** H descends to a child: H((x·κ)‾) ⊆ H(x). *)
Lemma rcH_desc x κ g : rcH (x·κ)‾ g → rcH x g.
Proof.
  intros [H|(w & Hw & H)]; right.
  - exists [κ]. split; [done|]. exact H.
  - exists (κ :: w). split; [done|]. by rewrite fpath_dual in H.
Qed.

Lemma rcH_root x u v : rcH x (FLt u v) → pt_root u = pt_root x ∧ pt_root v = pt_root x.
Proof.
  intros [E|(w & _ & E)]; injection E as -> ->; [done|].
  split; change (pt_root (fpath x w) = pt_root x); apply fpath_root.
Qed.

(** Every fact of H at x is a fact of H at ρ instantiated at x. *)
Lemma rcH_back x g : rcH x g → ∃ g0, rcH ρ g0 ∧ fact_scoped 1 g0 ∧ g = fact_map (pt_inst (plist [x])) g0.
Proof.
  assert (pt_inst (plist [x]) ρ = x) as Ex by (rewrite pt_inst_pvar_at; reflexivity).
  intros [->|(w & Hw & ->)].
  - exists (FLt (ρ·0) ρ‾). split_and!; [by left|split; apply pn_vb_root0; reflexivity|].
    cbn [fact_map]. repeat rewrite ?pt_inst_dual, ?pt_inst_field. by rewrite Ex.
  - exists (FLt ((fpath ρ w)‾·0) (fpath ρ w)‾‾). split_and!; [right; by exists w| |].
    + split; apply pn_vb_root0; change (pt_root (fpath ρ w) = NVar 0); by rewrite fpath_root.
    + cbn [fact_map]. repeat rewrite ?pt_inst_dual, ?pt_inst_field. by rewrite fpath_inst, Ex.
Qed.

(** A fact of H at a point ι, from the hypothesis (H, [ι]) of Γ. *)
Lemma rcH_slt W Γ ι u v : (BCs [] (rcH ρ), [ι]) ∈ hc_hyps Γ → rcH ι (FLt u v) → slt W Γ u v.
Proof.
  intros Hin Hf. destruct (rcH_back ι _ Hf) as (g0 & Hg0 & Hs & E).
  eapply (slt_hyp _ _ (rcH ρ) [ι] g0); [done|done|done|by rewrite <-E].
Qed.

Definition rc_H : bcs := BCs [] (rcH ρ).

(** ** (acyc-new) for the laws of main *)

Lemma rcF_lt z u v : pt_off z = 0 → rcF z (FLt u v) → fjr_lt u v.
Proof.
  intros Ho E. injection E as -> ->. right. cbn [pt_field pt_dual pt_pol pt_off].
  split; [done|]. destruct (pt_pol z) eqn:Hp; simpl.
  - left. done.
  - right. split; [done|]. unfold pt_depth. simpl. lia.
Qed.

Lemma rc_L_lt u v : rcH ρ (FLt u v) → fjr_lt u v.
Proof.
  intros [H|(w & Hw & H)].
  - by apply (rcF_lt ρ).
  - apply (rcF_lt (fpath ρ w)‾); [|exact H].
    change (pt_off (fpath ρ w)‾) with (pt_off (fpath ρ w)). by apply fpath_field.
Qed.

Lemma rc_step_lt u v : new_step (bcs_of (rcH ρ)) u v → fjr_lt u v.
Proof.
  intros (_ & _ & [[Hf _]|[-> | ->]]); [by apply rc_L_lt| |]; left; cbn [pt_shift pt_dual pt_off]; lia.
Qed.

Lemma rc_tc_lt u v : tc (new_step (bcs_of (rcH ρ))) u v → fjr_lt u v.
Proof.
  induction 1 as [u v H|u v w H _ IH]; [by apply rc_step_lt|].
  eapply fjr_lt_trans; [by apply rc_step_lt|exact IH].
Qed.

Lemma rc_acyc W Γ : acyc_new W Γ (bcs_of (rcH ρ)).
Proof.
  split.
  - intros x _ Hc. exact (fjr_lt_irrefl x (rc_tc_lt x x Hc)).
  - apply cons_open_1. intros z y (Hz & _ & [[Hf _]|(v & u & [Hf _] & _)]); exfalso; apply Hz; unfold in_tree0;
      by destruct (rcH_root _ _ _ Hf) as [-> _].
Qed.

Lemma rc_tree_ends : tree_ends (bcs_of (rcH ρ)).
Proof. intros x y Hf _. unfold in_tree0. by destruct (rcH_root _ _ _ Hf) as [_ ->]. Qed.

(** ** The constraint of d

    Variable 0 is π, variable 1 is ι, the point of its environment. *)

Definition rc_P (g : fact) : Prop :=
  ∃ s y, (s = pvar 0 ∨ s = (pvar 0)⁺) ∧ (y = (pvar 1)‾ ∨ y = (pvar 1)·0 ∨ y = ((pvar 1)·0)‾) ∧ g = FLt s y.
Definition rc_C : bcs := BCs [ρ] rc_P.

Lemma rc_P_left x y : rc_P (FLt x y) → in_tree0 x.
Proof. intros (s & y' & [-> | ->] & _ & E); injection E as -> ->; reflexivity. Qed.

Lemma rc_P_right x y : rc_P (FLt x y) → ¬ in_tree0 y.
Proof. intros (s & y' & _ & [-> |[-> | ->]] & E); injection E as -> ->; unfold in_tree0; cbn; congruence. Qed.

Lemma rc_po_lt C x y : (∀ u v, cfact C u v → in_tree0 u → in_tree0 v → False) →
  tc (new_step C) x y → pt_off x < pt_off y.
Proof.
  intros HC. induction 1 as [x y H|x y z H _ IH].
  - destruct H as (Hx & Hy & [Hf|[-> | ->]]); [exfalso; by apply (HC x y)|simpl; lia|simpl; lia].
  - destruct H as (Hx & Hy & [Hf|[-> | ->]]); [exfalso; by apply (HC x y)|simpl in *; lia|simpl in *; lia].
Qed.

Lemma rc_C_acyc W Γ : acyc_new W Γ rc_C.
Proof.
  split.
  - intros x _ Hc. apply rc_po_lt in Hc; [lia|]. intros u v [Hf _] _ Hv. by apply (rc_P_right u v Hf).
  - apply cons_open_1. intros z y (Hz & _ & [[Hf _]|(v & u & [Hf _] & _)]); exfalso; apply Hz;
      by apply (rc_P_left _ _ Hf).
Qed.

(** ** The programs *)

Definition rc_Sd : sty := SSeq (SSnd 0 TUnit) SEnd.

Definition rc_arr : ty := TLolli UTop LNone None (TSess SEnd ρ None None) TUnit None.
Definition rc_box : ty := TBox 1 0 rc_H None None rc_arr.

Lemma rc_box_shift n :
  lenv_pinst (pshift 1) (Some rc_box :: nones n) = Some rc_box :: nones n.
Proof. unfold lenv_pinst. rewrite fmap_cons, fmap_replicate. reflexivity. Qed.

Lemma rc_arr_inst x : ty_inst [x] rc_arr = TLolli UTop LNone None (TSess SEnd x None None) TUnit None.
Proof. unfold ty_inst, rc_arr. simpl. by rewrite pt_inst_pvar_at. Qed.

(** The recursive call: the box variable forced at x, where H holds. *)
Lemma rc_force_var W Γ Δ F i x :
  Δ !! i = Some (Some rc_box) → (∀ y o, y ≠ i → Δ !! y = Some o → spare o) →
  hold_at W Γ rc_H [x] →
  dftyped W ∅ Γ Δ F (EForce (Var i)) (TLolli UTop LNone None (TSess SEnd x None None) TUnit None).
Proof.
  intros Hi Hs HC. rewrite <-rc_arr_inst, <-(sinst_nil (ty_inst [x] rc_arr)).
  eapply d_force with (C := rc_H) (ub := None) (c := None);
    [done|exact HC|done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|].
  by eapply d_var'.
Qed.

(** H at (ι·0)‾ from H at ι. *)
Lemma rc_desc_hold W Γ ι : (BCs [] (rcH ρ), [ι]) ∈ hc_hyps Γ → hold_at W Γ rc_H [(ι·0)‾].
Proof.
  intros Hin. apply hold_at_nil. intros f Hf _.
  pose proof (rcH_inst (plist [(ι·0)‾]) ρ f Hf) as H.
  assert (pt_inst (plist [(ι·0)‾]) ρ = (ι·0)‾) as E by (rewrite pt_inst_pvar_at; reflexivity).
  rewrite E in H. apply rcH_desc in H.
  destruct (fact_map (pt_inst (plist [(ι·0)‾])) f) as [u v]. by apply (rcH_slt W Γ ι).
Qed.

Section rbody.
  Context (W : sworld) (Γ : hctx).
  Local Definition Γb : hctx := hc_open 1 rc_H Γ.
  Local Definition Γd : hctx := hc_open 1 rc_C Γb.

  Lemma rc_in_d : (BCs [] (rcH ρ), [pvar 1]) ∈ hc_hyps Γd.
  Proof.
    assert ((BCs [] (rcH ρ), [pvar 1]) =
            (bcs_inst (pshift 1) (bcs_inst (pshift 1) rc_H), pt_inst (pshift 1) <$> ids 1)) as -> by reflexivity.
    apply in_open_old. apply (Γbox_in 1 rc_H ρ Γ).
  Qed.

  Ltac rc_fact1 s y :=
    eapply (slt_hyp_env _ _ _ _ (FLt s y));
      [apply in_open_new|exists s, y; split_and!; [disj_tac|disj_tac|reflexivity]|cbn; lia|reflexivity].
  Ltac rc_fact s :=
    first [ rc_fact1 s (pvar 1)‾ | rc_fact1 s ((pvar 1)·0) | rc_fact1 s ((pvar 1)·0)‾ ].

  Lemma rc_body_typed n :
    dftyped W ∅ Γb (Some (TSess SEnd ρ None None) :: Some rc_box :: nones n)
      (∅, None) rc_body TUnit.
  Proof.
    unfold rc_body, let_new.
    (* c at ι·0 *)
    eapply d_let; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 0 SEnd None None None None); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    (* d at a fresh root *)
    eapply d_let; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_acyc _ _ _ _ rc_C rc_Sd None None None None); [apply spare_unl; spare_tac|apply rc_C_acyc|contr_tac]. }
    eapply d_open with (i := 0); [reflexivity|cbn; tauto|apply rc_C_acyc|].
    rewrite tenv_pinst_empty, sf_pinst_empty.
    rewrite !lenv_pinst_cons', lenv_pinst_nones.
    assert (fmap (M:=option) (pinst_ty (pshift 1)) (Some rc_box) = Some rc_box) as -> by reflexivity.
    cbn [fmap option_fmap option_map pinst_ty insert list_insert].
    fold Γd.
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    (* spawn (λ_. recvclose d′) *)
    eapply d_letu; [apply tsplit_empty
      |lsplit_tac (ESpawn (Lam (LetU (Var 0) (LetP (ERecv (Var 1)) (LetU (Var 1) (EClose (Var 0))))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
      - eapply d_recv with (x := (pvar 0)‾) (m := 0) (T := TUnit) (S0 := dual rc_Sd);
          [done|exact I| |eapply d_var'; [reflexivity|spare_tac]].
        apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy.
      - eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
        { eapply d_var'; [reflexivity|]. spare_tac. }
        eapply d_close with (S0 := SEnd) (x := (pvar 0)‾⁺); [done|apply ub_below_empty|].
        eapply d_var'; [reflexivity|]. spare_tac. }
    (* close (send ⟨∗, d⟩) *)
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (ESend (Pair EUnit (Var 1)))) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := (pvar 0)⁺); [done| |].
      - apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy;
          rc_fact ((pvar 0)⁺).
      - eapply d_send with (x := pvar 0) (m := 0) (T := TUnit) (S0 := rc_Sd);
          [done|exact I|done|cbn; set_solver| |].
        + apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy;
            rc_fact (pvar 0).
        + eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var 1)
                         |apply d_unit'; spare_tac|eapply d_var'; [reflexivity|spare_tac]]. }
    (* spawn (λ_. (force f) c′) *)
    eapply d_letu; [apply tsplit_empty
                   |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 8)) (Var 4))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce (Var 8)) EUnit|done| |].
      + apply rc_force_var; [reflexivity|spare_tac|apply rc_desc_hold, rc_in_d].
      + eapply d_var'; [reflexivity|]. spare_tac. }
    (* close c; close w *)
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 4)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := (pvar 1)·0); [done| |].
      - apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy.
        apply (rcH_slt _ _ (pvar 1)); [apply rc_in_d|left; reflexivity].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := pvar 1); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End rbody.

Lemma rc_typed W Γ n F : dftyped W ∅ Γ (nones n) F rc_grow rc_box.
Proof.
  eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. repeat (apply Is_true_andb; split); done. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil, rc_box_shift.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  { done. }
  apply rc_body_typed.
Qed.

(** ** main *)

Definition Γrc : hctx := hc_open 1 (bcs_of (rcH ρ)) hc_empty.

Lemma rc_force W n F :
  dftyped W ∅ Γrc (nones n) F (EForce rc_grow) (TLolli UTop LNone None (TSess SEnd ρ None None) TUnit None).
Proof.
  rewrite <-rc_arr_inst, <-(sinst_nil (ty_inst [ρ] rc_arr)).
  eapply d_force with (C := rc_H) (ub := None) (c := None);
    [done| |done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|apply rc_typed].
  apply hold_at_nil. intros f Hf Hs.
  assert (fact_map (pt_inst (plist [ρ])) f = f) as ->.
  { destruct f as [u v]. destruct Hs as [Hu Hv]. cbn [fact_map].
    change [ρ] with (ids 1). by rewrite !pt_inst_ids. }
  destruct f as [u v]. eapply hyp_slt_ids; [unfold Γrc, hc_open; simpl; by left|exact Hf|exact Hs].
Qed.

Theorem rc_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) rc_main TUnit.
Proof.
  unfold rc_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { apply (d_new_acyc _ _ _ _ (bcs_of (rcH ρ)) SEnd None None None None);
      [apply spare_unl; spare_tac|apply rc_acyc|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|apply cons_tree, rc_tree_ends|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γrc.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
                 |lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
  - apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce rc_grow) EUnit|done| |].
    + apply (rc_force _ 3).
    + eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

(** P-Term types the closed program over the empty world. *)
Theorem rc_term : ptyped None (khalf None) sw_empty ∅ (∅, {[+ rc_main +]}) TUnit.
Proof.
  apply (p_term_half None sw_empty ∅ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply pfree_empty.
  - intros o e He. by rewrite lookup_empty in He.
  - set_solver.
  - assert (tenv_of (fhalf None) ∅ ∪ ∅ = tenv_df ∅) as ->.
    { unfold tenv_of, tenv_df. by rewrite !fmap_empty, map_union_empty. }
    apply rc_dftyped.
  - apply sw_empty_wok.
Qed.

(** rx-chain is deadlock free, without excluded middle. *)
Theorem rc_deadlock_free : deadlock_free (∅, {[+ rc_main +]}).
Proof. exact (soundness _ _ TUnit rc_term). Qed.

Print Assumptions rc_dftyped.
Print Assumptions rc_deadlock_free.
