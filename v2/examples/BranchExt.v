(** * Per-branch worlds at E-Case fail in the Kripke relation (item C1)

      bx_arm a b = λw. close w; close a; close b
      bx_thread  = case branch e of inl w ⇒ close w; close c; close d
                                  | inr w ⇒ close w; close d; close c

    The thread holds e at z, c at x and d at y. Its left arm closes c
    while it holds d, so it asks x ≺ ȳ. Its right arm closes d while it
    holds c, so it asks y ≺ x̄. The base world [bx_W0] orders z and both
    branch points of z below x̄ and ȳ and says nothing about x and y. The
    left arm types at [bx_Wl] = [bx_W0] with x ≺ ȳ and the right arm at
    [bx_Wr] = [bx_W0] with y ≺ x̄ ([bx_left_typed], [bx_right_typed]).
    The scrutinee types at [bx_W0] ([bx_scrut_typed]). Each arm consumes
    w, c and d and returns unit, so every proposed join restriction holds.
    No point of the arms occurs in the result type, in the context after
    the case or in the future.

    A rule E-Case that types each arm at its own extension of the world
    and concludes at [bx_W0] therefore types the thread at [bx_W0]. The
    thread is not in E at the strict world [bx_R], which models [bx_W0]
    and adds x̄ ≺ y ([bx_not_E]). The partner of the right arm may
    have fixed that fact before the label arrives. When the right label
    arrives, the thread closes d while it holds c and x̄ ≺ y, so it is
    not ready. E and P hold in every extension of their world (decision
    Q9), and no extension of [bx_R] holds y ≺ x̄.

    So [fundamental] fails for such a rule, at N = ∞ already. The fact of
    a branch concerns the old points x and y, which other threads may
    order before the label arrives. Whole-world acyclicity is not
    preserved by the extension at the branch step. The two threads of
    counterexamples.md D23 (branch-local checks), each typed by such a
    rule, deadlock together.

    The fundamental theorem also rejects the thread on the current rules,
    at every static world that [bx_R] models ([bx_rejected]). *)

From GV Require Export examples.SemBranch.
From GV Require Import compat.Redex compat.Bind.

(** ** The program *)

Definition oe : cend := EPos "e".

Definition bx_arm (a b : cend) : expr := LetU (EClose (Var 0)) (cl2 a b).
Definition bx_thread : expr := Case (EBra (Chan oe)) (bx_arm oc od) (bx_arm od oc).

(** The points: e at z, c at x, d at y, constant roots 0, 1 and 2. *)
Definition qz : point := MkPt (NConst 0) true 0.
Definition qx : point := MkPt (NConst 1) true 0.
Definition qy : point := MkPt (NConst 2) true 0.

(** ** Worlds *)

Definition bx_consts : gset nat := {[0]} ∪ {[1]} ∪ {[2]}.

Definition bx_base (f : fact) : Prop :=
  f = FLt qz (qx‾) ∨ f = FLt qz (qy‾) ∨
  (∃ i, f = FLt (bra_pt qz i) (qx‾)) ∨ (∃ i, f = FLt (bra_pt qz i) (qy‾)).

Definition bx_W0 : sworld := SWorld bx_consts bx_base.
Definition bx_Wl : sworld := SWorld bx_consts (λ f, bx_base f ∨ f = FLt qx (qy‾)).
Definition bx_Wr : sworld := SWorld bx_consts (λ f, bx_base f ∨ f = FLt qy (qx‾)).
Definition bx_Wopp : sworld := SWorld bx_consts (λ f, bx_base f ∨ f = FLt (qx‾) qy).

Lemma bx_croot x : pt_root x = NConst 0 ∨ pt_root x = NConst 1 ∨ pt_root x = NConst 2 →
  croot_in bx_consts x.
Proof.
  unfold croot_in, bx_consts. intros [H|[H|H]]; rewrite H; eexists; (split; [reflexivity|set_solver]).
Qed.

Ltac bx_base_wf :=
  intros Hf; unfold bx_base in Hf;
  repeat match goal with
  | H : _ ∨ _ |- _ => destruct H as [H|H]
  | H : ∃ _, _ |- _ => destruct H as [? H]
  end;
  match goal with H : FLt _ _ = FLt _ _ |- _ => injection H as -> -> end;
  split; apply bx_croot; cbn; auto.

Lemma bx_W0_wf : sworld_wf bx_W0.
Proof. split. intros x y Hf. simpl in Hf. revert Hf. bx_base_wf. Qed.

Lemma bx_Wl_wf : sworld_wf bx_Wl.
Proof. split. intros x y Hf. simpl in Hf. revert Hf. bx_base_wf. Qed.

Lemma bx_Wr_wf : sworld_wf bx_Wr.
Proof. split. intros x y Hf. simpl in Hf. revert Hf. bx_base_wf. Qed.

Lemma bx_Wopp_wf : sworld_wf bx_Wopp.
Proof. split. intros x y Hf. simpl in Hf. revert Hf. bx_base_wf. Qed.

(** Every fact of [bx_Wopp] raises the constant. *)
Lemma bx_Wopp_swf : swf bx_Wopp.
Proof.
  apply swf_rank. simpl. intros x y Hf. unfold bx_base in Hf.
  repeat match goal with
  | H : _ ∨ _ |- _ => destruct H as [H|H]
  | H : ∃ _, _ |- _ => destruct H as [? H]
  end;
  match goal with H : FLt _ _ = FLt _ _ |- _ => injection H as -> -> end;
  unfold rk; cbn; try destruct_or?; repeat match goal with b : bool |- _ => destruct b end; cbn; lia.
Qed.

Definition bx_R : world := wstrict_of bx_Wopp (swf_sacyc _ bx_Wopp_swf).

Lemma bx_R_strict : wstrict bx_R.
Proof. done. Qed.

Lemma bx_R_models : wmodels bx_R bx_W0.
Proof.
  apply (wmodels_ext _ _ bx_Wopp); [|by apply wstrict_of_models, bx_Wopp_wf].
  split; [done|]. intros g Hg. by left.
Qed.

Lemma bx_R_opp : bx_R ⊢ qx‾ ≺ qy.
Proof.
  apply (wmodels_lt _ bx_Wopp); [by apply wstrict_of_models, bx_Wopp_wf|].
  apply sw_lt_fact. simpl. by right.
Qed.

(** ** The arms type at their own extensions *)

Definition bx_T (i : bool) : ty := TSess SEnd (bra_pt qz i) None None.

Definition bx_Θ (a b : cend) (xa xb : point) : tenv :=
  {[a := TE SEnd xa None None]} ∪ {[b := TE SEnd xb None None]}.

Lemma bx_heads a b xa xb y : y ∈ tenv_heads (bx_Θ a b xa xb) → y = xa‾ ∨ y = xb‾.
Proof.
  rewrite elem_of_tenv_heads. intros (o & e & Ho & ->). unfold bx_Θ in Ho.
  apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]];
    apply lookup_singleton_Some in Ho as [_ <-]; simpl; auto.
Qed.

Lemma tsplit_empty_l Θ : tsplit Θ ∅ Θ.
Proof. split; [apply map_disjoint_empty_l|by rewrite map_empty_union]. Qed.

(** close a; close b under one unused binder. *)
Lemma cl2_typed1 W a b xa xb :
  a ≠ b → slt W hc_empty xa (xb‾) →
  dftyped W (bx_Θ a b xa xb) hc_empty [None] (∅, None) (cl2 a b) TUnit.
Proof.
  intros Hab Hlt. unfold cl2, bx_Θ.
  eapply d_letu with (Θ1 := {[a := TE SEnd xa None None]}) (Θ2 := {[b := TE SEnd xb None None]})
    (Δ1 := [None]) (Δ2 := [None]); [|apply lsplit_none, lsplit_nil| |].
  - split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity].
  - eapply d_close with (S0 := SEnd) (x := xa) (a := None); [done| |].
    + cbn. split_and!; [|done]. intros y Hy.
      assert (y = xb‾) as -> by (rewrite tenv_heads_one' in Hy; simpl in Hy; set_solver).
      exact Hlt.
    + apply d_chan. apply spare_unl. spare_tac.
  - eapply d_close with (S0 := SEnd) (x := xb) (a := None); [done|apply ub_below_empty|].
    apply d_chan. apply spare_unl. spare_tac.
Unshelve. all: try exact None.
Qed.

(** λw. close w; close a; close b, the binder w at the branch point of
    z for label i. It closes w while it holds a and b, then a while it
    holds b. *)
Lemma bx_arm_typed W i a b xa xb :
  a ≠ b → slt W hc_empty xa (xb‾) →
  slt W hc_empty (bra_pt qz i) (xa‾) → slt W hc_empty (bra_pt qz i) (xb‾) →
  dftyped W (bx_Θ a b xa xb) hc_empty [Some (bx_T i)] (∅, None) (bx_arm a b) TUnit.
Proof.
  intros Hab Hlt H1 H2. unfold bx_arm.
  eapply d_letu with (Θ1 := ∅) (Θ2 := bx_Θ a b xa xb) (Δ1 := [Some (bx_T i)]) (Δ2 := [None]);
    [apply tsplit_empty_l|apply lsplit_l, lsplit_nil| |by apply cl2_typed1].
  eapply d_close with (S0 := SEnd) (x := bra_pt qz i) (a := None); [done| |].
  - cbn. split_and!; [|done]. intros y Hy.
    assert (y ∈ tenv_heads (bx_Θ a b xa xb)) as Hy' by set_solver.
    destruct (bx_heads _ _ _ _ _ Hy') as [->| ->]; done.
  - apply d_var. split; [done|]. intros [|y] U Hy HU; [done|]. done.
Unshelve. all: try exact None.
Qed.

Lemma bx_fact (W : sworld) f x y : sw_facts W f → f = FLt x y → slt W hc_empty x y.
Proof. intros Hf ->. apply sl_w, sw_lt_fact, Hf. Qed.

Lemma oc_od' : od ≠ oc.
Proof. unfold oc, od. congruence. Qed.

(** The left arm at [bx_Wl], which adds x ≺ ȳ. *)
Theorem bx_left_typed :
  dftyped bx_Wl (bx_Θ oc od qx qy) hc_empty [Some (bx_T false)] (∅, None) (bx_arm oc od) TUnit.
Proof.
  apply bx_arm_typed; [apply oc_od| | |].
  - eapply bx_fact; [by right|done].
  - eapply bx_fact; [left; right; right; left; by exists false|done].
  - eapply bx_fact; [left; right; right; right; by exists false|done].
Qed.

(** The right arm at [bx_Wr], which adds y ≺ x̄. *)
Theorem bx_right_typed :
  dftyped bx_Wr (bx_Θ od oc qy qx) hc_empty [Some (bx_T true)] (∅, None) (bx_arm od oc) TUnit.
Proof.
  apply bx_arm_typed; [apply oc_od'| | |].
  - eapply bx_fact; [by right|done].
  - eapply bx_fact; [left; right; right; right; by exists true|done].
  - eapply bx_fact; [left; right; right; left; by exists true|done].
Qed.

(** The scrutinee at [bx_W0], branch e at z while c and d are held. *)
Theorem bx_scrut_typed :
  dftyped bx_W0 {[oe := TE (SWith SEnd SEnd) qz None None]} hc_empty []
    (sf_unionb (∅, None) (tenv_heads (bx_Θ oc od qx qy) ∪ lenv_heads []) (lenv_bot []))
    (EBra (Chan oe)) (TSum (bx_T false) (bx_T true)).
Proof.
  eapply d_branch with (S0 := SWith SEnd SEnd) (a := None) (mS := None); [done| |].
  - cbn. split_and!; [|done]. intros y Hy.
    assert (y ∈ tenv_heads (bx_Θ oc od qx qy)) as Hy' by set_solver.
    destruct (bx_heads _ _ _ _ _ Hy') as [->| ->].
    + eapply bx_fact; [by left|done].
    + eapply bx_fact; [right; by left|done].
  - apply d_chan. intros o Ho. inversion Ho.
Qed.

Lemma bx_Θ_swap : bx_Θ od oc qy qx = bx_Θ oc od qx qy.
Proof. unfold bx_Θ. apply map_union_comm. apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne. Qed.

(** Both extensions keep every fact of [bx_W0]. *)
Lemma bx_Wl_ext : bx_W0 ⊑ₛ bx_Wl.
Proof. split; [done|]. intros g Hg. by left. Qed.

Lemma bx_Wr_ext : bx_W0 ⊑ₛ bx_Wr.
Proof. split; [done|]. intros g Hg. by left. Qed.

(** ** The steps of the right arm *)

Definition bx_Σ : senv :=
  <[oe := (SWith SEnd SEnd, qz)]> (<[oc := (SEnd, qx)]> {[od := (SEnd, qy)]}).

Lemma cl2_step_inv a b α t' :
  tstep (cl2 a b) α t' → α = LSess (SClose a) ∧ t' = LetU EUnit (EClose (Chan b)).
Proof.
  intros Hs. unfold cl2 in Hs.
  destruct (tstep_fill_inv (FLetU (EClose (Chan b))) (EClose (Chan a)) α t' I) as (e0 & Hs0 & ->);
    [by intros ?|exact Hs|].
  assert (head_step (EClose (Chan a)) α e0) as Hh by head_only.
  inversion Hh; subst. done.
Qed.

Lemma cl2_step a b : tstep (cl2 a b) (LSess (SClose a)) (LetU EUnit (EClose (Chan b))).
Proof.
  apply (tstep_fill (FLetU (EClose (Chan b))) (EClose (Chan a))); [done|].
  apply tstep_head. constructor.
Qed.

(** cl2 d c is not ready once x̄ ≺ y: it offers d at y while it holds c
    at x and does not offer it, so readiness asks y ≺ x̄. *)
Lemma cl2_not_ready Σ :
  Σ !! od = Some (SEnd, qy) → Σ !! oc = Some (SEnd, qx) →
  ¬ ready _ bx_R(Σ ∣ ∅, cl2 od oc).
Proof.
  intros Hd Hc Hr.
  assert (stable_t (cl2 od oc)) as Hst.
  { intros α t' Hs. apply cl2_step_inv in Hs as [-> _]. eauto. }
  destruct (Hr Hst) as [_ [(os & t' & Hl)|Hb]].
  { apply cl2_step_inv in Hl as [Hl _]. discriminate. }
  assert (offered_t Σ (cl2 od oc) od) as Hoff.
  { split; [by apply elem_of_dom_2 in Hd|]. exists (SClose od), (LetU EUnit (EClose (Chan oc))).
    split; [apply cl2_step|simpl; set_solver]. }
  destruct (Hb od SEnd qy Hoff Hd) as [H1 _].
  assert (bx_R ⊢ qy ≺ qx‾) as Hlt.
  { apply (H1 oc SEnd qx Hc). intros [_ (σ & t' & Hs & Hin)].
    apply cl2_step_inv in Hs as [Hσ _]. injection Hσ as ->. simpl in Hin.
    apply elem_of_singleton in Hin. discriminate. }
  apply (w_lt_irrefl bx_R qy). eapply w_lt_trans; [exact Hlt|exact bx_R_opp].
Qed.

(** ** The thread is not in E at [bx_R] *)

Theorem bx_not_E : ¬ Erel κ_DF (onat 3) bx_R bx_Σ TUnit ∅ bx_thread.
Proof.
  intros H.
  (* the right label arrives on e *)
  assert (tstep bx_thread (LSess (SBra oe true)) (Case (Inj true (Chan oe)) (bx_arm oc od) (bx_arm od oc)))
    as Hs1.
  { apply (tstep_fill (FCase (bx_arm oc od) (bx_arm od oc)) (EBra (Chan oe))); [done|].
    apply tstep_head. constructor. }
  pose proof (Erel_step κ_DF _ _ _ _ _ _ _ _ _ H (wext_refl _) Hs1) as H1.
  destruct H1 as (S0 & x & S1 & S2 & Hl & Hu & _ & H1).
  assert (bx_Σ !! oe = Some (SWith SEnd SEnd, qz)) as Hoe by (unfold bx_Σ; by simplify_map_eq).
  rewrite Hoe in Hl. injection Hl as <- <-. simpl in Hu. injection Hu as <- <-.
  specialize (H1 ltac:(done) (onat 2) ltac:(rewrite oadd_onat; apply ole_refl)).
  set (Σ2 := <[oe := (bsel true SEnd SEnd, bra_pt qz true)]> bx_Σ) in H1.
  (* the case takes the right arm *)
  assert (tstep (Case (Inj true (Chan oe)) (bx_arm oc od) (bx_arm od oc)) LBeta
            (LetU (EClose (Chan oe)) (cl2 od oc))) as Hs2.
  { apply tstep_head. apply (t_act_case_inr (Chan oe)). done. }
  pose proof (Erel_step κ_DF _ _ _ _ _ _ _ _ _ H1 (wext_refl _) Hs2) as H2.
  destruct H2 as [_ H2]. specialize (H2 ltac:(done) (onat 1) ltac:(rewrite oadd_onat; apply ole_refl)).
  (* close w *)
  assert (tstep (LetU (EClose (Chan oe)) (cl2 od oc)) (LSess (SClose oe)) (LetU EUnit (cl2 od oc))) as Hs3.
  { apply (tstep_fill (FLetU (cl2 od oc)) (EClose (Chan oe))); [done|]. apply tstep_head. constructor. }
  pose proof (Erel_step κ_DF _ _ _ _ _ _ _ _ _ H2 (wext_refl _) Hs3) as H3.
  destruct H3 as (S3 & x3 & _ & _ & H3 & _). specialize (H3 eq_refl).
  (* let () = () *)
  assert (tstep (LetU EUnit (cl2 od oc)) LBeta (cl2 od oc)) as Hs4 by (apply tstep_head; constructor).
  pose proof (Erel_step κ_DF _ _ _ _ _ _ _ _ _ H3 (wext_refl _) Hs4) as H4.
  destruct H4 as [_ H4]. specialize (H4 ltac:(done) (onat 0) ltac:(rewrite oadd_onat; apply ole_refl)).
  (* close d while c is held *)
  apply (cl2_not_ready (delete oe Σ2)).
  - unfold Σ2, bx_Σ. by simplify_map_eq.
  - unfold Σ2, bx_Σ. by simplify_map_eq.
  - apply (Erel_ready κ_DF _ _ _ _ _ _ H4). intros Hi. exact (Hi _ _ (cl2_step od oc)).
Qed.

(** The current rules reject the thread at every static world that
    [bx_R] models, by the fundamental theorem. *)
Theorem bx_rejected W Θ :
  sworld_wf W → wmodels bx_R W → tenv_df Θ = Θ → tenv_erase Θ = bx_Σ →
  ¬ dftyped W Θ hc_empty [] (∅, None) bx_thread TUnit.
Proof.
  intros HW HR Hd He Ht. apply bx_not_E. rewrite <-He.
  exact (typed_E_df W bx_R Θ bx_thread (onat 3) HW HR bx_R_strict Hd Ht).
Qed.
