(** * A thread that branches on its own flag, proved in the relation

      sb_not    = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
      sb_thread = case sb_not (inj₂ ∗) of inl _ ⇒ close c; close d
                                        | inr _ ⇒ close d; close c
      sb_partner = close c̄; close d̄

    The flag is always inj₁ ∗, so the thread closes c first and the second
    arm is dead. The thread holds c at x and d at y, the partner holds the
    other ends at x̄ and ȳ. The live arm closes c while it holds d, so it
    asks x ≺ ȳ. The dead arm asks y ≺ x̄. The partner closes c̄ while it
    holds d̄, so it asks x̄ ≺ y.

    The static system rejects the thread. E-Case types both arms under one
    Γ and one world, so the thread needs y ≺ x̄ and x ≺ ȳ, and the partner
    adds x̄ ≺ y. P-Connect joins the worlds of the two sides, and x̄ ≺ y ≺ x̄
    is a cycle, so the join is not strict (see docs/redesign/semantic-example.md).

    The semantic route does not need the dead arm. The thread is shown in E
    by hand. Three deterministic β steps reach the live arm, and the
    fundamental theorem types the live arm in a world that holds only
    x ≺ ȳ. The partner is typed statically in a world that holds only
    x̄ ≺ y. [sem_p_term] turns each side into a process, [sem_p_connect]
    composes them at the join of the two worlds, and [adequacy] applies
    because the join is strict.

    - [sb_thread_E]       : the thread is in E at every level.
    - [sb_deadlock_free]  : the closed process is deadlock free.
    - [Tbad_not_cons]     : E-Open cannot open an existential whose
                            constraint states y ≺ x̄ in Wa.
    - [sbv_thread_E], [sbv_deadlock_free] : the same for the variant
                            whose arms read their binder.
    - [sbv_rejected]      : no world and no bound type the variant. *)

From GV Require Export examples.Tools static.FundamentalProc compat.Redex.
From GV Require Import static.Inversion cost.Exact.

(** ** The program *)

Definition sb_not : expr := Lam (Case (Var 0) (Inj true (Var 0)) (Inj false (Var 0))).
Definition sb_flag : expr := App sb_not (Inj true EUnit).

(** close a; close b *)
Definition cl2 (a b : cend) : expr := LetU (EClose (Chan a)) (EClose (Chan b)).

Definition oc : cend := EPos "c".
Definition od : cend := EPos "d".

Definition sb_thread : expr := Case sb_flag (cl2 oc od) (cl2 od oc).
Definition sb_partner : expr := cl2 (edual oc) (edual od).

(** The points: c at x and d at y, both constant roots. *)
Definition px : point := MkPt (NConst 0) true 0.
Definition py : point := MkPt (NConst 1) true 0.

(** ** Worlds

    The thread's world holds x ≺ ȳ and the partner's holds x̄ ≺ y. A world
    with constants 0 and 1 and facts that raise the constant is
    well-founded, by a lexicographic order on (constant, offset). *)

Definition rk (x : point) : nat := match pt_root x with NConst a => a | _ => 0 end.

Definition Wa : sworld := SWorld ({[0]} ∪ {[1]}) (λ f, f = FLt px (py‾)).
Definition Wb : sworld := SWorld ({[0]} ∪ {[1]}) (λ f, f = FLt (px‾) py).

Lemma Wa_wf : sworld_wf Wa.
Proof.
  split; simpl. intros x y H. injection H as Hx Hy. subst. split; eexists; (split; [reflexivity|set_solver]).
Qed.

Lemma Wb_wf : sworld_wf Wb.
Proof.
  split; simpl. intros x y H. injection H as Hx Hy. subst. split; eexists; (split; [reflexivity|set_solver]).
Qed.

Lemma rk_shift n x : rk (pt_shift n x) = rk x.
Proof. unfold rk. by rewrite pt_root_shift. Qed.

Lemma rk_dual x : rk (x‾) = rk x.
Proof. reflexivity. Qed.

Lemma off_shift n x : pt_off (pt_shift n x) = pt_off x + n.
Proof. reflexivity. Qed.

Lemma off_dual x : pt_off (x‾) = pt_off x.
Proof. reflexivity. Qed.

Lemma swf_rank W : (∀ x y, sw_facts W (FLt x y) → rk x < rk y) → swf W.
Proof.
  intros Hr. apply swf_iff.
  assert (∀ a b, swstep W a b → lex3 (rk a, pt_off a, 0) (rk b, pt_off b, 0)) as Hs.
  { intros a b Hs. destruct Hs as [a b H|a|a]; cbv beta iota delta [lex3].
    - left. by apply Hr.
    - right. split; [by rewrite rk_shift|left; rewrite off_shift; lia].
    - right. split; [by rewrite rk_shift, rk_dual|left; rewrite off_shift, off_dual; lia]. }
  assert (∀ a b, W ⊢ₛ a ≺ b → lex3 (rk a, pt_off a, 0) (rk b, pt_off b, 0)) as H.
  { intros a b Hab. induction Hab as [a b H|a b c H _ IH]; [by apply Hs|].
    apply Hs in H. by transitivity (rk b, pt_off b, 0). }
  assert (∀ m x, (rk x, pt_off x, 0) = m → Acc (sw_lt W) x) as Hacc.
  { intros m. induction (lex3_wf m) as [m _ IH]. intros x <-. constructor.
    intros y Hy. eapply IH; [apply H, Hy|done]. }
  intros x. by apply (Hacc (rk x, pt_off x, 0) x).
Qed.

Lemma Wab_wf : swf (Wa ⊔ Wb).
Proof.
  apply swf_rank. simpl. intros x y [H|H]; injection H as Hx Hy; subst; unfold rk, px, py, pt_dual; simpl; lia.
Qed.

Lemma Wab_ok : sworld_wf (Wa ⊔ Wb) ∧ swf (Wa ⊔ Wb).
Proof. split; [apply swjoin_wf; [apply Wa_wf|apply Wb_wf]|apply Wab_wf]. Qed.

Lemma Wa_lt : Wa ⊢ₛ px ≺ py‾.
Proof. apply sw_lt_fact. simpl. reflexivity. Qed.

Lemma Wb_lt : Wb ⊢ₛ px‾ ≺ py.
Proof. apply sw_lt_fact. simpl. reflexivity. Qed.

(** ** Static typing of close a; close b *)

Lemma tenv_heads_one' o e : tenv_heads {[o := e]} = {[(te_pt e)‾]}.
Proof. unfold tenv_heads. rewrite map_to_list_singleton. simpl. set_solver. Qed.

Lemma cl2_typed W a b xa xb :
  a ≠ b → slt W hc_empty xa (xb‾) →
  dftyped W ({[a := TE SEnd xa None None]} ∪ {[b := TE SEnd xb None None]}) hc_empty [] (∅, None) (cl2 a b) TUnit.
Proof.
  intros Hab Hlt. unfold cl2.
  eapply d_letu with (Θ1 := {[a := TE SEnd xa None None]}) (Θ2 := {[b := TE SEnd xb None None]}); [|apply lsplit_nil| |].
  - split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity].
  - eapply d_close with (S0 := SEnd) (x := xa) (a := None); [done| |].
    + cbn. split_and!; [|done|done]. intros y Hy.
      assert (y = xb‾) as -> by (rewrite tenv_heads_one' in Hy; simpl in Hy; set_solver).
      exact Hlt.
    + apply d_chan; intros o Ho; inversion Ho.
  - eapply d_close with (S0 := SEnd) (x := xb) (a := None); [done|apply ub_below_empty|].
    apply d_chan; intros o Ho; inversion Ho.
Unshelve. all: try exact None.
Qed.

(** ** The thread in E

    A term that takes a deterministic β step to a term in E is in E
    ([Erel_beta]). *)

Definition det_beta (e e' : expr) : Prop :=
  tstep e LBeta e' ∧ ∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e'.

Lemma det_beta_case e e' a b : det_beta e e' → det_beta (Case e a b) (Case e' a b).
Proof.
  intros [Hs Hd]. split; [by apply (tstep_fill (FCase a b))|].
  assert (¬ is_val e) as Hv by (intros Hv; exact (val_no_tstep _ _ _ Hs Hv)).
  intros α e'' H. destruct (tstep_fill_inv (FCase a b) e α e'' I Hv H) as (e0 & Hs0 & ->).
  destruct (Hd _ _ Hs0) as [-> ->]. done.
Qed.

Lemma det_beta_app v e : is_val v → det_beta (App (Lam e) v) (subst1 v e).
Proof.
  intros Hv. split; [by apply tstep_head; constructor|].
  intros α e'' H. assert (head_step (App (Lam e) v) α e'') as Hh by head_only.
  by inversion Hh; subst.
Qed.

Lemma det_beta_inl v a b : is_val v → det_beta (Case (Inj false v) a b) (subst1 v a).
Proof.
  intros Hv. split; [by apply tstep_head; constructor|].
  intros α e'' H. assert (head_step (Case (Inj false v) a b) α e'') as Hh by head_only.
  by inversion Hh; subst.
Qed.

Lemma det_beta_inr v a b : is_val v → det_beta (Case (Inj true v) a b) (subst1 v b).
Proof.
  intros Hv. split; [by apply tstep_head; constructor|].
  intros α e'' H. assert (head_step (Case (Inj true v) a b) α e'') as Hh by head_only.
  by inversion Hh; subst.
Qed.

Lemma Erel_det κ n W Θ T F e e' : det_beta e e' →
  (∀ j, ole (oadd j (c_beta κ)) n → Erel κ j W Θ T F e') → Erel κ n W Θ T F e.
Proof. intros [Hs Hd] H. exact (Erel_beta κ n W Θ T F e e' Hd Hs H). Qed.

(** The ends of the thread, c at x and d at y, and the cut. *)
Definition Θa : tenv := {[oc := TE SEnd px None None]} ∪ {[od := TE SEnd py None None]}.
Definition ΣC : senv := {[oc := (SEnd, px)]} ∪ {[od := (SEnd, py)]}.

(** The ends of the partner, c̄ at x̄ and d̄ at ȳ. *)
Definition Θb : tenv := {[edual oc := TE SEnd (px‾) None None]} ∪ {[edual od := TE SEnd (py‾) None None]}.

Lemma oc_od : oc ≠ od.
Proof. unfold oc, od. congruence. Qed.

Lemma Θa_df : tenv_df Θa = Θa.
Proof. unfold tenv_df, Θa. rewrite map_fmap_union, !map_fmap_singleton. reflexivity. Qed.

Lemma Θb_df : tenv_df Θb = Θb.
Proof. unfold tenv_df, Θb. rewrite map_fmap_union, !map_fmap_singleton. reflexivity. Qed.

Lemma erase_Θa : tenv_erase Θa = ΣC.
Proof. unfold tenv_erase, Θa, ΣC. rewrite map_fmap_union, !map_fmap_singleton. reflexivity. Qed.

Lemma erase_Θb : tenv_erase Θb = senv_dual ΣC.
Proof.
  unfold tenv_erase, Θb, senv_dual, ΣC.
  rewrite !map_fmap_union, kmap_union, !map_fmap_singleton, !kmap_singleton.
  all: first [reflexivity|apply _].
Qed.

(** A term typed in the DF projection is in E at the erased environment,
    in every ranked world that models its static world. *)
Lemma typed_E_df W R Θ t n :
  sworld_wf W → wmodels R W → tenv_df Θ = Θ → dftyped W Θ hc_empty [] (∅, None) t TUnit →
  Erel κ_DF n R (tenv_erase Θ) TUnit ∅ t.
Proof.
  intros HW HR Hd Ht. apply (typed_E κ_DF R Θ t TUnit n). rewrite Hd.
  exact (fundamental W R Θ [] (∅, None) t TUnit HW Ht HR).
Qed.

(** The semantic side reads one ranked world R that models both static
    worlds. *)
Section sem.
  Context (R : world) (HR : wmodels R (Wa ⊔ Wb)).
  Local Lemma HRa : wmodels R Wa.
  Proof. by eapply wmodels_ext; [apply swext_join_l|]. Qed.
  Local Lemma HRb : wmodels R Wb.
  Proof. by eapply wmodels_ext; [apply swext_join_r|]. Qed.

Lemma arm_E n : Erel κ_DF n R (tenv_erase Θa) TUnit ∅ (cl2 oc od).
Proof.
  apply (typed_E_df Wa); [apply Wa_wf|apply HRa|apply Θa_df|].
  apply cl2_typed; [apply oc_od|]. apply sl_w. exact Wa_lt.
Qed.

(** The thread is in E: three deterministic β steps, then the live arm. *)
Theorem sb_thread_E n : Erel κ_DF n R (tenv_erase Θa) TUnit ∅ sb_thread.
Proof.
  unfold sb_thread, sb_flag, sb_not.
  apply (Erel_det _ _ _ _ _ _ _
    (Case (Case (Inj true EUnit) (Inj true (Var 0)) (Inj false (Var 0))) (cl2 oc od) (cl2 od oc))).
  { apply det_beta_case. apply det_beta_app. done. }
  intros j1 _. apply (Erel_det _ _ _ _ _ _ _ (Case (Inj false EUnit) (cl2 oc od) (cl2 od oc))).
  { apply det_beta_case. apply (det_beta_inr EUnit). done. }
  intros j2 _. apply (Erel_det _ _ _ _ _ _ _ (cl2 oc od)).
  { apply (det_beta_inl EUnit). done. }
  intros j3 _. apply arm_E.
Qed.

(** The partner is in E, typed statically at x̄ ≺ y. *)
Lemma partner_E n : Erel κ_DF n R (tenv_erase Θb) TUnit ∅ sb_partner.
Proof.
  apply (typed_E_df Wb); [apply Wb_wf|apply HRb|apply Θb_df|].
  apply cl2_typed; [unfold oc, od; simpl; congruence|]. apply sl_w. exact Wb_lt.
Qed.

(** ** The closed process *)

Lemma chans_of_empty' : chans_of ∅ = ∅.
Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

Lemma dom_ΣC : dom ΣC = ({[oc]} ∪ {[od]}).
Proof. unfold ΣC. rewrite dom_union_L, !dom_singleton_L. set_solver. Qed.

Lemma chans_ΣC : chans_of ΣC = ({["c"]} ∪ {["d"]}).
Proof. unfold chans_of. rewrite dom_ΣC, set_map_union_L, !set_map_singleton_L. reflexivity. Qed.

Lemma pfree_ΣC : pfree ΣC.
Proof.
  intros o Ho Hn. rewrite dom_ΣC in Ho, Hn. set_unfold in Ho; set_unfold in Hn.
  unfold oc, od in *. destruct Ho as [Ho|Ho]; subst; simpl in Hn; destruct Hn as [Hn|Hn]; discriminate.
Qed.

Lemma pfree_dual Σ : pfree Σ → pfree (senv_dual Σ).
Proof.
  intros Hf o Ho Hn. pose proof (senv_dual_cut Σ) as [Hd _].
  apply Hd in Ho. apply Hd in Hn. rewrite edual_edual in Hn. exact (Hf _ Hn Ho).
Qed.

Lemma sth_a : sth (tenv_erase Θa) ΣC ∅ ∅.
Proof.
  constructor.
  - rewrite erase_Θa. by rewrite (right_id_L ∅ (∪)).
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_ΣC.
  - intros c Hc. set_solver.
Qed.

Lemma sth_b : sth (tenv_erase Θb) (senv_dual ΣC) ∅ ∅.
Proof.
  constructor.
  - rewrite erase_Θb. by rewrite (right_id_L ∅ (∪)).
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_dual, pfree_ΣC.
  - intros c Hc. set_solver.
Qed.

Lemma sb_conn : conn ∅ ΣC (∅ : gset chan) ∅ (senv_dual ΣC) (∅ : gset chan).
Proof.
  constructor.
  all: first [apply map_disjoint_empty_l|apply pfree_empty|apply senv_dual_cut|apply pfree_ΣC
             |(rewrite ?chans_of_empty'; set_solver)].
Qed.

(** The closed process: the thread and the partner over the cut {c, d}. *)
Definition sb_config : proc := (({["c"]} ∪ {["d"]}), {[+ sb_thread +]} ⊎ {[+ sb_partner +]}).

Lemma sb_deadlock_free_R : deadlock_free sb_config.
Proof.
  apply (adequacy R TUnit sb_config). intros n.
  assert (Prel κ_DF n R (∅ ∪ ΣC) TUnit (∅, {[+ sb_thread +]})) as H1.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n R _ ΣC ∅ ∅ _ TUnit _ sth_a (sb_thread_E n)).
    constructor. }
  assert (Prel κ_DF n R (∅ ∪ senv_dual ΣC) TUnit (∅, {[+ sb_partner +]})) as H2.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n R _ _ ∅ ∅ _ TUnit _ sth_b (partner_E n)).
    constructor. }
  pose proof (sem_p_connect κ_DF n R ∅ ΣC ∅ (senv_dual ΣC) _ _ TUnit ltac:(constructor) H1 H2 sb_conn) as H.
  unfold pconn in H. simpl in H. rewrite chans_ΣC in H. rewrite !(left_id_L ∅ (∪)) in H.
  exact H.
Qed.

(** ** The opening of an uninhabited existential is not conservative

    A derivation may give the binder of the dead arm an existential type
    whose constraint states y ≺ x̄ over the outer points. No value needs
    to inhabit it. E-Open asks [cons_open], and opening this existential
    in Wa would derive y ≺ x̄ between the outer points, which Wa does not
    derive. *)

Definition Cbad : bcs := BCs (py :: px‾ :: []) (λ f, f = FLt (pvar 0) (pvar 1)).
Definition Tbad : ty := TEx LNone 0 Cbad TUnit.

Lemma slt_empty_w W x y : slt W hc_empty x y → W ⊢ₛ x ≺ y.
Proof.
  unfold slt. induction 1 as [x y H|x y (C & xs & Hin & _)|x y z _ IH1 _ IH2].
  - done.
  - by apply not_elem_of_nil in Hin.
  - by eapply sw_lt_trans.
Qed.

(** In Wa the constant never decreases along ≺. *)
Lemma Wa_rk_step x y : swstep Wa x y → rk x ≤ rk y.
Proof.
  destruct 1 as [x y Hf|x|x].
  - simpl in Hf. injection Hf as -> ->. unfold rk, px, py, pt_dual. simpl. lia.
  - unfold rk. by rewrite pt_root_shift.
  - unfold rk. by rewrite pt_root_shift, pt_root_dual.
Qed.

Lemma Wa_rk x y : Wa ⊢ₛ x ≺ y → rk x ≤ rk y.
Proof.
  induction 1 as [x y Hs|x y z Hs _ IH]; [by apply Wa_rk_step|].
  apply Wa_rk_step in Hs. lia.
Qed.

Lemma Wa_not_yx : ¬ Wa ⊢ₛ py ≺ px‾.
Proof. intros H. apply Wa_rk in H. unfold rk, py, px, pt_dual in H. simpl in H. lia. Qed.

Lemma Tbad_not_cons : ¬ cons_open Wa hc_empty 0 Cbad.
Proof.
  intros Hc. apply Wa_not_yx, slt_empty_w, Hc.
  rewrite !pt_inst_novar by (intros ?; unfold px, py, pt_dual, pt_root; simpl; congruence).
  apply fl_h. exists (bcs_inst (pshift 0) Cbad), (ids 0). split; [by left|].
  exists (FLt py (px‾)). split; [|reflexivity].
  exists (FLt (pvar 0) (pvar 1)). split_and!; [reflexivity| |reflexivity].
  split; apply pn_vb_root; eexists; (split; [reflexivity|simpl; lia]).
Qed.

(** ** The variant whose arms read their binder

      sbv_thread = case sb_not (inj₂ ∗) of inl w ⇒ let ∗ = w in close c; close d
                                         | inr w ⇒ let ∗ = w in close d; close c

    It is semantically typed as [sb_thread] is, and statically rejected
    in every world and at every bound ([sbv_rejected]). *)

Definition sbv_thread : expr :=
  Case sb_flag (LetU (Var 0) (cl2 oc od)) (LetU (Var 0) (cl2 od oc)).
Definition sbv_config : proc := (({["c"]} ∪ {["d"]}), {[+ sbv_thread +]} ⊎ {[+ sb_partner +]}).

Lemma arm_v_E n : Erel κ_DF n R (tenv_erase Θa) TUnit ∅ (LetU EUnit (cl2 oc od)).
Proof.
  apply (typed_E_df Wa); [apply Wa_wf|apply HRa|apply Θa_df|].
  eapply d_letu with (Θ1 := ∅) (Θ2 := Θa).
  - split; [apply map_disjoint_empty_l|by rewrite map_empty_union].
  - apply lsplit_nil.
  - apply d_unit. intros ? Hin. by apply not_elem_of_nil in Hin.
  - apply cl2_typed; [apply oc_od|]. apply sl_w. exact Wa_lt.
Unshelve. all: try exact None.
Qed.

Theorem sbv_thread_E n : Erel κ_DF n R (tenv_erase Θa) TUnit ∅ sbv_thread.
Proof.
  unfold sbv_thread, sb_flag, sb_not.
  apply (Erel_det _ _ _ _ _ _ _
    (Case (Case (Inj true EUnit) (Inj true (Var 0)) (Inj false (Var 0)))
      (LetU (Var 0) (cl2 oc od)) (LetU (Var 0) (cl2 od oc)))).
  { apply det_beta_case. apply det_beta_app. done. }
  intros j1 _. apply (Erel_det _ _ _ _ _ _ _ (Case (Inj false EUnit) (LetU (Var 0) (cl2 oc od)) (LetU (Var 0) (cl2 od oc)))).
  { apply det_beta_case. apply (det_beta_inr EUnit). done. }
  intros j2 _. apply (Erel_det _ _ _ _ _ _ _ (LetU EUnit (cl2 oc od))).
  { apply (det_beta_inl EUnit). done. }
  intros j3 _. apply arm_v_E.
Qed.

Lemma sbv_deadlock_free_R : deadlock_free sbv_config.
Proof.
  apply (adequacy R TUnit sbv_config). intros n.
  assert (Prel κ_DF n R (∅ ∪ ΣC) TUnit (∅, {[+ sbv_thread +]})) as H1.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n R _ ΣC ∅ ∅ _ TUnit _ sth_a (sbv_thread_E n)).
    constructor. }
  assert (Prel κ_DF n R (∅ ∪ senv_dual ΣC) TUnit (∅, {[+ sb_partner +]})) as H2.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n R _ _ ∅ ∅ _ TUnit _ sth_b (partner_E n)).
    constructor. }
  pose proof (sem_p_connect κ_DF n R ∅ ΣC ∅ (senv_dual ΣC) _ _ TUnit ltac:(constructor) H1 H2 sb_conn) as H.
  unfold pconn in H. simpl in H. rewrite chans_ΣC in H. rewrite !(left_id_L ∅ (∪)) in H.
  exact H.
Qed.
End sem.

Theorem sb_deadlock_free : deadlock_free sb_config.
Proof. destruct (wmodels_exists _ (proj1 Wab_ok) (proj2 Wab_ok)) as [R HR]. exact (sb_deadlock_free_R R HR). Qed.

Theorem sbv_deadlock_free : deadlock_free sbv_config.
Proof. destruct (wmodels_exists _ (proj1 Wab_ok) (proj2 Wab_ok)) as [R HR]. exact (sbv_deadlock_free_R R HR). Qed.

(** ** The static rejection of the variant

    [cl2_needs]: close a; close b asks a ≺ b̄ in the context it is typed
    in, through any openings, by [opened_cons]. The dead arm of the
    variant asks y ≺ x̄ at Γ = ∅, so its world derives it. The partner's
    world derives x̄ ≺ y, and the join of the two is not strict. *)

Lemma te_pt_pinst σ e : te_pt (tentry_pinst σ e) = pt_inst σ (te_pt e).
Proof. done. Qed.

Lemma thage_pt c Θ Θ' o e : thage c Θ Θ' → Θ !! o = Some e → ∃ e', Θ' !! o = Some e' ∧ te_pt e' = te_pt e.
Proof.
  intros H Ho. specialize (H o). rewrite Ho in H.
  destruct (Θ' !! o) as [e'|]; [|done]. exists e'. split; [done|]. naive_solver.
Qed.

Lemma tsplit_lookup_l Θ Θ1 Θ2 o e : tsplit Θ Θ1 Θ2 → o ∉ dom Θ2 → Θ !! o = Some e → Θ1 !! o = Some e.
Proof.
  intros [Hd ->] Ho H. apply not_elem_of_dom in Ho. apply lookup_union_Some in H as [H|H]; [done| |done].
  congruence.
Qed.

Lemma tsplit_lookup_r Θ Θ1 Θ2 o e : tsplit Θ Θ1 Θ2 → o ∉ dom Θ1 → Θ !! o = Some e → Θ2 !! o = Some e.
Proof.
  intros [Hd ->] Ho H. apply not_elem_of_dom in Ho. apply lookup_union_Some in H as [H|H]; [congruence|done|done].
Qed.

Lemma sf_unionb_fst F X b : (sf_unionb F X b).1 = F.1 ∪ X.
Proof. by destruct b. Qed.

Lemma cl2_needs W N Θ Γ Δ F a b T c ea eb :
  a ≠ b → typed W N Θ Γ Δ F (cl2 a b) T c →
  Θ !! a = Some ea → Θ !! b = Some eb → slt W Γ (te_pt ea) (te_pt eb)‾.
Proof.
  intros Hab H Ha Hb. unfold cl2 in H.
  apply inv_letu in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T' & c1 & c2
    & Ho & Hs & _ & H1 & Hage & _ & H2).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H1) as [Hd1 _].
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H2) as [Hd2 _].
  rewrite (thage_dom _ _ _ Hage) in Hd2. simpl in Hd1, Hd2.
  assert (Θ1 !! a = Some (tentry_pinst σ ea)) as Ha1.
  { eapply tsplit_lookup_l; [done| |by apply Hσl]. rewrite <-Hd2. set_solver. }
  assert (Θ2 !! b = Some (tentry_pinst σ eb)) as Hb2.
  { eapply tsplit_lookup_r; [done| |by apply Hσl]. rewrite <-Hd1. set_solver. }
  apply inv_close in H1 as (Θ'' & Γ'' & Δ'' & F'' & S0 & x & a0 & mS & c0 & Ho2 & _ & Hub & Hch).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho2) as (σ2 & Hl2 & Hf2 & Hs2).
  destruct (inv_chan _ _ _ _ _ _ _ _ _ Hch _ _ _ _ eq_refl) as (e & He & Hx).
  rewrite (Hl2 _ _ Ha1) in He. injection He as <-.
  destruct Hub as [Hub _].
  assert (pt_inst σ2 (te_pt (tentry_pinst σ eb))‾ ∈ F''.1) as Hy.
  { apply Hf2. rewrite sf_unionb_fst. apply elem_of_union_r, elem_of_union_l.
    apply elem_of_tenv_heads. eauto. }
  apply Hub in Hy. rewrite <-Hx, !te_pt_pinst in Hy.
  apply Hσs. rewrite pt_inst_dual. apply Hs2. first [exact Hy | (rewrite pt_inst_dual; exact Hy) | (rewrite <-pt_inst_dual; exact Hy) | (rewrite pt_inst_dual in Hy; exact Hy) | (rewrite <-pt_inst_dual in Hy; exact Hy)].
Qed.

Lemma letu_cl2_needs W N Θ Γ Δ F a b T c ea eb :
  a ≠ b → typed W N Θ Γ Δ F (LetU (Var 0) (cl2 a b)) T c →
  Θ !! a = Some ea → Θ !! b = Some eb → slt W Γ (te_pt ea) (te_pt eb)‾.
Proof.
  intros Hab H Ha Hb.
  apply inv_letu in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T' & c1 & c2
    & Ho & Hs & _ & H1 & Hage & _ & H2).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H1) as [Hd1 _]. simpl in Hd1.
  assert (∀ o, o ∉ dom Θ1) as Hn1 by (intros o; rewrite <-Hd1; set_solver).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 a) (Hσl _ _ Ha)))
    as (ea' & Ha' & Hpa).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 b) (Hσl _ _ Hb)))
    as (eb' & Hb' & Hpb).
  pose proof (cl2_needs _ _ _ _ _ _ _ _ _ _ _ _ Hab H2 Ha' Hb') as H.
  rewrite Hpa, Hpb, !te_pt_pinst, <-pt_inst_dual in H. by apply Hσs.
Qed.

(** The dead arm: the thread asks y ≺ x̄. *)
Lemma sbv_thread_needs W N Θ Γ Δ F T c ec ed :
  typed W N Θ Γ Δ F sbv_thread T c →
  Θ !! oc = Some ec → Θ !! od = Some ed → slt W Γ (te_pt ed) (te_pt ec)‾.
Proof.
  intros H Hc Hd. unfold sbv_thread in H.
  apply inv_case in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c0 & c1 & c2
    & Ho & Hs & _ & H0 & Hage & _ & _ & H2).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H0) as [Hd0 _]. unfold sb_flag, sb_not in Hd0. simpl in Hd0.
  assert (∀ o, o ∉ dom Θ1) as Hn1 by (intros o; rewrite <-Hd0; set_solver).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 oc) (Hσl _ _ Hc)))
    as (ec' & Hc' & Hpc).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 od) (Hσl _ _ Hd)))
    as (ed' & Hd' & Hpd).
  pose proof (letu_cl2_needs _ _ _ _ _ _ _ _ _ _ _ _ (not_eq_sym oc_od) H2 Hd' Hc') as H.
  rewrite Hpc, Hpd, !te_pt_pinst, <-pt_inst_dual in H. by apply Hσs.
Qed.

(** The ends of one side of P-Connect. An end the thread mentions without
    its partner is not restricted, so it sits in the interface, at the
    same point in the thread's Θ. *)
Lemma side_lookup N W Σ C0 u T :
  ptyped N W Σ (C0, {[+ u +]}) T →
  ∃ Θ c, typed W N Θ hc_empty [] (∅, None) u T c ∧
    ∀ o, o ∈ fends u → edual o ∉ fends u →
      ∃ S x e, Σ !! o = Some (S, x) ∧ Θ !! o = Some e ∧ te_pt e = x.
Proof.
  intros H. apply ptyped_one in H as (ΘB & c & _ & HB & _ & _ & HBs & Ht & _).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ Ht) as [Hd _].
  exists (tenv_of (fhalf N) Σ ∪ ΘB), c. split; [done|]. intros o Ho Hn.
  destruct (Σ !! o) as [[S x]|] eqn:HΣ.
  - exists S, x, (TE S x (fhalf N) (fhalf N)). split_and!; [done| |done].
    apply lookup_union_Some_l. unfold tenv_of. by rewrite lookup_fmap, HΣ.
  - exfalso. apply Hn. rewrite Hd, dom_union_L. apply elem_of_union_r.
    assert (o ∈ dom ΘB) as HoB.
    { rewrite Hd, dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho]; [|done].
      unfold tenv_of in Ho. rewrite dom_fmap_L in Ho. by apply not_elem_of_dom in HΣ. }
    apply HB in HoB. destruct (HBs _ HoB) as (S & x & m & m' & _ & H1 & H2).
    destruct o; simpl; apply elem_of_dom; eauto.
Qed.

Lemma sdual_lookup (Σ : senv) o S (x : point) : Σ !! o = Some (S, x) → senv_dual Σ !! edual o = Some (dual S, x‾).
Proof.
  intros H. unfold senv_dual. rewrite lookup_kmap; [by rewrite lookup_fmap, H|].
  intros o1 o2 E. by rewrite <-(edual_edual o1), E, edual_edual.
Qed.

Lemma ocd_dual_ne : edual oc ≠ edual od.
Proof. intros E. apply oc_od. apply (f_equal edual) in E. by rewrite !edual_edual in E. Qed.

Lemma sbv_partner_ne : sbv_thread ≠ sb_partner.
Proof. discriminate. Qed.

Ltac fends_tac := unfold sbv_thread, sb_partner, sb_flag, sb_not, cl2, oc, od; simpl; set_unfold; intuition congruence.

(** No world and no bound type the closed process of the variant. *)
Theorem sbv_rejected N W : ¬ ptyped N W ∅ sbv_config TUnit.
Proof.
  intros H. pose proof (ptyped_wf _ _ _ _ _ H) as [_ HWf].
  pose proof (λ x, swf_irrefl _ x HWf) as Hirr.
  apply ptyped_two in H as (W1 & W2 & Σ1 & Σ2 & ΣC & C1 & C2 & u1 & u2 & -> & HΣ & _ & Hu & H1 & H2 & _).
  symmetry in HΣ. pose proof (map_positive_l _ _ HΣ) as ->. rewrite (left_id_L ∅ (∪)) in HΣ. subst Σ2.
  rewrite !(left_id_L ∅ (∪)) in H1, H2.
  assert ((u1 = sbv_thread ∧ u2 = sb_partner) ∨ (u1 = sb_partner ∧ u2 = sbv_thread)) as Hcase.
  { pose proof sbv_partner_ne as Hne.
    assert (u1 ∈ ({[+ u1 +]} ⊎ {[+ u2 +]} : gmultiset expr)) as Hu1 by multiset_solver.
    assert (u2 ∈ ({[+ u1 +]} ⊎ {[+ u2 +]} : gmultiset expr)) as Hu2 by multiset_solver.
    rewrite Hu in Hu1, Hu2. apply gmultiset_elem_of_disj_union in Hu1, Hu2.
    rewrite !gmultiset_elem_of_singleton in Hu1, Hu2.
    destruct Hu1 as [->| ->], Hu2 as [->| ->]; auto; exfalso.
    - assert (sb_partner ∈ ({[+ sbv_thread +]} ⊎ {[+ sbv_thread +]} : gmultiset expr)) as Hp
        by (rewrite Hu; multiset_solver).
      apply gmultiset_elem_of_disj_union in Hp. rewrite !gmultiset_elem_of_singleton in Hp.
      destruct Hp as [Hp|Hp]; by apply Hne.
    - assert (sbv_thread ∈ ({[+ sb_partner +]} ⊎ {[+ sb_partner +]} : gmultiset expr)) as Hp
        by (rewrite Hu; multiset_solver).
      apply gmultiset_elem_of_disj_union in Hp. rewrite !gmultiset_elem_of_singleton in Hp.
      destruct Hp as [Hp|Hp]; by apply Hne. }
  destruct Hcase as [[-> ->]|[-> ->]].
  - destruct (side_lookup _ _ _ _ _ _ H1) as (Θt & ct & Ht & Hlt).
    destruct (side_lookup _ _ _ _ _ _ H2) as (Θp & cp & Hp & Hlp).
    destruct (Hlt oc) as (Sc & x & ec & Hc & Hec & <-); [fends_tac|fends_tac|].
    destruct (Hlt od) as (Sd & y & ed & Hd & Hed & <-); [fends_tac|fends_tac|].
    destruct (Hlp (edual oc)) as (Sc' & x' & ec' & Hc' & Hec' & <-); [fends_tac|fends_tac|].
    destruct (Hlp (edual od)) as (Sd' & y' & ed' & Hd' & Hed' & <-); [fends_tac|fends_tac|].
    rewrite (sdual_lookup _ _ _ _ Hc) in Hc'. rewrite (sdual_lookup _ _ _ _ Hd) in Hd'.
    injection Hc' as _ Hx'. injection Hd' as _ Hy'.
    pose proof (slt_empty_w _ _ _ (sbv_thread_needs _ _ _ _ _ _ _ _ _ _ Ht Hec Hed)) as Ha.
    pose proof (slt_empty_w _ _ _ (cl2_needs _ _ _ _ _ _ _ _ _ _ _ _
      ocd_dual_ne Hp Hec' Hed')) as Hb.
    rewrite <-Hx', <-Hy', pt_dual_dual in Hb.
    apply (Hirr (te_pt ed)). eapply sw_lt_trans; [eapply sw_lt_mono; [apply swext_join_l|exact Ha]|].
    eapply sw_lt_mono; [apply swext_join_r|exact Hb].
  - destruct (side_lookup _ _ _ _ _ _ H2) as (Θt & ct & Ht & Hlt).
    destruct (side_lookup _ _ _ _ _ _ H1) as (Θp & cp & Hp & Hlp).
    destruct (Hlt oc) as (Sc & x & ec & Hc & Hec & <-); [fends_tac|fends_tac|].
    destruct (Hlt od) as (Sd & y & ed & Hd & Hed & <-); [fends_tac|fends_tac|].
    destruct (Hlp (edual oc)) as (Sc' & p & ec' & Hc' & Hec' & <-); [fends_tac|fends_tac|].
    destruct (Hlp (edual od)) as (Sd' & q & ed' & Hd' & Hed' & <-); [fends_tac|fends_tac|].
    pose proof (sdual_lookup _ _ _ _ Hc') as Hc2. pose proof (sdual_lookup _ _ _ _ Hd') as Hd2.
    rewrite edual_edual in Hc2, Hd2. rewrite Hc2 in Hc. rewrite Hd2 in Hd.
    injection Hc as _ Hx. injection Hd as _ Hy.
    pose proof (slt_empty_w _ _ _ (sbv_thread_needs _ _ _ _ _ _ _ _ _ _ Ht Hec Hed)) as Ha.
    pose proof (slt_empty_w _ _ _ (cl2_needs _ _ _ _ _ _ _ _ _ _ _ _
      ocd_dual_ne Hp Hec' Hed')) as Hb.
    rewrite <-Hx, <-Hy, pt_dual_dual in Ha.
    apply (Hirr (te_pt ec')). eapply sw_lt_trans; [eapply sw_lt_mono; [apply swext_join_l|exact Hb]|].
    eapply sw_lt_mono; [apply swext_join_r|exact Ha].
Qed.

Print Assumptions sb_thread_E.
Print Assumptions sb_deadlock_free.
Print Assumptions sbv_thread_E.
Print Assumptions sbv_deadlock_free.
Print Assumptions Tbad_not_cons.
Print Assumptions sbv_rejected.
