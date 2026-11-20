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
    - [sb_deadlock_free]  : the closed process is deadlock free. *)

From GV Require Export examples.Tools static.FundamentalProc compat.Redex.

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
    with constants 0 and 1, no families and facts that raise the constant
    is strict, by a lexicographic order on (constant, offset). *)

Definition rk (x : point) : nat := match pt_root x with NConst a => a | _ => 0 end.

Definition Wa : world := World ({[0]} ∪ {[1]}) (λ f, f = FLt px (py‾)) ∅ (λ _ _, False).
Definition Wb : world := World ({[0]} ∪ {[1]}) (λ f, f = FLt (px‾) py) ∅ (λ _ _, False).

Lemma Wa_wf : world_wf Wa.
Proof.
  split; simpl; [|done]. intros x y H. injection H as Hx Hy. subst. split; eexists; (split; [reflexivity|set_solver]).
Qed.

Lemma Wb_wf : world_wf Wb.
Proof.
  split; simpl; [|done]. intros x y H. injection H as Hx Hy. subst. split; eexists; (split; [reflexivity|set_solver]).
Qed.

Lemma rk_shift n x : rk (pt_shift n x) = rk x.
Proof. unfold rk. by rewrite pt_root_shift. Qed.

Lemma rk_dual x : rk (x‾) = rk x.
Proof. reflexivity. Qed.

Lemma off_shift n x : pt_off (pt_shift n x) = pt_off x + n.
Proof. reflexivity. Qed.

Lemma off_dual x : pt_off (x‾) = pt_off x.
Proof. reflexivity. Qed.

Lemma strict_rank W :
  world_wf W → w_fams W = ∅ → (∀ x y, w_facts W (FLt x y) → rk x < rk y) → strict W.
Proof.
  intros Hwf Hf Hr. split; [done|]. intros x Hx.
  assert (∀ a b, wstep W a b → rk a < rk b ∨ (rk a = rk b ∧ pt_off a < pt_off b)) as Hs.
  { intros a b Hs. destruct Hs as [a b H|ℓ g a b Hℓ _|a|a].
    - left. by apply Hr.
    - rewrite Hf in Hℓ. set_solver.
    - right. rewrite rk_shift, off_shift. lia.
    - right. rewrite rk_shift, rk_dual, off_shift, off_dual. lia. }
  assert (∀ a b, W ⊢ a ≺ b → rk a < rk b ∨ (rk a = rk b ∧ pt_off a < pt_off b)) as H.
  { intros a b Hab. induction Hab as [a b H|a b c H _ IH]; [by apply Hs|].
    apply Hs in H. lia. }
  destruct (H x x Hx); lia.
Qed.

Lemma Wab_strict : strict (Wa ⊔ Wb).
Proof.
  apply strict_rank.
  - apply wjoin_wf; [apply Wa_wf|apply Wb_wf].
  - simpl. set_solver.
  - simpl. intros x y [H|H]; injection H as Hx Hy; subst; unfold rk, px, py, pt_dual; simpl; lia.
Qed.

Lemma Wa_strict : strict Wa.
Proof. apply (strict_mono _ (Wa ⊔ Wb)); [apply Wa_wf|apply wext_join_l|apply Wab_strict]. Qed.

Lemma Wb_strict : strict Wb.
Proof. apply (strict_mono _ (Wa ⊔ Wb)); [apply Wb_wf|apply wext_join_r|apply Wab_strict]. Qed.

Lemma Wa_lt : Wa ⊢ px ≺ py‾.
Proof. apply w_lt_fact. simpl. reflexivity. Qed.

Lemma Wb_lt : Wb ⊢ px‾ ≺ py.
Proof. apply w_lt_fact. simpl. reflexivity. Qed.

(** ** Static typing of close a; close b *)

Lemma tenv_heads_one' o e : tenv_heads {[o := e]} = {[(te_pt e)‾]}.
Proof. unfold tenv_heads. rewrite map_to_list_singleton. simpl. set_solver. Qed.

Lemma cl2_typed W a b xa xb :
  a ≠ b → slt W hc_empty xa (xb‾) →
  dftyped W ({[a := TE SEnd xa None]} ∪ {[b := TE SEnd xb None]}) hc_empty [] (∅, None) (cl2 a b) TUnit.
Proof.
  intros Hab Hlt. unfold cl2.
  eapply d_letu with (Θ1 := {[a := TE SEnd xa None]}) (Θ2 := {[b := TE SEnd xb None]}); [|apply lsplit_nil| |].
  - split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity].
  - eapply d_close with (S0 := SEnd) (x := xa) (a := None); [done| |].
    + cbn. split_and!; [|done|done]. intros y Hy.
      assert (y = xb‾) as -> by (rewrite tenv_heads_one' in Hy; simpl in Hy; set_solver).
      exact Hlt.
    + apply d_chan; intros o Ho; inversion Ho.
  - eapply d_close with (S0 := SEnd) (x := xb) (a := None); [done|apply ub_below_empty|].
    apply d_chan; intros o Ho; inversion Ho.
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
  Erel κ (n - c_beta κ) W Θ T F e' → Erel κ n W Θ T F e.
Proof. intros [Hs Hd] H. exact (Erel_beta κ n W Θ T F e e' Hd Hs H). Qed.

(** The ends of the thread, c at x and d at y, and the cut. *)
Definition Θa : tenv := {[oc := TE SEnd px None]} ∪ {[od := TE SEnd py None]}.
Definition ΣC : senv := {[oc := (SEnd, px)]} ∪ {[od := (SEnd, py)]}.

(** The ends of the partner, c̄ at x̄ and d̄ at ȳ. *)
Definition Θb : tenv := {[edual oc := TE SEnd (px‾) None]} ∪ {[edual od := TE SEnd (py‾) None]}.

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

(** A term typed in the DF projection is in E at the erased environment. *)
Lemma typed_E_df W Θ t n :
  strict W → tenv_df Θ = Θ → dftyped W Θ hc_empty [] (∅, None) t TUnit →
  Erel κ_DF n W (tenv_erase Θ) TUnit ∅ t.
Proof.
  intros HW Hd Ht. apply (typed_E κ_DF W Θ t TUnit n). rewrite Hd.
  exact (fundamental W Θ [] (∅, None) t TUnit HW Ht).
Qed.

Lemma arm_E n : Erel κ_DF n Wa (tenv_erase Θa) TUnit ∅ (cl2 oc od).
Proof.
  apply typed_E_df; [apply Wa_strict|apply Θa_df|].
  apply cl2_typed; [apply oc_od|]. apply sl_w. exact Wa_lt.
Qed.

(** The thread is in E: three deterministic β steps, then the live arm. *)
Theorem sb_thread_E n : Erel κ_DF n Wa (tenv_erase Θa) TUnit ∅ sb_thread.
Proof.
  unfold sb_thread, sb_flag, sb_not.
  apply (Erel_det _ _ _ _ _ _ _
    (Case (Case (Inj true EUnit) (Inj true (Var 0)) (Inj false (Var 0))) (cl2 oc od) (cl2 od oc))).
  { apply det_beta_case. apply det_beta_app. done. }
  apply (Erel_det _ _ _ _ _ _ _ (Case (Inj false EUnit) (cl2 oc od) (cl2 od oc))).
  { apply det_beta_case. apply (det_beta_inr EUnit). done. }
  apply (Erel_det _ _ _ _ _ _ _ (cl2 oc od)).
  { apply (det_beta_inl EUnit). done. }
  apply arm_E.
Qed.

(** The partner is in E, typed statically at x̄ ≺ y. *)
Lemma partner_E n : Erel κ_DF n Wb (tenv_erase Θb) TUnit ∅ sb_partner.
Proof.
  apply typed_E_df; [apply Wb_strict|apply Θb_df|].
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

Theorem sb_deadlock_free : deadlock_free sb_config.
Proof.
  apply (adequacy (Wa ⊔ Wb) TUnit sb_config Wab_strict). intros n.
  assert (Prel κ_DF n Wa (∅ ∪ ΣC) TUnit (∅, {[+ sb_thread +]})) as H1.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n Wa _ ΣC ∅ ∅ _ TUnit _ sth_a (sb_thread_E n)).
    constructor. }
  assert (Prel κ_DF n Wb (∅ ∪ senv_dual ΣC) TUnit (∅, {[+ sb_partner +]})) as H2.
  { rewrite (left_id_L ∅ (∪)). refine (sem_p_term κ_DF n Wb _ _ ∅ ∅ _ TUnit _ sth_b (partner_E n)).
    constructor. }
  pose proof (sem_p_connect κ_DF n Wa Wb ∅ ΣC ∅ (senv_dual ΣC) _ _ TUnit ltac:(constructor) H1 H2 sb_conn) as H.
  unfold pconn in H. simpl in H. rewrite chans_ΣC in H. rewrite !(left_id_L ∅ (∪)) in H.
  exact H.
Qed.

Print Assumptions sb_thread_E.
Print Assumptions sb_deadlock_free.
