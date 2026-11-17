(** * E-SpawnLam is not valid for the relation of stage S3 (stage S5)

    O-Spawn reads the spawned thunk in V at an arrow 1 ⊸^u_l 1 for some
    u and l ([o_spawn]), and V at an arrow asks l ≼ heads Θ_M of the
    ends the thunk takes along. D-SpawnLam (static/Typing.v) asks no
    lower bound of a spawned λ. So a thread that captures two ends whose
    heads have no common lower point in W types by D-SpawnLam, and its
    spawn is in E at no positive level.

    The world [w_gap] has the constants 1 and 2 and the one fact
    1 ≺ (2)‾. The thread holds a⁺ : end@1 and b⁺ : end@2 and runs
    spawn (λ_. let ∗ = _ in let ∗ = close a⁺ in close b⁺). Closing a⁺
    while it holds b⁺ asks 1 ≺ (2)‾, which W gives. The heads are (1)‾
    and (2)‾, and no point of W lies at or below both
    ([gap_no_lower]). [spawn_gap] concludes that the fundamental
    theorem of A.3 fails for the relation as defined, at every cost
    table. *)

From GV Require Export compat.SemTyped.

Definition w_gap : world :=
  World ({[1]} ∪ {[2]}) (λ g, g = FLt (pconst 1) (pconst 2)‾) ∅ (λ _ _, False).

(** ** The world *)

Definition gap_rank (x : point) : nat :=
  2 * pt_off x + (if decide (pt_name x = NConst 2) then 1 else 0).

Lemma wstep_gap_rank x y : wstep w_gap x y → gap_rank x < gap_rank y.
Proof.
  destruct 1 as [x y Hf|ℓ g x y Hℓ _|x|x].
  - simpl in Hf. injection Hf as -> ->. unfold gap_rank. simpl. lia.
  - simpl in Hℓ. set_solver.
  - unfold gap_rank, pt_shift. simpl. destruct (decide _); lia.
  - unfold gap_rank, pt_shift, pt_dual. simpl. destruct (decide _); lia.
Qed.

Lemma lt_gap_rank x y : w_gap ⊢ x ≺ y → gap_rank x < gap_rank y.
Proof.
  induction 1 as [x y H|x y z H _ IH]; [by apply wstep_gap_rank|].
  pose proof (wstep_gap_rank _ _ H). lia.
Qed.

Lemma strict_gap : strict w_gap.
Proof.
  split.
  - split.
    + intros x y Hf. simpl in Hf. injection Hf as -> ->.
      split; [exists 1|exists 2]; split; try done; set_solver.
    + intros ℓ x y Hℓ. simpl in Hℓ. set_solver.
  - intros x Hx. apply lt_gap_rank in Hx. lia.
Qed.

(** Only the fact ends at a point of offset 0. *)
Lemma wstep_gap_off0 x y : wstep w_gap x y → pt_off y = 0 → x = pconst 1 ∧ y = (pconst 2)‾.
Proof.
  destruct 1 as [x y Hf|ℓ g x y Hℓ _|x|x]; intros Hy.
  - simpl in Hf. by injection Hf as -> ->.
  - simpl in Hℓ. set_solver.
  - unfold pt_shift in Hy. simpl in Hy. lia.
  - unfold pt_shift in Hy. simpl in Hy. lia.
Qed.

Lemma lt_gap_off0 x y : w_gap ⊢ x ≺ y → pt_off y = 0 → x = pconst 1 ∧ y = (pconst 2)‾.
Proof.
  induction 1 as [x y H|x y z H _ IH]; intros Hz; [by apply wstep_gap_off0|].
  destruct (IH Hz) as [-> ->]. by destruct (wstep_gap_off0 _ _ H eq_refl) as [_ ?].
Qed.

Lemma gap_no_lower l : w_le w_gap l (pconst 1)‾ → w_le w_gap l (pconst 2)‾ → False.
Proof.
  intros [->|H1] H2.
  - destruct H2 as [H2|H2]; [done|]. destruct (lt_gap_off0 _ _ H2 eq_refl) as [? _]. done.
  - destruct (lt_gap_off0 _ _ H1 eq_refl) as [_ ?]. done.
Qed.

(** ** The thread *)

Definition gap_env : tenv :=
  <[EPos "a" := TE SEnd (pconst 1) None]> {[EPos "b" := TE SEnd (pconst 2) None]}.

Definition gap_body : expr :=
  LetU (Var 0) (LetU (EClose (Chan (EPos "a"))) (EClose (Chan (EPos "b")))).

Definition gap_thread : expr := ESpawn (Lam gap_body).

Lemma gap_typed : gap_env ; hc_empty ; [] ⊢^(∅, None) _ w_gap gap_thread : TUnit.
Proof.
  apply d_spawn_lam with (a1 := None).
  apply (d_letu _ gap_env ∅ gap_env _ [Some (TUnit, None)] [Some (TUnit, None)] [None]).
  - split; [apply map_disjoint_empty_l|by rewrite map_empty_union].
  - apply lsplit_l, lsplit_nil.
  - apply (d_var _ _ _ _ _ _ None). split; [done|]. intros [|y] σ' Hy; simpl in Hy; [by simplify_eq|done].
  - apply (d_letu _ gap_env {[EPos "a" := TE SEnd (pconst 1) None]} {[EPos "b" := TE SEnd (pconst 2) None]}
             _ [None] [None] [None]).
    + split; [|unfold gap_env; by rewrite insert_union_singleton_l]. apply map_disjoint_singleton_l, lookup_singleton_ne. done.
    + apply lsplit_none, lsplit_nil.
    + apply (d_close _ _ _ _ _ _ SEnd (pconst 1)); [done| |].
      * unfold ub_below_s. simpl. split_and!; [|done|done]. intros y Hy.
        assert (y = (pconst 2)‾) as ->.
        { assert (y ∈ tenv_heads {[EPos "b" := TE SEnd (pconst 2) None]}) as Hy' by set_solver.
          apply elem_of_tenv_heads in Hy' as (o & e & He & ->).
          apply lookup_singleton_Some in He as [_ <-]. done. }
        apply sl_w, w_lt_fact. done.
      * apply (d_chan _ _ _ _ _ _ _ None). intros o Ho. apply list_elem_of_singleton in Ho. done.
    + apply (d_close _ _ _ _ _ _ SEnd (pconst 2)); [done|unfold ub_below_s; simpl; split_and!; [set_solver|done|done]|].
      apply (d_chan _ _ _ _ _ _ _ None). intros o Ho. apply list_elem_of_singleton in Ho. done.
Qed.

(** The spawn is in E at no positive level, for every cost table. *)
Lemma gap_not_E κ n F :
  ¬ gap_thread ∈ E[κ]^w_gap _ (S n)⟦tenv_erase gap_env ⊢ TUnit⟧^F.
Proof.
  intros HE.
  assert (tstep gap_thread (LSpawn (fends (Lam gap_body)) (Lam gap_body)) EUnit) as Hst
    by (by apply tstep_head, t_act_spawn).
  pose proof (Erel_S_step κ _ _ _ _ _ _ _ _ _ HE (wext_refl _) Hst) as Hob. simpl in Hob.
  destruct Hob as (ΘM & Θr & ub & lb & Hd & HΘ & HM & HV & _).
  destruct HV as (e & _ & _ & Hlb & _).
  assert (∀ o, o ∈ dom ΘM → ΘM !! o = tenv_erase gap_env !! o) as Hin.
  { intros o Ho. apply elem_of_dom in Ho as [p Hp].
    rewrite HΘ, Hp. symmetry. by apply lookup_union_Some_l. }
  assert ((pconst 1)‾ ∈ senv_heads ΘM) as H1.
  { apply elem_of_senv_heads. exists (EPos "a"), SEnd, (pconst 1). split; [|done].
    rewrite Hin; [|rewrite HM; set_solver]. unfold tenv_erase, gap_env. rewrite lookup_fmap. by simplify_map_eq. }
  assert ((pconst 2)‾ ∈ senv_heads ΘM) as H2.
  { apply elem_of_senv_heads. exists (EPos "b"), SEnd, (pconst 2). split; [|done].
    rewrite Hin; [|rewrite HM; set_solver]. unfold tenv_erase, gap_env. rewrite lookup_fmap. by simplify_map_eq. }
  destruct lb as [l|]; simpl in Hlb.
  - apply (gap_no_lower l); by apply Hlb.
  - rewrite Hlb in H1. set_solver.
Qed.

(** The fundamental theorem of A.3 fails for D-SpawnLam. *)
Theorem spawn_gap :
  ¬ (∀ W Θ Δ F t T, strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → Θ ; Δ ⊨^F _ W t : T).
Proof.
  intros H. pose proof (H _ _ _ _ _ _ strict_gap gap_typed (λ _, ∅) ∅ 1 w_gap ∅ Var
                          (wext_refl _) (map_disjoint_empty_r _) eq_refl) as HE.
  rewrite subst_ids, map_union_empty, sf_den_points in HE. by apply (gap_not_E κ_DF 0 ∅).
Qed.

Theorem spawn_gap_live :
  ¬ (∀ W Θ Δ F t T, strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → Θ ; Δ ⊫^F _ W t : T).
Proof.
  intros H. pose proof (H _ _ _ _ _ _ strict_gap gap_typed (λ _, ∅) ∅ 1 w_gap ∅ Var
                          (wext_refl _) (map_disjoint_empty_r _) eq_refl) as HE.
  rewrite subst_ids, map_union_empty, sf_den_points in HE. by apply (gap_not_E κ_L 0 ∅).
Qed.
