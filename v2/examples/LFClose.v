(** * Two threads closing one channel, lock free by the judgment ⊩ (stage S9)

      cl c⁺ ∥ cl c⁻,   cl o = close o

    Each thread is typed by P-Term at Some N over its end of c, and
    P-Connect cuts c at exactly dual types. The world has no constants,
    facts or families, and it is a lock-free world because every step of
    ≺ raises the offset of a point ([wfworld_bare]), and strict. [lf_soundness] then
    gives lock freedom. *)

From Stdlib Require Import Wf_nat.
From GV Require Import soup.LFTyped.

Definition W_cl : world := World ∅ (λ _, False) ∅ (λ _ _, False).

(** A world without facts and families is well formed and well founded. *)
Lemma wfworld_bare W : (∀ f, ¬ w_facts W f) → w_fams W = ∅ → world_wf W ∧ wfworld W.
Proof.
  intros Hf Hfam.
  assert (∀ x y, wstep W x y → pt_off x < pt_off y) as Hs.
  { intros x y H. destruct H as [x y H|ℓ g x y Hℓ _| x | x].
    - by destruct (Hf _ H).
    - rewrite Hfam in Hℓ. set_solver.
    - simpl. lia.
    - simpl. lia. }
  assert (∀ x y, W ⊢ x ≺ y → pt_off x < pt_off y) as Hlt.
  { induction 1 as [x y H|x z y H _ IH]; [by apply Hs|]. apply Hs in H. lia. }
  split.
  - constructor.
    + intros x y H. by destruct (Hf _ H).
    + intros ℓ x y Hℓ. rewrite Hfam in Hℓ. set_solver.
  - apply (well_founded_lt_compat _ pt_off). intros x y H. by apply Hlt.
Qed.

Lemma W_cl_bare : world_wf (W_cl ⊔ W_cl) ∧ wfworld (W_cl ⊔ W_cl).
Proof.
  apply wfworld_bare.
  - intros f [H|H]; done.
  - simpl. apply (left_id_L ∅ (∪)).
Qed.

Lemma W_cl_wfworld : wfworld (W_cl ⊔ W_cl).
Proof. exact (proj2 W_cl_bare). Qed.

Lemma W_cl_strict : strict (W_cl ⊔ W_cl).
Proof. exact (strict_wfworld _ (proj1 W_cl_bare) W_cl_wfworld). Qed.

Lemma W_cl_wf : world_wf W_cl.
Proof. constructor; simpl; [done|set_solver]. Qed.

Definition cl (o : cend) : expr := EClose (Chan o).

Lemma cl_typed N o x a m :
  typed W_cl (Some N) {[o := TE SEnd x a m]} hc_empty [] (∅, None) (cl o) TUnit
    (fadd (Some 0) (Some 1)).
Proof.
  eapply (e_close W_cl (Some N) _ _ _ _ _ SEnd); [reflexivity| |].
  - simpl. split_and!; [intros y Hy; exfalso; set_solver|done|done].
  - apply e_chan. intros ? Hin. inversion Hin.
Qed.

Lemma cl_term N o x : ptyped (Some N) W_cl {[o := (SEnd, x)]} (∅, {[+ cl o +]}) TUnit.
Proof.
  apply (p_term (Some N) W_cl _ ∅ ∅ _ TUnit (fadd (Some 0) (Some 1))).
  - constructor.
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of. rewrite map_fmap_singleton. apply cl_typed.
  - apply (strict_mono _ (W_cl ⊔ W_cl)); [apply W_cl_wf|apply wext_join_l|apply W_cl_strict].
Qed.

Theorem cl_lftyped N c (x : point) :
  ∅ ⊩^N _ (W_cl ⊔ W_cl) ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}) : TUnit.
Proof.
  set (ΣC := {[(c⁺)%cend := (SEnd, x)]} : senv).
  assert (senv_dual ΣC = {[(c⁻)%cend := (SEnd, x‾)]}) as Ed.
  { unfold senv_dual, ΣC. by rewrite map_fmap_singleton, kmap_singleton. }
  assert (chans_of ΣC = {[c]}) as Ec.
  { unfold chans_of, ΣC. by rewrite dom_singleton_L, set_map_singleton_L. }
  assert (chans_of ∅ = ∅) as E0 by (unfold chans_of; by rewrite dom_empty_L, set_map_empty).
  split; [|intros t Ht; simpl in Ht; apply gmultiset_elem_of_disj_union in Ht as [Ht|Ht];
             apply gmultiset_elem_of_singleton in Ht as ->; repeat constructor].
  pose proof (p_connect (Some N) W_cl W_cl ∅ ∅ ΣC ∅ ∅ {[+ cl (c⁺)%cend +]} {[+ cl (c⁻)%cend +]} TUnit) as H.
  rewrite Ec, E0, !(left_id_L ∅ (∪)) in H. rewrite Ed in H.
  apply H; clear H.
  - apply cl_term.
  - apply cl_term.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - intros o. unfold ΣC. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - simpl. set_solver.
  - exact (proj2 (proj2 (proj1 (strict_join_iff W_cl W_cl W_cl_wf W_cl_wf ltac:(simpl; set_solver))
      W_cl_strict))).
Qed.

Theorem cl_lock_free c :
  lock_free ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}).
Proof. exact (lf_soundness 0 _ _ TUnit W_cl_wfworld (cl_lftyped 0 c (MkPt (NConst 0) true 0))). Qed.
