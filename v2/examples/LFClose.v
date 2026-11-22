(** * Two threads closing one channel, lock free by the judgment ⊩ (stage S9)

      cl c⁺ ∥ cl c⁻,   cl o = close o

    Each thread is typed by P-Term at Some N over its end of c, and
    P-Connect cuts c at exactly dual types. The world has no constants
    and no facts, so it is well-founded ([swf_bare]). [lf_soundness] then
    gives lock freedom. *)

From Stdlib Require Import Wf_nat.
From GV Require Import lockfree.FairRun.
From GV Require Import soup.LFTyped.

Definition W_cl : sworld := sw_empty.

Lemma W_cl_join : sworld_wf (W_cl ⊔ W_cl) ∧ swf (W_cl ⊔ W_cl).
Proof.
  split; [apply swjoin_wf; apply sw_empty_ok|]. apply swf_bare. intros g [H|H]; done.
Qed.

Definition cl (o : cend) : expr := EClose (Chan o).

Lemma cl_typed N o x a m :
  fle a m →
  typed W_cl (Some N) {[o := TE SEnd x a m]} hc_empty [] (∅, None) (cl o) TUnit
    (fadd (Some 0) (Some 1)).
Proof.
  intros Ham. eapply (e_close W_cl (Some N) _ _ _ _ _ SEnd); [reflexivity| |].
  - simpl. split_and!; [intros y Hy; exfalso; set_solver|done|done].
  - apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
Qed.

Lemma cl_term N o x : fptyped (Some N) W_cl {[o := (SEnd, x)]} (∅, {[+ cl o +]}) TUnit.
Proof.
  apply (fp_term (Some N) W_cl _ ∅ ∅ _ TUnit (fadd (Some 0) (Some 1))).
  - constructor.
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o' e' He. apply lookup_singleton_Some in He as [_ <-]. done.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of. rewrite map_fmap_singleton. apply cl_typed, fle_refl.
  - apply sw_empty_ok.
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
  pose proof (fp_connect (Some N) W_cl W_cl ∅ ∅ ΣC ∅ ∅ {[+ cl (c⁺)%cend +]} {[+ cl (c⁻)%cend +]} TUnit) as H.
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
  - exact (proj2 (proj2 (proj1 (wf_join_iff W_cl W_cl (proj1 sw_empty_ok) (proj1 sw_empty_ok))
      (proj2 W_cl_join)))).
Qed.

Theorem cl_lock_free c : excluded_middle → functional_choice →
  lock_free ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}).
Proof.
  intros EM FC. exact (lf_soundness 0 _ _ TUnit EM FC (cl_lftyped 0 c (MkPt (NConst 0) true 0))).
Qed.
