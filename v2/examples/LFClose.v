(** * Two threads closing one channel, lock free by the judgment ⊩ (stage S9)

      cl c⁺ ∥ cl c⁻,   cl o = close o

    Each thread is typed by P-Term at Some N over its end of c, and
    P-Connect cuts c at exactly dual types. The world has no constants
    and no facts, so it is well-founded ([swf_bare]). [lf_soundness_h] then
    gives lock freedom. *)

From Stdlib Require Import Wf_nat.
From GV Require Import lockfree.FairRun.
From GV Require Import soup.LFTyped.

Definition W_cl : sworld := sw_empty.

Definition cl (o : cend) : expr := EClose (Chan o).

Lemma cl_typed N o x a m :
  fle a m →
  typed W_cl (Some N) {[o := TE SEnd x a m]} hc_empty [] (∅, None) (cl o) TUnit
    (fadd (Some 0) (Some 1)).
Proof.
  intros Ham. eapply (e_close W_cl (Some N) _ _ _ _ _ SEnd); [reflexivity| |].
  - simpl. split_and!; [intros y Hy; exfalso; set_solver|done].
  - apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
Qed.

Lemma cl_term N o x :
  ptyped (Some N) (khalf (Some N)) (swrestrict W_cl (iface {[o := (SEnd, x)]} TUnit)) {[o := (SEnd, x)]} (∅, {[+ cl o +]}) TUnit.
Proof.
  apply (p_term_half (Some N) W_cl _ ∅ ∅ _ TUnit (fadd (Some 0) (Some 1))).
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
  ∃ W, ∅ ⊩^N,(khalf (Some N)) _ W ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}) : TUnit.
Proof.
  set (ΣC := {[(c⁺)%cend := (SEnd, x)]} : senv).
  assert (senv_dual ΣC = {[(c⁻)%cend := (SEnd, x‾)]}) as Ed.
  { unfold senv_dual, ΣC. by rewrite map_fmap_singleton, kmap_singleton. }
  assert (chans_of ΣC = {[c]}) as Ec.
  { unfold chans_of, ΣC. by rewrite dom_singleton_L, set_map_singleton_L. }
  assert (chans_of ∅ = ∅) as E0 by (unfold chans_of; by rewrite dom_empty_L, set_map_empty).
  pose proof (p_connect_half (Some N) (swrestrict W_cl (iface ΣC TUnit)) (swrestrict W_cl (iface (senv_dual ΣC) TUnit))
    ∅ ∅ ΣC ∅ ∅ {[+ cl (c⁺)%cend +]} {[+ cl (c⁻)%cend +]} TUnit) as H.
  rewrite Ec, E0, !(left_id_L ∅ (∪)) in H. rewrite Ed in H.
  eexists. apply H; clear H.
  - apply cl_term.
  - apply cl_term.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply wok_join_bare_r; [apply swrestrict_empty_bare|]. apply swf_wok, swf_bare, swrestrict_empty_bare.
Qed.

Theorem cl_lock_free c : excluded_middle → functional_choice →
  lock_free ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}).
Proof.
  intros EM FC. destruct (cl_lftyped 0 c (MkPt (NConst 0) true 0)) as [W H].
  exact (lf_soundness_h 0 _ _ _ TUnit EM FC H).
Qed.
