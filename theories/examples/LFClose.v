(** * Two threads closing one channel (stage S9)

      cl c⁺ ∥ cl c⁻,   cl o = close o

    Each thread is typed by P-Term over its end of c, and P-Connect cuts
    c at exactly dual types. The world has no constants and no facts, so
    it is well-founded ([swf_bare]). At N = ∞ [soundness] gives deadlock
    freedom ([cl_deadlock_free]), and at each finite N [lf_soundness]
    gives lock freedom ([cl_lock_free]). *)

From Stdlib Require Import Wf_nat.
From GV Require Import lockfree.FairRun.
From GV Require Import soup.LFTyped.

Definition W_cl : sworld := sw_empty.

Definition cl (o : cend) : expr := EClose (Chan o).

Lemma cl_typed (N : fuel) o x a m :
  fle a m →
  typed W_cl N {[o := TE SEnd x a m]} hc_empty [] (∅, None) (cl o) TUnit
    (fadd (Some 0) (Some 1)).
Proof.
  intros Ham. eapply (e_close W_cl N _ _ _ _ _ SEnd); [reflexivity| |].
  - simpl. split_and!; [intros y Hy; exfalso; set_solver|done].
  - apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
Qed.

Lemma cl_term (N : fuel) o x :
  ptyped N (khalf N) W_cl {[o := (SEnd, x)]} (∅, {[+ cl o +]}) TUnit.
Proof.
  apply (p_term_half N W_cl _ ∅ ∅ _ TUnit (fadd (Some 0) (Some 1))).
  - constructor.
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o' e' He. apply lookup_singleton_Some in He as [_ <-]. done.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of. rewrite map_fmap_singleton. apply cl_typed, fle_refl.
  - destruct sw_empty_ok as [Hw Hf]. split; [exact Hw|by apply swf_wok].
Qed.

(** The composite at any bound, at the join of the two thread worlds. *)
Lemma cl_ptyped (N : fuel) c (x : point) :
  ptyped N (khalf N) (W_cl ⊔ W_cl) ∅ ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}) TUnit.
Proof.
  set (ΣC := {[(c⁺)%cend := (SEnd, x)]} : senv).
  assert (senv_dual ΣC = {[(c⁻)%cend := (SEnd, x‾)]}) as Ed.
  { unfold senv_dual, ΣC. by rewrite map_fmap_singleton, kmap_singleton. }
  assert (chans_of ΣC = {[c]}) as Ec.
  { unfold chans_of, ΣC. by rewrite dom_singleton_L, set_map_singleton_L. }
  assert (chans_of ∅ = ∅) as E0 by (unfold chans_of; by rewrite dom_empty_L, set_map_empty).
  pose proof (p_connect_half N W_cl W_cl
    ∅ ∅ ΣC ∅ ∅ {[+ cl (c⁺)%cend +]} {[+ cl (c⁻)%cend +]} TUnit) as H.
  rewrite Ec, E0, !(left_id_L ∅ (∪)) in H. rewrite Ed in H.
  apply H; clear H.
  - apply cl_term.
  - apply cl_term.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply swf_wok, swf_bare. intros g [Hg|Hg]; destruct Hg.
Qed.

Theorem cl_lftyped N c :
  ∃ W, ∅ ⊩^N,(khalf (Some N)) _ W ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}) : TUnit.
Proof. eexists. apply (cl_ptyped (Some N) c (MkPt (NConst 0) true 0)). Qed.

(** The same process in the deadlock-free judgment, and deadlock free
    by [soundness]. *)
Theorem cl_dftyped c :
  ∃ W, ∅ ⊢_ W ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}) : TUnit.
Proof. eexists. apply (cl_ptyped None c (MkPt (NConst 0) true 0)). Qed.

Theorem cl_deadlock_free c : deadlock_free ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}).
Proof.
  destruct (cl_dftyped c) as [W H]. exact (soundness W _ _ H).
Qed.

Theorem cl_lock_free c : excluded_middle → functional_choice →
  lock_free ({[c]}, {[+ cl (c⁺)%cend +]} ⊎ {[+ cl (c⁻)%cend +]}).
Proof.
  intros EM FC. destruct (cl_lftyped 0 c) as [W H].
  exact (lf_soundness 0 _ _ _ TUnit EM FC H).
Qed.
