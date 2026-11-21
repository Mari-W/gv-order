(** * The lock-free judgment Σ ⊩^N _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental : Σ ⊩^N _ W p : T → R ⊨ W → Σ ⊪^N _ R p : T
      lf_soundness   : ∅ ⊩^N _ W p : T → lock_free p
      lf_soundness_run : with excluded middle and dependent choice, also
                       a maximal weakly fair run starts from p
      lf_soundness_padovani : with the same hypotheses, every pending
                       thread of a reachable configuration can take part
                       in a later step

    Σ ⊩^N _ W p : T is process typing [ptyped] at Some N together with
    the guard of every thread, ⊢▷ p. N bounds the tickets of every
    channel, and P-Connect types the cut at exactly dual types
    ([senv_dual]). The proof reads fsem^N off the typing through
    [fsem_of_cost] and the live relation through
    [live_fundamental_typed], inside [lf_p_term]. *)

From GV Require Import soup.LFAdequacy lockfree.FairRun.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N '_' W p : T" := (ptyped (Some N) W Σ p T ∧ ⊢▷ p)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N  '_'  W  p  :  T").

(** ** The fundamental theorem *)

Theorem lf_fundamental N W R Σ p T : Σ ⊩^N _ W p : T → wmodels R W → Σ ⊪^N _ R p : T.
Proof.
  intros [Hty Hg]. remember (Some N) as N' eqn:EN. revert R Hg. induction Hty as
    [W Σ ΘB C0 t T c Hp HB HΣ Hpf Hd Ht HW
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 HJ];
    intros R Hg HR; subst.
  - eapply (lf_p_term W); [exact (proj1 HW)|done|done|done|done|exact Hd|exact Ht|].
    apply Hg. simpl. multiset_solver.
  - try specialize (IH1 eq_refl). try specialize (IH2 eq_refl).
    apply lf_p_connect; try done.
    + apply IH1; [intros t Ht; apply Hg; simpl; multiset_solver|].
      by eapply wmodels_ext; [apply swext_join_l|].
    + apply IH2; [intros t Ht; apply Hg; simpl; multiset_solver|].
      by eapply wmodels_ext; [apply swext_join_r|].
Qed.

(** ** Soundness *)

(** Excluded middle and functional choice are hypotheses of lock-free
    adequacy (relation/ExProp.v). A typed process sits over a well-founded
    static world, which a ranked world models. *)
Theorem lf_soundness N W p T :
  excluded_middle → functional_choice → ∅ ⊩^N _ W p : T → lock_free p.
Proof.
  intros EM FC Hty. destruct (ptyped_wf _ _ _ _ _ (proj1 Hty)) as [Hwf HW].
  destruct (wmodels_exists W Hwf HW) as [R HR].
  apply (lf_adequacy EM FC N R T p). exact (lf_fundamental N W R ∅ p T Hty HR).
Qed.

(** ** Soundness with a run, and Padovani-style lock freedom

    [lock_free p] quantifies over every maximal weakly fair run. With
    excluded middle and dependent choice as hypotheses such a run exists
    ([fair_run_exists_proc]), so the statement is not vacuous, and the
    reachability form of Padovani 2014, Def. II.1 follows per thread
    ([lock_free_padovani]). *)

Corollary lf_soundness_run N W p T :
  excluded_middle → dependent_choice → functional_choice → ∅ ⊩^N _ W p : T →
  lock_free p ∧ ∃ r l, erase (r 0) = p ∧ maximal r l ∧ wfair r l.
Proof.
  intros EM DC FC Hty. split; [exact (lf_soundness N W p T EM FC Hty)|].
  exact (fair_run_exists_proc EM DC p).
Qed.

Corollary lf_soundness_padovani N W p T :
  excluded_middle → dependent_choice → functional_choice → ∅ ⊩^N _ W p : T →
  lf_padovani p.
Proof.
  intros EM DC FC Hty. exact (lock_free_padovani EM DC p (lf_soundness N W p T EM FC Hty)).
Qed.
