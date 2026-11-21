(** * The lock-free judgment Σ ⊩^N _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental : Σ ⊩^N _ W p : T → Σ ⊪^N _ W p : T
      lf_soundness   : wfworld W → ∅ ⊩^N _ W p : T → lock_free p
      lf_soundness_run : with excluded middle and dependent choice, also
                       a maximal weakly fair run starts from p
      lf_soundness_padovani : with the same hypotheses, every pending
                       thread of a reachable configuration can take part
                       in a later step

    Σ ⊩^N _ W p : T is process typing [ptyped] at Some N together with
    the guard of every thread, ⊢▷ p. N bounds the tickets of every
    channel, and P-Connect types the cut at exactly dual types
    ([senv_dual]). No rule
    renames families. The proof reads fsem^N off the typing through
    [fsem_of_cost] and the live relation through
    [live_fundamental_typed], inside [lf_p_term]. *)

From GV Require Import soup.LFAdequacy lockfree.FairRun.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N '_' W p : T" := (ptyped (Some N) W Σ p T ∧ ⊢▷ p)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N  '_'  W  p  :  T").

(** ** The fundamental theorem *)

Theorem lf_fundamental N W Σ p T : Σ ⊩^N _ W p : T → Σ ⊪^N _ W p : T.
Proof.
  intros [Hty Hg]. remember (Some N) as N' eqn:EN. revert Hg. induction Hty as
    [W Σ ΘB C0 t T c Hp HB HΣ Hpf Hd Ht HW
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hfam HJ];
    intros Hg; subst.
  - eapply lf_p_term; [done|done|done|done|exact Hd|exact Ht|].
    apply Hg. simpl. multiset_solver.
  - apply lf_p_connect; auto.
    + apply IH1; intros t Ht; apply Hg; simpl; multiset_solver.
    + apply IH2; intros t Ht; apply Hg; simpl; multiset_solver.
Qed.

(** ** Soundness *)

Theorem lf_soundness N W p T : wfworld W → ∅ ⊩^N _ W p : T → lock_free p.
Proof.
  intros HW Hty. apply (lf_adequacy N W T p (ptyped_strict _ _ _ _ _ (proj1 Hty)) HW).
  exact (lf_fundamental N W ∅ p T Hty).
Qed.

(** ** Soundness with a run, and Padovani-style lock freedom

    [lock_free p] quantifies over every maximal weakly fair run. With
    excluded middle and dependent choice as hypotheses such a run exists
    ([fair_run_exists_proc]), so the statement is not vacuous, and the
    reachability form of Padovani 2014, Def. II.1 follows per thread
    ([lock_free_padovani]). *)

Corollary lf_soundness_run N W p T :
  excluded_middle → dependent_choice → wfworld W → ∅ ⊩^N _ W p : T →
  lock_free p ∧ ∃ r l, erase (r 0) = p ∧ maximal r l ∧ wfair r l.
Proof.
  intros EM DC HW Hty. split; [exact (lf_soundness N W p T HW Hty)|].
  exact (fair_run_exists_proc EM DC p).
Qed.

Corollary lf_soundness_padovani N W p T :
  excluded_middle → dependent_choice → wfworld W → ∅ ⊩^N _ W p : T → lf_padovani p.
Proof.
  intros EM DC HW Hty. exact (lock_free_padovani EM DC p (lf_soundness N W p T HW Hty)).
Qed.
