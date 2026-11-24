(** * The lock-free judgment Σ ⊩^N,η _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental   : Σ ⊩^N,η _ W p : T → lf_sems N η W Σ p T
      lf_soundness     : ∅ ⊩^N,η _ W p : T → lock_free p
      lf_soundness_run : with excluded middle and dependent choice, also
                       a maximal weakly fair run starts from p
      lf_soundness_padovani : with the same hypotheses, every pending
                       thread of a reachable configuration can take part
                       in a later step

    Σ ⊩^N,η _ W p : T is process typing [ptyped] at Some N with the
    interface annotations η. N bounds the tickets of every channel, and
    P-Connect types the cut at exactly dual types ([senv_dual]) with
    tickets that sum to at most N. The proof reads a component at the
    world of its derivation, fsem^N off the typing through [fsem_of_cost] and
    the live relation through [live_fundamental_ranked] on the
    derivation at Some N, inside [lf_p_term]. The soup reads ranked
    worlds. *)

From GV Require Import soup.LFAdequacy lockfree.FairRun.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N , η '_' W p : T" := (ptyped (Some N) η W Σ p T)
  (at level 74, N at level 0, η at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N , η  '_'  W  p  :  T").

(** ** The fundamental theorem and lock freedom

    A process typed at W has the soup at every ranked world that models
    W ([lf_fundamental]). One induction on the derivation. P-Term holds
    by [lf_p_term], P-Connect by [lf_p_connect] at the join. *)
Theorem lf_fundamental (EM : excluded_middle) N η W Σ p T : Σ ⊩^N,η _ W p : T → lf_sems N η W Σ p T.
Proof.
  induction 1 as [W' Σ' ΘB C0 t T' c Hp HB HΣ _ _ Hd Htk Ht [Hw _]
                 |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' Hty1 IH1 Hty2 IH2 H12 H1C H2C HC HC1 HC2 Hts _].
  - eapply (lf_p_term EM W'); [exact Hw|done|done|done|exact Htk| |exact Ht].
    intros ch Hch. destruct (Hd ch Hch) as (S & x & m & m' & ? & _ & ?). eauto 10.
  - pose proof (ptyped_pfree _ _ _ _ _ _ Hty1) as F1.
    exact (lf_p_connect N η W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' IH1 IH2 Hts (pfree_union_r _ _ F1) H12 H1C H2C HC HC1 HC2).
Qed.

Theorem lf_soundness N η W p T :
  excluded_middle → functional_choice → ptyped (Some N) η W ∅ p T → lock_free p.
Proof.
  intros EM FC Hty. destruct (ptyped_wf _ _ _ _ _ _ Hty) as [Hwf HW].
  exact (lf_sems_adequacy EM FC N η W p T Hwf HW (lf_fundamental EM N η W ∅ p T Hty)).
Qed.

(** ** Soundness with a run, and Padovani-style lock freedom

    [lock_free p] quantifies over every maximal weakly fair run. With
    excluded middle and dependent choice as hypotheses such a run exists
    ([fair_run_exists_proc]), so the statement is not vacuous, and the
    reachability form of Padovani 2014, Def. II.1 follows per thread
    ([lock_free_padovani]). *)

Corollary lf_soundness_run N η W p T :
  excluded_middle → dependent_choice → functional_choice → ∅ ⊩^N,η _ W p : T →
  lock_free p ∧ ∃ r l, erase (r 0) = p ∧ maximal r l ∧ wfair r l.
Proof.
  intros EM DC FC Hty. split; [exact (lf_soundness N η W p T EM FC Hty)|].
  exact (fair_run_exists_proc EM DC p).
Qed.

Corollary lf_soundness_padovani N η W p T :
  excluded_middle → dependent_choice → functional_choice → ∅ ⊩^N,η _ W p : T →
  lf_padovani p.
Proof.
  intros EM DC FC Hty. exact (lock_free_padovani EM DC p (lf_soundness N η W p T EM FC Hty)).
Qed.
