(** * The lock-free judgment Σ ⊩^N _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental : Σ ⊩^N _ W p : T → ∀ R ⊨ W, Σ ⊪^N _ R p : T
      lf_soundness   : ∅ ⊩^N _ W p : T → lock_free p
      lf_soundness_run : with excluded middle and dependent choice, also
                       a maximal weakly fair run starts from p
      lf_soundness_padovani : with the same hypotheses, every pending
                       thread of a reachable configuration can take part
                       in a later step

    Σ ⊩^N _ W p : T is process typing [fptyped] at Some N together with
    the guard of every thread, ⊢▷ p. N bounds the tickets of every
    channel, and P-Connect types the cut at exactly dual types
    ([senv_dual]). The proof reads fsem^N off the typing through
    [fsem_of_cost] and the live relation through
    [live_fundamental_ranked] on the derivation at Some N, inside
    [lf_p_term]. The soup reads ranked worlds. *)

From GV Require Import soup.LFAdequacy lockfree.FairRun.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N '_' W p : T" := (fptyped (Some N) W Σ p T ∧ ⊢▷ p)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N  '_'  W  p  :  T").

(** ** The fundamental theorem *)

Theorem lf_fundamental (EM : excluded_middle) N W Σ p T : Σ ⊩^N _ W p : T → lf_sems N W Σ p T.
Proof.
  intros [Hty Hg]. remember (Some N) as N' eqn:EN. revert Hg. induction Hty as
    [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Ht HW
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T Hty1 IH1 _ IH2 H12 H1C H2C HC HC1 HC2 HJ];
    intros Hg; subst.
  - eapply (lf_p_term EM W); [exact (proj1 HW)|done|done|done| |exact Ht|].
    { intros ch Hch. destruct (Hd ch Hch) as (S & x & m & m' & ? & _ & ?). eauto 10. }
    apply Hg. simpl. multiset_solver.
  - try specialize (IH1 eq_refl). try specialize (IH2 eq_refl).
    apply lf_p_connect; try done.
    + apply IH1. intros t Ht; apply Hg; simpl; multiset_solver.
    + apply IH2. intros t Ht; apply Hg; simpl; multiset_solver.
    + exact (pfree_union_r _ _ (fptyped_pfree _ _ _ _ _ Hty1)).
Qed.

(** ** Soundness *)

(** Excluded middle and functional choice are hypotheses of lock-free
    adequacy (relation/ExProp.v). A typed process sits over a well-founded
    static world, which a ranked world models. *)
Theorem lf_soundness N W p T :
  excluded_middle → functional_choice → ∅ ⊩^N _ W p : T → lock_free p.
Proof.
  intros EM FC Hty. destruct (fptyped_wf _ _ _ _ _ (proj1 Hty)) as [Hwf HW].
  exact (lf_sems_adequacy EM FC N W p T Hwf HW (lf_fundamental EM N W ∅ p T Hty)).
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

(** ** The hidden judgment

    The lock-free reading of a process typed with hiding: a whole world
    that hides to its world, with the soup at every ranked world that
    models it ([lf_sems_h]). P-Connect reads the two interface worlds
    once the private constants are apart ([lf_p_connect_h]), and the
    fundamental theorem goes through [ptyped_full]. *)
Definition lf_sems_h (N : nat) (Wi : sworld) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∃ W, sworld_wf W ∧ swf W ∧ hides W (iface Σ T) Wi ∧ lf_sems N W Σ p T.

Theorem lf_p_connect_h N V1 V2 W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  sworld_wf V1 → sworld_wf V2 → swf V1 → swf V2 →
  lf_sems N V1 (Σ1 ∪ ΣC) (C1, E1) T → lf_sems N V2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  hides V1 (iface (Σ1 ∪ ΣC) T) W1 → hides V2 (iface (Σ2 ∪ senv_dual ΣC) TUnit) W2 →
  (∀ a, a ∈ sw_consts V1 → a ∉ iface (Σ1 ∪ ΣC) T → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit) →
  (∀ a, a ∈ sw_consts V2 → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit → a ∉ sw_consts V1 ∪ iface (Σ1 ∪ ΣC) T) →
  swf (W1 ⊔ W2) →
  lf_sems_h N (swrestrict (W1 ⊔ W2) (iface (Σ1 ∪ Σ2) T)) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof.
  intros Hw1 Hw2 HS1 HS2 H1 H2 Hf H12 H1C H2C HC HC1 HC2 Hh1 Hh2 Hav1 Hav2 HS.
  destruct (connect_hidden (Some N) V1 V2 W1 W2 _ _ (iface (Σ1 ∪ Σ2) T) Hw1 Hw2 Hh1 Hh2 Hav1 Hav2
              (iface_connect _ _ _ _) HS) as [HR Hh].
  exists (V1 ⊔ V2). split_and!; [by apply swjoin_wf|by apply (wf_join_iff V1 V2 Hw1 Hw2)|exact Hh|].
  by apply lf_p_connect.
Qed.

Theorem lf_fundamental_h (EM : excluded_middle) N W Σ p T : ptyped (Some N) W Σ p T → ⊢▷ p → lf_sems_h N W Σ p T.
Proof.
  intros Hty Hg. destruct (ptyped_full _ _ _ _ _ Hty) as (W' & Hf & Hh). destruct (fptyped_wf _ _ _ _ _ Hf).
  exists W'. split_and!; try done. by apply (lf_fundamental EM).
Qed.

Theorem lf_sems_h_adequacy (EM : excluded_middle) (FC : functional_choice) N W p T :
  lf_sems_h N W ∅ p T → lock_free p.
Proof. intros (W' & Hwf & HW & _ & Hs). exact (lf_sems_adequacy EM FC N W' p T Hwf HW Hs). Qed.

(** Lock freedom of the hidden judgment. *)
Theorem lf_soundness_h N W p T :
  excluded_middle → functional_choice → ptyped (Some N) W ∅ p T → ⊢▷ p → lock_free p.
Proof. intros EM FC Hty Hg. exact (lf_sems_h_adequacy EM FC N W p T (lf_fundamental_h EM N W ∅ p T Hty Hg)). Qed.
