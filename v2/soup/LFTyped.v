(** * The lock-free judgment Σ ⊩^N,η _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental_h : Σ ⊩^N,η _ W p : T → Σ ⊪^{N,h} _ W p : T
      lf_soundness_h   : ∅ ⊩^N,η _ W p : T → lock_free p
      lf_soundness_run : with excluded middle and dependent choice, also
                       a maximal weakly fair run starts from p
      lf_soundness_padovani : with the same hypotheses, every pending
                       thread of a reachable configuration can take part
                       in a later step

    Σ ⊩^N,η _ W p : T is process typing [ptyped] at Some N with the
    interface annotations η. N bounds the tickets of every channel, and
    P-Connect types the cut at exactly dual types ([senv_dual]) with
    tickets that sum to at most N. The proof reads a component at a
    well-founded whole world that hides to its world ([ptyped_sem],
    static/Hiding.v), fsem^N off the typing through [fsem_of_cost] and
    the live relation through [live_fundamental_ranked] on the
    derivation at Some N, inside [lf_p_term]. The soup reads ranked
    worlds. *)

From GV Require Import soup.LFAdequacy lockfree.FairRun.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N , η '_' W p : T" := (ptyped (Some N) η W Σ p T)
  (at level 74, N at level 0, η at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N , η  '_'  W  p  :  T").

(** ** The hidden judgment

    The lock-free reading of a process typed with hiding: a whole world
    that hides to its world, with the soup at every ranked world that
    models it ([lf_sems_h]). P-Connect reads the two interface worlds
    once the private constants are apart ([lf_p_connect_h]). *)
Definition lf_sems_h (N : nat) (η : iann) (Wi : sworld) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∃ W, sworld_wf W ∧ swf W ∧ hides W (iface Σ T) Wi ∧ lf_sems N η W Σ p T.

Theorem lf_p_connect_h N η V1 V2 W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  sworld_wf V1 → sworld_wf V2 → swf V1 → swf V2 →
  lf_sems N η V1 (Σ1 ∪ ΣC) (C1, E1) T → lf_sems N η V2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  (∀ o, o ∈ dom ΣC → tsum_ok (Some N) (η o).2 (η (edual o)).2) →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  hides V1 (iface (Σ1 ∪ ΣC) T) W1 → hides V2 (iface (Σ2 ∪ senv_dual ΣC) TUnit) W2 →
  (∀ a, a ∈ sw_consts V1 → a ∉ iface (Σ1 ∪ ΣC) T → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit) →
  (∀ a, a ∈ sw_consts V2 → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit → a ∉ sw_consts V1 ∪ iface (Σ1 ∪ ΣC) T) →
  swf (W1 ⊔ W2) →
  lf_sems_h N η (swrestrict (W1 ⊔ W2) (iface (Σ1 ∪ Σ2) T)) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof.
  intros Hw1 Hw2 HS1 HS2 H1 H2 Hts Hf H12 H1C H2C HC HC1 HC2 Hh1 Hh2 Hav1 Hav2 HS.
  destruct (connect_hidden (Some N) V1 V2 W1 W2 _ _ (iface (Σ1 ∪ Σ2) T) Hw1 Hw2 Hh1 Hh2 Hav1 Hav2
              (iface_connect _ _ _ _) HS) as [HR Hh].
  exists (V1 ⊔ V2). split_and!; [by apply swjoin_wf|by apply (wf_join_iff V1 V2 Hw1 Hw2)|exact Hh|].
  by apply lf_p_connect.
Qed.

Theorem lf_fundamental_h (EM : excluded_middle) N η W Σ p T : Σ ⊩^N,η _ W p : T → lf_sems_h N η W Σ p T.
Proof.
  intros Hty. destruct (ptyped_sem (Some N) η (lf_sems N η)) with W Σ p T as (W' & ? & ? & ? & ?); [..|done|by exists W'].
  - intros W' Σ' ΘB C0 t T' c Hp HB HΣ _ _ Hd Htk Ht Hw _.
    eapply (lf_p_term EM W'); [exact Hw|done|done|done|exact Htk| |exact Ht].
    intros ch Hch. destruct (Hd ch Hch) as (S & x & m & m' & ? & _ & ?). eauto 10.
  - intros W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' H1 H2 _ F1 _ _ _ H12 H1C H2C HC HC1 HC2 Hts _ _ _.
    exact (lf_p_connect N η W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' H1 H2 Hts (pfree_union_r _ _ F1) H12 H1C H2C HC HC1 HC2).
  - intros W1 W2 Σ' p' T' Hx H R HR Hr. apply H; [by eapply wmodels_ext|done].
Qed.

Theorem lf_sems_h_adequacy (EM : excluded_middle) (FC : functional_choice) N η W p T :
  lf_sems_h N η W ∅ p T → lock_free p.
Proof. intros (W' & Hwf & HW & _ & Hs). exact (lf_sems_adequacy EM FC N η W' p T Hwf HW Hs). Qed.

(** Lock freedom of the hidden judgment. *)
Theorem lf_soundness_h N η W p T :
  excluded_middle → functional_choice → ptyped (Some N) η W ∅ p T → lock_free p.
Proof. intros EM FC Hty. exact (lf_sems_h_adequacy EM FC N η W p T (lf_fundamental_h EM N η W ∅ p T Hty)). Qed.

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
  intros EM DC FC Hty. split; [exact (lf_soundness_h N η W p T EM FC Hty)|].
  exact (fair_run_exists_proc EM DC p).
Qed.

Corollary lf_soundness_padovani N η W p T :
  excluded_middle → dependent_choice → functional_choice → ∅ ⊩^N,η _ W p : T →
  lf_padovani p.
Proof.
  intros EM DC FC Hty. exact (lock_free_padovani EM DC p (lf_soundness_h N η W p T EM FC Hty)).
Qed.
