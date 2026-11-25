(** * The fundamental theorems for processes and soundness (stage S5,
      Appendix A.3)

      fundamental_proc      : Σ ⊢_W p : T → sem_ptyped_sw κ_DF W Σ p T
      live_fundamental_proc : Σ ⊢_W p : T → sem_ptyped_sw κ_L W Σ p T
      soundness             : ∅ ⊢_W p : T → deadlock_free p
      live_soundness        : ∅ ⊢_W p : T →
                                deadlock_free p ∧ no_free_divergence p
      soundness_source      : wf W → tfree T → ∅ ; ∅ ; [] ⊢^(∅, None) _ W t : T →
                                deadlock_free (∅, {[+ t +]})

    One induction on [ptyped] for every cost table whose threads satisfy
    the term-level theorem ([proc_gen]). A component is read at the
    world of its derivation, at every strict world that models it
    ([sem_ptyped_sw]). P-Term holds by [sem_p_term], P-Connect by
    [sem_p_connect], whose side condition [conn] the premises of the
    rule give ([conn_of]). The results hold at every fuel N, ⊢_W is the
    instance N = ∞. An acyclic world has a strict world that models it,
    constructively ([dmodels_exists]), so soundness takes no excluded
    middle (.claude/notes/redesign/check-df-acyclic.md). *)

From GV Require Export compat.PTerm static.Fundamental static.Hiding.
From GV Require Import compat.Conv.


(** ** The side conditions of P-Connect from the typing premises *)

Lemma senv_dual_cut (ΣC : senv) : cut_dual ΣC (senv_dual ΣC).
Proof.
  split.
  - intros o. unfold senv_dual. rewrite dom_kmap_L by apply _. rewrite dom_fmap_L, elem_of_map. split.
    + intros (o' & -> & Ho'). by rewrite edual_edual.
    + intros Ho. exists (edual o). by rewrite edual_edual.
  - intros o S x Ho. exists (dual S). unfold senv_dual. rewrite (lookup_kmap edual), lookup_fmap, Ho.
    split; [done|]. apply seqv_refl.
Qed.

Lemma conn_of Σ1 Σ2 ΣC C1 C2 :
  pfree (Σ1 ∪ ΣC) → pfree (Σ2 ∪ senv_dual ΣC) →
  C1 ## chans_of (Σ1 ∪ ΣC) → C2 ## chans_of (Σ2 ∪ senv_dual ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  conn Σ1 ΣC C1 Σ2 (senv_dual ΣC) C2.
Proof.
  intros F1 F2 K1 K2 H12 H1C H2C HC HC1 HC2.
  pose proof (chans_disj_map _ _ H1C) as D1. pose proof (chans_disj_map_dual _ _ H2C) as D2.
  rewrite chans_of_union in K1, K2.
  rewrite (cut_dual_chans _ _ (senv_dual_cut ΣC)) in K2.
  constructor; try done.
  - apply senv_dual_cut.
  - eapply pfree_sub'; [|exact F1]. rewrite dom_union_L. set_solver.
  - eapply pfree_sub'; [|exact F2]. rewrite dom_union_L. set_solver.
  - exact (pfree_union_r _ _ F1).
  - clear -K1 HC1. set_solver.
  - clear -K2 HC2. set_solver.
Qed.

(** ** The thread of P-Term *)

Lemma tenv_erase_ofk η Σ : tenv_erase (tenv_ofk η Σ) = Σ.
Proof.
  apply map_eq. intros o. unfold tenv_erase. rewrite lookup_fmap, lookup_tenv_ofk.
  by destruct (Σ !! o) as [[? ?]|].
Qed.

Lemma pterm_sth N η Σ (ΘB : tenv) C0 :
  (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
  (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
     ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
  sth (tenv_erase (tenv_ofk η Σ ∪ ΘB)) Σ (tenv_erase ΘB) C0.
Proof.
  intros HB HΣ Hf Hd. constructor; [|intros o; unfold tenv_erase; rewrite dom_fmap_L; apply HB|done|done|].
  - unfold tenv_erase at 1. rewrite map_fmap_union. f_equal. apply tenv_erase_ofk.
  - intros o Ho. destruct (Hd (ech o) Ho) as (S & x & m & m' & _ & _ & H1 & H2). unfold tenv_erase.
    destruct o as [c|c]; cbn [ech] in H1, H2; simpl.
    + exists S, x, (dual S). rewrite !lookup_fmap, H1, H2. split_and!; [done|done|apply seqv_refl].
    + exists (dual S), x‾, S. rewrite !lookup_fmap, H1, H2. simpl. rewrite pt_dual_dual.
      split_and!; [done|done|]. unfold sdual. rewrite dual_involutive. apply seqv_refl.
Qed.

(** A thread typed by the merged judgment at the empty context, read in E
    at its erased environment, through the term theorem at N = ∞. *)
Lemma typed_E κ W Θ t T n :
  sem_typed κ W (tenv_df Θ) (lenv_df []) (∅, None) t (ty_df T) →
  t ∈ E[κ]^W _ n⟦tenv_erase Θ ⊢ T⟧^∅.
Proof.
  intros Hs. pose proof (Hs ∅ ltac:(by intros u Hu) n W ∅ Var (wext_refl _) (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty in H.
  assert (sf_den ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. set_solver. }
  rewrite E in H. apply (Erel_blind _ _ _ _ (ty_df T)); [apply ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem. apply sequiv_refl.
Qed.

(** ** P-Connect at static worlds

    The deadlock-free judgment composes the way the lock-free one does
    (soup/LFCompose.v, [lf_p_connect]). Each component is read at every
    strict world that models its own static world, and a strict world of
    the join models both. P holds a process itself at a strict world, with
    no starting state, so both components are read at that one world. *)
Definition sem_ptyped_sw (κ : ctable) (W : sworld) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ R, wmodels R W → wstrict R → sem_ptyped κ R Σ p T.

Lemma sem_p_connect_sw κ W1 W2 Σ1 ΣC Σ2 ΣD p1 p2 T :
  tfree T →
  sem_ptyped_sw κ W1 (Σ1 ∪ ΣC) p1 T → sem_ptyped_sw κ W2 (Σ2 ∪ ΣD) p2 TUnit →
  conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 →
  sem_ptyped_sw κ (W1 ⊔ W2) (Σ1 ∪ Σ2) (pconn p1 p2 (chans_of ΣC)) T.
Proof.
  intros HT H1 H2 Hc R HR HS n. apply (sem_p_connect κ n R Σ1 ΣC Σ2 ΣD); [done| | |done].
  - apply H1; [|done]. by eapply wmodels_ext; [apply swext_join_l|].
  - apply H2; [|done]. by eapply wmodels_ext; [apply swext_join_r|].
Qed.

(** ** One induction for every cost table

    A component typed at a world W is read at W ([sem_ptyped_sw]).
    P-Term gives it by [sem_p_term], and P-Connect composes it at the
    join by [sem_p_connect_sw], whose side condition [conn] the premises
    of the rule give ([conn_of]). *)

Section proc.
  Context (κ : ctable).
  Context (Hthr : ∀ W R N Θ t T c, sworld_wf W → Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} t : T ▷ c →
                    wmodels R W → wstrict R → sem_typed κ R (tenv_df Θ) (lenv_df []) (∅, None) t (ty_df T)).

  (** P-Term at the whole world of the thread. *)
  Lemma sem_p_term_sw N η W Σ ΘB C0 t T c :
    tfree T → (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
    (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
       ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
    typed W N (tenv_ofk η Σ ∪ ΘB) hc_empty [] (∅, None) t T c → sworld_wf W →
    sem_ptyped_sw κ W Σ (C0, {[+ t +]}) T.
  Proof.
    intros Hp HB HΣ Hpf Hd Ht Hw R HR HS n.
    apply (sem_p_term κ n R _ Σ (tenv_erase ΘB) C0 t T Hp (pterm_sth N η Σ ΘB C0 HB HΣ Hpf Hd)).
    apply typed_E. exact (Hthr W R N _ t T c Hw Ht HR HS).
  Qed.

  Lemma proc_gen N η W Σ p T : ptyped N η W Σ p T → sem_ptyped_sw κ W Σ p T.
  Proof.
    induction 1 as [W' Σ' ΘB C0 t T' c Hp HB HΣ Hpf _ Hd _ Ht [Hw _]
                   |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' Hty1 IH1 Hty2 IH2 H12 H1C H2C HC HC1 HC2 _ _].
    - by eapply sem_p_term_sw.
    - pose proof (ptyped_pfree _ _ _ _ _ _ Hty1) as F1. pose proof (ptyped_pfree _ _ _ _ _ _ Hty2) as F2.
      pose proof (ptyped_chans _ _ _ _ _ _ Hty1) as K1. pose proof (ptyped_chans _ _ _ _ _ _ Hty2) as K2.
      simpl in K1, K2.
      exact (sem_p_connect_sw κ W1 W2 Σ1 ΣC Σ2 (senv_dual ΣC) (C1, E1) (C2, E2) T'
               (ptyped_tfree _ _ _ _ _ _ Hty1) IH1 IH2
               (conn_of Σ1 Σ2 ΣC C1 C2 F1 F2 K1 K2 H12 H1C H2C HC HC1 HC2)).
  Qed.
End proc.

(** One closed thread of the DF judgment, with no creation constraint. *)
Theorem soundness_source W t T : sworld_wf W → sacyc W → tfree T →
  ∅ ; hc_empty ; [] ⊢^(∅, None) _ W t : T → deadlock_free (∅, {[+ t +]}).
Proof.
  intros Hwf HW HT Ht. destruct (dmodels_exists W Hwf HW) as (R & HS & HR).
  apply (adequacy R T _). intros n.
  pose proof (fundamental W R ∅ [] (∅, None) t T Hwf Ht HR HS ∅ ltac:(by intros u Hu) n R ∅ Var (wext_refl _)
                (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty, tenv_erase_empty in H.
  assert (sf_den ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. set_solver. }
  rewrite E in H. apply (sem_p_term κ_DF n R ∅ ∅ ∅ ∅ t T HT); [|exact H].
  constructor; [by rewrite map_union_empty|intros o; rewrite dom_empty_L; set_solver
    |unfold chans_of; rewrite dom_empty_L; set_solver|apply pfree_empty|intros o Ho; set_solver].
Qed.

(** ** The fundamental theorems and soundness

    A process typed at W is in the relation at every strict world that
    models W ([fundamental_proc], [live_fundamental_proc]). W is
    acyclic, so such a world exists ([dmodels_exists]), and adequacy
    gives deadlock freedom ([soundness], [live_soundness]). *)
Theorem fundamental_proc W Σ p T : Σ ⊢_W p : T → sem_ptyped_sw κ_DF W Σ p T.
Proof.
  exact (proc_gen κ_DF (λ W' R' N Θ t T' c HW' Ht HR' HS',
    fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht HR' HS') None (khalf None) W Σ p T).
Qed.

Theorem live_fundamental_proc W Σ p T : Σ ⊢_W p : T → sem_ptyped_sw κ_L W Σ p T.
Proof.
  exact (proc_gen κ_L (λ W' R' N Θ t T' c HW' Ht HR' HS',
    live_fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht HR' HS') None (khalf None) W Σ p T).
Qed.

Theorem adequacy_sw W p T : sworld_wf W → sacyc W → sem_ptyped_sw κ_DF W ∅ p T → deadlock_free p.
Proof.
  intros Hwf HW Hs. destruct (dmodels_exists W Hwf HW) as (R & HS & HR).
  apply (adequacy R T p). by apply Hs.
Qed.

Theorem live_adequacy_sw W p T : sworld_wf W → sacyc W → sem_ptyped_sw κ_L W ∅ p T →
  deadlock_free p ∧ no_free_divergence p.
Proof.
  intros Hwf HW Hs. destruct (dmodels_exists W Hwf HW) as (R & HS & HR).
  apply (live_adequacy R T p). by apply Hs.
Qed.

Theorem soundness W p T : ∅ ⊢_W p : T → deadlock_free p.
Proof.
  intros Hty. destruct (ptyped_wf _ _ _ _ _ _ Hty) as [Hwf HW].
  exact (adequacy_sw W p T Hwf HW (fundamental_proc W ∅ p T Hty)).
Qed.

Theorem live_soundness W p T : ∅ ⊢_W p : T → deadlock_free p ∧ no_free_divergence p.
Proof.
  intros Hty. destruct (ptyped_wf _ _ _ _ _ _ Hty) as [Hwf HW].
  exact (live_adequacy_sw W p T Hwf HW (live_fundamental_proc W ∅ p T Hty)).
Qed.
