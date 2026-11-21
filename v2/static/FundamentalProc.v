(** * The fundamental theorems for processes and soundness (stage S5,
      Appendix A.3)

      fundamental_proc      : Σ ⊢_W p : T → R ⊨ W → Σ ⊨_R p : T
      live_fundamental_proc : Σ ⊢_W p : T → ⊢▷ p → R ⊨ W → Σ ⊫_R p : T
      soundness             : ∅ ⊢_W p : T → deadlock_free p
      live_soundness        : ∅ ⊢_W p : T → ⊢▷ p →
                                deadlock_free p ∧ no_tau_divergence p
      soundness_source      : wf W → tfree T → ∅ ; ∅ ; [] ⊢^(∅, None) _ W t : T →
                                deadlock_free (∅, {[+ t +]})

    One induction on [ptyped] for every cost table whose threads satisfy
    the term-level theorem ([proc_gen]): P-Term by [sem_p_term], P-Connect
    by [sem_p_connect], whose side condition [conn] the premises of the
    rule give ([ptyped_conn]). The results
    hold at every fuel N, ⊢_W is the instance N = ∞. The process
    theorems read a ranked world R that models the static world W
    ([wmodels]). A process derivation sits over a well-founded static
    world ([ptyped_wf]), so such an R exists ([wmodels_exists]) and
    soundness asks nothing of W. *)

From GV Require Export compat.PTerm static.Fundamental.
From GV Require Import compat.Conv.

(** The guard of a process, ⊢▷ p: every thread t of p has ∅ ⊢▷ t. *)
Definition pguard (p : proc) : Prop := ∀ t, t ∈ p.2 → ∅ ⊢▷ t.

Notation "⊢▷ p" := (pguard p) (at level 74, p at level 60, format "⊢▷  p").

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

Lemma ptyped_conn N W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  ptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T → ptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  conn Σ1 ΣC C1 Σ2 (senv_dual ΣC) C2.
Proof.
  intros H1 H2 D1 D2 Hf H12 H1C H2C HC HC1 HC2.
  pose proof (ptyped_pfree _ _ _ _ _ H1) as F1. pose proof (ptyped_pfree _ _ _ _ _ H2) as F2.
  pose proof (ptyped_chans _ _ _ _ _ H1) as K1. pose proof (ptyped_chans _ _ _ _ _ H2) as K2.
  simpl in K1, K2. rewrite chans_of_union in K1, K2.
  rewrite (cut_dual_chans _ _ (senv_dual_cut ΣC)) in K2.
  constructor; try done.
  - apply senv_dual_cut.
  - eapply pfree_sub'; [|exact F1]. rewrite dom_union_L. set_solver.
  - eapply pfree_sub'; [|exact F2]. rewrite dom_union_L. set_solver.
  - clear -K1 HC1. set_solver.
  - clear -K2 HC2. set_solver.
Qed.

(** ** The thread of P-Term *)

Lemma pterm_sth N Σ (ΘB : tenv) C0 :
  (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
  (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧
     ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
  sth (tenv_erase (tenv_of (fhalf N) Σ ∪ ΘB)) Σ (tenv_erase ΘB) C0.
Proof.
  intros HB HΣ Hf Hd. constructor; [|intros o; unfold tenv_erase; rewrite dom_fmap_L; apply HB|done|done|].
  - unfold tenv_erase, tenv_of. rewrite map_fmap_union, <-map_fmap_compose. f_equal.
    rewrite <-(map_fmap_id Σ) at 2. apply map_fmap_ext. by intros ? [? ?] _.
  - intros o Ho. destruct (Hd (ech o) Ho) as (S & x & m & m' & _ & H1 & H2). unfold tenv_erase.
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
  intros Hs. pose proof (Hs ∅ ∅ ltac:(by intros u Hu) n W ∅ Var (wext_refl _) (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty in H.
  assert (sf_den ∅ ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. destruct (fs_bot None); set_solver. }
  rewrite E in H. apply (Erel_blind _ _ _ _ (ty_df T)); [apply ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem. apply sequiv_refl.
Qed.

(** ** P-Connect at static worlds

    The deadlock-free judgment composes the way the lock-free one does
    (soup/LFCompose.v, [lf_p_connect]). Each component is read at every
    ranked world that models its own static world, and a ranked world of
    the join models both. P holds a process itself at a ranked world, with
    no starting state, so both components are read at that one world. *)
Definition sem_ptyped_sw (κ : ctable) (W : sworld) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ R, wmodels R W → sem_ptyped κ R Σ p T.

Lemma sem_p_connect_sw κ W1 W2 Σ1 ΣC Σ2 ΣD p1 p2 T :
  tfree T →
  sem_ptyped_sw κ W1 (Σ1 ∪ ΣC) p1 T → sem_ptyped_sw κ W2 (Σ2 ∪ ΣD) p2 TUnit →
  conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 →
  sem_ptyped_sw κ (W1 ⊔ W2) (Σ1 ∪ Σ2) (pconn p1 p2 (chans_of ΣC)) T.
Proof.
  intros HT H1 H2 Hc R HR n. apply (sem_p_connect κ n R Σ1 ΣC Σ2 ΣD); [done| | |done].
  - apply H1. by eapply wmodels_ext; [apply swext_join_l|].
  - apply H2. by eapply wmodels_ext; [apply swext_join_r|].
Qed.

(** ** One induction for every cost table *)

Section proc.
  Context (κ : ctable) (G : expr → Prop).
  Context (Hthr : ∀ W R N Θ t T c, sworld_wf W → Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} t : T ▷ c →
                    G t → wmodels R W → sem_typed κ R (tenv_df Θ) (lenv_df []) (∅, None) t (ty_df T)).

  Lemma proc_gen N W Σ p T : ptyped N W Σ p T → (∀ t, t ∈ p.2 → G t) →
    ∀ R, wmodels R W → sem_ptyped κ R Σ p T.
  Proof.
    induction 1 as
      [W Σ ΘB C0 t T c Hp HB HΣ Hpf Hd Ht HW
      |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T H1 IH1 H2 IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 HJ];
      intros HG R HR n; simpl in HG.
    - apply (sem_p_term κ n R _ Σ (tenv_erase ΘB) C0 t T Hp (pterm_sth N Σ ΘB C0 HB HΣ Hpf Hd)).
      assert (G t) as Hg by (apply HG; multiset_solver).
      apply typed_E. exact (Hthr W R N _ t T c (proj1 HW) Ht Hg HR).
    - pose proof (ptyped_conn _ _ _ _ _ _ _ _ _ _ _ H1 H2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2) as Hc.
      refine (sem_p_connect κ n R Σ1 ΣC Σ2 (senv_dual ΣC) (C1, E1) (C2, E2) T (ptyped_tfree _ _ _ _ _ H1)
                (IH1 _ R _ n) (IH2 _ R _ n) Hc).
      + intros t Ht; apply HG; simpl; multiset_solver.
      + by eapply wmodels_ext; [apply swext_join_l|].
      + intros t Ht; apply HG; simpl; multiset_solver.
      + by eapply wmodels_ext; [apply swext_join_r|].
  Qed.
End proc.

(** ** The theorems of A.3 *)

Theorem fundamental_proc W R Σ p T : Σ ⊢_W p : T → wmodels R W → Σ ⊨_R p : T.
Proof.
  intros Hty HR. refine (proc_gen κ_DF (λ _, True) _ None W Σ p T Hty _ R HR); [|done].
  intros W' R' N Θ t T' c HW' Ht _ HR'. exact (fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht HR').
Qed.

Theorem live_fundamental_proc W R Σ p T : Σ ⊢_W p : T → ⊢▷ p → wmodels R W → Σ ⊫_R p : T.
Proof.
  intros Hty Hg HR. refine (proc_gen κ_L (lguard ∅) _ None W Σ p T Hty Hg R HR).
  intros W' R' N Θ t T' c HW' Ht Hgt HR'. exact (live_fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht Hgt HR').
Qed.

(** A typed process sits over a well-founded static world, which a ranked
    world models ([wmodels_exists]). *)
Theorem soundness W p T : ∅ ⊢_W p : T → deadlock_free p.
Proof.
  intros Hty. destruct (ptyped_wf _ _ _ _ _ Hty) as [Hwf HW].
  destruct (wmodels_exists W Hwf HW) as [R HR].
  apply (adequacy R T p). by apply (fundamental_proc W).
Qed.

Theorem live_soundness W p T : ∅ ⊢_W p : T → ⊢▷ p →
  deadlock_free p ∧ no_tau_divergence p.
Proof.
  intros Hty Hg. destruct (ptyped_wf _ _ _ _ _ Hty) as [Hwf HW].
  destruct (wmodels_exists W Hwf HW) as [R HR].
  apply (live_adequacy R T p). by apply (live_fundamental_proc W).
Qed.

(** One closed thread of the DF judgment, with no creation constraint. *)
Theorem soundness_source W t T : sworld_wf W → swf W → tfree T → ∅ ; hc_empty ; [] ⊢^(∅, None) _ W t : T →
  deadlock_free (∅, {[+ t +]}).
Proof.
  intros Hwf HW HT Ht. destruct (wmodels_exists W Hwf HW) as [R HR].
  apply (adequacy R T _). intros n.
  pose proof (fundamental W R ∅ [] (∅, None) t T Hwf Ht HR ∅ ∅ ltac:(by intros u Hu) n R ∅ Var (wext_refl _)
                (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty, tenv_erase_empty in H.
  assert (sf_den ∅ ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. destruct (fs_bot None); set_solver. }
  rewrite E in H. apply (sem_p_term κ_DF n R ∅ ∅ ∅ ∅ t T HT); [|exact H].
  constructor; [by rewrite map_union_empty|intros o; rewrite dom_empty_L; set_solver
    |unfold chans_of; rewrite dom_empty_L; set_solver|apply pfree_empty|intros o Ho; set_solver].
Qed.
