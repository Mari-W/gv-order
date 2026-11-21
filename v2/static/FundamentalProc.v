(** * The fundamental theorems for processes and soundness (stage S5,
      Appendix A.3)

      fundamental_proc      : Σ ⊢_W p : T → Σ ⊨_W p : T
      live_fundamental_proc : Σ ⊢_W p : T → ⊢▷ p → Σ ⊫_W p : T
      soundness             : ∅ ⊢_W p : T → deadlock_free p
      live_soundness        : ∅ ⊢_W p : T → ⊢▷ p →
                                deadlock_free p ∧ no_tau_divergence p
      soundness_source      : strict W → tfree T → ∅ ; ∅ ; [] ⊢^(∅, None) _ W t : T →
                                deadlock_free (∅, {[+ t +]})

    One induction on [ptyped] for every cost table whose threads satisfy
    the term-level theorem ([proc_gen]): P-Term by [sem_p_term], P-Connect
    by [sem_p_connect], whose side condition [conn] the premises of the
    rule give ([ptyped_conn]). The results
    hold at every fuel N, ⊢_W is the instance N = ∞. A process derivation
    sits over a strict world ([ptyped_strict]), so the process theorems
    ask no strictness of their own. *)

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

(** ** One induction for every cost table *)

Section proc.
  Context (κ : ctable) (G : expr → Prop).
  Context (Hthr : ∀ W N Θ t T c, strict W → Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} t : T ▷ c →
                    G t → sem_typed κ W (tenv_df Θ) (lenv_df []) (∅, None) t (ty_df T)).

  Lemma proc_gen N W Σ p T : ptyped N W Σ p T → (∀ t, t ∈ p.2 → G t) → sem_ptyped κ W Σ p T.
  Proof.
    induction 1 as
      [W Σ ΘB C0 t T c Hp HB HΣ Hpf Hd Ht HW
      |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T H1 IH1 H2 IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hfam HJ];
      intros HG n; simpl in HG.
    - apply (sem_p_term κ n W _ Σ (tenv_erase ΘB) C0 t T Hp (pterm_sth N Σ ΘB C0 HB HΣ Hpf Hd)).
      assert (G t) as Hg by (apply HG; multiset_solver).
      apply typed_E. exact (Hthr W N _ t T c HW Ht Hg).
    - pose proof (ptyped_conn _ _ _ _ _ _ _ _ _ _ _ H1 H2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2) as Hc.
      refine (sem_p_connect κ n W1 W2 Σ1 ΣC Σ2 (senv_dual ΣC) (C1, E1) (C2, E2) T (ptyped_tfree _ _ _ _ _ H1)
                (IH1 _ n) (IH2 _ n) Hc); intros t Ht; apply HG; simpl; multiset_solver.
  Qed.
End proc.

(** ** The theorems of A.3 *)

Theorem fundamental_proc W Σ p T : Σ ⊢_W p : T → Σ ⊨_W p : T.
Proof.
  intros Hty. refine (proc_gen κ_DF (λ _, True) _ None W Σ p T Hty _); [|done].
  intros W' N Θ t T' c HW' Ht _. exact (fundamental_typed W' N Θ [] (∅, None) t T' c HW' Ht).
Qed.

Theorem live_fundamental_proc W Σ p T : Σ ⊢_W p : T → ⊢▷ p → Σ ⊫_W p : T.
Proof.
  intros Hty Hg. refine (proc_gen κ_L (lguard ∅) _ None W Σ p T Hty Hg).
  intros W' N Θ t T' c HW' Ht Hgt. exact (live_fundamental_typed W' N Θ [] (∅, None) t T' c HW' Ht Hgt).
Qed.

Theorem soundness W p T : ∅ ⊢_W p : T → deadlock_free p.
Proof.
  intros Hty. apply (adequacy W T p (ptyped_strict _ _ _ _ _ Hty)). by apply fundamental_proc.
Qed.

Theorem live_soundness W p T : ∅ ⊢_W p : T → ⊢▷ p →
  deadlock_free p ∧ no_tau_divergence p.
Proof.
  intros Hty Hg. apply (live_adequacy W T p (ptyped_strict _ _ _ _ _ Hty)). by apply live_fundamental_proc.
Qed.

(** One closed thread of the DF judgment, with no creation constraint. *)
Theorem soundness_source W t T : strict W → tfree T → ∅ ; hc_empty ; [] ⊢^(∅, None) _ W t : T →
  deadlock_free (∅, {[+ t +]}).
Proof.
  intros HW HT Ht. apply (adequacy W T _ HW). intros n.
  pose proof (fundamental W ∅ [] (∅, None) t T HW Ht ∅ ∅ ltac:(by intros u Hu) n W ∅ Var (wext_refl _)
                (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty, tenv_erase_empty in H.
  assert (sf_den ∅ ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. destruct (fs_bot None); set_solver. }
  rewrite E in H. apply (sem_p_term κ_DF n W ∅ ∅ ∅ ∅ t T HT); [|exact H].
  constructor; [by rewrite map_union_empty|intros o; rewrite dom_empty_L; set_solver
    |unfold chans_of; rewrite dom_empty_L; set_solver|apply pfree_empty|intros o Ho; set_solver].
Qed.
