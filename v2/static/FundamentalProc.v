(** * The fundamental theorems for processes and soundness (stage S5,
      Appendix A.3)

      fundamental_proc_h      : Σ ⊢_W p : T → Σ ⊨^h_W p : T
      live_fundamental_proc_h : Σ ⊢_W p : T → Σ ⊫^h_W p : T
      soundness_h             : ∅ ⊢_W p : T → deadlock_free p
      live_soundness_h        : ∅ ⊢_W p : T →
                                  deadlock_free p ∧ no_free_divergence p
      soundness_source        : wf W → tfree T → ∅ ; ∅ ; [] ⊢^(∅, None) _ W t : T →
                                  deadlock_free (∅, {[+ t +]})

    One induction on [ptyped] for every cost table whose threads satisfy
    the term-level theorem ([proc_gen]), through [ptyped_sem]
    (static/Hiding.v). A component is read at an acyclic whole world
    that hides to its world ([sem_ptyped_h]), and there at every strict
    world that models it. P-Term holds by [sem_p_term], P-Connect by
    [sem_p_connect], whose side condition [conn] the premises of the
    rule give ([conn_of]). The results hold at every fuel N, ⊢_W is the
    instance N = ∞. An acyclic whole world has a strict world that
    models it, constructively ([dmodels_exists]), so soundness asks
    nothing of W and takes no excluded middle
    (docs/redesign/check-df-acyclic.md). *)

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

    A component typed at a world W is read at some acyclic whole world
    that hides to W ([ptyped_sem], static/Hiding.v). The reading at whole
    worlds is [sem_ptyped_sw]. P-Term gives it by [sem_p_term], P-Connect
    composes it by [sem_p_connect_sw], whose side condition [conn] the
    premises of the rule give ([conn_of]), and an extension of a world
    keeps it ([wmodels_ext]). *)

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

  Lemma proc_gen N η W Σ p T : ptyped N η W Σ p T →
    ∃ W', sworld_wf W' ∧ wok N W' ∧ hides W' (iface Σ T) W ∧ sem_ptyped_sw κ W' Σ p T.
  Proof.
    apply ptyped_sem.
    - intros W' Σ' ΘB C0 t T' c Hp HB HΣ Hpf _ Hd _ Ht Hw _. by eapply sem_p_term_sw.
    - intros W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' H1 H2 HT F1 F2 K1 K2 H12 H1C H2C HC HC1 HC2 _ _ _ _.
      exact (sem_p_connect_sw κ W1 W2 Σ1 ΣC Σ2 (senv_dual ΣC) (C1, E1) (C2, E2) T' HT H1 H2
               (conn_of Σ1 Σ2 ΣC C1 C2 F1 F2 K1 K2 H12 H1C H2C HC HC1 HC2)).
    - intros W1 W2 Σ' p' T' Hx H R HR HS. apply H; [by eapply wmodels_ext|done].
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

(** ** The hidden judgment

    A process typed with hiding is read at a whole world that hides to
    its world ([sem_ptyped_h]): some acyclic W whose order between
    interface points lies in the hidden world, with the component in
    the relation at every strict world that models W. P-Connect reads
    the two interface worlds ([sem_p_connect_h]) once the private
    constants of the two whole worlds are apart, which renaming provides
    ([qren_side], static/Hiding.v). *)
Definition sem_ptyped_h (κ : ctable) (Wi : sworld) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∃ W, sworld_wf W ∧ sacyc W ∧ hides W (iface Σ T) Wi ∧ sem_ptyped_sw κ W Σ p T.

Theorem sem_p_connect_h κ V1 V2 W1 W2 Σ1 ΣC Σ2 p1 p2 T :
  tfree T → sworld_wf V1 → sworld_wf V2 → sacyc V1 → sacyc V2 →
  sem_ptyped_sw κ V1 (Σ1 ∪ ΣC) p1 T → sem_ptyped_sw κ V2 (Σ2 ∪ senv_dual ΣC) p2 TUnit →
  conn Σ1 ΣC p1.1 Σ2 (senv_dual ΣC) p2.1 →
  hides V1 (iface (Σ1 ∪ ΣC) T) W1 → hides V2 (iface (Σ2 ∪ senv_dual ΣC) TUnit) W2 →
  (∀ a, a ∈ sw_consts V1 → a ∉ iface (Σ1 ∪ ΣC) T → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit) →
  (∀ a, a ∈ sw_consts V2 → a ∉ iface (Σ2 ∪ senv_dual ΣC) TUnit → a ∉ sw_consts V1 ∪ iface (Σ1 ∪ ΣC) T) →
  sacyc (W1 ⊔ W2) →
  sem_ptyped_h κ (swrestrict (W1 ⊔ W2) (iface (Σ1 ∪ Σ2) T)) (Σ1 ∪ Σ2) (pconn p1 p2 (chans_of ΣC)) T.
Proof.
  intros HT Hw1 Hw2 HS1 HS2 H1 H2 Hc Hh1 Hh2 Hav1 Hav2 HS.
  destruct (connect_hidden None V1 V2 W1 W2 _ _ (iface (Σ1 ∪ Σ2) T) Hw1 Hw2 Hh1 Hh2 Hav1 Hav2
              (iface_connect _ _ _ _) HS) as [HR Hh].
  exists (V1 ⊔ V2). split_and!; [by apply swjoin_wf|by apply (acyc_join_iff V1 V2 Hw1 Hw2)|exact Hh|].
  by apply (sem_p_connect_sw κ V1 V2 Σ1 ΣC Σ2 (senv_dual ΣC)).
Qed.

Theorem fundamental_proc_h W Σ p T : Σ ⊢_W p : T → sem_ptyped_h κ_DF W Σ p T.
Proof.
  intros Hty. destruct (proc_gen κ_DF (λ W' R' N Θ t T' c HW' Ht HR' HS',
    fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht HR' HS') None (khalf None) W Σ p T Hty) as (W' & ? & ? & ? & ?).
  by exists W'.
Qed.

Theorem live_fundamental_proc_h W Σ p T : Σ ⊢_W p : T → sem_ptyped_h κ_L W Σ p T.
Proof.
  intros Hty. destruct (proc_gen κ_L (λ W' R' N Θ t T' c HW' Ht HR' HS',
    live_fundamental_typed W' R' N Θ [] (∅, None) t T' c HW' Ht HR' HS') None (khalf None) W Σ p T Hty) as (W' & ? & ? & ? & ?).
  by exists W'.
Qed.

Theorem adequacy_h W p T : sem_ptyped_h κ_DF W ∅ p T → deadlock_free p.
Proof.
  intros (W' & Hwf & HW & _ & Hs). destruct (dmodels_exists W' Hwf HW) as (R & HS & HR).
  apply (adequacy R T p). by apply Hs.
Qed.

Theorem live_adequacy_h W p T : sem_ptyped_h κ_L W ∅ p T → deadlock_free p ∧ no_free_divergence p.
Proof.
  intros (W' & Hwf & HW & _ & Hs). destruct (dmodels_exists W' Hwf HW) as (R & HS & HR).
  apply (live_adequacy R T p). by apply Hs.
Qed.

(** Soundness of the hidden judgment. *)
Theorem soundness_h W p T : ∅ ⊢_W p : T → deadlock_free p.
Proof. intros Hty. exact (adequacy_h W p T (fundamental_proc_h W ∅ p T Hty)). Qed.

Theorem live_soundness_h W p T : ∅ ⊢_W p : T → deadlock_free p ∧ no_free_divergence p.
Proof. intros Hty. exact (live_adequacy_h W p T (live_fundamental_proc_h W ∅ p T Hty)). Qed.
