(** * P-Connect (stage S4)

    Well-founded induction on the level. At a level n above 0, an
    induction over the steps of p1, and inside it one over the steps of
    p2, establish the clauses of the composite ([pc_clauses],
    compat/ConnectExtMsg.v). Both inductions are closed under fusion
    ([Prel_ind_fuse], compat/Fusion.v), because a link of one component
    joins two cut ends of the other (compat/ConnectLink.v). *)

From GV Require Export compat.ConnectExtMsg.
From GV Require Import fuel.FuelMono.

Section wrapper.
  Context (κ : ctable) (n : Ix) (T : ty) (HT : tfree T).
  Context (Hn : olt ozero n) (IH : ∀ j W, olt j n → ConnL κ j W T).

  (** The predicate of the induction on p1. *)
  Local Definition Φ1 : prel := λ W Σa U p1,
    U = T → ∀ Σ1 ΣC Σ2 ΣD p2, Σa = Σ1 ∪ ΣC → Prel κ n W (Σ2 ∪ ΣD) TUnit p2 →
      conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ n W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

  Local Abbreviation X1 := (λ W Σ U p, Prel κ n W Σ U p ∧ Φfuse Φ1 W Σ U p).

  Local Abbreviation PB1 W Σ p := (Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X1 W Σ T p).

  (** The predicate of the induction on p2. *)
  Local Definition Φ2 : prel := λ W Σb U p2,
    U = TUnit → ∀ Σ1 ΣC Σ2 ΣD p1, Σb = Σ2 ∪ ΣD → PB1 W (Σ1 ∪ ΣC) p1 →
      conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ n W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

  Local Abbreviation X2 := (λ W Σ U p, Prel κ n W Σ U p ∧ Φfuse Φ2 W Σ U p).

  Local Lemma Pbody_P (Φ : prel) W Σ U p :
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) (λ W Σ U p, Prel κ n W Σ U p ∧ Φ W Σ U p) W Σ U p →
    Prel κ n W Σ U p.
  Proof.
    intros H. apply Prel_iff. intros _. revert H.
    apply Pbody_mono; [intros; reflexivity|intros ? ? ? ? ? ? H; exact H|intros ? ? ? ? H; exact H|].
    intros ? ? ? [H _]; exact H.
  Qed.

  Local Lemma Pbody_later X W W' Σ U p : W ⊑ W' →
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X W Σ U p →
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X W' Σ U p.
  Proof. intros HW H W1 HW1. apply H. by eapply wext_trans. Qed.

  (** Φ1 and Φ2 read the interface only up to ≈. *)
  Local Lemma Φ1_conv W Σ Σ' U p : senv_eqv Σ Σ' → Φ1 W Σ U p → Φ1 W Σ' U p.
  Proof.
    intros HΣ H -> Σ1 ΣC Σ2 ΣD p2 -> HP Hc.
    destruct (senv_eqv_split Σ1 ΣC Σ (senv_eqv_sym _ _ HΣ)) as (Σ1o & ΣCo & -> & _ & E1 & EC).
    { by destruct Hc. }
    rewrite (chans_of_conv _ _ EC).
    eapply Prel_conv; [apply senv_eqv_union; [exact (senv_eqv_sym _ _ E1)|apply senv_eqv_refl]|].
    apply (H eq_refl Σ1o ΣCo Σ2 ΣD p2 eq_refl HP).
    eapply conn_conv; [exact (senv_eqv_sym _ _ E1)|exact (senv_eqv_sym _ _ EC)|exact Hc].
  Qed.

  Local Lemma Φ2_conv W Σ Σ' U p : senv_eqv Σ Σ' → Φ2 W Σ U p → Φ2 W Σ' U p.
  Proof.
    intros HΣ H -> Σ1 ΣC Σ2 ΣD p1 -> B1 Hc.
    destruct (senv_eqv_split Σ2 ΣD Σ (senv_eqv_sym _ _ HΣ)) as (Σ2o & ΣDo & -> & _ & E2 & ED).
    { by destruct Hc. }
    eapply Prel_conv; [apply senv_eqv_union; [apply senv_eqv_refl|exact (senv_eqv_sym _ _ E2)]|].
    apply (H eq_refl Σ1 ΣC Σ2o ΣDo p1 eq_refl B1).
    apply conn_sym. eapply conn_conv; [exact (senv_eqv_sym _ _ E2)|exact (senv_eqv_sym _ _ ED)|].
    by apply conn_sym.
  Qed.

  (** The clauses of the composite. *)
  Local Lemma step W Σ1 ΣC Σ2 ΣD p1 p2 :
    PB1 W (Σ1 ∪ ΣC) p1 →
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X2 W (Σ2 ∪ ΣD) TUnit p2 →
    conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ n W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).
  Proof.
    intros B1 B2 Hc. apply Prel_iff. intros _ W1 HW1.
    pose proof (Pbody_P _ _ _ _ _ B1) as P1. pose proof (Pbody_P _ _ _ _ _ B2) as P2.
    assert (∀ W Σ U p, X1 W Σ U p → Prel κ n W Σ U p) as X1P by (by intros ? ? ? ? [? _]).
    assert (∀ W Σ U p, X2 W Σ U p → Prel κ n W Σ U p) as X2P by (by intros ? ? ? ? [? _]).
    assert (∀ j W', olt j n → ConnL κ j W' T) as L by (intros j W' Hj; by apply IH).
    assert (∀ h D, fuse_ok h D (Σ1 ∪ ΣC) p1 →
      Prel κ n W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D p1)) as HP1.
    { intros h D Hh. apply Prel_fuse; [done|exact (conn_fside1 _ _ _ _ _ _ p1 D T HT eq_refl Hc)|].
      by eapply Prel_mono. }
    assert (∀ h D, fuse_ok h D (Σ2 ∪ ΣD) p2 →
      Prel κ n W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D p2)) as HP2.
    { intros h D Hh. apply Prel_fuse; [done|exact (conn_fside2 _ _ _ _ _ _ p2 D TUnit tfree_unit eq_refl Hc)|].
      by eapply Prel_mono. }
    assert (∀ W' p1' Σa h Σ1' ΣC' Σ2' ΣD' p2', W1 ⊑ W' → X1 W' Σa T p1' → fuse_ok h ∅ Σa p1' →
      sdrop ∅ (kren h Σa) = Σ1' ∪ ΣC' → Prel κ n W' (Σ2' ∪ ΣD') TUnit p2' →
      conn Σ1' ΣC' (pfuse h ∅ p1').1 Σ2' ΣD' p2'.1 →
      Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h ∅ p1') p2' (chans_of ΣC'))) as G1.
    { intros W' p1' Σa h Σ1' ΣC' Σ2' ΣD' p2' _ [_ HΦ] Hh EΣ HP Hcc.
      assert (fside ∅ Σa T p1') as Hs.
      { rewrite sdrop_empty in EΣ. rewrite pfuse_empty in Hcc. exact (ren_fside1 h Σa T p1' _ _ _ _ _ HT Hh EΣ Hcc). }
      refine (HΦ h ∅ (pfuse h ∅ p1') (Σ1' ∪ ΣC') Hs (gfuse_pfuse h ∅ Σa p1' Hh) _ eq_refl Σ1' ΣC' Σ2' ΣD' p2' eq_refl HP Hcc).
      rewrite EΣ. apply senv_eqv_refl. }
    assert (∀ W' p2' Σb h Σ1' ΣC' Σ2' ΣD' h1 D1, W1 ⊑ W' → X2 W' Σb TUnit p2' → fuse_ok h ∅ Σb p2' →
      sdrop ∅ (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) p1 →
      sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
      conn Σ1' ΣC' (pfuse h1 D1 p1).1 Σ2' ΣD' (pfuse h ∅ p2').1 →
      Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 p1) (pfuse h ∅ p2') (chans_of ΣC'))) as G2.
    { intros W' p2' Σb h Σ1' ΣC' Σ2' ΣD' h1 D1 HW' [_ HΦ] Hh EΣ Hh1 EΣ1 Hcc.
      assert (fside ∅ Σb TUnit p2') as Hs.
      { rewrite sdrop_empty in EΣ. rewrite pfuse_empty in Hcc. exact (ren_fside2 h Σb TUnit p2' _ _ _ _ _ tfree_unit Hh EΣ Hcc). }
      refine (HΦ h ∅ (pfuse h ∅ p2') (Σ2' ∪ ΣD') Hs (gfuse_pfuse h ∅ Σb p2' Hh) _ eq_refl Σ1' ΣC' Σ2' ΣD' _ eq_refl _ Hcc).
      - rewrite EΣ. apply senv_eqv_refl.
      - rewrite <-EΣ1. apply (Pbody_gfuse κ n _ W' (Σ1 ∪ ΣC) T p1 _ h1 D1); [done|apply Φfuse_closed|exact X1P|exact (conn_fside1 _ _ _ _ _ _ p1 D1 T HT eq_refl Hc)|by apply gfuse_pfuse|].
        eapply Pbody_later; [|exact B1]. by eapply wext_trans. }
    exact (pc_clauses _ _ _ _ _ _ _ _ _ _ _ _
      (CCtx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD p1 p2 Hn HT Hc (B1 W1 HW1) (B2 W1 HW1) L X1P X2P HP1 HP2 G1 G2)).
  Qed.

  Local Lemma ind2 W Σb U p2 : Prel κ n W Σb U p2 → Φfuse Φ2 W Σb U p2.
  Proof.
    apply Prel_ind_fuse; [done|exact Φ2_conv|]. intros W' Σb' U' p2' B2 -> Σ1 ΣC Σ2 ΣD p1 -> B1 Hc.
    by apply (step W' Σ1 ΣC Σ2 ΣD).
  Qed.

  Local Lemma ind1 W Σa U p1 : Prel κ n W Σa U p1 → Φfuse Φ1 W Σa U p1.
  Proof.
    apply Prel_ind_fuse; [done|exact Φ1_conv|]. intros W' Σa' U' p1' B1 -> Σ1 ΣC Σ2 ΣD p2 -> HP2 Hc.
    exact (Φfuse_id _ _ _ _ _ (conn_fside2 _ _ _ _ _ _ p2 ∅ TUnit tfree_unit eq_refl Hc) (ind2 _ _ _ _ HP2)
      eq_refl Σ1 ΣC Σ2 ΣD p1' eq_refl B1 Hc).
  Qed.

  Lemma conn_level W : ConnL κ n W T.
  Proof.
    intros Σ1 ΣC Σ2 ΣD p1 p2 HP1 HP2 Hc.
    exact (Φfuse_id _ _ _ _ _ (conn_fside1 _ _ _ _ _ _ p1 ∅ T HT eq_refl Hc) (ind1 _ _ _ _ HP1)
      eq_refl Σ1 ΣC Σ2 ΣD p2 eq_refl HP2 Hc).
  Qed.
End wrapper.

Lemma conn_all κ T : tfree T → ∀ j W, ConnL κ j W T.
Proof.
  intros HT j. induction j as [j IH] using oind. intros W Σ1 ΣC Σ2 ΣD p1 p2 HP1 HP2 Hc.
  apply Prel_iff. intros Hj0.
  pose proof (conn_level κ j T HT Hj0 (λ j' W' Hj', IH j' Hj' W') W Σ1 ΣC Σ2 ΣD p1 p2 HP1 HP2 Hc) as H.
  by apply Prel_iff in H.
Qed.

(** P-Connect: two components in P over a cut compose, at one ranked
    world. The static worlds of the two components meet in a ranked
    world that models their join (static/FundamentalProc.v). *)
Theorem sem_p_connect κ n W Σ1 ΣC Σ2 ΣD p1 p2 T :
  tfree T →
  p1 ∈ P[κ]^W _ n⟦Σ1 ∪ ΣC ⊢ T⟧ → p2 ∈ P[κ]^W _ n⟦Σ2 ∪ ΣD ⊢ TUnit⟧ →
  conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 →
  pconn p1 p2 (chans_of ΣC) ∈ P[κ]^W _ n⟦Σ1 ∪ Σ2 ⊢ T⟧.
Proof. intros HT HP1 HP2 Hc. exact (conn_all κ T HT n W Σ1 ΣC Σ2 ΣD p1 p2 HP1 HP2 Hc). Qed.
