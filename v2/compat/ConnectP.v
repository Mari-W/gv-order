(** * P-Connect (stage S4)

    Strong induction on the level. At a level S n, an induction over the
    steps of p1 (closed under fusion), and inside it one over the steps
    of p2, establish the clauses of every fusion of the composite: a
    fusion of the composite is a composite of fusions of the components
    over a larger cut (compat/ConnectFuse.v), whose clauses are
    [pc_clauses] (compat/ConnectExtMsg.v). *)

From GV Require Export compat.ConnectExtMsg compat.ConnectFuse.
From GV Require Import fuel.FuelMono.

Section wrapper.
  Context (κ : ctable) (n : nat) (T : ty) (HT : prim T).
  Context (IH : ∀ j W, j < S n → ConnL κ j W T).

  (** The predicate of the induction on p1. *)
  Local Definition Φ1 : prel := λ W Σa U p1,
    U = T → ∀ Σ1 ΣC Σ2 ΣD p2, Σa = Σ1 ∪ ΣC → Prel κ (S n) W (Σ2 ∪ ΣD) TUnit p2 →
      conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ (S n) W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

  Local Abbreviation X1 := (λ W Σ U p, Prel κ (S n) W Σ U p ∧ Φfuse Φ1 W Σ U p).

  Local Abbreviation PB1 W Σ p := (Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W Σ T p).

  (** The predicate of the induction on p2. *)
  Local Definition Φ2 : prel := λ W Σb U p2,
    U = TUnit → ∀ Σ1 ΣC Σ2 ΣD p1, Σb = Σ2 ∪ ΣD → PB1 W (Σ1 ∪ ΣC) p1 →
      conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ (S n) W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

  Local Abbreviation X2 := (λ W Σ U p, Prel κ (S n) W Σ U p ∧ Φfuse Φ2 W Σ U p).

  Local Lemma Pbody_P (Φ : prel) W Σ U p :
    Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (λ W Σ U p, Prel κ (S n) W Σ U p ∧ Φ W Σ U p) W Σ U p →
    Prel κ (S n) W Σ U p.
  Proof.
    intros H. apply Prel_S_iff. revert H.
    apply Pbody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? H; exact H|intros ? ? ? ? H; exact H|].
    intros ? ? ? [H _]; exact H.
  Qed.

  Local Lemma Pbody_later X W W' Σ U p : W ⊑ W' →
    Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X W Σ U p →
    Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X W' Σ U p.
  Proof. intros HW H W1 HW1. apply H. by eapply wext_trans. Qed.

  (** The clauses of every fusion of the composite. *)
  Local Lemma step W Σ1 ΣC Σ2 ΣD p1 p2 :
    PB1 W (Σ1 ∪ ΣC) p1 →
    Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W (Σ2 ∪ ΣD) TUnit p2 →
    conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ (S n) W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).
  Proof.
    intros B1 B2 Hc. apply Prel_S_iff. intros W1 HW1 HS1 h D Hh.
    pose proof (Pbody_P _ _ _ _ _ B1) as P1. pose proof (Pbody_P _ _ _ _ _ B2) as P2.
    pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs.
    pose proof (fs_sym _ _ _ _ _ _ _ _ _ Hc Hh) as Hhs.
    pose proof (fs_conn _ _ _ _ _ _ _ _ _ Hc Hh) as Hc'. cbv zeta in Hc'.
    pose proof (fs_iface _ _ _ _ _ _ Hc h D _ Hh) as Hif.
    pose proof (fs_chans _ _ _ _ _ _ Hc h D _ Hh) as Hch.
    pose proof (fs_ok1 _ _ _ _ _ _ Hc h D _ Hh p1 eq_refl) as Hok1.
    pose proof (fs_ok1 _ _ _ _ _ _ Hcs h D _ Hhs p2 eq_refl) as Hok2.
    set (Σf := sdrop D (kren h (Σ1 ∪ Σ2))) in *.
    set (D1 := dside h Σ1 D) in *. set (D2 := dside h Σ2 D) in *.
    set (E1 := sdrop D1 (kren h (Σ1 ∪ ΣC))) in *. set (E2 := sdrop D2 (kren h (Σ2 ∪ ΣD))) in *.
    assert (E1 = ConnectSplit.fin Σf E1 ∪ fout Σf E1) as EE1 by (symmetry; apply fin_fout).
    assert (E2 = ConnectSplit.fin Σf E2 ∪ fout Σf E2) as EE2 by (symmetry; apply fin_fout).
    assert (pfuse h D (pconn p1 p2 (chans_of ΣC)) =
      pconn (pfuse h D1 p1) (pfuse h D2 p2) (chans_of (fout Σf E1))) as Ep.
    { unfold pfuse, pconn. simpl. rewrite emapE_disj_union. f_equal. exact Hch. }
    rewrite Ep.
    (* the clauses of the two fused components *)
    assert (Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1
      (ConnectSplit.fin Σf E1 ∪ fout Σf E1) T (pfuse h D1 p1)) as C1.
    { rewrite <-EE1. by apply B1. }
    assert (Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1
      (ConnectSplit.fin Σf E2 ∪ fout Σf E2) TUnit (pfuse h D2 p2)) as C2.
    { rewrite <-EE2. by apply B2. }
    assert (∀ j, j < S n → ConnL κ j W1 T) as L by (intros j Hj; by apply IH).
    assert (∀ W Σ U p, X1 W Σ U p → Prel κ (S n) W Σ U p) as X1P by (by intros ? ? ? ? [? _]).
    assert (∀ W Σ U p, X2 W Σ U p → Prel κ (S n) W Σ U p) as X2P by (by intros ? ? ? ? [? _]).
    assert (∀ h' D', fuse_ok h' D' (ConnectSplit.fin Σf E1 ∪ fout Σf E1) (pfuse h D1 p1) →
      Prel κ (S n) W1 (sdrop D' (kren h' (ConnectSplit.fin Σf E1 ∪ fout Σf E1))) T (pfuse h' D' (pfuse h D1 p1))) as HP1.
    { intros h' D' Hh'. apply Prel_fuse; [done|]. rewrite <-EE1. apply Prel_fuse; [done|].
      by eapply Prel_mono. }
    assert (∀ h' D', fuse_ok h' D' (ConnectSplit.fin Σf E2 ∪ fout Σf E2) (pfuse h D2 p2) →
      Prel κ (S n) W1 (sdrop D' (kren h' (ConnectSplit.fin Σf E2 ∪ fout Σf E2))) TUnit (pfuse h' D' (pfuse h D2 p2))) as HP2.
    { intros h' D' Hh'. apply Prel_fuse; [done|]. rewrite <-EE2. apply Prel_fuse; [done|].
      by eapply Prel_mono. }
    assert (∀ p1' Σa h' D' Σ1' ΣC' Σ2' ΣD' p2', X1 W1 Σa T p1' → fuse_ok h' D' Σa p1' →
      sdrop D' (kren h' Σa) = Σ1' ∪ ΣC' → Prel κ (S n) W1 (Σ2' ∪ ΣD') TUnit p2' →
      conn Σ1' ΣC' (pfuse h' D' p1').1 Σ2' ΣD' p2'.1 →
      Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h' D' p1') p2' (chans_of ΣC'))) as G1.
    { intros p1' Σa h' D' Σ1' ΣC' Σ2' ΣD' p2' [_ HΦ] Hh' EΣ HP Hcc. exact (HΦ h' D' Hh' eq_refl Σ1' ΣC' Σ2' ΣD' p2' EΣ HP Hcc). }
    assert (∀ p2' Σb h' D' Σ1' ΣC' Σ2' ΣD' h1 D1', X2 W1 Σb TUnit p2' → fuse_ok h' D' Σb p2' →
      sdrop D' (kren h' Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1' (ConnectSplit.fin Σf E1 ∪ fout Σf E1) (pfuse h D1 p1) →
      sdrop D1' (kren h1 (ConnectSplit.fin Σf E1 ∪ fout Σf E1)) = Σ1' ∪ ΣC' →
      conn Σ1' ΣC' (pfuse h1 D1' (pfuse h D1 p1)).1 Σ2' ΣD' (pfuse h' D' p2').1 →
      Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1' (pfuse h D1 p1)) (pfuse h' D' p2') (chans_of ΣC'))) as G2.
    { intros p2' Σb h' D' Σ1' ΣC' Σ2' ΣD' h1 D1' [_ HΦ] Hh' EΣ Hh1 EΣ1 Hcc.
      apply (HΦ h' D' Hh' eq_refl Σ1' ΣC' Σ2' ΣD' _ EΣ); [|done].
      rewrite <-EΣ1. apply Pbody_fuse; [done|]. rewrite <-EE1. apply Pbody_fuse; [done|].
      by eapply Pbody_later. }
    pose proof (pc_clauses κ n W1 HS1 T HT X1 X2 (ConnectSplit.fin Σf E1) (fout Σf E1)
      (ConnectSplit.fin Σf E2) (fout Σf E2) (pfuse h D1 p1) (pfuse h D2 p2) Hc' C1 C2 L X1P X2P HP1 HP2 G1 G2) as R.
    by rewrite Hif in R.
  Qed.

  Local Lemma ind2 W Σb U p2 : Prel κ (S n) W Σb U p2 → Φfuse Φ2 W Σb U p2.
  Proof.
    apply Prel_S_ind_fuse. intros W' Σb' U' p2' B2 -> Σ1 ΣC Σ2 ΣD p1 -> B1 Hc.
    by apply (step W' Σ1 ΣC Σ2 ΣD).
  Qed.

  Local Lemma ind1 W Σa U p1 : Prel κ (S n) W Σa U p1 → Φfuse Φ1 W Σa U p1.
  Proof.
    apply Prel_S_ind_fuse. intros W' Σa' U' p1' B1 -> Σ1 ΣC Σ2 ΣD p2 -> HP2 Hc.
    exact (Φfuse_id _ _ _ _ _ (ind2 _ _ _ _ HP2) eq_refl Σ1 ΣC Σ2 ΣD p1' eq_refl B1 Hc).
  Qed.

  Lemma conn_level W : ConnL κ (S n) W T.
  Proof.
    intros Σ1 ΣC Σ2 ΣD p1 p2 HP1 HP2 Hc.
    exact (Φfuse_id _ _ _ _ _ (ind1 _ _ _ _ HP1) eq_refl Σ1 ΣC Σ2 ΣD p2 eq_refl HP2 Hc).
  Qed.
End wrapper.

Lemma conn_all κ T : prim T → ∀ j W, ConnL κ j W T.
Proof.
  intros HT j. induction (lt_wf j) as [j _ IH]. intros W. destruct j as [|n].
  - intros ? ? ? ? ? ? _ _ _. apply Prel_0.
  - apply conn_level; [done|]. intros j' W' Hj. by apply IH.
Qed.

(** P-Connect: two components in P over a cut compose, at the join of
    their worlds. *)
Theorem sem_p_connect κ n W1 W2 Σ1 ΣC Σ2 ΣD p1 p2 T :
  prim T →
  p1 ∈ P[κ]^W1 _ n⟦Σ1 ∪ ΣC ⊢ T⟧ → p2 ∈ P[κ]^W2 _ n⟦Σ2 ∪ ΣD ⊢ TUnit⟧ →
  conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 →
  pconn p1 p2 (chans_of ΣC) ∈ P[κ]^(W1 ⊔ W2) _ n⟦Σ1 ∪ Σ2 ⊢ T⟧.
Proof.
  intros HT HP1 HP2 Hc. refine (conn_all κ T HT n (W1 ⊔ W2) Σ1 ΣC Σ2 ΣD p1 p2 _ _ Hc).
  - eapply Prel_mono; [apply wext_join_l|done].
  - eapply Prel_mono; [apply wext_join_r|done].
Qed.

(** P-Join: the same composite. The rules P-Join and P-Connect differ
    only in their side conditions on worlds, which agree by
    [p_join_iff_connect], and the semantic lemma asks none of them. *)
Theorem sem_p_join κ n W1 W2 Σ1 ΣC Σ2 ΣD p1 p2 T :
  prim T →
  p1 ∈ P[κ]^W1 _ n⟦Σ1 ∪ ΣC ⊢ T⟧ → p2 ∈ P[κ]^W2 _ n⟦Σ2 ∪ ΣD ⊢ TUnit⟧ →
  conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 →
  pconn p1 p2 (chans_of ΣC) ∈ P[κ]^(W1 ⊔ W2) _ n⟦Σ1 ∪ Σ2 ⊢ T⟧.
Proof. apply sem_p_connect. Qed.
