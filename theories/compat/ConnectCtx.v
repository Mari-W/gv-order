(** * P-Connect, the context of the step clause (stage S4)

    [ConnL κ j W T] is P-Connect at level j. [cctx] packs what the step
    clause of the composite knows at a level n above 0: T is primitive, the two components q1 and q2 are connected
    over the cut ([conn]), their clauses at n over X1 and X2, P-Connect
    below n ([L]), X1 and X2 inside P, every fusion of a component in P
    ([HP1], [HP2]), and the composite of a fused step of one component
    with the other in P ([G1], [G2]), in W1 and in every world a τ step
    grows W1 to ([G1W], [G2W]). The sections of
    compat/ConnectSteps.v, ConnectCross.v, ConnectLink.v, ConnectTau.v,
    ConnectExt.v and ConnectExtMsg.v take one [cctx] and name its fields
    by [Let]. *)

From GV Require Export compat.Fusion compat.ConnectSplit.

(** ** Side conditions of a fusion of a component *)

(** A component of a cut meets the side conditions of [Prel_gfuse]. *)
Lemma conn_fside1 Σ1 ΣC Σ2 ΣD (C1 C2 : gset chan) (p1 : proc) D U : tfree U → p1.1 = C1 →
  conn Σ1 ΣC C1 Σ2 ΣD C2 → fside D (Σ1 ∪ ΣC) U p1.
Proof.
  intros HU <- Hc. destruct Hc as [_ _ _ Hf1 _ HfC _ H1C _ _ HC1 _]. split_and!; [|done|].
  - rewrite chans_of_union. set_solver.
  - by apply pfree_union.
Qed.

Lemma conn_fside2 Σ1 ΣC Σ2 ΣD (C1 C2 : gset chan) (p2 : proc) D U : tfree U → p2.1 = C2 →
  conn Σ1 ΣC C1 Σ2 ΣD C2 → fside D (Σ2 ∪ ΣD) U p2.
Proof. intros HU E Hc. apply (conn_fside1 Σ2 ΣD Σ1 ΣC C2 C1 p2 D U HU E). by apply conn_sym. Qed.

(** The side conditions pass to a smaller interface. *)
Lemma fside_sub D D' (Σ Σ' : senv) T (p p' : proc) : fside D Σ T p → dom Σ' ⊆ dom Σ → p'.1 = p.1 → fside D' Σ' T p'.
Proof.
  intros (Hd & HT & Hf) Hs E. split_and!; [|done|].
  - rewrite E. intros c H1 H2. apply chans_of_elem in H2 as (u & Hu & <-). apply (Hd (ech u) H1).
    apply chans_of_elem. exists u. split; [set_solver|done].
  - intros o Ho Hdo. apply (Hf o); set_solver.
Qed.

(** A renaming reflects freedom of dual pairs. *)
Lemma pfree_kren h D (Σ : senv) p : fuse_ok h D Σ p → pfree (kren h Σ) → pfree Σ.
Proof.
  intros Hh Hf o Ho Hd. pose proof (fuse_ok_kinj _ _ _ _ Hh) as Hk. destruct Hh as (Hdc & _).
  apply (Hf (h o)); rewrite (kren_dom _ _ Hk); [by apply elem_of_map_2|].
  rewrite <-Hdc. by apply elem_of_map_2.
Qed.

(** A renamed component whose composite satisfies [conn] meets the side
    conditions of [Prel_gfuse]. *)
Lemma ren_fside1 h (Σa : senv) U (p : proc) Σ1' ΣC' Σ2' ΣD' C2 : tfree U →
  fuse_ok h ∅ Σa p → kren h Σa = Σ1' ∪ ΣC' → conn Σ1' ΣC' (pmap h p).1 Σ2' ΣD' C2 →
  fside ∅ Σa U p.
Proof.
  intros HU Hh EΣ Hc. pose proof (fuse_ok_kinj _ _ _ _ Hh) as Hk.
  pose proof (conn_fside1 _ _ _ _ _ _ (pmap h p) ∅ U HU eq_refl Hc) as (Hd' & _ & Hf').
  rewrite <-EΣ in Hd', Hf'. split_and!; [|done|by eapply pfree_kren].
  intros c Hc1 Hc2. apply chans_of_elem in Hc2 as (u & Hu & <-).
  apply (Hd' (gch h (ech u))); [simpl; by apply elem_of_map_2|].
  rewrite <-(ech_gch h u (proj1 Hh)). apply chans_of_elem. exists (h u). split; [|done].
  rewrite (kren_dom _ _ Hk). by apply elem_of_map_2.
Qed.

Lemma ren_fside2 h (Σb : senv) U (p : proc) Σ1' ΣC' Σ2' ΣD' C1 : tfree U →
  fuse_ok h ∅ Σb p → kren h Σb = Σ2' ∪ ΣD' → conn Σ1' ΣC' C1 Σ2' ΣD' (pmap h p).1 →
  fside ∅ Σb U p.
Proof. intros HU Hh EΣ Hc. apply (ren_fside1 h Σb U p Σ2' ΣD' Σ1' ΣC' C1); [done|done|done|by apply conn_sym]. Qed.

(** [conn] reads the interface only up to ≈. *)
Lemma conn_conv Σ1 ΣC Σ2 ΣD C1 C2 Σ1' ΣC' :
  senv_eqv Σ1 Σ1' → senv_eqv ΣC ΣC' → conn Σ1' ΣC' C1 Σ2 ΣD C2 → conn Σ1 ΣC C1 Σ2 ΣD C2.
Proof.
  intros E1 EC [Hd1 Hd2 [Hcd Hct] Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
  rewrite <-!(chans_of_conv _ _ E1), <-!(chans_of_conv _ _ EC) in *.
  constructor; try done.
  - apply map_disjoint_dom. rewrite (senv_eqv_dom _ _ E1), (senv_eqv_dom _ _ EC). by apply map_disjoint_dom.
  - split.
    + intros o. rewrite Hcd. by rewrite (senv_eqv_dom _ _ EC).
    + intros o S x Ho. destruct (senv_eqv_lookup _ _ _ _ _ EC Ho) as (S0 & Ho' & HS).
      destruct (Hct o S0 x Ho') as (S' & L & Hsd). exists S'. split; [done|].
      eapply sdual_conv; [exact Hsd|by apply seqv_sym|apply seqv_refl].
  - intros o. rewrite (senv_eqv_dom _ _ E1). apply Hf1.
  - intros o. rewrite (senv_eqv_dom _ _ EC). apply HfC.
Qed.

(** A synchronization of cost κ(give) + κ(take) at level n reads both
    sides at every level j with j + κ(give) + κ(take) ≤ n. *)
Lemma oadd_le_part j a b n : ole (oadd j (a + b)) n → ole (oadd j a) n ∧ ole (oadd j b) n.
Proof. intros H. split; (eapply ole_trans; [|exact H]); apply oadd_mono_r; lia. Qed.

Lemma sync_lt κ j n : ole (oadd j (c_give κ + c_take κ)) n → olt j n.
Proof. apply oadd_lt. pose proof (c_take_pos κ). lia. Qed.

Definition ConnL (κ : ctable) (j : Ix) (W : world) (T : ty) : Prop :=
  ∀ Σ1 ΣC Σ2 ΣD p1 p2, Prel κ j W (Σ1 ∪ ΣC) T p1 → Prel κ j W (Σ2 ∪ ΣD) TUnit p2 →
    conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ j W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

(** One constructor with named premises, as [sth] (compat/PTerm.v). A
    [Record] does not parse here, because the typing notation
    Θ ; Γ ; Δ ⊢ … makes ';' a term token. *)
Inductive cctx (κ : ctable) (n : Ix) (W1 : world) (T : ty) (X1 X2 : prel)
    (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) : Prop :=
  | CCtx
      (cc_Hn : olt ozero n)
      (cc_HT : tfree T)
      (cc_Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1)
      (cc_H1 : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) X1 W1 (Σ1 ∪ ΣC) T q1)
      (cc_H2 : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) X2 W1 (Σ2 ∪ ΣD) TUnit q2)
      (cc_LW : ∀ j W', olt j n → ConnL κ j W' T)
      (cc_X1P : ∀ W Σ T p, X1 W Σ T p → Prel κ n W Σ T p)
      (cc_X2P : ∀ W Σ T p, X2 W Σ T p → Prel κ n W Σ T p)
      (cc_HP1 : ∀ h D, fuse_ok h D (Σ1 ∪ ΣC) q1 →
        Prel κ n W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D q1))
      (cc_HP2 : ∀ h D, fuse_ok h D (Σ2 ∪ ΣD) q2 →
        Prel κ n W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D q2))
      (cc_G1W0 : ∀ W' p1' Σa h Σ1' ΣC' Σ2' ΣD' p2', W1 ⊑ W' → X1 W' Σa T p1' → fuse_ok h ∅ Σa p1' →
        sdrop ∅ (kren h Σa) = Σ1' ∪ ΣC' → Prel κ n W' (Σ2' ∪ ΣD') TUnit p2' →
        conn Σ1' ΣC' (pfuse h ∅ p1').1 Σ2' ΣD' p2'.1 →
        Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h ∅ p1') p2' (chans_of ΣC')))
      (cc_G2W0 : ∀ W' p2' Σb h Σ1' ΣC' Σ2' ΣD' h1 D1, W1 ⊑ W' → X2 W' Σb TUnit p2' → fuse_ok h ∅ Σb p2' →
        sdrop ∅ (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
        sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
        conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h ∅ p2').1 →
        Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h ∅ p2') (chans_of ΣC'))).

Section cctx_proj.
  Context κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 (H : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Lemma cc_Hn : olt ozero n.
  Proof. by destruct H. Qed.
  Lemma cc_HT : tfree T.
  Proof. by destruct H. Qed.
  Lemma cc_Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1.
  Proof. by destruct H. Qed.
  Lemma cc_H1 : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) X1 W1 (Σ1 ∪ ΣC) T q1.
  Proof. by destruct H. Qed.
  Lemma cc_H2 : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) X2 W1 (Σ2 ∪ ΣD) TUnit q2.
  Proof. by destruct H. Qed.
  Lemma cc_LW : ∀ j W', olt j n → ConnL κ j W' T.
  Proof. by destruct H. Qed.
  Lemma cc_L : ∀ j, olt j n → ConnL κ j W1 T.
  Proof. intros j Hj. by apply cc_LW. Qed.
  Lemma cc_X1P : ∀ W Σ T p, X1 W Σ T p → Prel κ n W Σ T p.
  Proof. by destruct H. Qed.
  Lemma cc_X2P : ∀ W Σ T p, X2 W Σ T p → Prel κ n W Σ T p.
  Proof. by destruct H. Qed.
  Lemma cc_HP1 : ∀ h D, fuse_ok h D (Σ1 ∪ ΣC) q1 →
    Prel κ n W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D q1).
  Proof. by destruct H. Qed.
  Lemma cc_HP2 : ∀ h D, fuse_ok h D (Σ2 ∪ ΣD) q2 →
    Prel κ n W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D q2).
  Proof. by destruct H. Qed.
  Lemma cc_G1 : ∀ p1' Σa h Σ1' ΣC' Σ2' ΣD' p2', X1 W1 Σa T p1' → fuse_ok h ∅ Σa p1' →
    sdrop ∅ (kren h Σa) = Σ1' ∪ ΣC' → Prel κ n W1 (Σ2' ∪ ΣD') TUnit p2' →
    conn Σ1' ΣC' (pfuse h ∅ p1').1 Σ2' ΣD' p2'.1 →
    Prel κ n W1 (Σ1' ∪ Σ2') T (pconn (pfuse h ∅ p1') p2' (chans_of ΣC')).
  Proof. destruct H. intros. eapply cc_G1W0; [apply wext_refl|done..]. Qed.
  Lemma cc_G1W : ∀ W' p1' Σa h Σ1' ΣC' Σ2' ΣD' p2', W1 ⊑ W' → X1 W' Σa T p1' → fuse_ok h ∅ Σa p1' →
    sdrop ∅ (kren h Σa) = Σ1' ∪ ΣC' → Prel κ n W' (Σ2' ∪ ΣD') TUnit p2' →
    conn Σ1' ΣC' (pfuse h ∅ p1').1 Σ2' ΣD' p2'.1 →
    Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h ∅ p1') p2' (chans_of ΣC')).
  Proof. by destruct H. Qed.
  Lemma cc_G2 : ∀ p2' Σb h Σ1' ΣC' Σ2' ΣD' h1 D1, X2 W1 Σb TUnit p2' → fuse_ok h ∅ Σb p2' →
    sdrop ∅ (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
    sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
    conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h ∅ p2').1 →
    Prel κ n W1 (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h ∅ p2') (chans_of ΣC')).
  Proof. destruct H. intros. eapply cc_G2W0; [apply wext_refl|done..]. Qed.
  Lemma cc_G2W : ∀ W' p2' Σb h Σ1' ΣC' Σ2' ΣD' h1 D1, W1 ⊑ W' → X2 W' Σb TUnit p2' → fuse_ok h ∅ Σb p2' →
    sdrop ∅ (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
    sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
    conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h ∅ p2').1 →
    Prel κ n W' (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h ∅ p2') (chans_of ΣC')).
  Proof. by destruct H. Qed.
End cctx_proj.
Arguments cc_Hn {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_HT {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_Hc {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_H1 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_H2 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_L {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_X1P {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_X2P {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_HP1 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_HP2 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_G1 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_G2 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_G1W {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_G2W {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments cc_LW {_ _ _ _ _ _ _ _ _ _ _ _} _.

(** [set_solver] with the premises of [cctx] that are no facts about sets
    cleared first. Their unfolding is most of the time [set_solver]
    spends in the sections that name them. *)
Ltac cc_set_solver :=
  repeat match goal with
  | H := cc_G1 _ |- _ => clear H | H := cc_G2 _ |- _ => clear H
  | H := cc_HP1 _ |- _ => clear H | H := cc_HP2 _ |- _ => clear H
  | H := cc_H1 _ |- _ => clear H | H := cc_H2 _ |- _ => clear H
  | H := cc_L _ |- _ => clear H | H := cc_Hn _ |- _ => clear H | H := cc_X1P _ |- _ => clear H | H := cc_X2P _ |- _ => clear H
  end; set_solver.
