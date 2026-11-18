(** * P-Connect, the context of the step clause (stage S4)

    [ConnL κ j W T] is P-Connect at level j. [cctx] packs what the step
    clause of the composite knows at a level S n: the world W1 is strict
    and T primitive, the two components q1 and q2 are connected over the
    cut ([conn]), their clauses at S n over X1 and X2, P-Connect below
    S n ([L]), X1 and X2 inside P, every fusion of a component in P
    ([HP1], [HP2]), and the composite of a fused step of one component
    with the other in P ([G1], [G2]). The sections of
    compat/ConnectSteps.v, ConnectCross.v, ConnectLink.v, ConnectTau.v,
    ConnectExt.v and ConnectExtMsg.v take one [cctx] and name its fields
    by [Let]. *)

From GV Require Export compat.Connect.

Definition ConnL (κ : ctable) (j : nat) (W : world) (T : ty) : Prop :=
  ∀ Σ1 ΣC Σ2 ΣD p1 p2, Prel κ j W (Σ1 ∪ ΣC) T p1 → Prel κ j W (Σ2 ∪ ΣD) TUnit p2 →
    conn Σ1 ΣC p1.1 Σ2 ΣD p2.1 → Prel κ j W (Σ1 ∪ Σ2) T (pconn p1 p2 (chans_of ΣC)).

(** One constructor with named premises, as [sth] (compat/PTerm.v). A
    [Record] does not parse here, because the typing notation
    Θ ; Γ ; Δ ⊢ … makes ';' a term token. *)
Inductive cctx (κ : ctable) (n : nat) (W1 : world) (T : ty) (X1 X2 : prel)
    (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) : Prop :=
  | CCtx
      (cc_HS : strict W1)
      (cc_HT : prim T)
      (cc_Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1)
      (cc_H1 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T q1)
      (cc_H2 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) TUnit q2)
      (cc_L : ∀ j, j < S n → ConnL κ j W1 T)
      (cc_X1P : ∀ W Σ T p, X1 W Σ T p → Prel κ (S n) W Σ T p)
      (cc_X2P : ∀ W Σ T p, X2 W Σ T p → Prel κ (S n) W Σ T p)
      (cc_HP1 : ∀ h D, fuse_ok h D (Σ1 ∪ ΣC) q1 →
        Prel κ (S n) W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D q1))
      (cc_HP2 : ∀ h D, fuse_ok h D (Σ2 ∪ ΣD) q2 →
        Prel κ (S n) W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D q2))
      (cc_G1 : ∀ p1' Σa h D Σ1' ΣC' Σ2' ΣD' p2', X1 W1 Σa T p1' → fuse_ok h D Σa p1' →
        sdrop D (kren h Σa) = Σ1' ∪ ΣC' → Prel κ (S n) W1 (Σ2' ∪ ΣD') TUnit p2' →
        conn Σ1' ΣC' (pfuse h D p1').1 Σ2' ΣD' p2'.1 →
        Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h D p1') p2' (chans_of ΣC')))
      (cc_G2 : ∀ p2' Σb h D Σ1' ΣC' Σ2' ΣD' h1 D1, X2 W1 Σb TUnit p2' → fuse_ok h D Σb p2' →
        sdrop D (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
        sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
        conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h D p2').1 →
        Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h D p2') (chans_of ΣC'))).

Section cctx_proj.
  Context κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 (H : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Lemma cc_HS : strict W1.
  Proof. by destruct H. Qed.
  Lemma cc_HT : prim T.
  Proof. by destruct H. Qed.
  Lemma cc_Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1.
  Proof. by destruct H. Qed.
  Lemma cc_H1 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T q1.
  Proof. by destruct H. Qed.
  Lemma cc_H2 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) TUnit q2.
  Proof. by destruct H. Qed.
  Lemma cc_L : ∀ j, j < S n → ConnL κ j W1 T.
  Proof. by destruct H. Qed.
  Lemma cc_X1P : ∀ W Σ T p, X1 W Σ T p → Prel κ (S n) W Σ T p.
  Proof. by destruct H. Qed.
  Lemma cc_X2P : ∀ W Σ T p, X2 W Σ T p → Prel κ (S n) W Σ T p.
  Proof. by destruct H. Qed.
  Lemma cc_HP1 : ∀ h D, fuse_ok h D (Σ1 ∪ ΣC) q1 →
    Prel κ (S n) W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D q1).
  Proof. by destruct H. Qed.
  Lemma cc_HP2 : ∀ h D, fuse_ok h D (Σ2 ∪ ΣD) q2 →
    Prel κ (S n) W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D q2).
  Proof. by destruct H. Qed.
  Lemma cc_G1 : ∀ p1' Σa h D Σ1' ΣC' Σ2' ΣD' p2', X1 W1 Σa T p1' → fuse_ok h D Σa p1' →
    sdrop D (kren h Σa) = Σ1' ∪ ΣC' → Prel κ (S n) W1 (Σ2' ∪ ΣD') TUnit p2' →
    conn Σ1' ΣC' (pfuse h D p1').1 Σ2' ΣD' p2'.1 →
    Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h D p1') p2' (chans_of ΣC')).
  Proof. by destruct H. Qed.
  Lemma cc_G2 : ∀ p2' Σb h D Σ1' ΣC' Σ2' ΣD' h1 D1, X2 W1 Σb TUnit p2' → fuse_ok h D Σb p2' →
    sdrop D (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
    sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
    conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h D p2').1 →
    Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h D p2') (chans_of ΣC')).
  Proof. by destruct H. Qed.
End cctx_proj.
Arguments cc_HS {_ _ _ _ _ _ _ _ _ _ _ _} _.
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

(** [set_solver] with the premises of [cctx] that are no facts about sets
    cleared first. Their unfolding is most of the time [set_solver]
    spends in the sections that name them. *)
Ltac cc_set_solver :=
  repeat match goal with
  | H := cc_G1 _ |- _ => clear H | H := cc_G2 _ |- _ => clear H
  | H := cc_HP1 _ |- _ => clear H | H := cc_HP2 _ |- _ => clear H
  | H := cc_H1 _ |- _ => clear H | H := cc_H2 _ |- _ => clear H
  | H := cc_L _ |- _ => clear H | H := cc_X1P _ |- _ => clear H | H := cc_X2P _ |- _ => clear H
  end; set_solver.
