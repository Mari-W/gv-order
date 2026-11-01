(** * Coinductive session equivalence and relational duality

    S ≈ R ([seq]), its congruence T ≈ U through the type grammar
    ([teq]), and the duality S ⊥ R ([sdual]). The rules follow the
    coinductive model of Thiemann's dual-session development
    (github.com/peterthiemann/dual-session). GV♯ has no choice former,
    so the ⊕ and & rules are the ! and ? rules at a [TSum] payload.

    ≈ and ⊥ are ∀ n of a depth-n approximation ([aeq], [adual]) instead
    of a cofix, which would have to be guarded through [unfoldS] and the
    mutual type grammar. [seq_coind] and [sdual_coind] recover the
    coinduction principles. A non-contractive head relates only to an
    equal head (≈) or its dual (⊥). *)

From stdpp Require Import base tactics.
From LRGV Require Export types.Types.

(** ** Part 1: type equivalence, parameterised by a session relation

    [eqT ρ] is the figure's T ≈_ρ U, extended by congruence to GV#'s
    type formers. It is a [Fixpoint] rather than an [Inductive] so
    that it can be destructed by [simpl] and needs no inversion. *)

Fixpoint eqT (ρ : sty → sty → Prop) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      ub = ub' ∧ lb = lb' ∧ eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TProd T1 T2, TProd U1 U2 => eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TSum T1 T2, TSum U1 U2 => eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TBox n C T1, TBox n' C' U1 => n = n' ∧ C = C' ∧ eqT ρ T1 U1

  | TSess s x, TSess r y => x = y ∧ ρ s r
  | TEx lb n C T1, TEx lb' n' C' U1 => lb = lb' ∧ n = n' ∧ C = C' ∧ eqT ρ T1 U1
  | _, _ => False
  end.

Lemma eqT_mono ρ ρ' T : ∀ U,
  (∀ s r, ρ s r → ρ' s r) → eqT ρ T U → eqT ρ' T U.
Proof.
  induction T; intros [] Hρ; simpl; naive_solver.
Qed.

Lemma eqT_refl ρ T : (∀ s, ρ s s) → eqT ρ T T.
Proof. intros Hρ. induction T; simpl; auto. Qed.

Lemma eqT_sym ρ T : ∀ U,
  (∀ s r, ρ s r → ρ r s) → eqT ρ T U → eqT ρ U T.
Proof.
  induction T; intros [] Hρ; simpl; naive_solver.
Qed.

Lemma eqT_trans ρ T : ∀ U V,
  (∀ s r t, ρ s r → ρ r t → ρ s t) →
  eqT ρ T U → eqT ρ U V → eqT ρ T V.
Proof.
  induction T; intros [] []; simpl; naive_solver.
Qed.

(** ** Parts 2 and 3: the one-step unfoldings

    Both relations observe their arguments through [unfoldS], so that
    µα.S and S[µα.S/α] are indistinguishable by construction. *)

Definition eq_step (τ : sty → sty → Prop) (s r : sty) : Prop :=
  match unfoldS s, unfoldS r with
  | SRcv m T s', SRcv m' U r' => m = m' ∧ eqT τ T U ∧ τ s' r'
  | SSnd m T s', SSnd m' U r' => m = m' ∧ eqT τ T U ∧ τ s' r'
  | SEnd, SEnd => True
  | u, v => u = v
  end.

Definition dual_step (τ δ : sty → sty → Prop) (s r : sty) : Prop :=
  match unfoldS s, unfoldS r with
  | SRcv m T s', SSnd m' U r' => m = m' ∧ eqT τ T U ∧ δ s' r'
  | SSnd m T s', SRcv m' U r' => m = m' ∧ eqT τ T U ∧ δ s' r'
  | SEnd, SEnd => True
  | u, v => u = dual v
  end.

(** The single place the 36-way split on the two head normal forms is
    performed; everything below reuses these. *)

Lemma eq_step_mono τ τ' s r :
  (∀ a b, τ a b → τ' a b) → eq_step τ s r → eq_step τ' s r.
Proof.
  unfold eq_step. intros Hτ.
  destruct (unfoldS s), (unfoldS r); try done;
    intros (? & ? & ?); split_and!; eauto using eqT_mono.
Qed.

Lemma dual_step_mono τ τ' δ δ' s r :
  (∀ a b, τ a b → τ' a b) → (∀ a b, δ a b → δ' a b) →
  dual_step τ δ s r → dual_step τ' δ' s r.
Proof.
  unfold dual_step. intros Hτ Hδ.
  destruct (unfoldS s), (unfoldS r); try done;
    intros (? & ? & ?); split_and!; eauto using eqT_mono.
Qed.

(** ** The approximations *)

Fixpoint aeq (n : nat) (s r : sty) : Prop :=
  match n with
  | 0 => True
  | S n' => eq_step (aeq n') s r
  end.

Fixpoint adual (n : nat) (s r : sty) : Prop :=
  match n with
  | 0 => True
  | S n' => dual_step (aeq n') (adual n') s r
  end.

(** The relations themselves: agreement at every observation depth. *)

Definition seq (s r : sty) : Prop := ∀ n, aeq n s r.
Definition sdual (s r : sty) : Prop := ∀ n, adual n s r.
Definition teq (T U : ty) : Prop := eqT seq T U.

(** ** The coinduction principles

    What makes the step-indexed presentation as strong as a native
    [cofix]: a relation contained in its own one-step unfolding is
    contained in ≈ resp. ⊥. Every use of ≈ that would be a
    [cofix] elsewhere goes through these. *)

Lemma seq_coind (τ : sty → sty → Prop) :
  (∀ s r, τ s r → eq_step τ s r) → ∀ s r, τ s r → seq s r.
Proof.
  intros Hτ s r Hsr n. revert s r Hsr.
  induction n as [|n IH]; intros s r Hsr; [done|].
  eapply eq_step_mono; [exact IH|by apply Hτ].
Qed.

Lemma sdual_coind (δ : sty → sty → Prop) :
  (∀ s r, δ s r → dual_step seq δ s r) → ∀ s r, δ s r → sdual s r.
Proof.
  intros Hδ s r Hsr n. revert s r Hsr.
  induction n as [|n IH]; intros s r Hsr; [done|].
  eapply dual_step_mono; [|exact IH|by apply Hδ].
  intros a b Hab. apply Hab.
Qed.

(** ** ≈ is an equivalence *)

Lemma aeq_refl n : ∀ s, aeq n s s.
Proof.
  induction n as [|n IH]; intros s; [done|].
  unfold aeq; fold aeq. unfold eq_step.
  destruct (unfoldS s); try done; split_and!; auto using eqT_refl.
Qed.

Lemma aeq_sym n : ∀ s r, aeq n s r → aeq n r s.
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  destruct (unfoldS s), (unfoldS r); try (by symmetry);
    try done; destruct H as (-> & ? & ?); split_and!; eauto using eqT_sym.
Qed.

Lemma aeq_trans n : ∀ s r t, aeq n s r → aeq n r t → aeq n s t.
Proof.
  induction n as [|n IH]; intros s r t H1 H2; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  destruct (unfoldS s), (unfoldS r), (unfoldS t); try congruence;
    try done; destruct H1 as (-> & ? & ?), H2 as (-> & ? & ?);
    split_and!; eauto using eqT_trans.
Qed.

(** The payload congruence at a fixed depth, packaged so that the
    case analyses below can discharge payload goals by [eauto]. *)

Lemma aeqT_sym n T U : eqT (aeq n) T U → eqT (aeq n) U T.
Proof. apply eqT_sym, aeq_sym. Qed.

Lemma aeqT_trans n T U V :
  eqT (aeq n) T U → eqT (aeq n) U V → eqT (aeq n) T V.
Proof. apply eqT_trans. intros ? ? ?. apply aeq_trans. Qed.

Lemma seq_refl s : seq s s.
Proof. intros n. apply aeq_refl. Qed.

Lemma seq_sym s r : seq s r → seq r s.
Proof. intros H n. by apply aeq_sym. Qed.

Lemma seq_trans s r t : seq s r → seq r t → seq s t.
Proof. intros H1 H2 n. by eapply aeq_trans. Qed.

(** ** ≈ lifted to the full type grammar *)

Lemma teq_refl T : teq T T.
Proof. apply eqT_refl, seq_refl. Qed.

Lemma teq_sym T U : teq T U → teq U T.
Proof. apply eqT_sym, seq_sym. Qed.

(** Depth-indexed agreement at every depth *is* agreement, because
    the type grammar itself is finite: the index only ever guards the
    session positions. This is what lets the inversion lemmas below
    hand out a [teq] payload. *)

Lemma eqT_all T : ∀ U, (∀ n, eqT (aeq n) T U) → teq T U.
Proof.
  unfold teq, seq; induction T; intros [] H; simpl in *;
    try (by specialize (H 0)); try done;
    try (split; [apply IHT1|apply IHT2]; intros n; by destruct (H n)).
  - destruct (H 0) as (-> & -> & _). split_and!; [done|done| |].
    + apply IHT1. intros n. by destruct (H n) as (_ & _ & ? & _).
    + apply IHT2. intros n. by destruct (H n) as (_ & _ & _ & ?).
  - destruct (H 0) as (-> & -> & _). split_and!; [done|done|].
    apply IHT. intros n. by destruct (H n) as (_ & _ & ?).

  - destruct (H 0) as (-> & _). split; [done|]. intros n. by destruct (H n).
  - destruct (H 0) as (-> & -> & -> & _). split_and!; [done|done|done|].
    apply IHT. intros n. by destruct (H n) as (_ & _ & _ & ?).
Qed.

(** ** ≈ is a congruence for [dual] *)

Lemma aeq_dual n : ∀ s r, aeq n s r → aeq n (dual s) (dual r).
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  rewrite <-!dual_unfoldS.
  destruct (unfoldS s), (unfoldS r); simpl in *; try congruence;
    try done; destruct H as (-> & ? & ?); split_and!; auto.
Qed.

Lemma seq_dual s r : seq s r → seq (dual s) (dual r).
Proof. intros H n. by apply aeq_dual. Qed.

(** ** ⊥ is symmetric, and [dual] is sound for it *)

Lemma adual_sym n : ∀ s r, adual n s r → adual n r s.
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold adual in *; fold adual in *. unfold dual_step in *.
  destruct (unfoldS s), (unfoldS r); try done;
    try (by rewrite H, dual_involutive);
    try done; destruct H as (-> & ? & ?); split_and!; eauto using aeqT_sym.
Qed.

Lemma sdual_sym s r : sdual s r → sdual r s.
Proof. intros H n. by apply adual_sym. Qed.

(** The syntactic dual function is sound for relational duality. This
    holds unconditionally — including on non-contractive types —
    because [dual] commutes with [unfoldS] ([dual_unfoldS]). *)

Lemma adual_dual n : ∀ s, adual n (dual s) s.
Proof.
  induction n as [|n IH]; intros s; [done|].
  unfold adual; fold adual. unfold dual_step. rewrite <-dual_unfoldS.
  destruct (unfoldS s); simpl; try done;
    split_and!; auto using eqT_refl, aeq_refl.
Qed.

Lemma dual_sdual s : sdual (dual s) s.
Proof. intros n. apply adual_dual. Qed.

Lemma sdual_dual s : sdual s (dual s).
Proof. apply sdual_sym, dual_sdual. Qed.

(** ** ≈ respects ⊥ *)

Lemma adual_seq_l n : ∀ s s' t, aeq n s s' → adual n s t → adual n s' t.
Proof.
  induction n as [|n IH]; intros s s' t He Hd; [done|].
  unfold aeq in He; fold aeq in He. unfold eq_step in He.
  unfold adual in *; fold adual in *. unfold dual_step in *.
  destruct (unfoldS s), (unfoldS s'), (unfoldS t); simpl in *;
    try done; try congruence;
    try done; destruct He as (-> & ? & ?), Hd as (-> & ? & ?);
    split_and!; eauto using aeqT_sym, aeqT_trans.
Qed.

Lemma sdual_seq_l s s' t : seq s s' → sdual s t → sdual s' t.
Proof. intros He Hd n. eapply adual_seq_l; [apply He|apply Hd]. Qed.

Lemma sdual_seq_r s t t' : seq t t' → sdual s t → sdual s t'.
Proof. intros He Hd. apply sdual_sym. eapply sdual_seq_l; [done|]. by apply sdual_sym. Qed.

(** ⊥ is [dual] up to ≈ — the functional and relational presentations
    agree, which is the figure's closing remark. *)

Lemma adual_aeq_dual n : ∀ s r, adual n s r → aeq n s (dual r).
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold adual in H; fold adual in H. unfold dual_step in H.
  unfold aeq; fold aeq. unfold eq_step. rewrite <-dual_unfoldS.
  destruct (unfoldS s), (unfoldS r); simpl in *; try congruence;
    try done; destruct H as (-> & ? & ?); split_and!; auto.
Qed.

Lemma sdual_seq_dual s r : sdual s r ↔ seq s (dual r).
Proof.
  split.
  - intros Hd n. by apply adual_aeq_dual.
  - intros He. eapply sdual_seq_l; [by apply seq_sym|apply dual_sdual].
Qed.

(** ** Head inversion

    An ≈-partner of a type in head normal form is itself in head
    normal form, with the same prefix and ≈-related components. This
    is how the logical relation reads a session type it only knows up
    to ≈: it recovers a head, exactly as [senv_hd] does for a type it
    knows up to [unfoldS]. *)

Lemma aeq_S_rcv n s r m T r' :
  aeq (S n) s r → unfoldS r = SRcv m T r' →
  ∃ U s', unfoldS s = SRcv m U s' ∧ eqT (aeq n) U T ∧ aeq n s' r'.
Proof.
  unfold aeq; fold aeq. unfold eq_step. intros H Hr. rewrite Hr in H.
  destruct (unfoldS s) as [m' U s'|m' U s'| |x|a|a]; try discriminate;
    destruct H as (-> & ? & ?); by exists U, s'.
Qed.

Lemma aeq_S_snd n s r m T r' :
  aeq (S n) s r → unfoldS r = SSnd m T r' →
  ∃ U s', unfoldS s = SSnd m U s' ∧ eqT (aeq n) U T ∧ aeq n s' r'.
Proof.
  unfold aeq; fold aeq. unfold eq_step. intros H Hr. rewrite Hr in H.
  destruct (unfoldS s) as [m' U s'|m' U s'| |x|a|a]; try discriminate;
    destruct H as (-> & ? & ?); by exists U, s'.
Qed.

Lemma seq_rcv_inv s r m T r' :
  seq s r → unfoldS r = SRcv m T r' →
  ∃ U s', unfoldS s = SRcv m U s' ∧ teq U T ∧ seq s' r'.
Proof.
  intros Hs Hr.
  destruct (aeq_S_rcv 0 s r m T r' (Hs 1) Hr) as (U & s' & Es & _ & _).
  exists U, s'. split; [done|]. split.
  - apply eqT_all. intros n.
    destruct (aeq_S_rcv n s r m T r' (Hs (S n)) Hr) as (? & ? & Es0 & ? & ?).
    rewrite Es in Es0. by simplify_eq.
  - intros n.
    destruct (aeq_S_rcv n s r m T r' (Hs (S n)) Hr) as (? & ? & Es0 & ? & ?).
    rewrite Es in Es0. by simplify_eq.
Qed.

Lemma seq_snd_inv s r m T r' :
  seq s r → unfoldS r = SSnd m T r' →
  ∃ U s', unfoldS s = SSnd m U s' ∧ teq U T ∧ seq s' r'.
Proof.
  intros Hs Hr.
  destruct (aeq_S_snd 0 s r m T r' (Hs 1) Hr) as (U & s' & Es & _ & _).
  exists U, s'. split; [done|]. split.
  - apply eqT_all. intros n.
    destruct (aeq_S_snd n s r m T r' (Hs (S n)) Hr) as (? & ? & Es0 & ? & ?).
    rewrite Es in Es0. by simplify_eq.
  - intros n.
    destruct (aeq_S_snd n s r m T r' (Hs (S n)) Hr) as (? & ? & Es0 & ? & ?).
    rewrite Es in Es0. by simplify_eq.
Qed.

Lemma seq_end_inv s r : seq s r → unfoldS r = SEnd → unfoldS s = SEnd.
Proof.
  intros Hs Hr. specialize (Hs 1).
  unfold aeq in Hs; fold aeq in Hs. unfold eq_step in Hs.
  rewrite Hr in Hs.
  by destruct (unfoldS s) as [m U s'|m U s'| |x|a|a].
Qed.

(** ** Term-level environments with both ends

    A term-level environment holds both ends of a channel only at dual
    types and aliased points (§4: Θ, c : S@x, c : S′@x′ with S ⊥ S′
    and x ≡ x′). The aliases are read in a relation [peq], the ≡ of a
    world, so that aliased points are interchangeable without any
    conversion. *)

Definition tenv_dual (peq : point → point → Prop) (Θ : tenv) : Prop :=
  ∀ c e1 e2, Θ !! c = Some (Both e1 e2) → peq e1.2 e2.2 ∧ sdual e1.1 e2.1.

(** Θ = Θ1, Θ2, defined when every overlap is a pair of dual ends at
    aliased points. *)
Definition tenv_comp (peq : point → point → Prop) (Θ Θ1 Θ2 : tenv) : Prop :=
  tenv_join Θ Θ1 Θ2 ∧
  ∀ c e1 e2, Θ1 !! c = Some (One e1) → Θ2 !! c = Some (One e2) →
    peq e1.2 e2.2 ∧ sdual e1.1 e2.1.

(** Two process-level environments agree on their overlap up to
    duality, at aliased points. *)
Definition senv_dual_on (peq : point → point → Prop) (Σ1 Σ2 : senv) : Prop :=
  ∀ c e1 e2, Σ1 !! c = Some e1 → Σ2 !! c = Some e2 →
    peq e1.2 e2.2 ∧ sdual e1.1 e2.1.

Lemma tenv_dual_mono (peq peq' : point → point → Prop) Θ :
  (∀ x y, peq x y → peq' x y) → tenv_dual peq Θ → tenv_dual peq' Θ.
Proof. intros Hp H c e1 e2 He. destruct (H c e1 e2 He). auto. Qed.

Lemma tenv_comp_mono (peq peq' : point → point → Prop) Θ Θ1 Θ2 :
  (∀ x y, peq x y → peq' x y) → tenv_comp peq Θ Θ1 Θ2 → tenv_comp peq' Θ Θ1 Θ2.
Proof.
  intros Hp [Hj H]. split; [done|]. intros c e1 e2 H1 H2.
  destruct (H c e1 e2 H1 H2). auto.
Qed.
