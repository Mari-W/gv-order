(** * Coinductive session equivalence and relational duality

    S ≈ R ([seq]), its congruence T ≈ U through the type grammar
    ([teq]), and the duality S ⊥ R ([sdual]). The rules follow the
    coinductive model of Thiemann's dual-session development
    (github.com/peterthiemann/dual-session), extended to the context-free
    session types of K1 (Skip, ;, ⊕ and &), whose heads [unfoldS] computes.

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
  | TBox n k C T1, TBox n' k' C' U1 =>
      (* a body over session variables compares on the nose: ≈ of open
         session types is not closed under their instances (sharp edges 73) *)
      n = n' ∧ k = k' ∧ C = C' ∧ match k with 0 => eqT ρ T1 U1 | S _ => T1 = U1 end
  | TSess s x, TSess r y => x = y ∧ ρ s r
  | TEx lb n C T1, TEx lb' n' C' U1 => lb = lb' ∧ n = n' ∧ C = C' ∧ eqT ρ T1 U1
  | _, _ => False
  end.

Lemma eqT_mono ρ ρ' T : ∀ U,
  (∀ s r, ρ s r → ρ' s r) → eqT ρ T U → eqT ρ' T U.
Proof.
  induction T; intros [] Hρ; simpl; repeat case_match; naive_solver.
Qed.

Lemma eqT_refl ρ T : (∀ s, ρ s s) → eqT ρ T T.
Proof. intros Hρ. induction T; simpl; repeat case_match; auto. Qed.

Lemma eqT_sym ρ T : ∀ U,
  (∀ s r, ρ s r → ρ r s) → eqT ρ T U → eqT ρ U T.
Proof.
  induction T; intros [] Hρ; simpl; repeat case_match; naive_solver.
Qed.

Lemma eqT_trans ρ T : ∀ U V,
  (∀ s r t, ρ s r → ρ r t → ρ s t) →
  eqT ρ T U → eqT ρ U V → eqT ρ T V.
Proof.
  induction T; intros [] []; simpl; repeat case_match; naive_solver.
Qed.

(** ** Parts 2 and 3: the one-step unfoldings

    Both relations observe their arguments through the head normal form
    [unfoldS] (unr, K3), read through the view [hd] below, so that
    µα.S and S[µα.S/α], Skip;S and S, and ⊕(S₁, S₂);S and ⊕(S₁;S, S₂;S)
    are indistinguishable whenever the heads exist. The LTS of Thiemann
    and Vasconcelos (Fig. 5) is deterministic, so a bisimulation
    compares exactly these heads, the action of the head and the
    continuations. *)

(** Reading a head off [hd]. *)
Lemma unfoldS_rcv_iff s m T r : unfoldS s = SSeq (SRcv m T) r ↔ hd s = HRcv m T r.
Proof.
  split; [intros H; by rewrite (hd_of _ _ H)|]. intros H. by rewrite unfoldS_unview, H.
Qed.

Lemma unfoldS_snd_iff s m T r : unfoldS s = SSeq (SSnd m T) r ↔ hd s = HSnd m T r.
Proof.
  split; [intros H; by rewrite (hd_of _ _ H)|]. intros H. by rewrite unfoldS_unview, H.
Qed.

Lemma unfoldS_plus_iff s s1 s2 : unfoldS s = SPlus s1 s2 ↔ hd s = HPlus s1 s2.
Proof.
  split; [intros H; by rewrite (hd_of _ _ H)|]. intros H. by rewrite unfoldS_unview, H.
Qed.

Lemma unfoldS_with_iff s s1 s2 : unfoldS s = SWith s1 s2 ↔ hd s = HWith s1 s2.
Proof.
  split; [intros H; by rewrite (hd_of _ _ H)|]. intros H. by rewrite unfoldS_unview, H.
Qed.

Lemma unfoldS_end_iff s : unfoldS s = SEnd ↔ hd s = HEnd.
Proof.
  split; [intros H; by rewrite (hd_of _ _ H)|]. intros H. by rewrite unfoldS_unview, H.
Qed.

(** A stuck head is no head. *)
Lemma view_stuck u v : view u = HStuck v → u = v ∧ ¬ hnf_shape u.
Proof.
  destruct u as [| | | | | | |o r| |]; simpl; intros H; try done;
    try (injection H as <-; split; [done|]; simpl; tauto).
  destruct o; simpl in H; try done; injection H as <-; split; simpl; tauto.
Qed.

Lemma hd_stuck s u : hd s = HStuck u → u = unfoldS s ∧ ¬ contractive s.
Proof.
  unfold hd, contractive. intros H. apply view_stuck in H as [<- Hn]. done.
Qed.

Definition vdual (h : hview) : hview :=
  match h with
  | HSkip => HSkip
  | HRcv m T s => HSnd m T (dual s)
  | HSnd m T s => HRcv m T (dual s)
  | HVar a s => HVarD a (dual s)
  | HVarD a s => HVar a (dual s)
  | HPlus a b => HWith (dual a) (dual b)
  | HWith a b => HPlus (dual a) (dual b)
  | HEnd => HEnd
  | HStuck u => HStuck (dual u)
  end.

Lemma view_dual u : view (dual u) = vdual (view u).
Proof. destruct u as [| | | | | | |o r| |]; try done. by destruct o. Qed.

Lemma hd_dual s : hd (dual s) = vdual (hd s).
Proof. unfold hd. by rewrite <-dual_unfoldS, view_dual. Qed.

Definition eq_step (τ : sty → sty → Prop) (s r : sty) : Prop :=
  match hd s, hd r with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T s', HRcv m' U r' | HSnd m T s', HSnd m' U r' =>
      m = m' ∧ eqT τ T U ∧ τ s' r'
  | HVar a s', HVar a' r' | HVarD a s', HVarD a' r' => a = a' ∧ τ s' r'
  | HPlus s1 s2, HPlus r1 r2 | HWith s1 s2, HWith r1 r2 => τ s1 r1 ∧ τ s2 r2
  | HStuck u, HStuck v => u = v
  | _, _ => False
  end.

Definition dual_step (τ δ : sty → sty → Prop) (s r : sty) : Prop :=
  match hd s, hd r with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T s', HSnd m' U r' | HSnd m T s', HRcv m' U r' =>
      m = m' ∧ eqT τ T U ∧ δ s' r'
  | HVar a s', HVarD a' r' | HVarD a s', HVar a' r' => a = a' ∧ δ s' r'
  | HPlus s1 s2, HWith r1 r2 | HWith s1 s2, HPlus r1 r2 => δ s1 r1 ∧ δ s2 r2
  | HStuck u, HStuck v => u = dual v
  | _, _ => False
  end.

(** The case splits on the heads are performed by [hd_cases]. *)

Ltac hd_cases s := destruct (hd s) as [|?m ?T ?s'|?m ?T ?s'|?a ?s'|?a ?s'|?s1 ?s2|?s1 ?s2| |?u].

Lemma eq_step_mono τ τ' s r :
  (∀ a b, τ a b → τ' a b) → eq_step τ s r → eq_step τ' s r.
Proof.
  unfold eq_step. intros Hτ. hd_cases s; hd_cases r; try done;
    intuition eauto using eqT_mono.
Qed.

Lemma dual_step_mono τ τ' δ δ' s r :
  (∀ a b, τ a b → τ' a b) → (∀ a b, δ a b → δ' a b) →
  dual_step τ δ s r → dual_step τ' δ' s r.
Proof.
  unfold dual_step. intros Hτ Hδ. hd_cases s; hd_cases r; try done;
    intuition eauto using eqT_mono.
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
  hd_cases s; try done; split_and!; auto using eqT_refl.
Qed.

Lemma aeq_sym n : ∀ s r, aeq n s r → aeq n r s.
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  hd_cases s; hd_cases r; try done; try (by symmetry);
    intuition (subst; eauto using eqT_sym).
Qed.

Lemma aeq_trans n : ∀ s r t, aeq n s r → aeq n r t → aeq n s t.
Proof.
  induction n as [|n IH]; intros s r t H1 H2; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  hd_cases s; hd_cases r; try done; hd_cases t; try done; try congruence;
    intuition (subst; eauto using eqT_trans).
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
  - destruct (H 0) as (-> & -> & -> & H0). split_and!; [done|done|done|].
    destruct k0; [|done].
    apply IHT. intros n. by destruct (H n) as (_ & _ & _ & ?).
  - destruct (H 0) as (-> & _). split; [done|]. intros n. by destruct (H n).
  - destruct (H 0) as (-> & -> & -> & _). split_and!; [done|done|done|].
    apply IHT. intros n. by destruct (H n) as (_ & _ & _ & ?).
Qed.

(** ≈ is its own one-step unfolding. *)
Lemma seq_step s r : seq s r → eq_step seq s r.
Proof.
  intros H. pose proof (H 1) as H1. unfold aeq, eq_step in H1 |- *.
  pose proof (λ n, H (S n)) as HS. unfold aeq in HS; fold aeq in HS.
  unfold eq_step in HS.
  hd_cases s; hd_cases r; try done.
  - destruct H1 as (-> & _). split_and!; [done| |].
    + apply eqT_all. intros n. by destruct (HS n) as (_ & ? & _).
    + intros n. by destruct (HS n) as (_ & _ & ?).
  - destruct H1 as (-> & _). split_and!; [done| |].
    + apply eqT_all. intros n. by destruct (HS n) as (_ & ? & _).
    + intros n. by destruct (HS n) as (_ & _ & ?).
  - destruct H1 as (-> & _). split; [done|]. intros n. by destruct (HS n).
  - destruct H1 as (-> & _). split; [done|]. intros n. by destruct (HS n).
  - split; intros n; by destruct (HS n).
  - split; intros n; by destruct (HS n).
Qed.

(** Two types with the same head are equivalent. *)
Lemma seq_unf s r : unfoldS s = unfoldS r → seq s r.
Proof.
  intros E n. destruct n as [|n]; [done|]. unfold aeq; fold aeq. unfold eq_step.
  rewrite (hd_of r _ (eq_sym E)). fold (hd s).
  hd_cases s; try done; split_and!; auto using eqT_refl, aeq_refl.
Qed.

(** ≈ preserves contractiveness. *)
Lemma seq_contractive s r : seq s r → contractive s → contractive r.
Proof.
  intros H Hs. specialize (H 1). unfold aeq, eq_step in H.
  destruct (hd s) eqn:Es; destruct (hd r) eqn:Er; try done;
    try (apply hd_stuck in Es as [_ Hn]; by destruct Hn);
    unfold contractive; rewrite unfoldS_unview, Er; done.
Qed.

(** ** ≈ is a congruence for [dual] *)

Lemma aeq_dual n : ∀ s r, aeq n s r → aeq n (dual s) (dual r).
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  rewrite !hd_dual.
  hd_cases s; hd_cases r; simpl in *; try done; try congruence;
    intuition (subst; auto).
Qed.

Lemma seq_dual s r : seq s r → seq (dual s) (dual r).
Proof. intros H n. by apply aeq_dual. Qed.

(** ** ⊥ is symmetric, and [dual] is sound for it *)

Lemma adual_sym n : ∀ s r, adual n s r → adual n r s.
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold adual in *; fold adual in *. unfold dual_step in *.
  hd_cases s; hd_cases r; try done;
    try (by rewrite H, dual_involutive);
    intuition (subst; eauto using aeqT_sym).
Qed.

Lemma sdual_sym s r : sdual s r → sdual r s.
Proof. intros H n. by apply adual_sym. Qed.

(** The syntactic dual function is sound for relational duality. This
    holds unconditionally — including on non-contractive types —
    because [dual] commutes with [unfoldS] ([dual_unfoldS]). *)

Lemma adual_dual n : ∀ s, adual n (dual s) s.
Proof.
  induction n as [|n IH]; intros s; [done|].
  unfold adual; fold adual. unfold dual_step. rewrite hd_dual.
  hd_cases s; simpl; try done;
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
  hd_cases s; hd_cases s'; try done; hd_cases t; try done; try congruence;
    intuition (subst; eauto using aeqT_sym, aeqT_trans).
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
  unfold aeq; fold aeq. unfold eq_step. rewrite hd_dual.
  hd_cases s; hd_cases r; simpl in *; try done;
    intuition (subst; auto).
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

Lemma seq_rcv_inv s r m T r' :
  seq s r → unfoldS r = SSeq (SRcv m T) r' →
  ∃ U s', unfoldS s = SSeq (SRcv m U) s' ∧ teq U T ∧ seq s' r'.
Proof.
  intros Hs Hr. pose proof (seq_step _ _ Hs) as H. unfold eq_step in H.
  rewrite (hd_of _ _ Hr) in H. rewrite unfoldS_unview.
  hd_cases s; try done. destruct H as (-> & ? & ?). by eexists _, _.
Qed.

Lemma seq_snd_inv s r m T r' :
  seq s r → unfoldS r = SSeq (SSnd m T) r' →
  ∃ U s', unfoldS s = SSeq (SSnd m U) s' ∧ teq U T ∧ seq s' r'.
Proof.
  intros Hs Hr. pose proof (seq_step _ _ Hs) as H. unfold eq_step in H.
  rewrite (hd_of _ _ Hr) in H. rewrite unfoldS_unview.
  hd_cases s; try done. destruct H as (-> & ? & ?). by eexists _, _.
Qed.

Lemma seq_plus_inv s r r1 r2 :
  seq s r → unfoldS r = SPlus r1 r2 →
  ∃ s1 s2, unfoldS s = SPlus s1 s2 ∧ seq s1 r1 ∧ seq s2 r2.
Proof.
  intros Hs Hr. pose proof (seq_step _ _ Hs) as H. unfold eq_step in H.
  rewrite (hd_of _ _ Hr) in H. rewrite unfoldS_unview.
  hd_cases s; try done. destruct H. by eexists _, _.
Qed.

Lemma seq_with_inv s r r1 r2 :
  seq s r → unfoldS r = SWith r1 r2 →
  ∃ s1 s2, unfoldS s = SWith s1 s2 ∧ seq s1 r1 ∧ seq s2 r2.
Proof.
  intros Hs Hr. pose proof (seq_step _ _ Hs) as H. unfold eq_step in H.
  rewrite (hd_of _ _ Hr) in H. rewrite unfoldS_unview.
  hd_cases s; try done. destruct H. by eexists _, _.
Qed.

Lemma seq_end_inv s r : seq s r → unfoldS r = SEnd → unfoldS s = SEnd.
Proof.
  intros Hs Hr. pose proof (seq_step _ _ Hs) as H. unfold eq_step in H.
  rewrite (hd_of _ _ Hr) in H. rewrite unfoldS_unview.
  by hd_cases s.
Qed.

(** ⊥ is its own one-step unfolding. *)
Lemma sdual_step s r : sdual s r → dual_step seq sdual s r.
Proof.
  intros Hd. apply sdual_seq_dual in Hd. pose proof (seq_step _ _ Hd) as H.
  unfold eq_step in H. unfold dual_step. rewrite hd_dual in H.
  hd_cases s; hd_cases r; simpl in *; try done;
    try (destruct H as (-> & ? & ?); split_and!; [done|done|];
         apply sdual_seq_dual; by rewrite ?dual_involutive);
    try (destruct H as (-> & ?); split; [done|];
         apply sdual_seq_dual; by rewrite ?dual_involutive);
    try (destruct H; split; apply sdual_seq_dual; by rewrite ?dual_involutive).
Qed.

(** Inversion of ⊥ at the heads of both sides. *)
Lemma sdual_snd_rcv s r m T s' m' U r' :
  sdual s r → unfoldS s = SSeq (SSnd m T) s' → unfoldS r = SSeq (SRcv m' U) r' →
  m = m' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs Hr. pose proof (sdual_step _ _ H) as Hd. unfold dual_step in Hd.
  by rewrite (hd_of _ _ Hs), (hd_of _ _ Hr) in Hd.
Qed.

Lemma sdual_rcv_snd s r m T s' m' U r' :
  sdual s r → unfoldS s = SSeq (SRcv m T) s' → unfoldS r = SSeq (SSnd m' U) r' →
  m = m' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs Hr. pose proof (sdual_step _ _ H) as Hd. unfold dual_step in Hd.
  by rewrite (hd_of _ _ Hs), (hd_of _ _ Hr) in Hd.
Qed.

Lemma sdual_plus_with s r s1 s2 r1 r2 :
  sdual s r → unfoldS s = SPlus s1 s2 → unfoldS r = SWith r1 r2 → sdual s1 r1 ∧ sdual s2 r2.
Proof.
  intros H Hs Hr. pose proof (sdual_step _ _ H) as Hd. unfold dual_step in Hd.
  by rewrite (hd_of _ _ Hs), (hd_of _ _ Hr) in Hd.
Qed.

Lemma sdual_with_plus s r s1 s2 r1 r2 :
  sdual s r → unfoldS s = SWith s1 s2 → unfoldS r = SPlus r1 r2 → sdual s1 r1 ∧ sdual s2 r2.
Proof.
  intros H Hs Hr. pose proof (sdual_step _ _ H) as Hd. unfold dual_step in Hd.
  by rewrite (hd_of _ _ Hs), (hd_of _ _ Hr) in Hd.
Qed.

Lemma sdual_sbranch b s1 s2 r1 r2 :
  sdual s1 r1 → sdual s2 r2 → sdual (sbranch b s1 s2) (sbranch b r1 r2).
Proof. by destruct b. Qed.

(** The kind of a head, and what duality does to it. *)
Inductive hkind := KdSkip | KdRcv | KdSnd | KdVar | KdVarD | KdPlus | KdWith | KdEnd | KdStuck.

Definition kind (h : hview) : hkind :=
  match h with
  | HSkip => KdSkip | HRcv _ _ _ => KdRcv | HSnd _ _ _ => KdSnd | HVar _ _ => KdVar
  | HVarD _ _ => KdVarD | HPlus _ _ => KdPlus | HWith _ _ => KdWith | HEnd => KdEnd
  | HStuck _ => KdStuck
  end.

Definition kdual (k : hkind) : hkind :=
  match k with
  | KdRcv => KdSnd | KdSnd => KdRcv | KdVar => KdVarD | KdVarD => KdVar
  | KdPlus => KdWith | KdWith => KdPlus | k => k
  end.

Lemma sdual_kind s r : sdual s r → kind (hd r) = kdual (kind (hd s)).
Proof.
  intros H. specialize (H 1). simpl in H. unfold dual_step in H.
  hd_cases s; hd_cases r; done.
Qed.

(** ** Laws of sequential composition (Lemma 3.4 of Thiemann and
    Vasconcelos) and of µ (Lemma 3.5)

    The laws hold for contractive types, as in the paper, which states
    them for well-formed types. Skip;S ≈ S and µα.S ≈ S[µα.S/α] need
    the head of S, S;Skip ≈ S and associativity need it hereditarily
    ([hcontractive]), because their bisimulations visit the
    continuations. Distribution of a choice over ; and Close;S ≈ Close
    hold for every type. *)

(** Hereditary contractiveness: every type reachable from S by actions
    has a head. *)
Lemma hcontractive_contractive s : hcontractive s → contractive s.
Proof.
  intros H. specialize (H 1). simpl in H. unfold hc_step in H.
  unfold contractive. rewrite unfoldS_unview.
  destruct (hd s) eqn:E; done.
Qed.

Lemma hcontractive_step s : hcontractive s →
  match hd s with
  | HSkip | HEnd => True
  | HRcv _ _ s' | HSnd _ _ s' | HVar _ s' | HVarD _ s' => hcontractive s'
  | HPlus a b | HWith a b => hcontractive a ∧ hcontractive b
  | HStuck _ => False
  end.
Proof.
  intros H. pose proof (λ n, H (S n)) as HS. simpl in HS. unfold hc_step in HS.
  specialize (H 1). simpl in H. unfold hc_step in H.
  destruct (hd s); try done; try (intros n; apply HS).
  all: split; intros n; apply HS.
Qed.

Lemma sfuel_sinst s : ∀ σ, sfuel s ≤ sfuel (sinst σ s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2];
    intros σ; simpl; try lia.
  - specialize (IH (sty_up σ)). lia.
  - apply sfuel_pos.
  - rewrite sfuel_dual. apply sfuel_pos.
  - specialize (IH1 σ). specialize (IH2 σ). lia.
Qed.

(** The head of S₁;S₂ from the heads of S₁ and S₂. *)
Lemma unfoldS_seq_skip s1 s2 :
  unfoldS s1 = SSkip → contractive s2 → unfoldS (SSeq s1 s2) = unfoldS s2.
Proof.
  intros H1 H2. unfold unfoldS at 1. simpl.
  rewrite (unfoldS_unrN s1 (sfuel s1 + sfuel s2)) by (rewrite ?H1; simpl; lia).
  rewrite H1. by rewrite (unfoldS_unrN s2 (sfuel s1 + sfuel s2)) by (done || lia).
Qed.

Lemma unfoldS_seq_hd s1 s2 :
  contractive s1 → unfoldS s1 ≠ SSkip → unfoldS (SSeq s1 s2) = hseq (unfoldS s1) s2.
Proof.
  intros H1 Hne. unfold unfoldS at 1. simpl.
  rewrite (unfoldS_unrN s1 (sfuel s1 + sfuel s2)) by (done || lia).
  destruct (unfoldS s1); done.
Qed.

Lemma contractive_seq s1 s2 : contractive s1 → unfoldS s1 ≠ SSkip → contractive (SSeq s1 s2).
Proof.
  intros H1 Hne. unfold contractive. rewrite unfoldS_seq_hd by done.
  by apply hseq_shape.
Qed.

Lemma seq_skip_l s : contractive s → seq (SSeq SSkip s) s.
Proof. intros H. apply seq_unf. by apply unfoldS_seq_skip. Qed.

Lemma seq_choice_dist_plus s1 s2 s3 :
  seq (SSeq (SPlus s1 s2) s3) (SPlus (SSeq s1 s3) (SSeq s2 s3)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|done|done]. by rewrite unfoldS_plus.
Qed.

Lemma seq_choice_dist_with s1 s2 s3 :
  seq (SSeq (SWith s1 s2) s3) (SWith (SSeq s1 s3) (SSeq s2 s3)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|done|done]. by rewrite unfoldS_with.
Qed.

Lemma seq_close_seq s : seq (SSeq SEnd s) SEnd.
Proof. apply seq_unf. by rewrite unfoldS_seq_hd. Qed.

Lemma seq_mu s : contractive (SMu s) → seq (SMu s) (unroll s).
Proof.
  intros H. apply seq_unf. destruct (unfoldS_cases (SMu s)) as [[E _]|[_ E]].
  - simpl in E. symmetry. unfold unfoldS at 1.
    rewrite (unrN_mono _ (sfuel (unroll s)) _ _ E) by apply sfuel_sinst.
    done.
  - exfalso. unfold contractive in H. rewrite E in H. done.
Qed.

(** The head of S₁;S₂ as a function of the head of S₁. *)
Lemma hd_seq x y : contractive x → contractive y →
  hd (SSeq x y) = match hd x with HSkip => hd y | h => view (hseq (unview h) y) end.
Proof.
  intros Hx Hy. unfold hd at 1. pose proof (unfoldS_unview x) as Ux.
  destruct (hd x) eqn:E;
    try (rewrite unfoldS_seq_hd; [by rewrite Ux|done|by rewrite Ux]).
  - rewrite unfoldS_seq_skip; [done|by rewrite Ux|done].
  - exfalso. apply hd_stuck in E as [_ Hn]. by apply Hn.
Qed.

Lemma contractive_seq2 x y : contractive x → contractive y → contractive (SSeq x y).
Proof.
  intros Hx Hy. pose proof (unfoldS_unview x) as Ux.
  destruct (hd x) eqn:E; try (apply contractive_seq; [done|by rewrite Ux]).
  - unfold contractive. by rewrite unfoldS_seq_skip.
  - exfalso. apply hd_stuck in E as [_ Hn]. by apply Hn.
Qed.

Lemma hcontractive_skip : hcontractive SSkip.
Proof. intros [|n]; done. Qed.

(** The continuation of an atom after ;. *)
Definition sk (r y : sty) : sty := match r with SSkip => y | _ => SSeq r y end.

Lemma hseq_atom o r y : satom o → hseq (SSeq o r) y = SSeq o (sk r y).
Proof. by destruct r. Qed.

Lemma sk_cases r y : (r = SSkip ∧ sk r y = y) ∨ sk r y = SSeq r y.
Proof. destruct r; first [by left | by right]. Qed.

Lemma eq_step_hd τ s r : (∀ a, τ a a) → hd s = hd r → eq_step τ s r.
Proof.
  intros Hτ E. unfold eq_step. rewrite <-E.
  hd_cases s; try done; split_and!; auto using eqT_refl.
Qed.

Lemma seq_skip_r s : hcontractive s → seq (SSeq s SSkip) s.
Proof.
  intros Hs.
  set (R := λ a b, (∃ x, hcontractive x ∧ a = SSeq x SSkip ∧ b = x) ∨ seq a b).
  assert (∀ a, R a a) as Hrefl by (intros; right; apply seq_refl).
  apply (seq_coind R); [|by left; eauto].
  intros a b [(x & Hx & -> & ->)|Hab];
    [|eapply eq_step_mono; [|by apply seq_step]; intros; by right].
  pose proof (hcontractive_step _ Hx) as Hst.
  pose proof (hcontractive_contractive _ Hx) as Hc.
  assert (∀ r, hcontractive r → R (sk r SSkip) r) as Hk.
  { intros r Hr. destruct (sk_cases r SSkip) as [[-> ->]| ->]; [done|left; eauto]. }
  unfold eq_step. rewrite hd_seq by (done || apply hcontractive_contractive, hcontractive_skip).
  destruct (hd x) as [|m T s'|m T s'|a s'|a s'|s1 s2|s1 s2| |u]; cbn [unview]; try done;
    try (rewrite hseq_atom by exact I; simpl; split_and!; auto using eqT_refl);
    try (simpl; destruct Hst; split; left; by eauto).
Qed.

Lemma seq_assoc a b c : hcontractive a → hcontractive b → hcontractive c →
  seq (SSeq (SSeq a b) c) (SSeq a (SSeq b c)).
Proof.
  intros Ha Hb Hc.
  set (R := λ X Y, (∃ a b c, hcontractive a ∧ hcontractive b ∧ hcontractive c ∧
                     X = SSeq (SSeq a b) c ∧ Y = SSeq a (SSeq b c)) ∨ seq X Y).
  assert (∀ a, R a a) as Hrefl by (intros; right; apply seq_refl).
  apply (seq_coind R); [|left; by eauto 10].
  intros X Y [(a' & b' & c' & Ha' & Hb' & Hc' & -> & ->)|HXY];
    [|eapply eq_step_mono; [|by apply seq_step]; intros; by right].
  clear a b c Ha Hb Hc. rename a' into a, b' into b, c' into c.
  rename Ha' into Ha, Hb' into Hb, Hc' into Hc.
  pose proof (hcontractive_contractive _ Ha) as Ca.
  pose proof (hcontractive_contractive _ Hb) as Cb.
  pose proof (hcontractive_contractive _ Hc) as Cc.
  pose proof (hcontractive_step _ Ha) as Sa.
  assert (∀ r, hcontractive r → R (sk (sk r b) c) (sk r (SSeq b c))) as Hk.
  { intros r Hr. destruct r; try (left; by eauto 10). simpl.
    destruct (sk_cases b c) as [[-> ->]| ->]; [|done].
    right. apply seq_sym, seq_skip_l. done. }
  assert (contractive (SSeq a b)) as Cab by by apply contractive_seq2.
  assert (contractive (SSeq b c)) as Cbc by by apply contractive_seq2.
  destruct (hd a) as [|m T s'|m T s'|x s'|x s'|s1 s2|s1 s2| |u] eqn:Eha.
  { apply eq_step_hd; [done|].
    rewrite (hd_seq (SSeq a b) c), (hd_seq a (SSeq b c)), (hd_seq a b), Eha by done.
    by rewrite (hd_seq b c) by done. }
  all: unfold eq_step.
  all: rewrite (hd_seq (SSeq a b) c), (hd_seq a (SSeq b c)), (hd_seq a b), Eha by done.
  all: cbn [unview]; try done.
  - rewrite (hseq_atom (SRcv m T)) by exact I. cbn [view unview].
    rewrite !hseq_atom by exact I. cbn [view]. split_and!; auto using eqT_refl.
  - rewrite (hseq_atom (SSnd m T)) by exact I. cbn [view unview].
    rewrite !hseq_atom by exact I. cbn [view]. split_and!; auto using eqT_refl.
  - rewrite (hseq_atom (SVar x)) by exact I. cbn [view unview].
    rewrite !hseq_atom by exact I. cbn [view]. auto.
  - rewrite (hseq_atom (SVarD x)) by exact I. cbn [view unview].
    rewrite !hseq_atom by exact I. cbn [view]. auto.
  - destruct Sa. simpl. split; left; by eauto 10.
  - destruct Sa. simpl. split; left; by eauto 10.
Qed.

(** ** Term-level environments with both ends

    A term-level environment holds both ends of a channel only at dual
    types and dual points (§4: Θ, c : S@x, c : S′@x′ with S ⊥ S′
    and x ≡ x̄′, end points). The aliases are read in a relation [peq], the ≡ of a
    world, so that aliased points are interchangeable without any
    conversion. *)

Definition tenv_dual (peq : point → point → Prop) (Θ : tenv) : Prop :=
  ∀ c e1 e2, Θ !! c = Some (Both e1 e2) → peq e1.2 (pt_dual e2.2) ∧ sdual e1.1 e2.1.

(** Θ = Θ1, Θ2, defined when every overlap is a pair of dual ends at
    aliased points. *)
Definition tenv_comp (peq : point → point → Prop) (Θ Θ1 Θ2 : tenv) : Prop :=
  tenv_join Θ Θ1 Θ2 ∧
  ∀ c e1 e2, Θ1 !! c = Some (One e1) → Θ2 !! c = Some (One e2) →
    peq e1.2 (pt_dual e2.2) ∧ sdual e1.1 e2.1.

(** Two process-level environments agree on their overlap up to
    duality, at aliased points. *)
Definition senv_dual_on (peq : point → point → Prop) (Σ1 Σ2 : senv) : Prop :=
  ∀ c e1 e2, Σ1 !! c = Some e1 → Σ2 !! c = Some e2 →
    peq e1.2 (pt_dual e2.2) ∧ sdual e1.1 e2.1.

Lemma tenv_dual_mono (peq peq' : point → point → Prop) Θ :
  (∀ x y, peq x y → peq' x y) → tenv_dual peq Θ → tenv_dual peq' Θ.
Proof. intros Hp H c e1 e2 He. destruct (H c e1 e2 He). auto. Qed.

Lemma tenv_comp_mono (peq peq' : point → point → Prop) Θ Θ1 Θ2 :
  (∀ x y, peq x y → peq' x y) → tenv_comp peq Θ Θ1 Θ2 → tenv_comp peq' Θ Θ1 Θ2.
Proof.
  intros Hp [Hj H]. split; [done|]. intros c e1 e2 H1 H2.
  destruct (H c e1 e2 H1 H2). auto.
Qed.
