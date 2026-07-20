(** * Syntax of GV♯ (Fig. 1)

    Terms use de Bruijn indices for variables; channels are names.
    Values are the sub-language carved out by [is_val] (single inductive
    [expr], heap_lang style), so that ⟨v,v⟩ and ⟨e,e⟩ need not be
    distinguished syntactically. *)

From stdpp Require Import base strings gmap countable.

Definition chan := string.

(** Constants for the concurrency primitives. *)
Inductive konst := KFork | KRecv | KSend | KClos.

Inductive expr :=
  | Var (x : nat)
  | EUnit                          (* the unit value ∗ *)
  | Konst (k : konst)
  | Chan (c : chan)
  | Lam (e : expr)                 (* λa.e — binds 1 *)
  | App (e1 e2 : expr)
  | Pair (e1 e2 : expr)            (* ⟨e1,e2⟩ *)
  | LetU (e1 e2 : expr)            (* let ∗ = e1 in e2 *)
  | LetP (e1 e2 : expr).           (* let ⟨a,b⟩ = e1 in e2 — binds 2 in e2:
                                      index 1 = a, index 0 = b *)

Notation EFork := (Konst KFork).
Notation ERecv := (Konst KRecv).
Notation ESend := (Konst KSend).
Notation EClos := (Konst KClos).

(** ** Values *)

Fixpoint is_val (e : expr) : bool :=
  match e with
  | EUnit | Konst _ | Chan _ | Lam _ => true
  | Pair e1 e2 => is_val e1 && is_val e2
  | _ => false
  end.

(** ** Decidable equality and countability

    [Countable expr] is needed to form multisets of terms
    ([gmultiset expr]) for the process semantics. *)

Global Instance konst_eq_dec : EqDecision konst.
Proof. solve_decision. Defined.

Global Instance konst_countable : Countable konst.
Proof.
  apply (inj_countable'
    (λ k, match k with KFork => 0 | KRecv => 1 | KSend => 2 | KClos => 3 end)
    (λ n, match n with 0 => KFork | 1 => KRecv | 2 => KSend | _ => KClos end)).
  by intros [].
Qed.

Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.

Global Instance expr_countable : Countable expr.
Proof.
  set (enc := fix go e : gen_tree (nat + konst + chan) :=
    match e with
    | Var x => GenLeaf (inl (inl x))
    | EUnit => GenNode 0 []
    | Konst k => GenLeaf (inl (inr k))
    | Chan c => GenLeaf (inr c)
    | Lam e => GenNode 1 [go e]
    | App e1 e2 => GenNode 2 [go e1; go e2]
    | Pair e1 e2 => GenNode 3 [go e1; go e2]
    | LetU e1 e2 => GenNode 4 [go e1; go e2]
    | LetP e1 e2 => GenNode 5 [go e1; go e2]
    end).
  set (dec := fix go t : expr :=
    match t with
    | GenLeaf (inl (inl x)) => Var x
    | GenNode 0 [] => EUnit
    | GenLeaf (inl (inr k)) => Konst k
    | GenLeaf (inr c) => Chan c
    | GenNode 1 [t] => Lam (go t)
    | GenNode 2 [t1; t2] => App (go t1) (go t2)
    | GenNode 3 [t1; t2] => Pair (go t1) (go t2)
    | GenNode 4 [t1; t2] => LetU (go t1) (go t2)
    | GenNode 5 [t1; t2] => LetP (go t1) (go t2)
    | _ => EUnit
    end).
  apply (inj_countable' enc dec).
  intros e; induction e; simpl; congruence.
Qed.

(** ** Renaming and parallel substitution *)

Definition scons {A} (a : A) (σ : nat → A) : nat → A :=
  λ x, match x with 0 => a | S x' => σ x' end.
Infix ".:" := scons (at level 55, right associativity).

Definition upren (r : nat → nat) : nat → nat := 0 .: (S ∘ r).

Fixpoint rename (r : nat → nat) (e : expr) : expr :=
  match e with
  | Var x => Var (r x)
  | EUnit | Konst _ | Chan _ => e
  | Lam e => Lam (rename (upren r) e)
  | App e1 e2 => App (rename r e1) (rename r e2)
  | Pair e1 e2 => Pair (rename r e1) (rename r e2)
  | LetU e1 e2 => LetU (rename r e1) (rename r e2)
  | LetP e1 e2 => LetP (rename r e1) (rename (upren (upren r)) e2)
  end.

Definition up (σ : nat → expr) : nat → expr := Var 0 .: (rename S ∘ σ).

Fixpoint subst (σ : nat → expr) (e : expr) : expr :=
  match e with
  | Var x => σ x
  | EUnit | Konst _ | Chan _ => e
  | Lam e => Lam (subst (up σ) e)
  | App e1 e2 => App (subst σ e1) (subst σ e2)
  | Pair e1 e2 => Pair (subst σ e1) (subst σ e2)
  | LetU e1 e2 => LetU (subst σ e1) (subst σ e2)
  | LetP e1 e2 => LetP (subst σ e1) (subst (up (up σ)) e2)
  end.

(** β-substitutions: [subst1 v e] is e[v/a] for a Lam-bound a;
    [subst2 u v e] instantiates the two binders of LetP with the pair
    components, i.e. e[u/a][v/b]. *)
Definition subst1 (v : expr) (e : expr) : expr := subst (v .: Var) e.
Definition subst2 (u v : expr) (e : expr) : expr := subst (v .: u .: Var) e.

(** ** Closedness and free channels *)

Fixpoint closed_at (n : nat) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x < n)
  | EUnit | Konst _ | Chan _ => true
  | Lam e => closed_at (S n) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => closed_at n e1 && closed_at n e2
  | LetP e1 e2 => closed_at n e1 && closed_at (S (S n)) e2
  end.

Definition closed (e : expr) : bool := closed_at 0 e.

(** All channels in a term are considered free (terms only bind variables). *)
Fixpoint fchans (e : expr) : gset chan :=
  match e with
  | Var _ | EUnit | Konst _ => ∅
  | Chan c => {[c]}
  | Lam e => fchans e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => fchans e1 ∪ fchans e2
  end.

(** ** Basic lemmas about substitution *)

Lemma upren_ext r r' : (∀ x, r x = r' x) → ∀ x, upren r x = upren r' x.
Proof. intros H [|x]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma rename_ext e : ∀ r r', (∀ x, r x = r' x) → rename r e = rename r' e.
Proof.
  induction e; intros r r' H; simpl; f_equal; eauto using upren_ext.
Qed.

Lemma up_ext σ σ' : (∀ x, σ x = σ' x) → ∀ x, up σ x = up σ' x.
Proof. intros H [|x]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma subst_ext e : ∀ σ σ', (∀ x, σ x = σ' x) → subst σ e = subst σ' e.
Proof.
  induction e; intros σ σ' H; simpl; f_equal; eauto using up_ext.
Qed.

Lemma subst_ids e : subst Var e = e.
Proof.
  induction e; simpl; f_equal; auto.
  - rewrite (subst_ext _ (up Var) Var); [done|by intros [|x]].
  - rewrite (subst_ext _ (up (up Var)) Var); [done|].
    intros [|[|x]]; done.
Qed.

(** Substitutions agreeing below the closedness bound act identically. *)
Lemma subst_closed_at_ext e : ∀ n σ σ',
  closed_at n e → (∀ x, x < n → σ x = σ' x) → subst σ e = subst σ' e.
Proof.
  induction e; intros n σ σ' Hcl Hag; simpl in *; f_equal;
    repeat match goal with
    | H : Is_true (_ && _) |- _ => apply andb_True in H as [? ?]
    end; eauto.
  - apply bool_decide_unpack in Hcl. by apply Hag.
  - eapply IHe; [done|]. intros [|x] Hx; simpl; [done|].
    unfold compose. rewrite Hag; [done|lia].
  - eapply IHe2; [done|]. intros [|[|x]] Hx; simpl; [done..|].
    unfold compose. rewrite Hag; [done|lia].
Qed.

Lemma subst_closed e σ : closed e → subst σ e = e.
Proof.
  intros Hcl. rewrite (subst_closed_at_ext e 0 σ Var); [|done|lia].
  apply subst_ids.
Qed.

Lemma subst1_closed e v : closed e → subst1 v e = e.
Proof. apply subst_closed. Qed.

(** ** Composition laws for renaming and substitution *)

Lemma rename_rename e : ∀ r r',
  rename r (rename r' e) = rename (λ x, r (r' x)) e.
Proof.
  induction e; intros r r'; simpl; f_equal; auto.
  - rewrite IHe. apply rename_ext. by intros [|x].
  - rewrite IHe2. apply rename_ext. by intros [|[|x]].
Qed.

Lemma subst_rename e : ∀ σ r,
  subst σ (rename r e) = subst (λ x, σ (r x)) e.
Proof.
  induction e; intros σ r; simpl; f_equal; auto.
  - rewrite IHe. apply subst_ext. by intros [|x].
  - rewrite IHe2. apply subst_ext. by intros [|[|x]].
Qed.

Lemma rename_subst e : ∀ r σ,
  rename r (subst σ e) = subst (λ x, rename r (σ x)) e.
Proof.
  induction e; intros r σ; simpl; f_equal; auto.
  - rewrite IHe. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. by rewrite !rename_rename.
  - rewrite IHe2. apply subst_ext. intros [|[|x]]; simpl; [done..|].
    unfold compose. by rewrite !rename_rename.
Qed.

Lemma subst_subst e : ∀ σ τ,
  subst σ (subst τ e) = subst (λ x, subst σ (τ x)) e.
Proof.
  induction e; intros σ τ; simpl; f_equal; auto.
  - rewrite IHe. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. rewrite subst_rename, rename_subst.
    apply subst_ext. by intros y.
  - rewrite IHe2. apply subst_ext. intros [|[|x]]; simpl; [done..|].
    unfold compose. rewrite !subst_rename, !rename_subst.
    apply subst_ext. by intros y.
Qed.

(** β-substitution after substitution under one/two binders. *)
Lemma subst1_subst w γ e : subst1 w (subst (up γ) e) = subst (w .: γ) e.
Proof.
  unfold subst1. rewrite subst_subst. apply subst_ext.
  intros [|x]; simpl; [done|]. unfold compose. rewrite subst_rename.
  etrans; [apply subst_ext; by intros y|]. apply subst_ids.
Qed.

Lemma subst2_subst u w γ e :
  subst2 u w (subst (up (up γ)) e) = subst (w .: u .: γ) e.
Proof.
  unfold subst2. rewrite subst_subst. apply subst_ext.
  intros [|[|x]]; simpl; [done..|]. unfold compose.
  rewrite !subst_rename.
  etrans; [apply subst_ext; by intros y|]. apply subst_ids.
Qed.

(** ** Free-variable predicates

    [allfv P e] states that every free variable of e satisfies P;
    binders lift P by [upP]. *)

Definition upP (P : nat → Prop) : nat → Prop :=
  λ x, match x with 0 => True | S x' => P x' end.

Fixpoint allfv (P : nat → Prop) (e : expr) : Prop :=
  match e with
  | Var x => P x
  | EUnit | Konst _ | Chan _ => True
  | Lam e => allfv (upP P) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => allfv P e1 ∧ allfv P e2
  | LetP e1 e2 => allfv P e1 ∧ allfv (upP (upP P)) e2
  end.

Lemma upP_mono (P Q : nat → Prop) :
  (∀ x, P x → Q x) → ∀ x, upP P x → upP Q x.
Proof. intros H [|x]; simpl; auto. Qed.

Lemma allfv_mono e : ∀ (P Q : nat → Prop),
  (∀ x, P x → Q x) → allfv P e → allfv Q e.
Proof.
  induction e; simpl; intros P Q H HP; auto.
  - eapply IHe; [|done]. by apply upP_mono.
  - destruct HP; eauto.
  - destruct HP; eauto.
  - destruct HP; eauto.
  - destruct HP; split; [by eapply IHe1|].
    eapply IHe2; [|done]. by apply upP_mono, upP_mono.
Qed.

(** Occurrence of a free variable (the dual of [allfv]). *)
Fixpoint freevar (x : nat) (e : expr) : Prop :=
  match e with
  | Var y => x = y
  | EUnit | Konst _ | Chan _ => False
  | Lam e => freevar (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => freevar x e1 ∨ freevar x e2
  | LetP e1 e2 => freevar x e1 ∨ freevar (S (S x)) e2
  end.

(** ** Closedness under renaming and substitution *)

Lemma closed_at_rename e : ∀ r m m',
  (∀ x, x < m → r x < m') → closed_at m e → closed_at m' (rename r e).
Proof.
  induction e; simpl; intros r m m' Hr Hcl;
    repeat match goal with
    | H : Is_true (_ && _) |- _ => apply andb_True in H as [? ?]
    end; try (apply andb_True; split); eauto.
  - apply bool_decide_unpack in Hcl. case_bool_decide; [done|]. exfalso; auto with lia.
  - eapply IHe; [|done]. intros [|x] Hx; simpl; [lia|].
    unfold compose. assert (r x < m') by (apply Hr; lia). lia.
  - eapply IHe2; [|done]. intros [|[|x]] Hx; simpl; [lia|lia|].
    unfold compose. assert (r x < m') by (apply Hr; lia). lia.
Qed.

Lemma closed_at_subst e : ∀ m γ,
  allfv (λ x, closed_at m (γ x)) e → closed_at m (subst γ e).
Proof.
  induction e; simpl; intros m γ HP;
    try (destruct HP; apply andb_True; split); eauto.
  - apply IHe. eapply allfv_mono; [|done]. intros [|x]; simpl.
    + intros _. done.
    + intros Hc. unfold compose. eapply closed_at_rename; [|done].
      intros; lia.
  - apply IHe2. eapply allfv_mono; [|done]. intros [|[|x]]; simpl.
    + intros _. done.
    + intros _. done.
    + intros Hc. unfold compose.
      eapply (closed_at_rename _ S (S m)); [intros; lia|].
      eapply (closed_at_rename _ S m); [intros; lia|done].
Qed.

(** ** Channels under renaming and substitution *)

Lemma fchans_rename e : ∀ r, fchans (rename r e) = fchans e.
Proof.
  induction e; intros r; simpl; auto.
  all: by rewrite IHe1, IHe2.
Qed.

(** Substitution can only add channels... *)
Lemma fchans_subst_super e : ∀ γ, fchans e ⊆ fchans (subst γ e).
Proof. induction e; intros γ; simpl; set_solver. Qed.

(** ... and the channels of values substituted for occurring variables
    all appear in the result. *)
Lemma fchans_subst_free e : ∀ y γ,
  freevar y e → fchans (γ y) ⊆ fchans (subst γ e).
Proof.
  induction e; simpl; intros y γ Hf; try done.
  - by subst.
  - specialize (IHe (S y) (up γ) Hf). simpl in IHe.
    unfold compose in IHe. rewrite fchans_rename in IHe. exact IHe.
  - destruct Hf as [Hf|Hf];
      [specialize (IHe1 _ γ Hf)|specialize (IHe2 _ γ Hf)]; set_solver.
  - destruct Hf as [Hf|Hf];
      [specialize (IHe1 _ γ Hf)|specialize (IHe2 _ γ Hf)]; set_solver.
  - destruct Hf as [Hf|Hf];
      [specialize (IHe1 _ γ Hf)|specialize (IHe2 _ γ Hf)]; set_solver.
  - destruct Hf as [Hf|Hf]; [specialize (IHe1 _ γ Hf); set_solver|].
    specialize (IHe2 _ (up (up γ)) Hf). simpl in IHe2.
    unfold compose in IHe2. rewrite !fchans_rename in IHe2. set_solver.
Qed.

Lemma fchans_subst e : ∀ γ (D : gset chan),
  allfv (λ x, fchans (γ x) ⊆ D) e →
  fchans (subst γ e) ⊆ fchans e ∪ D.
Proof.
  induction e; simpl; intros γ D HP;
    try (destruct HP as [H1 H2];
         specialize (IHe1 _ _ H1); specialize (IHe2 _ _ H2); set_solver);
    try set_solver.
  - (* Lam *)
    apply (IHe (up γ) D). eapply allfv_mono; [|done]. intros [|x]; simpl.
    + intros _. set_solver.
    + intros Hc. unfold compose. by rewrite fchans_rename.
  - (* LetP *)
    destruct HP as [H1 H2].
    specialize (IHe1 _ _ H1).
    assert (allfv (λ x, fchans (up (up γ) x) ⊆ D) e2) as H2'.
    { eapply allfv_mono; [|done]. intros [|[|x]]; simpl.
      - intros _. set_solver.
      - intros _. set_solver.
      - intros Hc. unfold compose. by rewrite !fchans_rename. }
    specialize (IHe2 _ _ H2'). set_solver.
Qed.
