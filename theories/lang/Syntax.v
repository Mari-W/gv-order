(** * Syntax of GV♯ (Fig. 1)

    Terms use de Bruijn indices for variables; channels are names.
    Values are the sub-language carved out by [is_val] (single inductive
    [expr], heap_lang style), so that ⟨v,v⟩ and ⟨e,e⟩ need not be
    distinguished syntactically. *)

From stdpp Require Import base strings gmap gmultiset countable.

Definition chan := string.

(** Constants for the concurrency primitives. [new] creates a channel
    and returns both of its ends; [spawn] starts a thread running a
    thunk (they replace the paper's fork, which did both at once). *)
Inductive konst :=
  | KNew | KSpawn | KRecv | KSend | KClos | KLink
  | KForce
  | KSel1 | KSel2 | KBra.          (* select₁, select₂ and branch (K4) *)

Inductive expr :=
  | Var (x : nat)
  | EUnit                          (* the unit value ∗ *)
  | Konst (k : konst)
  | Chan (c : chan)
  | Lam (e : expr)                 (* λa.e — binds 1 *)
  | App (e1 e2 : expr)
  | Pair (e1 e2 : expr)            (* ⟨e1,e2⟩ *)
  | LetU (e1 e2 : expr)            (* let ∗ = e1 in e2 *)
  | LetP (e1 e2 : expr)            (* let ⟨a,b⟩ = e1 in e2 — binds 2 in e2:
                                      index 1 = a, index 0 = b *)
  | Inj1 (e : expr)                (* left injection *)
  | Inj2 (e : expr)                (* right injection *)
  | Case (e e1 e2 : expr)          (* case e (a.e1) (a.e2) — each branch
                                      binds 1: index 0 = the payload *)
  | EBox (e : expr).              (* !e — a recursively defined thunk
                                      value (suspends e); binds 1:
                                      index 0 = the thunk itself *)

Notation ENew := (Konst KNew).
Notation ESpawn := (Konst KSpawn).
Notation ERecv := (Konst KRecv).
Notation ESend := (Konst KSend).
Notation EClos := (Konst KClos).
Notation ELink := (Konst KLink).
(** force is simply a function: forcing is application, so it needs no
    evaluation context of its own.  force (!e) —β→ e[!e/x]. *)
Notation EForce := (Konst KForce).
(** Binary choice (K4 of docs/extensions/context-free.md). select₁ c and
    select₂ c pick a branch of c, branch c waits for the pick and
    returns c in the matching injection, so case does the dispatch. *)
Notation ESel1 := (Konst KSel1).
Notation ESel2 := (Konst KSel2).
Notation EBra := (Konst KBra).

(** The selection constant of a branch: select₁ for false, select₂ for true. *)
Definition ksel (b : bool) : konst := if b then KSel2 else KSel1.

(** ** Values *)

Fixpoint is_val (e : expr) : bool :=
  match e with
  | EUnit | Konst _ | Chan _ | Lam _ | EBox _ => true
  | Pair e1 e2 => is_val e1 && is_val e2
  | Inj1 e | Inj2 e => is_val e
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
    (λ k, match k with
          | KNew => 0 | KSpawn => 1 | KRecv => 2 | KSend => 3 | KClos => 4
          | KLink => 5 | KForce => 6 | KSel1 => 7 | KSel2 => 8 | KBra => 9
          end)
    (λ n, match n with
          | 0 => KNew | 1 => KSpawn | 2 => KRecv | 3 => KSend | 4 => KClos
          | 5 => KLink | 6 => KForce | 7 => KSel1 | 8 => KSel2 | _ => KBra
          end)).
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
    | Inj1 e => GenNode 6 [go e]
    | Inj2 e => GenNode 7 [go e]
    | Case e e1 e2 => GenNode 8 [go e; go e1; go e2]
    | EBox e => GenNode 9 [go e]
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
    | GenNode 6 [t] => Inj1 (go t)
    | GenNode 7 [t] => Inj2 (go t)
    | GenNode 8 [t; t1; t2] => Case (go t) (go t1) (go t2)
    | GenNode 9 [t] => EBox (go t)
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
  | Inj1 e => Inj1 (rename r e)
  | Inj2 e => Inj2 (rename r e)
  | Case e e1 e2 =>
      Case (rename r e) (rename (upren r) e1) (rename (upren r) e2)
  | EBox e => EBox (rename (upren r) e)
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
  | Inj1 e => Inj1 (subst σ e)
  | Inj2 e => Inj2 (subst σ e)
  | Case e e1 e2 => Case (subst σ e) (subst (up σ) e1) (subst (up σ) e2)
  | EBox e => EBox (subst (up σ) e)
  end.

(** β-substitutions: [subst1 v e] is e[v/a] for a Lam-bound a;
    [subst2 u v e] instantiates the two binders of LetP with the pair
    components, i.e. e[u/a][v/b]. *)
Definition subst1 (v : expr) (e : expr) : expr := subst (v .: Var) e.
Definition subst2 (u v : expr) (e : expr) : expr := subst (v .: u .: Var) e.

(** The encoded let of new (sharp edges 99). The calculus has no let
    of a single variable, so let p = new ∗ in let ⟨a, b⟩ = p in e is a
    let pair on ⟨new ∗, ∗⟩ that drops the unit. p is variable 1 of the
    middle body, and e sees a and b at 1 and 0 and the spent p and unit
    at 3 and 2. *)
Definition let_new (e : expr) : expr :=
  LetP (Pair (App ENew EUnit) EUnit) (LetU (Var 0) (LetP (Var 1) e)).

(** The same program with e indexed as the body of a let pair, a at 1,
    b at 0 and the outer variables from 2. The examples write this. *)
Definition let_new_pair (e : expr) : expr :=
  let_new (rename (upren (upren (λ x, 2 + x))) e).

(** ** Closedness and free channels *)

Fixpoint closed_at (n : nat) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x < n)
  | EUnit | Konst _ | Chan _ => true
  | Lam e => closed_at (S n) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => closed_at n e1 && closed_at n e2
  | LetP e1 e2 => closed_at n e1 && closed_at (S (S n)) e2
  | Inj1 e | Inj2 e => closed_at n e
  | Case e e1 e2 => closed_at n e && closed_at (S n) e1 && closed_at (S n) e2
  | EBox e => closed_at (S n) e
  end.

(** All channels in a term are considered free (terms only bind variables). *)
Fixpoint fchans (e : expr) : gset chan :=
  match e with
  | Var _ | EUnit | Konst _ => ∅
  | Chan c => {[c]}
  | Lam e | Inj1 e | Inj2 e | EBox e => fchans e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => fchans e1 ∪ fchans e2
  | Case e e1 e2 => fchans e ∪ fchans e1 ∪ fchans e2
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
  - rewrite (subst_ext _ (up Var) Var); [done|by intros [|x]].
  - rewrite (subst_ext _ (up Var) Var); [done|by intros [|x]].
  - rewrite (subst_ext _ (up Var) Var); [done|by intros [|x]].
Qed.

(** ** Composition laws for renaming and substitution *)

Lemma rename_rename e : ∀ r r',
  rename r (rename r' e) = rename (λ x, r (r' x)) e.
Proof.
  induction e; intros r r'; simpl; f_equal; auto.
  - rewrite IHe. apply rename_ext. by intros [|x].
  - rewrite IHe2. apply rename_ext. by intros [|[|x]].
  - rewrite IHe2. apply rename_ext. by intros [|x].
  - rewrite IHe3. apply rename_ext. by intros [|x].
  - rewrite IHe. apply rename_ext. by intros [|x].
Qed.

Lemma subst_rename e : ∀ σ r,
  subst σ (rename r e) = subst (λ x, σ (r x)) e.
Proof.
  induction e; intros σ r; simpl; f_equal; auto.
  - rewrite IHe. apply subst_ext. by intros [|x].
  - rewrite IHe2. apply subst_ext. by intros [|[|x]].
  - rewrite IHe2. apply subst_ext. by intros [|x].
  - rewrite IHe3. apply subst_ext. by intros [|x].
  - rewrite IHe. apply subst_ext. by intros [|x].
Qed.

Lemma rename_subst e : ∀ r σ,
  rename r (subst σ e) = subst (λ x, rename r (σ x)) e.
Proof.
  induction e; intros r σ; simpl; f_equal; auto.
  - rewrite IHe. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. by rewrite !rename_rename.
  - rewrite IHe2. apply subst_ext. intros [|[|x]]; simpl; [done..|].
    unfold compose. by rewrite !rename_rename.
  - rewrite IHe2. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. by rewrite !rename_rename.
  - rewrite IHe3. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. by rewrite !rename_rename.
  - rewrite IHe. apply subst_ext. intros [|x]; simpl; [done|].
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
  - rewrite IHe2. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. rewrite subst_rename, rename_subst.
    apply subst_ext. by intros y.
  - rewrite IHe3. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. rewrite subst_rename, rename_subst.
    apply subst_ext. by intros y.
  - rewrite IHe. apply subst_ext. intros [|x]; simpl; [done|].
    unfold compose. rewrite subst_rename, rename_subst.
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

(** ** The encoded let of new under renaming and substitution *)

Lemma rename_let_new_pair r e :
  rename r (let_new_pair e) = let_new_pair (rename (upren (upren r)) e).
Proof.
  unfold let_new_pair, let_new. simpl. do 3 f_equal.
  rewrite !rename_rename. apply rename_ext. by intros [|[|x]].
Qed.

Lemma subst_let_new_pair σ e :
  subst σ (let_new_pair e) = let_new_pair (subst (up (up σ)) e).
Proof.
  unfold let_new_pair, let_new. simpl. do 3 f_equal.
  rewrite subst_rename, rename_subst. apply subst_ext. intros [|[|x]]; simpl; [done..|].
  unfold compose. by rewrite !rename_rename.
Qed.

(** The first β of the encoded let after new gives the body back. *)
Lemma let_new_body u v e :
  subst (up (up (v .: u .: Var))) (rename (upren (upren (λ x, 2 + x))) e) = e.
Proof.
  rewrite subst_rename. etrans; [|apply subst_ids]. apply subst_ext. by intros [|[|x]].
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
  | Inj1 e | Inj2 e => allfv P e
  | Case e e1 e2 => allfv P e ∧ allfv (upP P) e1 ∧ allfv (upP P) e2
  | EBox e => allfv (upP P) e
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
  - eauto.
  - eauto.
  - destruct HP as (?&?&?). split; [by eapply IHe1|]. split.
    + eapply IHe2; [|done]. by apply upP_mono.
    + eapply IHe3; [|done]. by apply upP_mono.
  - eapply IHe; [|done]. by apply upP_mono.
Qed.

(** Occurrence of a free variable (the dual of [allfv]). *)
Fixpoint freevar (x : nat) (e : expr) : Prop :=
  match e with
  | Var y => x = y
  | EUnit | Konst _ | Chan _ => False
  | Lam e => freevar (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => freevar x e1 ∨ freevar x e2
  | LetP e1 e2 => freevar x e1 ∨ freevar (S (S x)) e2
  | Inj1 e | Inj2 e => freevar x e
  | Case e e1 e2 => freevar x e ∨ freevar (S x) e1 ∨ freevar (S x) e2
  | EBox e => freevar (S x) e
  end.

(** Renaming and the variable predicates. *)

Lemma upP_upren (P : nat → Prop) r x :
  upP (λ y, P (r y)) x → upP P (upren r x).
Proof. destruct x; simpl; auto. Qed.

Lemma allfv_rename e : ∀ (P : nat → Prop) r,
  allfv (λ x, P (r x)) e → allfv P (rename r e).
Proof.
  induction e; simpl; intros P r H; auto.
  - apply IHe. eapply allfv_mono; [|exact H]. apply upP_upren.
  - destruct H; split; auto.
  - destruct H; split; auto.
  - destruct H; split; auto.
  - destruct H; split; [auto|]. apply IHe2.
    eapply allfv_mono; [|done]. intros x Hx.
    apply upP_upren. eapply upP_mono; [|exact Hx]. apply upP_upren.
  - destruct H as (?&?&?). split_and!; [auto| |].
    + apply IHe2. eapply allfv_mono; [|done]. apply upP_upren.
    + apply IHe3. eapply allfv_mono; [|done]. apply upP_upren.
  - apply IHe. eapply allfv_mono; [|exact H]. apply upP_upren.
Qed.

Lemma freevar_rename e : ∀ x r, freevar x e → freevar (r x) (rename r e).
Proof.
  induction e; simpl; intros y r H; auto.
  - apply (IHe (S y) (upren r) H).
  - destruct H; auto.
  - destruct H; auto.
  - destruct H; auto.
  - destruct H; [auto|]. right. apply (IHe2 (S (S y)) (upren (upren r)) H).
  - destruct H as [?|[?|?]]; [auto| |].
    + right; left. apply (IHe2 (S y) (upren r) H).
    + right; right. apply (IHe3 (S y) (upren r) H).
  - apply (IHe (S y) (upren r) H).
Qed.

(** ** Channels under renaming and substitution *)

Lemma fchans_rename e : ∀ r, fchans (rename r e) = fchans e.
Proof.
  induction e; intros r; simpl; auto.
  all: try by rewrite IHe1, IHe2.
  by rewrite IHe1, IHe2, IHe3.
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
  - by specialize (IHe _ γ Hf).
  - by specialize (IHe _ γ Hf).
  - destruct Hf as [Hf|[Hf|Hf]].
    + specialize (IHe1 _ γ Hf). set_solver.
    + specialize (IHe2 (S y) (up γ) Hf). simpl in IHe2.
      unfold compose in IHe2. rewrite fchans_rename in IHe2. set_solver.
    + specialize (IHe3 (S y) (up γ) Hf). simpl in IHe3.
      unfold compose in IHe3. rewrite fchans_rename in IHe3. set_solver.
  - specialize (IHe (S y) (up γ) Hf). simpl in IHe.
    unfold compose in IHe. rewrite fchans_rename in IHe. exact IHe.
Qed.

Lemma fchans_subst e : ∀ γ (D : gset chan),
  allfv (λ x, fchans (γ x) ⊆ D) e →
  fchans (subst γ e) ⊆ fchans e ∪ D.
Proof.
  induction e; simpl; intros γ D HP;
    [set_solver|set_solver|set_solver|set_solver| | | | | | | | |];
    [|destruct HP as [H1 H2];
      specialize (IHe1 _ _ H1); specialize (IHe2 _ _ H2); set_solver ..| |set_solver|set_solver| | ].
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
  - (* Case *)
    destruct HP as (H0 & H1 & H2).
    specialize (IHe1 _ _ H0).
    assert (allfv (λ x, fchans (up γ x) ⊆ D) e2) as H1'.
    { eapply allfv_mono; [|exact H1]. intros [|x]; simpl.
      - intros _. set_solver.
      - intros Hc. unfold compose. by rewrite fchans_rename. }
    assert (allfv (λ x, fchans (up γ x) ⊆ D) e3) as H2'.
    { eapply allfv_mono; [|exact H2]. intros [|x]; simpl.
      - intros _. set_solver.
      - intros Hc. unfold compose. by rewrite fchans_rename. }
    specialize (IHe2 _ _ H1'). specialize (IHe3 _ _ H2'). set_solver.
  - (* EBox *)
    apply (IHe (up γ) D). eapply allfv_mono; [|done]. intros [|x]; simpl.
    + intros _. set_solver.
    + intros Hc. unfold compose. by rewrite fchans_rename.
Qed.

(** ** Transposition of two channel names *)

Definition cswap (a b c : chan) : chan :=
  if decide (c = a) then b else if decide (c = b) then a else c.

Lemma cswap_involutive a b c : cswap a b (cswap a b c) = c.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma cswap_l a b : cswap a b a = b.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma cswap_r a b : cswap a b b = a.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma cswap_ne a b c : c ≠ a → c ≠ b → cswap a b c = c.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma cswap_inj a b c c' : cswap a b c = cswap a b c' → c = c'.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Lemma cswap_comm a b c : cswap a b c = cswap b a c.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Fixpoint eswap (a b : chan) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Konst k => Konst k
  | Chan c => Chan (cswap a b c)
  | Lam e => Lam (eswap a b e)
  | App e1 e2 => App (eswap a b e1) (eswap a b e2)
  | Pair e1 e2 => Pair (eswap a b e1) (eswap a b e2)
  | LetU e1 e2 => LetU (eswap a b e1) (eswap a b e2)
  | LetP e1 e2 => LetP (eswap a b e1) (eswap a b e2)
  | Inj1 e => Inj1 (eswap a b e)
  | Inj2 e => Inj2 (eswap a b e)
  | Case e e1 e2 => Case (eswap a b e) (eswap a b e1) (eswap a b e2)
  | EBox e => EBox (eswap a b e)
  end.

Lemma eswap_involutive a b e : eswap a b (eswap a b e) = e.
Proof.
  induction e; simpl; f_equal; auto using cswap_involutive.
Qed.

Lemma eswap_comm a b e : eswap a b e = eswap b a e.
Proof. induction e; simpl; f_equal; auto using cswap_comm. Qed.

Lemma is_val_eswap a b e : is_val (eswap a b e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2. Qed.

(** ** Channel substitution (§4.5)

    e[d/c] — retarget every occurrence of channel c to d. Channels are
    names, not indices, so this is a plain traversal with no binders to
    cross; it is the term-level part of the forwarding step P-Act-Link. *)

Fixpoint chsubst (c d : chan) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Konst k => Konst k
  | Chan c' => Chan (if decide (c' = c) then d else c')
  | Lam e => Lam (chsubst c d e)
  | App e1 e2 => App (chsubst c d e1) (chsubst c d e2)
  | Pair e1 e2 => Pair (chsubst c d e1) (chsubst c d e2)
  | LetU e1 e2 => LetU (chsubst c d e1) (chsubst c d e2)
  | LetP e1 e2 => LetP (chsubst c d e1) (chsubst c d e2)
  | Inj1 e => Inj1 (chsubst c d e)
  | Inj2 e => Inj2 (chsubst c d e)
  | Case e e1 e2 => Case (chsubst c d e) (chsubst c d e1) (chsubst c d e2)
  | EBox e => EBox (chsubst c d e)
  end.

(** A universally true predicate holds of all free variables. *)
Lemma allfv_forall (P : nat → Prop) e : (∀ x, P x) → allfv P e.
Proof.
  revert P. induction e; simpl; intros P HP; split_and?; auto.
  all: first [apply IHe|apply IHe0|apply IHe1|apply IHe2|apply IHe3];
    intros [|[|x]]; simpl; auto.
Qed.

(** Channel bounds for the β-substitutions. *)

Lemma fchans_subst1_sub v e : fchans (subst1 v e) ⊆ fchans e ∪ fchans v.
Proof.
  apply fchans_subst. apply allfv_forall. intros [|x]; simpl; set_solver.
Qed.

Lemma fchans_subst2_sub u v e :
  fchans (subst2 u v e) ⊆ fchans e ∪ (fchans u ∪ fchans v).
Proof.
  apply fchans_subst. apply allfv_forall.
  intros [|[|x]]; simpl; set_solver.
Qed.

(** Transposing after the reverse substitution gives the substitution:
    pointwise, both sides send b ↦ b?  No — both send a ↦ b and fix b
    and everything else; see the case analysis in the proof. *)
Lemma eswap_chsubst_flip a b e :
  eswap a b (chsubst b a e) = chsubst a b e.
Proof.
  induction e; simpl; f_equal; auto.
  unfold cswap. repeat case_decide; congruence.
Qed.

Lemma chsubst_id c d e : c ∉ fchans e → chsubst c d e = e.
Proof.
  induction e; simpl; intros Hc; f_equal; auto;
    try (case_decide; [set_solver|done]);
    match goal with
    | IH : c ∉ fchans ?e0 → chsubst c d ?e0 = ?e0 |- chsubst c d ?e0 = ?e0 =>
        apply IH; set_solver
    end.
Qed.

Lemma is_val_chsubst c d e : is_val (chsubst c d e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2. Qed.

Lemma fchans_chsubst c d e :
  fchans (chsubst c d e) ⊆ (fchans e ∖ {[c]}) ∪ {[d]}.
Proof.
  induction e; simpl; try set_solver. case_decide; set_solver.
Qed.

(** ** Processes: soups of threads over a set of restricted channels

    A process is a pair (C, E) of a finite set C of (restricted)
    channels and a finite multiset E of closed terms running in
    parallel. *)

Definition proc : Type := gset chan * gmultiset expr.

(** Channels occurring free in some thread of E. *)
Definition echans (E : gmultiset expr) : gset chan :=
  ⋃ (fchans <$> elements E).

(** E[d/c] — retarget channel c to d in every thread. *)
Definition echsubst (c d : chan) (E : gmultiset expr) : gmultiset expr :=
  gmultiset_map (chsubst c d) E.

(** E[c↔d], the transposition of two channel names in every thread.
    Channel renaming uses it (ChannelSwap.v). *)
Definition echswap (c d : chan) (E : gmultiset expr) : gmultiset expr :=
  gmultiset_map (eswap c d) E.

Lemma elem_of_echans x E : x ∈ echans E ↔ ∃ e, e ∈ E ∧ x ∈ fchans e.
Proof.
  unfold echans. rewrite elem_of_union_list. split.
  - intros (X & HX & Hx). apply list_elem_of_fmap in HX as (e & -> & He).
    exists e. split; [|done]. by apply gmultiset_elem_of_elements.
  - intros (e & He & Hx). exists (fchans e). split; [|done].
    apply list_elem_of_fmap. exists e. split; [done|].
    by apply gmultiset_elem_of_elements.
Qed.

Lemma echans_disj_union E1 E2 : echans (E1 ⊎ E2) = echans E1 ∪ echans E2.
Proof.
  apply set_eq. intros x. rewrite elem_of_union, !elem_of_echans.
  setoid_rewrite gmultiset_elem_of_disj_union. naive_solver.
Qed.

Lemma echans_empty : echans ∅ = ∅.
Proof.
  unfold echans. by rewrite gmultiset_elements_empty.
Qed.

Lemma echans_singleton e : echans {[+ e +]} = fchans e.
Proof.
  unfold echans. rewrite gmultiset_elements_singleton. simpl. set_solver.
Qed.

Lemma echsubst_id c d E : c ∉ echans E → echsubst c d E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; intros Hc.
  - unfold echsubst. by rewrite gmultiset_map_empty.
  - rewrite echans_disj_union, echans_singleton in Hc.
    unfold echsubst in *.
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
    rewrite chsubst_id by set_solver. rewrite IH by set_solver. done.
Qed.

Lemma echsubst_disj_union c d E1 E2 :
  echsubst c d (E1 ⊎ E2) = echsubst c d E1 ⊎ echsubst c d E2.
Proof. apply gmultiset_map_disj_union. Qed.

Lemma echsubst_singleton c d e :
  echsubst c d {[+ e +]} = {[+ chsubst c d e +]}.
Proof. apply gmultiset_map_singleton. Qed.

(** The soup substitution only introduces the surviving name. *)
Lemma echans_echsubst_sub c d E :
  echans (echsubst c d E) ⊆ echans E ∪ {[d]}.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echsubst. rewrite gmultiset_map_empty. set_solver.
  - unfold echsubst in *.
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton,
      !echans_disj_union, !echans_singleton.
    pose proof (fchans_chsubst c d e). set_solver.
Qed.
