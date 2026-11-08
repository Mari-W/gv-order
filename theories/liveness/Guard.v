(** * The guarded fragment (liveness.md §6, sharp edges 157, 160)

    The self of a box is a later hypothesis. A session primitive (send,
    receive, close, select, branch) discharges it for its continuation.
    A link does not: it costs nothing (lock-freedom plan §6.1). The guard passes through let, let-pair, pairs and the
    arguments of an application, through an applied λ (App (Lam b) e is
    a let), and through case when both branches are guarded. A closure
    built before the guard may not hold the self. Forcing the self is no
    use, only applying the forced value is: (force x) e is allowed when e
    itself is guarded, and only under the λs of the box body (sharp
    edges 161).

    [gtyped] and [gstyped] are the static judgments restricted to terms
    whose boxes are all guarded. They are sub-systems of [typed] and
    [styped] by definition ([gtyped_typed], [gstyped_styped]). E-Exp
    itself stays unguarded. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Source.

(** ** A term performs a session primitive before it returns *)

Definition prim_konst (k : konst) : bool :=
  match k with KRecv | KSend | KClos | KSel1 | KSel2 | KBra => true | _ => false end.

Fixpoint gd (e : expr) : bool :=
  match e with
  | App (Konst k) e2 => prim_konst k || gd e2
  | App (Lam b) e2 => gd e2 || gd b
  | App e1 e2 => gd e1 || gd e2
  | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => gd e1 || gd e2
  | Case e e1 e2 => gd e || (gd e1 && gd e2)
  | Inj1 e | Inj2 e => gd e
  | _ => false
  end.

(** ** x occurs free *)
Fixpoint occurs (x : nat) (e : expr) : bool :=
  match e with
  | Var y => Nat.eqb x y
  | EUnit | Konst _ | Chan _ => false
  | Lam e | EBox e => occurs (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occurs x e1 || occurs x e2
  | LetP e1 e2 => occurs x e1 || occurs (S (S x)) e2
  | Inj1 e | Inj2 e => occurs x e
  | Case e e1 e2 => occurs x e || occurs (S x) e1 || occurs (S x) e2
  end.

(** ** x, a later hypothesis, is used only after a guard

    [f] permits the special case (force x) e. It holds only under the λs
    of a box body, where forcing the self returns that λ in one step
    (sharp edges 161). *)
Fixpoint ok (f : bool) (x : nat) (e : expr) : bool :=
  match e with
  | Var y => negb (Nat.eqb x y)
  | EUnit | Konst _ | Chan _ => true
  | Lam b | EBox b => negb (occurs (S x) b)
  | App (App (Konst KForce) (Var y)) e2 =>
      if Nat.eqb x y then f && gd e2 && ok f x e2 else ok f x e2
  | App (Lam b) e2 => ok f x e2 && (gd e2 || ok f (S x) b)
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => ok f x e1 && (gd e1 || ok f x e2)
  | LetP e1 e2 => ok f x e1 && (gd e1 || ok f (S (S x)) e2)
  | Inj1 e | Inj2 e => ok f x e
  | Case e e1 e2 => ok f x e && (gd e || (ok f (S x) e1 && ok f (S x) e2))
  end.

(** The body of a box runs when the forced value is applied, so the
    guard is read under the λs of the body, and there forcing the self
    is allowed. *)
Fixpoint okv (f : bool) (x : nat) (e : expr) : bool :=
  match e with
  | Lam b => okv true (S x) b
  | _ => ok f x e
  end.

(** Every box of the term is guarded. *)
Fixpoint gall (e : expr) : bool :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => true
  | EBox b => okv false 0 b && gall b
  | Lam e | Inj1 e | Inj2 e => gall e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => gall e1 && gall e2
  | Case e e1 e2 => gall e && gall e1 && gall e2
  end.

Definition guarded (e : expr) : Prop := gall e = true.

(** ** The guarded judgments *)

Definition gtyped (W : world) Φ Ψ Θ Δ F (e : expr) (T : ty) : Prop :=
  typed W Φ Ψ Θ Δ F e T ∧ guarded e.

Definition gstyped Φ Ψ Δ F (e : expr) (T : ty) : Prop :=
  styped Φ Ψ Δ F e T ∧ guarded e.

Definition gptyped (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ptyped W Σ p T ∧ ∀ e, e ∈ p.2 → guarded e.

Lemma gtyped_typed W Φ Ψ Θ Δ F e T : gtyped W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F e T.
Proof. by intros [? _]. Qed.

Lemma gstyped_styped Φ Ψ Δ F e T : gstyped Φ Ψ Δ F e T → styped Φ Ψ Δ F e T.
Proof. by intros [? _]. Qed.

Lemma gptyped_ptyped W Σ p T : gptyped W Σ p T → ptyped W Σ p T.
Proof. by intros [? _]. Qed.
