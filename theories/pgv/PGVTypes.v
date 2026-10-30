(** * Types of Priority GV

    Kokke and Dardha, "Prioritise the Best Variation", LMCS 19(4):28
    (arXiv 2103.14466v6), §2.1, pdf pages 4 to 5. Priorities o ∈ ℕ on
    the connectives of session types, bounds p, q ∈ ℕ ∪ {⊥, ⊤} on
    arrows, duality that keeps priorities, and pr(·). The empty type 0
    is left out. *)

From stdpp Require Import base countable.

(** ** Priorities: ℕ ∪ {⊥, ⊤} *)

Inductive prio := PBot | PNat (n : nat) | PTop.

Definition prio_lt (a b : prio) : Prop :=
  match a, b with
  | PBot, PBot => False
  | PBot, _ => True
  | PNat n, PNat m => n < m
  | PNat _, PTop => True
  | _, _ => False
  end.

Definition prio_le (a b : prio) : Prop :=
  match a, b with
  | PBot, _ => True
  | PNat n, PNat m => n ≤ m
  | _, PTop => True
  | _, _ => False
  end.

(** p ⊔ q and p ⊓ q. *)
Definition prio_max (a b : prio) : prio :=
  match a, b with
  | PBot, x | x, PBot => x
  | PTop, _ | _, PTop => PTop
  | PNat n, PNat m => PNat (n `max` m)
  end.

Definition prio_min (a b : prio) : prio :=
  match a, b with
  | PTop, x | x, PTop => x
  | PBot, _ | _, PBot => PBot
  | PNat n, PNat m => PNat (n `min` m)
  end.

(** ** Types (p. 4)

    S ::= !ᵒT.S | ?ᵒT.S | endᵒ_! | endᵒ_?
    T ::= T × U | 1 | T + U | T ⊸^{p,q} U | S

    In [PLolli p q T U], p is the lower bound and q the upper bound. *)

Inductive pty :=
  | PUnit
  | PProd (T U : pty)
  | PSum (T U : pty)
  | PLolli (p q : prio) (T U : pty)
  | PSess (S : psty)
with psty :=
  | PSnd (o : nat) (T : pty) (S : psty)
  | PRcv (o : nat) (T : pty) (S : psty)
  | PEndS (o : nat)
  | PEndR (o : nat).

Scheme pty_mut_ind := Induction for pty Sort Prop
  with psty_mut_ind := Induction for psty Sort Prop.
Combined Scheme pty_psty_mut_ind from pty_mut_ind, psty_mut_ind.

(** ** Duality keeps priorities (p. 5) *)

Fixpoint pdual (S : psty) : psty :=
  match S with
  | PSnd o T S' => PRcv o T (pdual S')
  | PRcv o T S' => PSnd o T (pdual S')
  | PEndS o => PEndR o
  | PEndR o => PEndS o
  end.

Lemma pdual_involutive S : pdual (pdual S) = S.
Proof. induction S; simpl; by f_equal. Qed.

(** ** pr(·) (p. 5)

    The priority of the top connective of a session type, and the
    smallest priority inside other types, ⊤ when there is none. *)

Definition spr (S : psty) : nat :=
  match S with PSnd o _ _ | PRcv o _ _ | PEndS o | PEndR o => o end.

Fixpoint pr (T : pty) : prio :=
  match T with
  | PUnit => PTop
  | PProd T U | PSum T U => prio_min (pr T) (pr U)
  | PLolli p _ _ _ => p
  | PSess s => PNat (spr s)
  end.

Lemma spr_dual S : spr (pdual S) = spr S.
Proof. by destruct S. Qed.

(** ** The fragment (decided by the author)

    A session type is monotone when every connective lies below the top
    priority of its continuation, recursively. Our worlds order all
    instants at once, so a session that falls has no strict world of
    protocol points (docs/extensions/adequacy/pgv-adequacy.md §2). *)

Fixpoint pgv_mono (S : psty) : Prop :=
  match S with
  | PSnd o _ S' | PRcv o _ S' => o < spr S' ∧ pgv_mono S'
  | PEndS _ | PEndR _ => True
  end.

Lemma pgv_mono_dual S : pgv_mono (pdual S) ↔ pgv_mono S.
Proof. induction S; simpl; rewrite ?spr_dual; naive_solver. Qed.

(** ** Decidable equality and countability

    The protocol points of the world (PGVWorld.v) are slots indexed by
    a code of a session type. *)

Global Instance prio_eq_dec : EqDecision prio.
Proof. solve_decision. Defined.

Definition prio_enc (a : prio) : nat :=
  match a with PBot => 0 | PTop => 1 | PNat n => S (S n) end.
Definition prio_dec (n : nat) : prio :=
  match n with 0 => PBot | 1 => PTop | S (S n) => PNat n end.

Lemma prio_dec_enc a : prio_dec (prio_enc a) = a.
Proof. by destruct a. Qed.

Fixpoint pty_enc (T : pty) : gen_tree nat :=
  match T with
  | PUnit => GenNode 0 []
  | PProd T U => GenNode 1 [pty_enc T; pty_enc U]
  | PSum T U => GenNode 2 [pty_enc T; pty_enc U]
  | PLolli p q T U => GenNode 3 [GenLeaf (prio_enc p); GenLeaf (prio_enc q); pty_enc T; pty_enc U]
  | PSess s => GenNode 4 [psty_enc s]
  end
with psty_enc (S : psty) : gen_tree nat :=
  match S with
  | PSnd o T s => GenNode 5 [GenLeaf o; pty_enc T; psty_enc s]
  | PRcv o T s => GenNode 6 [GenLeaf o; pty_enc T; psty_enc s]
  | PEndS o => GenNode 7 [GenLeaf o]
  | PEndR o => GenNode 8 [GenLeaf o]
  end.

Fixpoint pty_dec (t : gen_tree nat) : pty :=
  match t with
  | GenNode 1 [t1; t2] => PProd (pty_dec t1) (pty_dec t2)
  | GenNode 2 [t1; t2] => PSum (pty_dec t1) (pty_dec t2)
  | GenNode 3 [GenLeaf p; GenLeaf q; t1; t2] => PLolli (prio_dec p) (prio_dec q) (pty_dec t1) (pty_dec t2)
  | GenNode 4 [t] => PSess (psty_dec t)
  | _ => PUnit
  end
with psty_dec (t : gen_tree nat) : psty :=
  match t with
  | GenNode 5 [GenLeaf o; t1; t2] => PSnd o (pty_dec t1) (psty_dec t2)
  | GenNode 6 [GenLeaf o; t1; t2] => PRcv o (pty_dec t1) (psty_dec t2)
  | GenNode 7 [GenLeaf o] => PEndS o
  | GenNode 8 [GenLeaf o] => PEndR o
  | _ => PEndS 0
  end.

Lemma pty_psty_dec_enc :
  (∀ T, pty_dec (pty_enc T) = T) ∧ (∀ S, psty_dec (psty_enc S) = S).
Proof. apply pty_psty_mut_ind; intros; simpl; rewrite ?prio_dec_enc; congruence. Qed.

Global Instance psty_eq_dec : EqDecision psty.
Proof.
  intros S1 S2. destruct (decide (psty_enc S1 = psty_enc S2)) as [E|E].
  - left. rewrite <-(proj2 pty_psty_dec_enc S1), <-(proj2 pty_psty_dec_enc S2). by rewrite E.
  - right. intros ->. by apply E.
Defined.

Global Instance psty_countable : Countable psty.
Proof.
  apply (inj_countable' psty_enc psty_dec). apply pty_psty_dec_enc.
Qed.
