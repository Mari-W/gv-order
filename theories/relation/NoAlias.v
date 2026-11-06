(** * Worlds without aliases (branch no-eq, Step 2 groundwork)

    A world has no alias when its ≡ is equality. Without ≡ facts in
    constraints the constructions of the semantics keep that property:
    the generated world of facts without ≡ generators, the join of two
    alias-free worlds and the restriction of one are alias-free. This
    is the justification for reading w_eq as syntactic equality once no
    rule introduces ≡ (docs/extensions/no-equality.md §5). *)

From stdpp Require Import base gmap relations.
From LRGV Require Export relation.Worlds.

Definition noalias (W : world) : Prop := ∀ x y, w_eq W x y → x = y.

(** The congruence closure of generators that are equalities is
    equality. *)
Lemma geq_eq (E : point → point → Prop) x y :
  (∀ x y, E x y → x = y) → geq E x y → x = y.
Proof.
  intros HE. induction 1; subst; auto; congruence.
Qed.

Lemma wgen_noalias N E L : (∀ x y, E x y → x = y) → noalias (wgen N E L).
Proof. intros HE x y H. by apply (geq_eq E). Qed.

Lemma wgen_noalias_nil N L : noalias (wgen N (λ _ _, False) L).
Proof. apply wgen_noalias. done. Qed.

Lemma wjoin_noalias W1 W2 : noalias W1 → noalias W2 → noalias (wjoin W1 W2).
Proof. intros H1 H2. apply wgen_noalias. intros x y [H|H]; auto. Qed.

Lemma wrestrict_noalias W A : noalias W → noalias (wrestrict W A).
Proof. intros H x y [Hxy _]. auto. Qed.

(** In an alias-free well-formed world, w_le is equality or ≺. *)
Lemma w_le_noalias W x y : noalias W → w_le W x y → x = y ∨ w_lt W x y.
Proof. intros H [E|L]; [left; auto|by right]. Qed.
