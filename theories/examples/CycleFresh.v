(** * cycle with fresh points

    [cycle_main] of Cycle.v. c is created at a fresh γ with no facts,
    d at a fresh ε with γ ≺ ε (L = [γ]). The world of Cycle.v had two
    constants and the fact (0, 0) ≺ (1, 0). Here it is empty. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Cycle.

Set Default Proof Using "All".

(** [cycle_main] with c and d bound by the encoded let of new (sharp
    edges 99, 103). let p = new ∗ in let (d, d′) = p in … *)
Definition cycle_main_ex : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Lemma cycle_typed_fresh : styped ∅ [] [] (∅, None) cycle_main_ex TUnit.
Proof. exact cycle_typed. Qed.

Lemma cycle_deadlock_free_fresh : deadlock_free (∅, {[+ cycle_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed_s; [constructor|apply cycle_typed_fresh].
Qed.
