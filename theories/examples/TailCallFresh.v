(** * tail call with a fresh point

    [tc_main] of TailCall.v. TailCall.v now creates c in the empty world
    with the creation constraint {ι+k ≺ ι[0] ∣ k ∈ ℕ}, whose ceiling is
    the carried point ι[0] (sharp edges 105). Before, the ceiling was
    the constant (1, 0) of the world. This file keeps the copy
    [tc_main_ex] of the program and its theorem. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.TailCall.

Set Default Proof Using "All".

(** [tc_main] with c bound by the encoded let of new. *)
Definition tc_main_ex : expr :=
  LetP (Pair tcs tcr) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Lemma tc_typed_fresh : styped ∅ [] [] (∅, None) tc_main_ex TUnit.
Proof. exact tc_typed. Qed.

Lemma tc_deadlock_free_fresh : deadlock_free (∅, {[+ tc_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed_s; [constructor|apply tc_typed_fresh].
Qed.
