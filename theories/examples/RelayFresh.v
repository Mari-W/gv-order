(** * relay with fresh points

    [rel_main] of Relay.v. Relay.v now creates both channels from
    creation constraints at top-level points (sharp edges 105, 172). c gets
    the facts of its own rounds, which relate (ι,k) to its carried
    points, and d gets the four facts of round 0 that mention it. This
    file keeps the copy [rel_main_ex] of the program and its theorem. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Relay.

Set Default Proof Using "All".

(** [rel_main] with d bound by the encoded let of new (sharp edges
    99). *)
Definition rel_main_ex : expr :=
  LetP (Pair relay prod) (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App (App EForce (Var 4)) (EPt (pt_dual (pconst 1)))) (Pair (Var 2) (Var 0)))))).

Lemma rel_typed_fresh : styped ∅ rel_Ψ [] (∅, None) rel_main_ex TUnit.
Proof. exact rel_typed. Qed.

Lemma rel_deadlock_free_fresh : deadlock_free (∅, {[+ rel_main_ex +]}).
Proof.
  apply (soundness_created_s rel_Ψ _ TUnit rel_created); [constructor|apply rel_typed_fresh].
Qed.
