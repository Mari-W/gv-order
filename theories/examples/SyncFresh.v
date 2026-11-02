(** * sync with a fresh point

    [sync_main] of Sync.v, its channel created by E-NewFresh with no
    facts. The world loses its one constant and becomes empty. The
    channel is bound by the encoded let of new, so the program is the
    copy [sync_main_ex] (sharp edges 99, 103). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Sync.

Set Default Proof Using "All".

(** [sync_main] with c bound by the encoded let of new. *)
Definition sync_main_ex : expr :=
  let_new_pair
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Lemma sync_typed_fresh : styped ∅ [] [] (∅, None) sync_main_ex TUnit.
Proof. exact sync_typed. Qed.

Lemma sync_deadlock_free_fresh : deadlock_free (∅, {[+ sync_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed_s; [constructor|apply sync_typed_fresh].
Qed.
