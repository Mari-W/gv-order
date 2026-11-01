(** * request/reply with fresh points

    [rr_main] of RequestReply.v. a is created at a fresh γ with no
    facts, b at a fresh ε with the infinite constraint

      {γ+k ≺ ε+k,  ε+k ≺ γ+k+1  ∣  k ∈ ℕ}.

    Betweenness asks γ+k ≺ γ+k′+1 for every pair of facts γ+k ≺ ε+k and
    ε+k′ ≺ γ+k′+1 with k ≤ k′, and program order gives it. The world of
    RequestReply.v held these facts on two constants. Here it is empty,
    and the box constraint is unchanged. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.RequestReply.

Set Default Proof Using "All".

(** [rr_main] with b bound by the encoded let of new (sharp edges
    99). *)
Definition rr_main_ex : expr :=
  LetP (Pair srv cli) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

Lemma rr_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) rr_main_ex TUnit.
Proof. exact (rr_typed W). Qed.

Lemma rr_deadlock_free_fresh : deadlock_free (∅, {[+ rr_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply rr_typed_fresh, Wpo_nil_strict.
Qed.
