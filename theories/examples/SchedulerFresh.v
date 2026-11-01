(** * scheduler with fresh points

    [sched_main] of Scheduler.v. r₀ is created at a fresh γ with no
    facts. r₁ needs the alias (r₁,0) ≡ (r₀,0) for the link, so the old
    rule E-Const creates it at γ itself, which the hypothesis of r₀
    makes known. r₂ is created at a fresh ε with γ+1 ≺ ε (L = [γ+1]).
    The world of Scheduler.v had three constants, one alias and one
    fact. Here it is empty. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Scheduler.

Set Default Proof Using "All".

(** [sched_main] with r₂ bound by the encoded let of new (sharp
    edges 99). *)
Definition sched_main_ex : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed_fresh W : strict W → typed W ∅ [] ∅ [] (∅, None) sched_main_ex TUnit.
Proof. exact (sched_typed W). Qed.

Lemma sched_deadlock_free_fresh : deadlock_free (∅, {[+ sched_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed; [constructor|]. apply sched_typed_fresh, Wpo_nil_strict.
Qed.
