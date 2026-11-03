(** * scheduler with fresh points

    [sched_main] of Scheduler.v. r₀ comes from new γ { } ∗. r₁ needs the
    alias r₁ ≡ r₀ for the link, so new κ { κ ≡ γ } ∗ puts it at γ
    itself, which the hypothesis of r₀ makes known. r₂ comes from
    new ε { γ+1 ≺ ε } ∗ (L = [γ+1]). An earlier version held three
    world constants, one alias and one fact. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools examples.Scheduler.

Set Default Proof Using "All".

(** [sched_main] with r₂ bound by the encoded let of
    new ε { γ+1 ≺ ε } ∗ (sharp edges 99). *)
Definition sched_main_ex : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed_fresh : styped ∅ [] [] (∅, None) sched_main_ex TUnit.
Proof. exact sched_typed. Qed.

Lemma sched_deadlock_free_fresh : deadlock_free (∅, {[+ sched_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit Wpo_nil_strict).
  apply ptyped_closed_s; [constructor|apply sched_typed_fresh].
Qed.
