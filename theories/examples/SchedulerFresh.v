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
  let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed_fresh : styped ∅ sched_Ψ [] (∅, None) sched_main_ex TUnit.
Proof. exact sched_typed. Qed.

Lemma sched_deadlock_free_fresh : deadlock_free (∅, {[+ sched_main_ex +]}).
Proof.
  apply (soundness_created_s sched_Ψ _ TUnit sched_created); [constructor|apply sched_typed_fresh].
Qed.
