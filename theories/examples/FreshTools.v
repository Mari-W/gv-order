(** * Tools for the closed examples retyped with fresh points

    Each file *Fresh.v next to an example types the same program with
    E-NewFresh at its top-level news and applies [soundness] in the
    world its facts still need, usually the empty world [Wpo []]
    (docs/extensions/fresh-points.md). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Lemma sf_pinst_none σ : sf_pinst σ (∅, None) = ((∅ : gset point), (None : option fslot)).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

Lemma fhyps_pinst_empty σ : fhyps_pinst σ ∅ = ∅.
Proof. unfold fhyps_pinst. by rewrite fmap_empty. Qed.

(** A point is known when its root is the root of an instance point
    of a hypothesis. *)
Lemma skn_inst W Ψ C xs y x : (C, xs) ∈ Ψ → y ∈ xs → pt_root x = pt_root y → skn W Ψ x.
Proof. intros Hg Hy E. right. by exists C, xs, y. Qed.

(** After E-NewFresh at the top level: Θ, F and Φ are empty. *)
Ltac fresh_clean :=
  rewrite ?tenv_pinst_empty, ?sf_pinst_none, ?fhyps_pinst_empty; cbn;
  rewrite ?fhyps_pinst_empty.

(** The empty world. *)
Lemma Wpo_nil_strict : strict (Wpo []).
Proof. apply Wpo_strict. Qed.
