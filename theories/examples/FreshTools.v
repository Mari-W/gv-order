(** * Tools for the closed examples retyped with fresh points

    Each file *Fresh.v next to an example types the same program with
    E-NewFresh at its top-level news and applies [soundness] in the
    world its facts still need, usually the empty world [Wpo []]
    (docs/extensions/fresh-points.md). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** [sf_pinst_none], [fhyps_pinst_empty], [skn_inst] and [fresh_clean]
    moved to examples/ExampleTools.v, because the base examples use
    them too (sharp edges 105). *)

(** The empty world. *)
Lemma Wpo_nil_strict : strict (Wpo []).
Proof. apply Wpo_strict. Qed.
