(** * Fuel of the examples from their cost derivations (lock-freedom plan §19.7, stage H4)

    [ctyped_fsem] turns a cost derivation of a closed thread into its
    fuel. The main threads of sync and of the callback server hold no
    end, so their fuel is [fsem W ∅] in every world that knows their
    point literals and fits their profiles there. *)

From stdpp Require Import base gmap.
From LRGV Require Import lockfree.CostFund examples.CostEx examples.Sync.

Lemma sync_fsem W :
  pt_known W (pconst 0) → cpfitpt W (pconst 0) sy_ρ → fsem W ∅ sync_main.
Proof.
  intros Hk Hf. apply (ctyped_fsem W ∅ sync_main _ _ _ W ∅ (sync_ctyped W Hk Hf) (wbext_refl W) (cfits_empty W)).
Qed.

Lemma cb_fsem W :
  pt_known W (pconst 0) → cpfitpt W (pconst 0) cb_ρ →
  pt_known W (pconst 1) → cpfitpt W (pconst 1) cb_ρl →
  fsem W ∅ cb_main.
Proof.
  intros H1 H2 H3 H4. apply (ctyped_fsem W ∅ cb_main _ _ _ W ∅ (cb_ctyped W H1 H2 H3 H4) (wbext_refl W) (cfits_empty W)).
Qed.
