(** * Cost derivations of the examples (lock-freedom plan §19.9, stage H2)

    Each example of §19.9 gets a derivation of the cost judgment of
    static/CostTyping.v for its closed main term, [X_ctyped]. The
    derivations are built by [ct] from the cost types of the boxes and
    the protocols, which are stated here. The world enters only through
    the point literals of a program: C-Pt asks that the world knows
    each literal and that it fits its profile, and the lemmas take
    these facts as hypotheses. *)

From stdpp Require Import base strings gmap.
From LRGV Require Import static.CostTyping.
From LRGV Require Import examples.Sync.

Set Default Proof Using "All".

Section examples.
Context (W : world).

(** ** sync

    The thunk sends ∗ on c and closes it, main receives on d and closes
    it. Budget bound 1 at every node. *)
Definition sy_Ps : cpro := PNode 1 (PSnd (CTa CVal None) (PNode 1 PCls)).
Definition sy_Pr : cpro := PNode 1 (PRcv (CTa CVal None) (PNode 1 PCls)).
Definition sy_ρ : cprof := Prof sy_Ps sy_Pr (λ _, PrTop) PrTop.

Lemma sync_ctyped :
  pt_known W (pconst 0) → cpfitpt W (pconst 0) sy_ρ →
  ctyped W ∅ [] sync_main (CTa CVal None) (Some 2) (Some 1, 0).
Proof.
  intros Hk Hf. unfold sync_main, sync_thunk, let_new_pair_at, let_new_at. cbn [rename upren].
  ct_prep. ct0.
Qed.

End examples.
