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
From LRGV Require Import examples.Sync examples.TailCall.

Set Default Proof Using "All".

(** [ct] with a hint for the goals of one example, then the default. *)
Ltac ct1 hint := ct ltac:(fun k => first [hint k | spawn_hint k]).

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

(** ** tail call

    Both boxes have arrows of cost ∞ and call themselves in tail
    position, so the call ages nothing: the end is the argument. *)
CoFixpoint tc_Ps : cpro := PNode 1 (PSnd (CTa CVal None) tc_Ps).
CoFixpoint tc_Pr : cpro := PNode 1 (PRcv (CTa CVal None) tc_Pr).
Definition tc_ρ : cprof := Prof tc_Ps tc_Pr (λ _, PrTop) PrTop.

Definition tcs_cty : cta :=
  CTa (CBox (Some 0) tid (CTa (CArr None tid 0 (CTa (CEnd tc_Ps) (Some 0)) (CTa CVal None)) None)) None.
Definition tcr_cty : cta :=
  CTa (CBox (Some 0) tid (CTa (CArr None tid 0 (CTa (CEnd tc_Pr) (Some 0)) (CTa CVal None)) None)) None.

Lemma tcs_ctyped : ctyped W ∅ [] tcs tcs_cty (Some 0) tid.
Proof. unfold tcs, tcs_cty. ct0. Qed.

Lemma tcr_ctyped : ctyped W ∅ [] tcr tcr_cty (Some 0) tid.
Proof. unfold tcr, tcr_cty. ct0. Qed.

Ltac tc_hint k :=
  lazymatch goal with
  | |- ctyped _ _ [] tcs _ _ _ => apply tcs_ctyped
  | |- ctyped _ _ [] tcr _ _ _ => apply tcr_ctyped
  end.

Lemma tc_ctyped :
  pt_known W (pconst 0) → cpfitpt W (pconst 0) tc_ρ →
  ctyped W ∅ [] tc_main (CTa CVal None) None (Some 1, 0).
Proof.
  intros Hk Hf. unfold tc_main, let_new_pair_at, let_new_at. ct_prep. ct1 tc_hint.
Qed.

End examples.
