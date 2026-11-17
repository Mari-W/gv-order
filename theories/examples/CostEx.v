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
From LRGV Require Import examples.Sync examples.TailCall examples.Forwarder.

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

(** ** forwarder

    The arrows of [fwd], [fprod] and [fcons] cost ∞, their calls are
    spawned in tail position. A payload channel is created at budget 2.
    The producer hands it over at credit 1, which is the floor in the
    payload cost type of a, and the forwarder hands it on at credit 0,
    the floor of b. The spawned call of [fwd] captures a after one
    action and b just refilled, so its floor is B − 2, and the next
    round needs b at credit 1 for the receive on a. That makes B = 3,
    one more than the estimate of plan §19.9, because a closure has
    one floor for all the ends it captures. *)
Definition fw_Pc : cpro := PNode 2 PCls.
Definition fw_ρc : cprof := Prof fw_Pc fw_Pc (λ _, PrTop) PrTop.
CoFixpoint fw_Pi : cpro := PNode 3 (PRcv (CTa (CEnd fw_Pc) (Some 1)) fw_Pi).
CoFixpoint fw_Pi' : cpro := PNode 3 (PSnd (CTa (CEnd fw_Pc) (Some 1)) fw_Pi').
CoFixpoint fw_Po : cpro := PNode 3 (PSnd (CTa (CEnd fw_Pc) (Some 0)) fw_Po).
CoFixpoint fw_Po' : cpro := PNode 3 (PRcv (CTa (CEnd fw_Pc) (Some 0)) fw_Po').
Definition fw_ρa : cprof := Prof fw_Pi fw_Pi' (λ _, PrTop) PrTop.
Definition fw_ρb : cprof := Prof fw_Po fw_Po' (λ _, PrTop) PrTop.
(** The producer's point: a fresh channel at every payload point x[0],
    and the same at x + 1. *)
CoFixpoint fw_ρp : cprof := Prof PTop PTop (λ _, fw_ρc) fw_ρp.

Definition fw_tix : tix := (Some 1, 0).

Definition fwd_cty : cta :=
  CTa (CBox (Some 0) tid (CTa (CArr None fw_tix 0
    (CTa (CProd (CTa (CEnd fw_Pi) (Some 1)) (CTa (CEnd fw_Po) (Some 1))) (Some 0))
    (CTa CVal None)) None)) None.
Definition fprod_cty : cta :=
  CTa (CBox (Some 0) tid (CTa (CArr (Some 0) tid 0 (CTa (CPt fw_ρp) None)
    (CTa (CArr None fw_tix 0 (CTa (CEnd fw_Pi') (Some 0)) (CTa CVal None)) None)) None)) None.
Definition fcons_cty : cta :=
  CTa (CBox (Some 0) tid (CTa (CArr None fw_tix 0 (CTa (CEnd fw_Po') (Some 0)) (CTa CVal None)) None)) None.

Lemma fwd_ctyped : ctyped W ∅ [] fwd fwd_cty (Some 0) tid.
Proof. unfold fwd, fwd_cty. ct0. Qed.

Lemma fprod_ctyped : ctyped W ∅ [] fprod fprod_cty (Some 0) tid.
Proof. unfold fprod, fprod_cty, let_new_pair_at, let_new_at. ct_prep. ct0. Qed.

Lemma fcons_ctyped : ctyped W ∅ [] fcons fcons_cty (Some 0) tid.
Proof. unfold fcons, fcons_cty. ct0. Qed.

Ltac fw_hint k :=
  lazymatch goal with
  | |- ctyped _ _ [] fwd _ _ _ => apply fwd_ctyped
  | |- ctyped _ _ [] fprod _ _ _ => apply fprod_ctyped
  | |- ctyped _ _ [] fcons _ _ _ => apply fcons_ctyped
  end.

Lemma fw_ctyped :
  pt_known W (pconst 1) → cpfitpt W (pconst 1) fw_ρa →
  pt_known W (pconst 0) → cpfitpt W (pconst 0) fw_ρb →
  pt_known W (pt_dual (pconst 1)) → cpfitpt W (pt_dual (pconst 1)) fw_ρp →
  ctyped W ∅ [] fw_main (CTa CVal None) None (Some 3, 0).
Proof.
  intros. unfold fw_main, let_new_pair_at, let_new_at. ct_prep. ct1 fw_hint.
Qed.

End examples.
