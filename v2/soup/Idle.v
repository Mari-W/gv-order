(** * Idle ends and duality (stage S8, decision Q5)

    An end is idle when its session type is Skip ([idle], types/Types.v,
    with [idle_hd] and [idle_sequiv]).
    The soup pairs the protocols of the two ends of a channel up to ≈ and
    duality, and adequacy moves "not idle" from the end a pending thread
    acts on to its partner. [idle_dual] is the step: S' ≈ dual S gives
    idle S ↔ idle S'. *)

From GV Require Export fuel.Fuel types.Duality.

Lemma vdual_skip h : vdual h = HSkip ↔ h = HSkip.
Proof. destruct h; done. Qed.

Lemma idle_dual_self S : idle (dual S) ↔ idle S.
Proof. rewrite !idle_hd, hd_dual. apply vdual_skip. Qed.

(** S' ≃ dual S gives idle S ↔ idle S'. *)
Theorem idle_dual S S' : sequiv S' (dual S) → idle S ↔ idle S'.
Proof. intros H. rewrite <-idle_dual_self. symmetry. by apply idle_sequiv. Qed.
