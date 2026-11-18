(** * Idle ends and duality (stage S8, decision Q5)

    An end is idle when its session type is Skip ([idle], fuel/Fuel.v).
    The soup pairs the protocols of the two ends of a channel up to ≈ and
    duality, and adequacy moves "not idle" from the end a pending thread
    acts on to its partner. [idle_dual] is the step: S' ≈ dual S gives
    idle S ↔ idle S'. *)

From GV Require Export fuel.Fuel types.Duality.

Lemma idle_hd S : idle S ↔ hd S = HSkip.
Proof.
  unfold idle, hd. split; [by intros ->|].
  intros H. rewrite <-(unview_view (unfoldS S)), H. done.
Qed.

Lemma vdual_skip h : vdual h = HSkip ↔ h = HSkip.
Proof. destruct h; done. Qed.

Lemma idle_dual_self S : idle (dual S) ↔ idle S.
Proof. rewrite !idle_hd, hd_dual. apply vdual_skip. Qed.

Lemma idle_sequiv S S' : sequiv S S' → idle S ↔ idle S'.
Proof.
  intros H. specialize (H 1). simpl in H. unfold eq_step in H. rewrite !idle_hd.
  destruct (hd S), (hd S'); naive_solver.
Qed.

(** S' ≃ dual S gives idle S ↔ idle S'. *)
Theorem idle_dual S S' : sequiv S' (dual S) → idle S ↔ idle S'.
Proof. intros H. rewrite <-idle_dual_self. symmetry. by apply idle_sequiv. Qed.
