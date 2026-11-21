(** * Ranks of points (stage 3, groundwork)

    Layers read a point by an ordinal rank (docs/redesign/check-layers.md,
    check-layers-open.md §4). Ranks are Brouwer trees whose limits range
    over types in Set, [rank_ord := ord@{Set}], one universe below the
    step index [Ix], so that a ranked world can be a creation choice of
    the existential property.

    - [ranked R ρ]: ρ strictly increases along every fact x R y.
    - [wf R]: some rank function exists.
    - [wf_wellfounded]: a ranked relation is well-founded.
    - [wellfounded_wf]: a well-founded relation on points has a rank
      function, [rank_of], the supremum of the successors of the ranks
      below. It is constructive, because the limits range over the
      subtype of points below a point, which lives in Set.

    The semantic worlds, (wf-new) at E-New and the wf premises of
    P-Connect and P-Term are not built on this file yet
    (docs/redesign/pending.md). *)

From GV Require Export relation.Ord types.Points.

#[local] Set Universe Polymorphism.

Definition rank_ord : Type := ord@{Set}.

Section ranks.
  Context (R : point → point → Prop).

  Definition ranked (ρ : point → rank_ord) : Prop := ∀ x y, R x y → olt (ρ x) (ρ y).

  Definition wf : Prop := ∃ ρ, ranked ρ.

  Lemma wf_wellfounded : wf → well_founded R.
  Proof.
    intros [ρ Hρ] x. remember (ρ x) as a eqn:Ha. revert x Ha.
    induction a as [a IH] using oind. intros x ->. constructor. intros y Hy.
    exact (IH (ρ y) (Hρ y x Hy) y eq_refl).
  Qed.

  (** The rank of x below an accessibility proof. *)
  Fixpoint rank_acc (x : point) (a : Acc R x) {struct a} : rank_ord :=
    match a with
    | Acc_intro _ h => olim (λ s : {y : point | R y x}, osucc (rank_acc (proj1_sig s) (h _ (proj2_sig s))))
    end.

  Lemma rank_acc_irr x (a1 : Acc R x) : ∀ a2 : Acc R x, ole (rank_acc x a1) (rank_acc x a2).
  Proof.
    induction a1 as [x h1 IH] using Acc_ind_dep. intros [h2]. cbn [rank_acc].
    apply ole_lim_l. intros s. apply (ole_lim_r _ _ s). apply ole_succ_succ, IH.
  Qed.

  Context (Hwf : well_founded R).

  Definition rank_of (x : point) : rank_ord := rank_acc x (Hwf x).

  Lemma rank_of_ranked : ranked rank_of.
  Proof.
    intros y x Hy. unfold rank_of at 2. generalize (Hwf x). intros [h]. cbn [rank_acc].
    apply (ole_lim_r _ _ (exist _ y Hy)). apply ole_succ_succ, rank_acc_irr.
  Qed.

  Lemma wellfounded_wf : wf.
  Proof. exists rank_of. apply rank_of_ranked. Qed.
End ranks.

Lemma wf_iff_wellfounded (R : point → point → Prop) : wf R ↔ well_founded R.
Proof. split; [apply wf_wellfounded|apply wellfounded_wf]. Qed.

(** A sub-relation of a ranked relation is ranked by the same ranks. *)
Lemma ranked_sub (R R' : point → point → Prop) ρ :
  (∀ x y, R' x y → R x y) → ranked R ρ → ranked R' ρ.
Proof. intros H Hρ x y Hxy. by apply Hρ, H. Qed.
