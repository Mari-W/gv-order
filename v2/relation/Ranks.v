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

    The ranked worlds of the relation live in types/Worlds.v. *)

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


(** ** Ranks above a base

    [rank_base R b] ranks a well-founded R so that every rank lies at or
    above its base b and rises along R. E-New ranks the tree of a fresh
    base this way, with the rank base above the ranks of the context points
    below it. *)
Section rank_base.
  Context (R : point → point → Prop) (b : point → rank_ord).

  Fixpoint rank_bacc (x : point) (a : Acc R x) {struct a} : rank_ord :=
    match a with
    | Acc_intro _ h =>
        olim (λ t : bool, if t then b x
          else olim (λ s : {y : point | R y x}, osucc (rank_bacc (proj1_sig s) (h _ (proj2_sig s)))))
    end.

  Lemma rank_bacc_irr x (a1 : Acc R x) : ∀ a2 : Acc R x, ole (rank_bacc x a1) (rank_bacc x a2).
  Proof.
    induction a1 as [x h1 IH] using Acc_ind_dep. intros [h2]. cbn [rank_bacc].
    apply ole_lim_l. intros [|].
    - apply (ole_lim_r _ _ true). apply ole_refl.
    - apply (ole_lim_r _ _ false). apply ole_lim_l. intros s. apply (ole_lim_r _ _ s).
      apply ole_succ_succ, IH.
  Qed.

  Context (Hwf : well_founded R).

  Definition rank_base (x : point) : rank_ord := rank_bacc x (Hwf x).

  Lemma rank_base_lt y x : R y x → olt (rank_base y) (rank_base x).
  Proof.
    intros Hy. unfold rank_base at 2. generalize (Hwf x). intros [h]. cbn [rank_bacc].
    unfold olt. apply (ole_lim_r _ _ false). apply (ole_lim_r _ _ (exist _ y Hy)).
    apply ole_succ_succ, rank_bacc_irr.
  Qed.

  Lemma rank_base_ge x : ole (b x) (rank_base x).
  Proof.
    unfold rank_base. generalize (Hwf x). intros [h]. cbn [rank_bacc].
    apply (ole_lim_r _ _ true). apply ole_refl.
  Qed.
End rank_base.

(** ** The maximum of finitely many ranks, under excluded middle

    Brouwer trees are totally preordered under excluded middle
    ([ole_total]), so a nonempty finite family of ranks has a largest
    member ([list_max_rank]). E-New with partner sets needs it
    (docs/redesign/check-general-new.md, section 6). Without excluded
    middle the maximum need not exist: two ranks below a limit need not
    lie below one member of its family. *)
Lemma ole_total (EM : ∀ P : Prop, P ∨ ¬ P) : ∀ a b : ord, ole a b ∨ olt b a.
Proof.
  induction a as [|a IHa|X f IHa]; intros b.
  - by left.
  - induction b as [|b IHb|Y g IHb].
    + right. done.
    + destruct (IHa b) as [H|H]; [left; exact H|right; exact H].
    + destruct (EM (∃ y, ole (osucc a) (g y))) as [[y Hy]|Hn].
      * left. exact (ole_lim_r _ g y Hy).
      * right. intros y. destruct (IHb y) as [H|H]; [exfalso; eauto|exact H].
  - destruct (EM (∃ x, olt b (f x))) as [[x Hx]|Hn].
    + right. exact (olt_trans_le _ _ _ Hx (olt_lim f x)).
    + left. intros x. destruct (IHa x b) as [H|H]; [done|exfalso; eauto].
Qed.

Lemma list_max_rank (EM : ∀ P : Prop, P ∨ ¬ P) {A} (r : A → rank_ord) (l : list A) :
  l ≠ [] → ∃ x, x ∈ l ∧ ∀ y, y ∈ l → ole (r y) (r x).
Proof.
  induction l as [|a l IH]; intros Hl; [done|].
  destruct (decide (l = [])) as [->|Hne].
  - exists a. split; [by apply list_elem_of_singleton|]. intros y ->%list_elem_of_singleton. apply ole_refl.
  - destruct (IH Hne) as (x & Hx & Hmax). destruct (ole_total EM (r a) (r x)) as [H|H].
    + exists x. split; [by apply list_elem_of_further|]. intros y [->|Hy]%elem_of_cons; [done|by apply Hmax].
    + exists a. split; [by apply list_elem_of_here|]. intros y [->|Hy]%elem_of_cons; [apply ole_refl|].
      apply olt_ole. exact (ole_trans_lt _ _ _ (Hmax y Hy) H).
Qed.

(** A rank strictly between two ranks and a third one above both is
    Gödel–Dummett linearity. Take a = sup over P of 1, b = sup over Q of
    1 and c = sup (a + 1, b + 1). A rank r with a, b ≤ r < c lies at or
    below a or at or below b, so Q → P or P → Q. The creation of the
    two-entry example (examples/GenNew.v) needs such an r at every model,
    so (gen-new) with partner sets has no proof without a classical
    principle. *)
Lemma two_below_gd :
  (∀ a b c : rank_ord, olt a c → olt b c → ∃ r, ole a r ∧ ole b r ∧ olt r c) →
  ∀ P Q : Prop, (P → Q) ∨ (Q → P).
Proof.
  intros H P Q.
  pose (a := olim (λ _ : P, osucc ozero) : rank_ord).
  pose (b := olim (λ _ : Q, osucc ozero) : rank_ord).
  pose (c := olim (λ t : bool, if t then osucc a else osucc b) : rank_ord).
  destruct (H a b c) as (r & Har & Hbr & [[|] Hr]).
  - exists true. apply ole_refl.
  - exists false. apply ole_refl.
  - right. intros q. destruct (ole_trans _ _ _ Hbr Hr q) as [p _]. exact p.
  - left. intros p. destruct (ole_trans _ _ _ Har Hr p) as [q _]. exact q.
Qed.
