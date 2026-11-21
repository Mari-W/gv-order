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

    Ranked worlds. A world of the relation is a finite set A of
    constants with a rank for every point, read only on points whose
    root lies in A ([world]). Program order raises the rank there.
    W ⊢ x ≺ y holds by program order, or between points with roots in A
    whose ranks rise. An extension keeps A and every rank on it, so the
    order is monotone, transitive and well-founded in every world, and
    no world needs a strictness premise.

    - [wmodels R W]: the ranked world R ranks every fact of the static
      world W.
    - [wmodels_exists]: a well-founded static world has a model, its
      rank function.
    - [wadd W a ρ]: W grown by a fresh constant a with the ranks ρ on
      the tree of a, as O-New grows it. *)

From GV Require Export relation.Ord types.Worlds.

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

(** ** Ranked worlds *)

#[local] Unset Universe Polymorphism.

Record world := World {
  w_roots : gset pname;
  w_rank : point → rank_ord;
  w_po x : pt_root x ∈ w_roots → olt (w_rank x) (w_rank x⁺) ∧ olt (w_rank x) (w_rank x‾⁺)
}.

(** x is ranked in W: its root is a root of W. *)
Definition rin (W : world) (x : point) : Prop := pt_root x ∈ w_roots W.

Global Instance rin_dec W x : Decision (rin W x).
Proof. unfold rin. apply _. Defined.

Definition w_lt (W : world) (x y : point) : Prop :=
  po x y ∨ (rin W x ∧ rin W y ∧ olt (w_rank W x) (w_rank W y)).

Notation "W ⊢ x ≺ y" := (w_lt W x y)
  (at level 74, x at level 60, y at level 60, format "W  ⊢  x  ≺  y").

Definition w_le (W : world) (x y : point) : Prop := x = y ∨ W ⊢ x ≺ y.

Lemma rin_po W x y : po x y → rin W x ↔ rin W y.
Proof. intros Hp. apply po_root in Hp as [Hr _]. unfold rin. by rewrite Hr. Qed.

Lemma rank_po W x y : rin W x → po x y → olt (w_rank W x) (w_rank W y).
Proof.
  intros Hx Hp. induction Hp as [x y Hxy|x y z Hxy Hp IH].
  - destruct Hxy as [->| ->]; apply (w_po W x Hx).
  - assert (olt (w_rank W x) (w_rank W y)) as H1 by (destruct Hxy as [->| ->]; apply (w_po W x Hx)).
    eapply olt_trans; [exact H1|]. apply IH.
    apply (rin_po _ x y); [by apply tc_once|done].
Qed.

Lemma w_lt_trans W x y z : W ⊢ x ≺ y → W ⊢ y ≺ z → W ⊢ x ≺ z.
Proof.
  intros [Hxy|(Hx & Hy & Hxy)] [Hyz|(Hy' & Hz & Hyz)].
  - left. by eapply po_trans.
  - right. split_and!; [by apply (rin_po _ x y)|done|].
    eapply olt_trans; [|exact Hyz]. apply rank_po; [by apply (rin_po _ x y)|done].
  - right. split_and!; [done|by apply (rin_po _ y z)|].
    eapply olt_trans; [exact Hxy|]. by apply rank_po.
  - right. split_and!; [done|done|]. by eapply olt_trans.
Qed.

Lemma po_lt W x y : po x y → W ⊢ x ≺ y.
Proof. by left. Qed.
Lemma w_lt_po W x : W ⊢ x ≺ x⁺.
Proof. left. apply tc_once. by left. Qed.
Lemma w_lt_dpo W x : W ⊢ x ≺ x‾⁺.
Proof. left. apply tc_once. by right. Qed.

Lemma w_lt_irrefl W x : ¬ W ⊢ x ≺ x.
Proof. intros [H|(_ & _ & H)]; [by apply po_irrefl in H|by apply olt_irrefl in H]. Qed.

(** Every ranked world is well-founded. A descending chain that meets a
    ranked point stays ranked and lowers the rank, and one that does not
    is program order and lowers the offset. *)
Lemma w_lt_wf W : well_founded (w_lt W).
Proof.
  assert (∀ x, rin W x → Acc (w_lt W) x) as Hin.
  { intros x. remember (w_rank W x) as a eqn:Ha. revert x Ha.
    induction a as [a IH] using oind. intros x -> Hx. constructor.
    intros y [Hy|(Hy & _ & Hyx)].
    - apply (IH (w_rank W y)); [by apply rank_po; [apply (rin_po _ y x)|]|done|].
      by apply (rin_po _ y x).
    - by apply (IH (w_rank W y)). }
  intros x. induction (po_wf x) as [x _ IH]. constructor. intros y [Hy|(Hy & _ & _)].
  - by apply IH.
  - by apply Hin.
Qed.

(** ** Extension *)

Record wext (W W' : world) : Prop := {
  wext_roots : w_roots W ⊆ w_roots W';
  wext_rank x : rin W x → w_rank W' x = w_rank W x
}.

Notation "W ⊑ W'" := (wext W W') (at level 70).

Lemma wext_refl W : W ⊑ W.
Proof. by split. Qed.

Lemma rin_mono W W' x : W ⊑ W' → rin W x → rin W' x.
Proof. intros HW. unfold rin. apply HW. Qed.

Lemma wext_trans W1 W2 W3 : W1 ⊑ W2 → W2 ⊑ W3 → W1 ⊑ W3.
Proof.
  intros H12 H23. split; [etrans; [apply H12|apply H23]|]. intros x Hx.
  rewrite (wext_rank _ _ H23); [by apply H12|]. by eapply rin_mono.
Qed.

Lemma w_lt_mono W W' x y : W ⊑ W' → W ⊢ x ≺ y → W' ⊢ x ≺ y.
Proof.
  intros HW [H|(Hx & Hy & H)]; [by left|right].
  split_and!; [by eapply rin_mono|by eapply rin_mono|]. by rewrite !(wext_rank _ _ HW).
Qed.

Lemma w_le_mono W W' x y : W ⊑ W' → w_le W x y → w_le W' x y.
Proof. intros HW [->|H]; [by left|right; by eapply w_lt_mono]. Qed.

(** ** Ranked worlds that model a static world *)

Definition wmodels (R : world) (W : sworld) : Prop :=
  (∀ a, a ∈ sw_consts W → NConst a ∈ w_roots R) ∧ ∀ x y, sw_facts W (FLt x y) → R ⊢ x ≺ y.

Lemma wmodels_lt R W x y : wmodels R W → W ⊢ₛ x ≺ y → R ⊢ x ≺ y.
Proof.
  intros [_ HR]. induction 1 as [x y Hs|x y z Hs _ IH].
  - destruct Hs as [x y Hf|x|x]; [by apply HR|apply w_lt_po|apply w_lt_dpo].
  - eapply w_lt_trans; [|exact IH].
    destruct Hs as [x y Hf|x|x]; [by apply HR|apply w_lt_po|apply w_lt_dpo].
Qed.

Lemma wmodels_mono R R' W : R ⊑ R' → wmodels R W → wmodels R' W.
Proof.
  intros HR [Hc Hf]. split; [intros a Ha; apply HR; by apply Hc|]. intros x y H. by eapply w_lt_mono, Hf.
Qed.

Lemma wmodels_ext R W W' : W ⊑ₛ W' → wmodels R W' → wmodels R W.
Proof.
  intros HW [Hc Hf]. split; [intros a Ha; apply Hc; by apply HW|]. intros x y H. by apply Hf, (swext_facts _ _ HW).
Qed.

(** The rank function of a well-founded static world models it. *)
Definition wrank (W : sworld) (HW : swf W) : world.
Proof.
  refine (World (set_map NConst (sw_consts W)) (rank_of (sw_lt W) HW) _).
  intros x _. split; apply rank_of_ranked; [apply sw_lt_po|apply sw_lt_dpo].
Defined.

Lemma wrank_models W HW : sworld_wf W → wmodels (wrank W HW) W.
Proof.
  intros Hwf. split; [intros a Ha; simpl; set_solver|]. intros x y Hf. right.
  destruct (wf_facts _ Hwf x y Hf) as [(a & Ha & Ha') (b & Hb & Hb')].
  split_and!; [unfold rin; simpl; rewrite Ha; set_solver|unfold rin; simpl; rewrite Hb; set_solver|].
  apply rank_of_ranked, sw_lt_fact, Hf.
Qed.

Lemma wmodels_exists W : sworld_wf W → swf W → ∃ R, wmodels R W.
Proof. intros Hwf HW. exists (wrank W HW). by apply wrank_models. Qed.

(** ** Growing a world by roots

    [wgrow W B ρ] ranks the points of the roots in B that W does not rank
    by ρ, and keeps every rank of W. O-New grows the world this way. *)

Definition ranks_po (B : gset pname) (ρ : point → rank_ord) : Prop :=
  ∀ x, pt_root x ∈ B → olt (ρ x) (ρ x⁺) ∧ olt (ρ x) (ρ x‾⁺).

Definition wgrow_rank (W : world) (ρ : point → rank_ord) (x : point) : rank_ord :=
  if decide (rin W x) then w_rank W x else ρ x.

Definition wgrow (W : world) (B : gset pname) (ρ : point → rank_ord) (Hρ : ranks_po B ρ) : world.
Proof.
  refine (World (B ∪ w_roots W) (wgrow_rank W ρ) _).
  intros x Hx. unfold wgrow_rank.
  assert (rin W x ↔ rin W x⁺) as E1 by (unfold rin, pt_root; done).
  assert (rin W x ↔ rin W x‾⁺) as E2 by (unfold rin, pt_root; done).
  destruct (decide (rin W x)) as [Ha|Ha].
  - rewrite !decide_True by tauto. by apply w_po.
  - rewrite !decide_False by tauto. apply Hρ. apply elem_of_union in Hx as [?|?]; [done|by destruct Ha].
Defined.

Lemma wgrow_ext W B ρ Hρ : W ⊑ wgrow W B ρ Hρ.
Proof.
  split; [simpl; set_solver|]. intros x Hx. simpl. unfold wgrow_rank. by rewrite decide_True.
Qed.

Lemma wgrow_rank_new W B ρ Hρ x : ¬ rin W x → w_rank (wgrow W B ρ Hρ) x = ρ x.
Proof. intros H. simpl. unfold wgrow_rank. by rewrite decide_False. Qed.

Lemma wgrow_rin W B ρ Hρ x : pt_root x ∈ B → rin (wgrow W B ρ Hρ) x.
Proof. intros H. unfold rin. simpl. set_solver. Qed.
