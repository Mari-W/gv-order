(** * Two components that branch on their own bits deadlock together
    (docs/extensions/data-dependent-worlds.md §4.2)

    K₁ holds one end of c and one end of d and branches on its bit. Its
    inl branch closes c and then d. K₂ holds the other ends and branches
    on its own bit. Its inl branch closes d and then c. With both bits
    inl the composition reaches a state where K₁ waits on c and K₂ waits
    on d, and nothing steps ([grow_not_df]). Under growth at internal
    choices without an owner (§4.2) each component types on its own, K₁
    with x ≺ y in its inl branch and K₂ with y ≺ x in its inl branch. So
    that candidate is unsound. With end points K₂ holds the other ends
    at x̄ and ȳ, and the two inl branches ask x ≺ ȳ and ȳ ≺ x, which is
    still a cycle. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.DataBranch.

Set Default Proof Using "All".

(** Syntactic points (sharp edges 173): K₁ holds the positive ends of
    c and d, K₂ the negative ones. *)
Definition gK1 : expr :=
  Case (Inj1 EUnit) (LetU (Var 0) (cc2 (chc, true) (chd, true))) (LetU (Var 0) (cc2 (chd, true) (chc, true))).
Definition gK2 : expr :=
  Case (Inj1 EUnit) (LetU (Var 0) (cc2 (chd, false) (chc, false))) (LetU (Var 0) (cc2 (chc, false) (chd, false))).

Definition grow_proc : proc := ({[chc; chd]}, {[+ gK1 +]} ⊎ {[+ gK2 +]}).

Lemma beta_l C a a' b : tstep a LBeta a' → preduction (C, {[+ a +]} ⊎ {[+ b +]}) (C, {[+ a' +]} ⊎ {[+ b +]}).
Proof. intros H. rewrite !(comm_L (⊎) {[+ _ +]} {[+ b +]}). by apply PStepBeta. Qed.

Lemma beta_r C a b b' : tstep b LBeta b' → preduction (C, {[+ a +]} ⊎ {[+ b +]}) (C, {[+ a +]} ⊎ {[+ b' +]}).
Proof. intros H. by apply PStepBeta. Qed.

Definition grow_stuck : proc :=
  ({[chc; chd]}, {[+ cc2 (chc, true) (chd, true) +]} ⊎ {[+ cc2 (chd, false) (chc, false) +]}).

Lemma grow_reach : pred_star grow_proc grow_stuck.
Proof.
  unfold grow_proc, grow_stuck.
  eapply rtc_l; [apply beta_l, TStepHead, HeadCase1; done|]. cbn.
  eapply rtc_l; [apply beta_l, TStepHead, HeadLetU|].
  eapply rtc_l; [apply beta_r, TStepHead, HeadCase1; done|]. cbn.
  eapply rtc_l; [apply beta_r, TStepHead, HeadLetU|].
  apply rtc_refl.
Qed.

Lemma soup2_elem (E : gmultiset expr) e a b :
  E ⊎ {[+ e +]} = {[+ a +]} ⊎ {[+ b +]} → e = a ∨ e = b.
Proof.
  intros H. assert (e ∈ {[+ a +]} ⊎ {[+ b +]}) as He by (rewrite <-H; multiset_solver).
  rewrite gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton in He. done.
Qed.

Lemma soup2_two (E : gmultiset expr) e f a b :
  a ≠ b → E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ a +]} ⊎ {[+ b +]} →
  (e = a ∧ f = b) ∨ (e = b ∧ f = a).
Proof.
  intros Hab H.
  assert (e ∈ {[+ a +]} ⊎ {[+ b +]}) as He by (rewrite <-H; multiset_solver).
  assert (f ∈ {[+ a +]} ⊎ {[+ b +]}) as Hf by (rewrite <-H; multiset_solver).
  rewrite gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton in He, Hf.
  destruct He as [->| ->], Hf as [->| ->]; auto; exfalso.
  - assert (multiplicity a (E ⊎ {[+ a +]} ⊎ {[+ a +]}) = multiplicity a ({[+ a +]} ⊎ {[+ b +]}))
      as Hm by by rewrite H.
    rewrite !multiplicity_disj_union, !multiplicity_singleton_eq, multiplicity_singleton_ne in Hm
      by done. lia.
  - assert (multiplicity b (E ⊎ {[+ b +]} ⊎ {[+ b +]}) = multiplicity b ({[+ a +]} ⊎ {[+ b +]}))
      as Hm by by rewrite H.
    rewrite !multiplicity_disj_union, !multiplicity_singleton_eq, multiplicity_singleton_ne in Hm
      by done. lia.
Qed.

Lemma cc2_ne : cc2 (chc, true) (chd, true) ≠ cc2 (chd, false) (chc, false).
Proof. done. Qed.

Ltac soup1 := match goal with
  | H : _ ⊎ {[+ ?e +]} = {[+ _ +]} ⊎ {[+ _ +]} |- _ => destruct (soup2_elem _ _ _ _ H) as [->| ->]
  end.
Ltac soup2 := match goal with
  | H : _ ⊎ {[+ _ +]} ⊎ {[+ _ +]} = {[+ _ +]} ⊎ {[+ _ +]} |- _ =>
      destruct (soup2_two _ _ _ _ _ cc2_ne H) as [[-> ->]|[-> ->]]
  end.

Lemma grow_stuck_irred : ∀ p', ¬ preduction grow_stuck p'.
Proof.
  intros p' H. unfold grow_stuck, preduction in H.
  inversion H as
    [|C0 E e e' Hs
     |C0 E e c x e' Hs Hc1 Hc2 Hc3
     |C0 E e v e' Hs
     |C0 E c β v e e' f f' He Hf
     |C0 E c β e e' f f' He Hf Hc
     |C0 E c β bb e e' f f' He Hf
     |C0 E e c bc d bd e' Hs Hc]; subst.
  - soup1; apply cc2_step in Hs; discriminate.
  - soup1; apply cc2_step in Hs; discriminate.
  - soup1; apply cc2_step in Hs; discriminate.
  - soup2; apply cc2_step in He; discriminate.
  - soup2; apply cc2_step in He; apply cc2_step in Hf; unfold chc, chd in *; simplify_eq.
  - soup2; apply cc2_step in He; discriminate.
  - soup1; apply cc2_step in Hs; discriminate.
Qed.

Theorem grow_not_df : ¬ deadlock_free grow_proc.
Proof.
  intros Hdf. destruct (Hdf _ grow_reach) as [(v & E & Heq & _)|(p' & Hp)].
  - apply (f_equal fst) in Heq. unfold grow_stuck in Heq. cbn [fst] in Heq.
    assert (chc ∈ ({[chc; chd]} : gset chan)) as Hin by set_solver.
    rewrite Heq in Hin. set_solver.
  - by apply (grow_stuck_irred p').
Qed.
