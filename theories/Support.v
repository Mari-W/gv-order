(** * Shared plumbing for the examples

    None of this is an example: linear-environment constructors for
    building typing derivations, inversions for splitting a soup into
    named threads, and a couple of step inversions.  It lives here
    because Leader, Balancer, Pingpong and Factory all need it, and
    two of them used to carry their own copies. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Invariant.

Local Open Scope string_scope.

Lemma lenv_empty_nil : lenv_empty [].
Proof. intros o Ho. by apply elem_of_nil in Ho. Qed.

Lemma lenv_empty_cons Δ : lenv_empty Δ → lenv_empty (None :: Δ).
Proof.
  intros HΔ o Ho. apply elem_of_cons in Ho as [->|Ho]; auto.
Qed.

#[export] Hint Resolve lenv_empty_nil lenv_empty_cons : core.

Lemma lenv_only_1 T : lenv_only [Some T] 0 T.
Proof.
  split; [done|]. intros [|y] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_20 T : lenv_only [Some T; None] 0 T.
Proof.
  split; [done|]. intros [|[|y]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_21 T : lenv_only [None; Some T] 1 T.
Proof.
  split; [done|]. intros [|[|y]] T' H; simplify_eq/=; auto.
Qed.



(** ** Multiset inversions for two-thread processes *)

Lemma gmultiset_pair_inv (E : gmultiset expr) e x y :
  E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ y +]} →
  (e = x ∧ E = {[+ y +]}) ∨ (e = y ∧ E = {[+ x +]}).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    apply gmultiset_elem_of_singleton in He; subst;
    [left|right]; (split; [done|multiset_solver]).
Qed.

Lemma gmultiset_pair_inv2 (E : gmultiset expr) e f x y :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ y +]} →
  E = ∅ ∧ ((e = x ∧ f = y) ∨ (e = y ∧ f = x)).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    apply gmultiset_elem_of_singleton in He; subst.
  - assert (E ⊎ {[+ f +]} = {[+ y +]}) as HE by multiset_solver.
    apply gmultiset_singleton_inv in HE as [-> ->]. auto.
  - assert (E ⊎ {[+ f +]} = {[+ x +]}) as HE by multiset_solver.
    apply gmultiset_singleton_inv in HE as [-> ->]. auto.
Qed.

(** The only transition of let ∗ = ∗ in e2 is the β step to e2. *)
Lemma tstep_letu_unit_inv e2 α e' :
  tstep (LetU EUnit e2) α e' → α = LBeta ∧ e' = e2.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep EUnit _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.
