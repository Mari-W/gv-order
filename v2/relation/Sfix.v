(** * One step-indexed fixpoint (stage S3, cleanup P15)

    [sfix d F n] is the value at level n of a family defined by
    course-of-values recursion on the step index. [F below n] defines
    level n from the family [below] of the lower levels, and reads
    [below j] only at j < n. [sfix_unfold] is the unfolding equation and
    [sfix_below_lt] says that [below] agrees with [sfix] below n, so no
    proof needs functional extensionality. Every step-indexed relation of
    v2 is an instance (the relation R^κ here, fuel in stage S6). *)

From stdpp Require Import base numbers.

Section sfix.
  Context {A : Type} (d : A) (F : (nat → A) → nat → A).

  (** [sfix_below n j] is level j for every j < n, and d above. *)
  Fixpoint sfix_below (n : nat) : nat → A :=
    match n with
    | 0 => λ _, d
    | S n' => λ j, if decide (j < n') then sfix_below n' j else F (sfix_below n') n'
    end.

  Definition sfix (n : nat) : A := sfix_below (S n) n.

  Lemma sfix_unfold n : sfix n = F (sfix_below n) n.
  Proof. unfold sfix. simpl. by rewrite decide_False by lia. Qed.

  Lemma sfix_below_lt n j : j < n → sfix_below n j = sfix j.
  Proof.
    revert j. induction n as [|n IH]; intros j Hj; [lia|].
    simpl. destruct (decide (j < n)) as [H|H]; [by apply IH|].
    assert (j = n) as -> by lia. by rewrite sfix_unfold.
  Qed.
End sfix.
