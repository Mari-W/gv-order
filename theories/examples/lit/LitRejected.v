(** * Literature programs that the core rejects, proved underivable

    Five closed programs from the literature that deadlock. Each runs
    to a configuration where every thread waits on a send or a receive
    that no other thread can answer ([offers_stuck], examples/lit/LitLib.v).
    So none of them is deadlock free, and [soundness_source] rules out a
    whole-program [styped] derivation under every acyclic top-level
    constraint. No inversion of typing derivations is needed.

    - [pcx1_main], program 1 of docs/extensions/adequacy/pgv-counterexamples.txt.
      PGV as printed types it (its T-Pair does not compare the right
      component with the left value). Repaired PGV rejects it by R2.
    - [pcx2_main], program 2 of the same file. PGV as printed types it
      (its send schema puts no condition on the payload). Repaired PGV
      rejects it by R1.
    - [msr_main], Milner's scheduler of Dardha and Gay (Example 1,
      dardha2018new p. 3) with A_0 reversed, so A_0 waits on d_0 before
      it sends on c_0. examples/Rejected.v proves that the three facts a
      derivation would need close a cycle ([ms_rev_underivable]). The
      theorem below removes the step from the program to those facts.
    - [mcx2_main], program 2 of
      docs/extensions/adequacy/mordido-perez-counterexamples.txt, with
      the partial send written as a closure. Mordido and Pérez's rules
      as printed type it.
    - [mcx3_main], program 3 of the same file, with the polymorphic
      payload erased. Their rules as printed, with repair R5, type it.

    Simplifications. PGV's [wait] and [close] are both [close] here, and
    a payload 1 is ∗. In [pcx1_main] the two lets
    [let z = (c, send ((), w)) in let (c, w) = z in …] are one let pair on
    the pair, which evaluates c, then the send on w, while it holds c,
    as PGV's does. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.lit.LitLib.
From LRGV Require Import examples.MilnerSched.

Set Default Proof Using "All".

(** ** Program 1 of pgv-counterexamples.txt

      let (c, c′) = new () in let (v, v′) = new () in let (w, w′) = new () in
      spawn (λ(). let (u, c′) = recv c′ in u; let (u, v′) = recv v′ in u;
                  wait c′; wait v′);
      spawn (λ(). let v = send ((), v) in let (u, w′) = recv w′ in u;
                  close v; wait w′);
      let (c, w) = (c, send ((), w)) in
      let c = send ((), c) in close c; close w

    After the three [new]s c, c′, v, v′, w, w′ are 5 to 0. *)

Definition pcx1_child1 : expr :=
  Lam (LetU (Var 0)
    (LetP (App ERecv (Var 5)) (LetU (Var 1)
      (LetP (App ERecv (Var 5)) (LetU (Var 1)
        (LetU (App EClos (Var 2)) (App EClos (Var 0)))))))).

Definition pcx1_child2 : expr :=
  Lam (LetU (Var 0)
    (App (Lam (LetP (App ERecv (Var 2)) (LetU (Var 1)
                (LetU (App EClos (Var 2)) (App EClos (Var 0))))))
         (App ESend (Pair EUnit (Var 4))))).

Definition pcx1_rest : expr :=
  LetP (Pair (Var 5) (App ESend (Pair EUnit (Var 1))))
    (App (Lam (LetU (App EClos (Var 0)) (App EClos (Var 1)))) (App ESend (Pair EUnit (Var 1)))).

Definition pcx1_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn pcx1_child1) (LetU (App ESpawn pcx1_child2) pcx1_rest)))).

(** ** Program 2 of pgv-counterexamples.txt

      let (c, c′) = new () in let (d, d′) = new () in let (e, e′) = new () in
      spawn (λ(). let d = send (c′, d) in close d);
      spawn (λ(). let (u, e′) = recv e′ in u;
                  let (c′, d′) = recv d′ in
                  let c′ = send ((), c′) in close c′; wait d′; wait e′);
      let (u, c) = recv c in u; let e = send ((), e) in wait c; close e

    After the three [new]s c, c′, d, d′, e, e′ are 5 to 0. *)

Definition pcx2_child1 : expr :=
  Lam (LetU (Var 0) (App EClos (App ESend (Pair (Var 5) (Var 4))))).

Definition pcx2_child2 : expr :=
  Lam (LetU (Var 0)
    (LetP (App ERecv (Var 1)) (LetU (Var 1)
      (LetP (App ERecv (Var 5))
        (App (Lam (LetU (App EClos (Var 0)) (LetU (App EClos (Var 1)) (App EClos (Var 3)))))
             (App ESend (Pair EUnit (Var 1)))))))).

Definition pcx2_rest : expr :=
  LetP (App ERecv (Var 5)) (LetU (Var 1)
    (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair EUnit (Var 3))))).

Definition pcx2_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn pcx2_child1) (LetU (App ESpawn pcx2_child2) pcx2_rest)))).

(** ** Milner's scheduler with A_0 reversed

      A_0 = let () = recvclose d_0 in
            let () = close (send ⟨∗, c_0⟩) in close (send ⟨∗, a_0⟩)

    The other five threads are those of examples/MilnerSched.v. *)

Definition msr_ag0 : expr :=
  LetU (recvclose (Var 2)) (LetU (sendclose (Var 11)) (sendclose (Var 1))).

Definition msr_main : expr :=
  let_new_pair (let_new_pair (let_new_pair (let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn ms_ag1)
      (LetU (App ESpawn ms_ag2)
        (LetU (App ESpawn ms_col0)
          (LetU (App ESpawn ms_col1)
            (LetU (App ESpawn ms_col2) msr_ag0)))))))))).

(** ** Program 2 of mordido-perez-counterexamples.txt

    Their partial send [send x] becomes the closure λc. send ⟨x, c⟩,
    which is how the file says our system reads it.

      let (x, y) = new X in let (b, b′) = new B in
      spawn (λu. let (u, y) = recv y in u; close y;
                 let b′ = send ((), b′) in close b′);
      let f = λc. send ⟨x, c⟩ in
      let (u, b) = recv b in u; close b;
      let (d, d′) = new D in
      spawn (λu. let (x, d′) = recv d′ in
                 let x = send ((), x) in close x; close d′);
      close (f d) *)

Definition mcx2_child1 : expr :=
  Lam (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
      (LetU (App EClos (Var 0)) (App EClos (App ESend (Pair EUnit (Var 3)))))))).

Definition mcx2_child2 : expr :=
  Lam (LetU (Var 0)
    (LetP (App ERecv (Var 1))
      (App (Lam (LetU (App EClos (Var 0)) (App EClos (Var 1)))) (App ESend (Pair EUnit (Var 1)))))).

Definition mcx2_rest : expr :=
  LetP (App ERecv (Var 2)) (LetU (Var 1) (LetU (App EClos (Var 0))
    (let_new_pair (LetU (App ESpawn mcx2_child2) (App EClos (App (Var 4) (Var 1))))))).

Definition mcx2_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn mcx2_child1)
      (App (Lam mcx2_rest) (Lam (App ESend (Pair (Var 4) (Var 0))))))).

(** ** Program 3 of mordido-perez-counterexamples.txt

    With the polymorphic payload erased it is program 2 of PGV, except
    that the second child ends with close c′; wait e′; wait d′.

      let (c′, c) = new P in let (d, d′) = new D in let (e, e′) = new E in
      spawn (λu. let d = send (c′, d) in close d);
      spawn (λu. let (u, e′) = recv e′ in u;
                 let (c′, d′) = recv d′ in
                 let c′ = send ((), c′) in close c′; wait e′; wait d′);
      let (u, c) = recv c in u; let e = send ((), e) in wait c; close e *)

Definition mcx3_child2 : expr :=
  Lam (LetU (Var 0)
    (LetP (App ERecv (Var 1)) (LetU (Var 1)
      (LetP (App ERecv (Var 5))
        (App (Lam (LetU (App EClos (Var 0)) (LetU (App EClos (Var 3)) (App EClos (Var 1)))))
             (App ESend (Pair EUnit (Var 1)))))))).

Definition mcx3_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn pcx2_child1) (LetU (App ESpawn mcx3_child2) pcx2_rest)))).

(** ** The runs *)

Ltac offers_done :=
  repeat (apply Forall_cons; split; [cbn; blocked|]); [apply Forall_nil|];
  intros t u Ht Hu E; rewrite !elem_of_cons, elem_of_nil in Ht, Hu;
  repeat match goal with H : _ ∨ _ |- _ => destruct H as [H|H] end;
  try done; subst; cbn in *; try done; discriminate.

Lemma pcx1_not_deadlock_free : ¬ deadlock_free (∅, {[+ pcx1_main +]}).
Proof.
  eapply not_df_of_stuck.
  - rewrite ms_one_lit. unfold pcx1_main, let_new_pair, let_new.
    pnew "c". pb. pb. pb. pnew "v". pb. pb. pb. pnew "w". pb. pb. pb.
    psp. pb. pb. rewrite ms_swap. pb. psp. pb. pb. rewrite ms_swap.
    pb. apply rtc_refl.
  - apply not_terminated_chan. set_solver.
  - intros p''. stuck.
Qed.

Lemma pcx2_not_deadlock_free : ¬ deadlock_free (∅, {[+ pcx2_main +]}).
Proof.
  eapply not_df_of_stuck.
  - rewrite ms_one_lit. unfold pcx2_main, let_new_pair, let_new.
    pnew "c". pb. pb. pb. pnew "d". pb. pb. pb. pnew "e". pb. pb. pb.
    psp. pb. pb. rewrite ms_swap. pb. psp. pb. pb. rewrite ms_swap.
    pb. apply rtc_refl.
  - apply not_terminated_chan. set_solver.
  - intros p''. stuck.
Qed.

Lemma msr_not_deadlock_free : ¬ deadlock_free (∅, {[+ msr_main +]}).
Proof.
  eapply not_df_of_stuck.
  - rewrite ms_one_lit. unfold msr_main, let_new_pair, let_new.
    pnew "r0". pb. pb. pb. pnew "s1". pb. pb. pb. pnew "r1". pb. pb. pb.
    pnew "s2". pb. pb. pb. pnew "r2". pb. pb. pb. pnew "s0". pb. pb. pb.
    psp. pb. pb. rewrite ms_swap. pb. psp. pb. pb. rewrite ms_swap. pb.
    psp. pb. pb. rewrite ms_swap. pb. psp. pb. pb. rewrite ms_swap. pb.
    psp. pb. pb. rewrite ms_swap. pb.
    apply rtc_refl.
  - apply not_terminated_chan. set_solver.
  - intros p''. stuck.
Qed.

Lemma mcx2_not_deadlock_free : ¬ deadlock_free (∅, {[+ mcx2_main +]}).
Proof.
  eapply not_df_of_stuck.
  - rewrite ms_one_lit. unfold mcx2_main, let_new_pair, let_new.
    pnew "x". pb. pb. pb. pnew "b". pb. pb. pb.
    psp. pb. pb. rewrite ms_swap. pb. pb. apply rtc_refl.
  - apply not_terminated_chan. set_solver.
  - intros p''. stuck.
Qed.

Lemma mcx3_not_deadlock_free : ¬ deadlock_free (∅, {[+ mcx3_main +]}).
Proof.
  eapply not_df_of_stuck.
  - rewrite ms_one_lit. unfold mcx3_main, let_new_pair, let_new.
    pnew "c". pb. pb. pb. pnew "d". pb. pb. pb. pnew "e". pb. pb. pb.
    psp. pb. pb. rewrite ms_swap. pb. psp. pb. pb. rewrite ms_swap.
    pb. apply rtc_refl.
  - apply not_terminated_chan. set_solver.
  - intros p''. stuck.
Qed.

(** ** No derivation

    Neither for the closed program at any primitive type nor under any
    top-level points with an acyclic constraint. *)

Theorem pcx1_untypable T : prim T → ¬ styped ∅ [] [] (∅, None) pcx1_main T.
Proof.
  intros HT Ht. apply pcx1_not_deadlock_free.
  apply (soundness (Wpo []) _ T (Wpo_strict _)). by apply ptyped_closed_s.
Qed.

Theorem pcx1_untypable_source n C0 T :
  c0_acyclic n C0 → prim T → ¬ styped ∅ [(C0, ids n)] [] (∅, None) pcx1_main T.
Proof.
  intros HC HT Ht. apply pcx1_not_deadlock_free.
  exact (soundness_source n C0 _ T (c0_acyclic_creation _ _ HC) HT Ht).
Qed.

Theorem pcx2_untypable T : prim T → ¬ styped ∅ [] [] (∅, None) pcx2_main T.
Proof.
  intros HT Ht. apply pcx2_not_deadlock_free.
  apply (soundness (Wpo []) _ T (Wpo_strict _)). by apply ptyped_closed_s.
Qed.

Theorem pcx2_untypable_source n C0 T :
  c0_acyclic n C0 → prim T → ¬ styped ∅ [(C0, ids n)] [] (∅, None) pcx2_main T.
Proof.
  intros HC HT Ht. apply pcx2_not_deadlock_free.
  exact (soundness_source n C0 _ T (c0_acyclic_creation _ _ HC) HT Ht).
Qed.

Theorem msr_untypable T : prim T → ¬ styped ∅ [] [] (∅, None) msr_main T.
Proof.
  intros HT Ht. apply msr_not_deadlock_free.
  apply (soundness (Wpo []) _ T (Wpo_strict _)). by apply ptyped_closed_s.
Qed.

Theorem msr_untypable_source n C0 T :
  c0_acyclic n C0 → prim T → ¬ styped ∅ [(C0, ids n)] [] (∅, None) msr_main T.
Proof.
  intros HC HT Ht. apply msr_not_deadlock_free.
  exact (soundness_source n C0 _ T (c0_acyclic_creation _ _ HC) HT Ht).
Qed.


Theorem mcx2_untypable T : prim T → ¬ styped ∅ [] [] (∅, None) mcx2_main T.
Proof.
  intros HT Ht. apply mcx2_not_deadlock_free.
  apply (soundness (Wpo []) _ T (Wpo_strict _)). by apply ptyped_closed_s.
Qed.

Theorem mcx2_untypable_source n C0 T :
  c0_acyclic n C0 → prim T → ¬ styped ∅ [(C0, ids n)] [] (∅, None) mcx2_main T.
Proof.
  intros HC HT Ht. apply mcx2_not_deadlock_free.
  exact (soundness_source n C0 _ T (c0_acyclic_creation _ _ HC) HT Ht).
Qed.

Theorem mcx3_untypable T : prim T → ¬ styped ∅ [] [] (∅, None) mcx3_main T.
Proof.
  intros HT Ht. apply mcx3_not_deadlock_free.
  apply (soundness (Wpo []) _ T (Wpo_strict _)). by apply ptyped_closed_s.
Qed.

Theorem mcx3_untypable_source n C0 T :
  c0_acyclic n C0 → prim T → ¬ styped ∅ [(C0, ids n)] [] (∅, None) mcx3_main T.
Proof.
  intros HC HT Ht. apply mcx3_not_deadlock_free.
  exact (soundness_source n C0 _ T (c0_acyclic_creation _ _ HC) HT Ht).
Qed.
