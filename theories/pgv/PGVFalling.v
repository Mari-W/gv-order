(** * Falling sessions in repaired PGV

    docs/extensions/adequacy/pgv-adequacy.md §8. Two closed programs whose
    session types fall, both typed in repaired PGV ([pgv_rep]) and outside
    the fragment [pgv_frag].

    - [fall2]: the program of §2. x : !⁵1.?⁰1.end⁶_? and its partner.
    - [fallxy]: two threads use channels at the same session types in
      opposite orders. Thread X holds x : S1 and b : S2 and sends on b
      before x. Main holds c : S1, acts on c, creates d : S2 and receives
      on c at 0 before it sends on d. With S1 = !⁵1.?⁰1.end⁶_? and
      S2 = !³1.end⁸_!, X needs the instant of b below (x, 0), and main
      needs (c, 1) below the instant of d. A translation that reads the
      point of a channel off its session type alone puts b and d at one
      point and (x, 0) and (c, 0) at one point, and program order closes
      the cycle (x, 0) ≺ (x, 1) ≺ d ≡ b ≺ (x, 0). *)

From stdpp Require Import base list.
From LRGV Require Export pgv.PGVExamples.

Set Default Proof Using "All".

Definition S1 : psty := PSnd 5 PUnit (PRcv 0 PUnit (PEndR 6)).
Definition S2 : psty := PSnd 3 PUnit (PEndS 8).

(** The partner of S1 at index i under the unit argument of a λ.
    let z = recv x̄ in let ((), x̄) = z in let x̄ = send ((), x̄) in close x̄.
    The let sugar receives, because T-LetPair would check the
    continuation at priority 0 against the receive at 5 (§2). *)
Definition s1_partner (i : nat) : expr :=
  Lam (LetU (Var 0) (plet (App (Konst KRecv) (Var i))
    (LetP (Var 0) (LetU (Var 1)
      (plet (App (Konst KSend) (Pair EUnit (Var 0))) (App (Konst KClos) (Var 0))))))).

(** The partner of S2 at index i: let ((), b̄) = recv b̄ in wait b̄. *)
Definition s2_partner (i : nat) : expr :=
  Lam (LetU (Var 0) (LetP (App (Konst KRecv) (Var i)) (LetU (Var 1) (App (Konst KClos) (Var 0))))).

(** ** The program of §2

    let (x, x̄) = new () in spawn (partner x̄);
    let x = send ((), x) in let ((), x) = recv x in wait x *)

Definition fall2 : expr :=
  LetP (App (Konst KNew) EUnit)
    (LetU (App (Konst KSpawn) (s1_partner 1))
      (plet (App (Konst KSend) (Pair EUnit (Var 1)))
        (LetP (App (Konst KRecv) (Var 0)) (LetU (Var 1) (App (Konst KClos) (Var 0)))))).

Lemma fall2_typed : ∃ p, pgv_rep [] p fall2 PUnit.
Proof.
  eexists. unfold fall2, s1_partner, plet. pnew S1. repeat pstep.
Qed.

(** S1 falls, so [fall2] lies outside the fragment of
    [pgv_deadlock_free_source]. *)
Lemma S1_not_mono : ¬ pgv_mono S1.
Proof. cbn. lia. Qed.

(** ** Two threads, the same types, opposite orders

    let (x, x̄) = new () in let (b, b̄) = new () in let (c, c̄) = new () in
    spawn (λ(). let b = send ((), b) in let x = send ((), x) in
                let ((), x) = recv x in wait x; close b);
    spawn (partner x̄); spawn (partner b̄); spawn (partner c̄);
    let c = send ((), c) in let (d, d̄) = new () in spawn (partner d̄);
    let z = recv c in let ((), c) = z in let d = send ((), d) in wait c; close d

    x, c : S1 and b, d : S2. *)

Definition xy_X : expr :=
  Lam (LetU (Var 0)
    (plet (App (Konst KSend) (Pair EUnit (Var 4)))
      (plet (App (Konst KSend) (Pair EUnit (Var 7)))
        (LetP (App (Konst KRecv) (Var 0))
          (LetU (Var 1) (LetU (App (Konst KClos) (Var 0)) (App (Konst KClos) (Var 3)))))))).

Definition xy_main : expr :=
  plet (App (Konst KSend) (Pair EUnit (Var 1)))
    (LetP (App (Konst KNew) EUnit)
      (LetU (App (Konst KSpawn) (s2_partner 1))
        (plet (App (Konst KRecv) (Var 2))
          (LetP (Var 0)
            (LetU (Var 1)
              (plet (App (Konst KSend) (Pair EUnit (Var 4)))
                (LetU (App (Konst KClos) (Var 1)) (App (Konst KClos) (Var 0))))))))).

Definition fallxy : expr :=
  LetP (App (Konst KNew) EUnit) (LetP (App (Konst KNew) EUnit) (LetP (App (Konst KNew) EUnit)
    (LetU (App (Konst KSpawn) xy_X)
      (LetU (App (Konst KSpawn) (s1_partner 5))
        (LetU (App (Konst KSpawn) (s2_partner 3))
          (LetU (App (Konst KSpawn) (s1_partner 1)) xy_main)))))).

Lemma fallxy_typed : ∃ p, pgv_rep [] p fallxy PUnit.
Proof.
  eexists. unfold fallxy, xy_X, xy_main, s1_partner, s2_partner, plet.
  pnew S1. pnew S2. pnew S1. repeat (first [pnew S2 | pstep]).
Qed.
