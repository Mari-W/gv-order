(** * Credits, costs and tickets (stage S2, proposal §2.11, §2.17)

    A credit, a cost, a counter and the tickets of an end range over
    ℕ ∪ {∞}, with [None] for ∞. Nothing here reads a point, a world or
    a term. *)

From stdpp Require Export base numbers.

(** ℕ ∪ {∞}. *)
Abbreviation fuel := (option nat).

Definition fle (a b : fuel) : Prop :=
  match a, b with
  | _, None => True
  | None, Some _ => False
  | Some m, Some n => m ≤ n
  end.

Definition fadd (a b : fuel) : fuel :=
  match a, b with Some m, Some n => Some (m + n) | _, _ => None end.

(** a − c, read where c ≤ a. ∞ − c = ∞. *)
Definition fsub (a c : fuel) : fuel :=
  match a, c with
  | None, _ => None
  | Some m, Some n => Some (m - n)
  | Some _, None => Some 0
  end.

Definition fmax (a b : fuel) : fuel :=
  match a, b with Some m, Some n => Some (Nat.max m n) | _, _ => None end.

Definition fmul (k : nat) (a : fuel) : fuel := (λ m, k * m) <$> a.

Global Instance fle_dec a b : Decision (fle a b).
Proof. destruct a, b; simpl; apply _. Defined.

Lemma fle_refl a : fle a a.
Proof. destruct a; simpl; lia. Qed.
Lemma fle_trans a b c : fle a b → fle b c → fle a c.
Proof. destruct a, b, c; simpl; lia. Qed.
Lemma fle_inf a : fle a None.
Proof. by destruct a. Qed.
Lemma fadd_0_l a : fadd (Some 0) a = a.
Proof. by destruct a. Qed.
Lemma fsub_inf a : fsub None a = None.
Proof. done. Qed.

(** Per-end capture reads f − a, the most a captured counter f may fall
    to before a call of a closure at credit a. *)
Lemma fsub_mono_l a f f' : fle f f' → fle (fsub f a) (fsub f' a).
Proof. destruct a, f, f'; simpl; lia. Qed.
Lemma fsub_anti_r f a a' : fle a' a → fle (fsub f a) (fsub f a').
Proof. destruct f, a, a'; simpl; lia. Qed.
Lemma fsub_age f a c : fle c a → fle (fsub f a) (fsub (fsub f c) (fsub a c)).
Proof. destruct f, a, c; simpl; lia. Qed.
Lemma fsub_le f a : fle (fsub f a) f.
Proof. destruct f, a; simpl; lia. Qed.

(** ** Tickets

    An end type carries its tickets m, an upper bound on the counter of
    the end, with credit a ≤ m. The judgment bound N bounds the tickets
    of the two ends of every channel, tk(o) + tk(ō) ≤ N, so an end with m
    tickets has a dual end with at most N − m. E-Link asks of the two
    linked ends a1 + m2 > N and a2 + m1 > N ([lgt]). At N = ∞ both
    premises hold. Tickets range over ℕ ∪ {∞}, and deadlock-free typing
    puts them at ∞ (decision of 2026-11-21,
    docs/redesign/check-links-without-tickets.md, last section). *)

(** a + m > N, true at N = ∞. *)
Definition lgt (N a m : fuel) : Prop :=
  match N with None => True | Some k => fle (Some (S k)) (fadd a m) end.

(** m1 + m2 ≤ N, the bound on the tickets of a channel. *)
Definition tsum_ok (N m1 m2 : fuel) : Prop := fle (fadd m1 m2) N.

(** The second end of a field creation takes what the bound leaves. *)
Definition ncap (N m : fuel) : fuel :=
  match N, m with Some k, Some m => Some (k - m) | Some k, None => Some 0 | None, _ => None end.

Lemma lgt_inf a m : lgt None a m.
Proof. done. Qed.

Lemma lgt_mono N a a' m m' : fle a a' → fle m m' → lgt N a m → lgt N a' m'.
Proof. destruct N as [k|], a as [a|], a' as [a'|], m as [m|], m' as [m'|]; simpl; try lia; done. Qed.

Lemma tsum_ok_inf m1 m2 : tsum_ok None m1 m2.
Proof. by destruct m1, m2. Qed.

Lemma tsum_ok_comm N m1 m2 : tsum_ok N m1 m2 → tsum_ok N m2 m1.
Proof. unfold tsum_ok. destruct N, m1, m2; simpl; lia. Qed.

Lemma tsum_ok_mono N m1 m2 m1' m2' : fle m1 m1' → fle m2 m2' → tsum_ok N m1' m2' → tsum_ok N m1 m2.
Proof. unfold tsum_ok. destruct N, m1, m2, m1', m2'; simpl; lia. Qed.

Lemma tsum_ncap N m : fle m N → tsum_ok N m (ncap N m).
Proof. unfold tsum_ok. destruct N as [k|], m as [m|]; simpl; try lia; done. Qed.

(** Half of the bound, the tickets of an interface end and of the
    positive end of a channel at a fresh base. *)
Definition fhalf (N : fuel) : fuel := (λ k, Nat.div2 k) <$> N.

Lemma fhalf_le N : fle (fhalf N) N.
Proof. destruct N as [k|]; simpl; [|done]. rewrite Nat.div2_div. apply Nat.Div0.div_le_upper_bound. lia. Qed.

Lemma tsum_half N : tsum_ok N (fhalf N) (ncap N (fhalf N)).
Proof. apply tsum_ncap, fhalf_le. Qed.

Lemma tsum_fhalf N : tsum_ok N (fhalf N) (fhalf N).
Proof.
  unfold tsum_ok, fhalf. destruct N as [k|]; simpl; [|done].
  rewrite Nat.div2_div. pose proof (Nat.Div0.mul_div_le k 2). lia.
Qed.

(** The arithmetic of a link. Let o1, o2 be the linked ends with
    counter c1 and tickets m1, m2, and r1, r2 the tickets of their
    dual ends. From c1 + m2 > N, c1 ≤ m1, m1 + r1 ≤ N and m2 + r2 ≤ N
    the two dual ends meet the bound together, and the tickets of the
    dual end of o2 lie below c1. *)
Lemma link_tsum N c1 m1 m2 r1 r2 :
  lgt (Some N) c1 m2 → fle c1 m1 → tsum_ok (Some N) m1 r1 → tsum_ok (Some N) m2 r2 →
  tsum_ok (Some N) r1 r2.
Proof. unfold tsum_ok. destruct c1, m1, m2, r1, r2; simpl; lia. Qed.

Lemma lgt_tsum_lt N k1 m2 r :
  lgt (Some N) (Some k1) m2 → tsum_ok (Some N) m2 r → ∃ kr, r = Some kr ∧ kr < k1.
Proof. unfold tsum_ok. destruct m2, r; simpl; try lia. intros. eexists; split; [done|lia]. Qed.

Lemma tsum_le_l N m1 m2 : tsum_ok (Some N) m1 m2 → fle m1 (Some N) ∧ is_Some m1.
Proof. unfold tsum_ok. destruct m1, m2; simpl; split; try lia; try done; by eexists. Qed.

Lemma tsum_le_r N m1 m2 : tsum_ok (Some N) m1 m2 → fle m2 (Some N) ∧ is_Some m2.
Proof. intros H. apply tsum_ok_comm in H. by apply tsum_le_l in H. Qed.

Lemma tsum_halves N m1 m2 : fle m1 (fhalf (Some N)) → fle m2 (fhalf (Some N)) → tsum_ok (Some N) m1 m2.
Proof.
  unfold tsum_ok, fhalf. destruct m1 as [a|], m2 as [b|]; simpl; try done.
  rewrite Nat.div2_div. intros Ha Hb. pose proof (Nat.Div0.mul_div_le N 2). lia.
Qed.
