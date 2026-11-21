(** * Credits, costs and ticket transformers (stage S2, proposal §2.11, §2.17)

    A credit, a cost and a counter range over ℕ ∪ {∞}, with
    [None] for ∞. A ticket transformer ϑ = (s, b) stands for
    r ↦ 2^s·r + b. Both the slope s and the offset b range over ℕ ∪ {∞}
    (decision Q11). A need of ∞ is met at no finite ticket count, so a
    transformer with offset ∞ is the transformer of the instance N = ∞.
    Nothing here reads a point, a world or a term. *)

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

(** ** Ticket transformers *)

Definition tix := (fuel * fuel)%type.

(** ϑ(r), ∞ when the slope is ∞ and r > 0 or the offset is ∞. *)
Definition tapp (t : tix) (r : nat) : fuel :=
  match t with
  | (Some s, b) => fadd (Some (2 ^ s * r)) b
  | (None, b) => if Nat.eqb r 0 then b else None
  end.

(** ϑ(r) ≤ tk on the map. *)
Definition meets (t : tix) (r tk : nat) : Prop :=
  match tapp t r with Some m => m ≤ tk | None => False end.

(** ϑ(0) ∈ ℕ on the map: a whole thread keeps no reserve, and some
    ticket count covers its need. *)
Definition tfin (t : tix) : Prop := ∃ tk, meets t 0 tk.

(** 1̂, the identity r ↦ r, and the transformer of N = ∞. *)
Definition tid : tix := (Some 0, Some 0).
Definition tinf : tix := (None, None).

Definition tle (t t' : tix) : Prop := ∀ r tk, meets t' r tk → meets t r tk.

Lemma tle_refl t : tle t t.
Proof. by intros r tk. Qed.
(** Nothing meets the transformer of N = ∞. *)
Lemma meets_tinf r tk : ¬ meets tinf r tk.
Proof. unfold meets, tapp, tinf. destruct (Nat.eqb r 0); simpl; tauto. Qed.
Lemma tle_tinf t : tle t tinf.
Proof. intros r tk H. by destruct (meets_tinf r tk). Qed.

(** Spawn: the child gets ⌈tk/2⌉ and needs bc, the parent ⌊tk/2⌋. *)
Definition tspawn (bc : fuel) (t : tix) : tix :=
  (S <$> t.1, fmax (fmul 2 t.2) (fsub (fmul 2 bc) (Some 1))).

(** Link: one ticket, then t. *)
Definition tlink (t : tix) : tix := (t.1, fadd t.2 (Some 1)).

(** Sequencing: first t1 then t2, (t1 ∘ t2)(r) = t1(t2(r)). *)
Definition tseq (t1 t2 : tix) : tix :=
  match t1, t2 with
  | (Some s1, b1), (Some s2, b2) => (Some (s1 + s2), fadd (fmul (2 ^ s1) b2) b1)
  | (Some s1, b1), (None, b2) => (None, fadd (fmul (2 ^ s1) b2) b1)
  | (None, b1), (_, Some 0) => (None, b1)
  | (None, b1), (_, _) => (None, fadd b1 (Some 1))
  end.

(** The pointwise bound of two transformers. *)
Definition tmax (t1 t2 : tix) : tix := (fmax t1.1 t2.1, fmax t1.2 t2.2).

(** t1 ∘ t2 is sound when t2 needs nothing at 0, t1 has a finite slope,
    or t1 has offset ∞ (then t1 ∘ t2 is met nowhere). *)
Definition tok (t1 t2 : tix) : Prop := t2.2 = Some 0 ∨ t1.1 ≠ None ∨ t1.2 = None.

Lemma link_split t r tk : meets (tlink t) r tk → 1 ≤ tk ∧ meets t r (tk - 1).
Proof.
  destruct t as [[s|] [b|]]; unfold meets, tlink, tapp; simpl; try done.
  - lia.
  - destruct (Nat.eqb r 0); lia.
  - by destruct (Nat.eqb r 0).
Qed.
