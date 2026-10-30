(** * Types of Padovani and Novara

    L. Padovani and L. Novara, Types for Deadlock-Free Higher-Order
    Programs, FORTE 2015 (HAL hal-01767327), pdf pages 7, 10, 12 and 13.
    Levels L = ℤ ∪ {⊥, ⊤}, channel types p[t]ⁿ, arrows t →^{ρ,σ} s, the
    level |t|, the shift ⇑ⁿ and the wrapping ⌈t⌉ⁿ.

    Fragment v1 (docs/extensions/adequacy/padovani-novara.md §7).

    - unit is the only basic type. Sums t + s of unlimited types stand in
      for int in the test of fibo. A sum is a basic type, so its level is
      ⊤ and ⇑ⁿ leaves it alone.
    - Polarities are ? and !. The full polarity # of a fresh channel
      becomes two variables (PNTyping.v).
    - The level ρ of an arrow is an integer or ⊤ ([None]). No rule
      produces level ⊥, and a function of level ⊥ cannot be applied.
    - Recursive types are the channels μα.p[⌈α⌉ᵐ]ⁿ ([PRec]) that carry a
      copy of themselves shifted by m. They cover the signal pipe. *)

From stdpp Require Import base countable list numbers.

(** Equalities of terms that differ in integer arithmetic only. *)
Ltac zeq := repeat (first [reflexivity | lia | f_equal]).

(** ** Levels *)

Inductive lvl := LBot | LZ (z : Z) | LTop.

Definition lvl_lt (a b : lvl) : Prop :=
  match a, b with
  | LBot, LBot => False
  | LBot, _ => True
  | LZ z, LZ z' => (z < z')%Z
  | LZ _, LTop => True
  | _, _ => False
  end.

Definition lvl_le (a b : lvl) : Prop :=
  match a, b with
  | LBot, _ => True
  | LZ z, LZ z' => (z ≤ z')%Z
  | _, LTop => True
  | _, _ => False
  end.

(** ρ ⊔ σ. *)
Definition lvl_max (a b : lvl) : lvl :=
  match a, b with
  | LBot, x | x, LBot => x
  | LTop, _ | _, LTop => LTop
  | LZ z, LZ z' => LZ (Z.max z z')
  end.

(** n + σ, with n + ⊥ = ⊥ and n + ⊤ = ⊤ (p. 10). *)
Definition lvl_sh (n : Z) (a : lvl) : lvl :=
  match a with LZ z => LZ (z + n) | x => x end.

(** A level of a type or an environment, ⊤ as [None]. *)
Definition olvl (o : option Z) : lvl :=
  match o with Some z => LZ z | None => LTop end.

Definition omin (a b : option Z) : option Z :=
  match a, b with
  | None, x | x, None => x
  | Some z, Some z' => Some (Z.min z z')
  end.

(** ** Types

    [PChan inp t n] is ?[t]ⁿ when [inp] and ![t]ⁿ otherwise.
    [PRec inp m n] is μα.p[⌈α⌉ᵐ]ⁿ, whose unfolding is p[⌈μα.p[⌈α⌉ᵐ]ⁿ⌉ᵐ]ⁿ.
    [PDisp m t] is ⌈t⌉ᵐ. [PArr t r σ s] is t →^{r,σ} s with r = [None]
    for ⊤. *)

Inductive pty :=
  | PUnit
  | PSum (t s : pty)
  | PChan (inp : bool) (t : pty) (n : Z)
  | PRec (inp : bool) (m n : Z)
  | PDisp (m : Z) (t : pty)
  | PArr (t : pty) (r : option Z) (σ : lvl) (s : pty).

(** |t| (p. 7, p. 13): |B| = ⊤, |p[t]ⁿ| = n, |t →^{ρ,σ} s| = ρ and
    |⌈t⌉ᵐ| = m + |t|. *)
Fixpoint tlev (t : pty) : option Z :=
  match t with
  | PUnit | PSum _ _ => None
  | PChan _ _ n | PRec _ _ n => Some n
  | PDisp m t => (λ z, z + m)%Z <$> tlev t
  | PArr _ r _ _ => r
  end.

(** un(t) (p. 7). *)
Definition un (t : pty) : Prop := tlev t = None.

(** ⇑ⁿ (p. 10, p. 13). It adds n to every finite level and leaves
    basic types alone. ⇑ⁿ(μα.p[⌈α⌉ᵐ]ᵏ) = μα.p[⌈α⌉ᵐ]^{k+n}, because the
    unfolding commutes with the shift. *)
Fixpoint lshift (k : Z) (t : pty) : pty :=
  match t with
  | PUnit => PUnit
  | PSum t s => PSum t s
  | PChan p t n => PChan p (lshift k t) (n + k)
  | PRec p m n => PRec p m (n + k)
  | PDisp m t => PDisp m (lshift k t)
  | PArr t r σ s => PArr (lshift k t) ((λ z, z + k)%Z <$> r) (lvl_sh k σ) (lshift k s)
  end.

Lemma lshift_0 t : lshift 0 t = t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; f_equal; auto; try lia.
  - destruct r; simpl; zeq.
  - destruct σ; simpl; zeq.
Qed.

Lemma lshift_lshift a b t : lshift a (lshift b t) = lshift (b + a) t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; f_equal; auto; try lia.
  - destruct r; simpl; zeq.
  - destruct σ; simpl; zeq.
Qed.

Lemma tlev_lshift k t : tlev (lshift k t) = (λ z, z + k)%Z <$> tlev t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; try done.
  - rewrite IH. destruct (tlev t); simpl; zeq.
Qed.

Lemma un_lshift k t : un (lshift k t) ↔ un t.
Proof. unfold un. rewrite tlev_lshift. destruct (tlev t); naive_solver. Qed.

(** ** Payloads (fragment v1)

    A payload is a channel, possibly wrapped, or an unlimited value. *)

Fixpoint chanlike (t : pty) : bool :=
  match t with
  | PChan _ _ _ | PRec _ _ _ => true
  | PDisp _ t => chanlike t
  | _ => false
  end.

Definition un_b (t : pty) : bool := match tlev t with None => true | Some _ => false end.

Lemma un_b_un t : un_b t = true ↔ un t.
Proof. unfold un_b, un. destruct (tlev t); naive_solver. Qed.

Definition payok (t : pty) : Prop := chanlike t = true ∨ un t.

Lemma chanlike_lshift k t : chanlike (lshift k t) = chanlike t.
Proof. induction t; simpl; auto. Qed.

Lemma un_b_lshift k t : un_b (lshift k t) = un_b t.
Proof. unfold un_b. rewrite tlev_lshift. by destruct (tlev t). Qed.

(** ** Channel codes

    [chres k t] is the code of the channel ⇑ᵏ t, wrappings resolved and
    one unfolding taken, with polarity ? whatever the polarity of t. Both
    ends of a channel and a recursive channel and its unfolding have one
    code. *)

Fixpoint chres (k : Z) (t : pty) : option pty :=
  match t with
  | PChan _ t n => Some (PChan true (lshift k t) (n + k))
  | PRec p m n => Some (PChan true (PDisp m (PRec p m (n + k))) (n + k))
  | PDisp m t => chres (k + m) t
  | _ => None
  end.

Lemma chres_lshift k j t : chres k (lshift j t) = chres (k + j) t.
Proof.
  revert k. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k; simpl; try done.
  - rewrite lshift_lshift. zeq.
  - zeq.
  - rewrite IH. zeq.
Qed.

Lemma chres_out k j t : chres (k + j) t = lshift j <$> chres k t.
Proof.
  revert k. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k; simpl; try done.
  - rewrite lshift_lshift. zeq.
  - zeq.
  - rewrite <-IH. zeq.
Qed.

Lemma chres_chanlike k t : chanlike t = true → ∃ c, chres k t = Some c.
Proof. revert k. induction t; intros k; simpl; try done; eauto. Qed.

(** The payload of a code: the code of the channel it carries. *)
Definition cpay (c : pty) : option pty :=
  match c with PChan _ pl _ => chres 0 pl | _ => None end.

Lemma cpay_lshift j c : cpay (lshift j c) = lshift j <$> cpay c.
Proof.
  destruct c; simpl; try done. rewrite chres_lshift, <-chres_out. zeq.
Qed.

(** The level of a code. *)
Definition clev (c : pty) : option Z := match c with PChan _ _ n => Some n | _ => None end.

Lemma clev_lshift j c : clev (lshift j c) = (λ z, z + j)%Z <$> clev c.
Proof. by destruct c. Qed.

(** The level of a channel and of its code agree. *)
Lemma chres_lev k t c : chres k t = Some c → ∃ z, tlev t = Some z ∧ clev c = Some (z + k)%Z.
Proof.
  revert k. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k Hc; simpl in *;
    try done; try (injection Hc as <-; eexists; split; [done|]; simpl; zeq).
  destruct (IH _ Hc) as (z & -> & Hz). eexists. split; [done|]. rewrite Hz. f_equal. lia.
Qed.

(** ** Normalization of level-⊤ arrows

    A function of level ⊤ is level polymorphic, and its translation is a
    box quantified over a level anchor. Shifted copies of one arrow get
    one box, read relative to the first finite level of the arrow
    ([mlev]). ⇑ⁿ moves that level by n ([mlev_lshift]), and an arrow
    without finite levels is fixed by ⇑ⁿ ([mlev_none]). *)

Fixpoint mlev (t : pty) : option Z :=
  match t with
  | PUnit | PSum _ _ => None
  | PChan _ _ n | PRec _ _ n => Some n
  | PDisp _ t => mlev t
  | PArr t r σ s =>
      match r with
      | Some z => Some z
      | None =>
          match σ with
          | LZ z => Some z
          | _ => match mlev t with Some z => Some z | None => mlev s end
          end
      end
  end.

Lemma mlev_lshift j t : mlev (lshift j t) = (λ z, z + j)%Z <$> mlev t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; try done.
  destruct r; simpl; [done|]. destruct σ; simpl; try done;
    rewrite IH1; destruct (mlev t); simpl; done.
Qed.

Lemma mlev_none j t : mlev t = None → lshift j t = t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; intros H; try done.
  - by rewrite IH.
  - destruct r; [done|]. destruct σ; try done;
      destruct (mlev t); try done; by rewrite IH1, IH2.
Qed.

(** ** Countability (codes are slot indices of points) *)

Global Instance lvl_eq_dec : EqDecision lvl.
Proof. solve_decision. Defined.

Global Instance pty_eq_dec : EqDecision pty.
Proof. solve_decision. Defined.

Definition lvl_enc (a : lvl) : gen_tree Z :=
  match a with LBot => GenNode 0 [] | LTop => GenNode 1 [] | LZ z => GenLeaf z end.
Definition lvl_dec (t : gen_tree Z) : lvl :=
  match t with GenNode 0 [] => LBot | GenLeaf z => LZ z | _ => LTop end.

Definition oz_enc (o : option Z) : gen_tree Z :=
  match o with None => GenNode 0 [] | Some z => GenLeaf z end.
Definition oz_dec (t : gen_tree Z) : option Z :=
  match t with GenLeaf z => Some z | _ => None end.

Definition b_enc (b : bool) : gen_tree Z := GenNode (if b then 1 else 0) [].
Definition b_dec (t : gen_tree Z) : bool := match t with GenNode 1 [] => true | _ => false end.

Fixpoint pty_enc (t : pty) : gen_tree Z :=
  match t with
  | PUnit => GenNode 0 []
  | PSum t s => GenNode 1 [pty_enc t; pty_enc s]
  | PChan p t n => GenNode 2 [b_enc p; pty_enc t; GenLeaf n]
  | PRec p m n => GenNode 3 [b_enc p; GenLeaf m; GenLeaf n]
  | PDisp m t => GenNode 4 [GenLeaf m; pty_enc t]
  | PArr t r σ s => GenNode 5 [pty_enc t; oz_enc r; lvl_enc σ; pty_enc s]
  end.

Fixpoint pty_dec (t : gen_tree Z) : pty :=
  match t with
  | GenNode 1 [t; s] => PSum (pty_dec t) (pty_dec s)
  | GenNode 2 [p; t; GenLeaf n] => PChan (b_dec p) (pty_dec t) n
  | GenNode 3 [p; GenLeaf m; GenLeaf n] => PRec (b_dec p) m n
  | GenNode 4 [GenLeaf m; t] => PDisp m (pty_dec t)
  | GenNode 5 [t; r; σ; s] => PArr (pty_dec t) (oz_dec r) (lvl_dec σ) (pty_dec s)
  | _ => PUnit
  end.

Lemma pty_dec_enc t : pty_dec (pty_enc t) = t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; f_equal; auto;
    try (by destruct p); [by destruct r|by destruct σ].
Qed.

Global Instance pty_countable : Countable pty.
Proof. apply (inj_countable' pty_enc pty_dec). apply pty_dec_enc. Qed.
