(** * Types, session types, duality, environments (§2.2, Fig. 5 top)

    T, U ::= ∗ | T ⊸^β_λ U | T ⊗ U | T ⊕ U | S@ι | □(∀ιs αs. C. T) | ∃^ℓ ιs. C. T
    S    ::= Skip | S;S | ?P | !P | ⊕(S, S) | &(S, S) | Close | µα.S | α | α̅
                                                    P ::= ∃ιs. T
    (context-free session types, K1 of docs/extensions/context-free.md)
    β, λ ::= ι, optional (absent bounds are left out, sharp edges 149)
    ℓ    ::= absent | ι | ⊥   (⊥ the unknown point)
    ι    ::= (p, b)       p ::= a | point variable | (p, b)[i]   (no channels) *)

From stdpp Require Import base strings gmap countable.
From LRGV Require Export lang.Syntax.

(** ** Points

    One sort of names (decision N). A point (p, b) is a name p with an
    offset b. A name is a point constant, a point variable (de Bruijn,
    bound by ∀ under □ or by ∃ in a payload), or (p, b)[i], "the point
    of the i-th channel carried by the message sent at (p, b)". The
    channel continues at (p, b)[i] after branch i was picked at (p, b),
    the same point the i-th channel of a message sent at (p, b) gets
    (K11 of docs/extensions/context-free.md). Worlds and environments
    use ground points (constants and their payload points), static
    types also use variables. No point mentions a channel, so renaming channels
    changes no type and no world.

    The name of (p, b)[i] writes p and b unpacked, so that
    names are not mutual with points. *)

Inductive pname :=
  | NConst (a : nat)
  | NVar (a : nat)
  | NPayload (p : pname) (b : nat) (i : nat).   (* (p, b)[i] *)

(** A point carries a polarity (end points, docs/extensions/end-points.md).
    The two ends of a channel sit at dual points x and x̄, which share
    name and offset and differ in [pt_pol]. [Pt p o] is the point of
    positive polarity. *)
Record point := MkPt { pt_name : pname; pt_pol : bool; pt_off : nat }.
Abbreviation Pt p o := (MkPt p true o).

Global Instance pname_eq_dec : EqDecision pname.
Proof. solve_decision. Defined.

Global Instance pname_countable : Countable pname.
Proof.
  set (enc := fix go p : gen_tree nat :=
    match p with
    | NConst a => GenNode 1 [GenLeaf a]
    | NVar a => GenLeaf a
    | NPayload p b i => GenNode 0 [go p; GenLeaf b; GenLeaf i]
    end).
  set (dec := fix go t : pname :=
    match t with
    | GenNode 1 [GenLeaf a] => NConst a
    | GenLeaf a => NVar a
    | GenNode 0 [t; GenLeaf b; GenLeaf i] => NPayload (go t) b i
    | _ => NVar 0
    end).
  apply (inj_countable' enc dec).
  intros p; induction p; simpl; congruence.
Qed.

Global Instance point_eq_dec : EqDecision point.
Proof. solve_decision. Defined.

Global Instance point_countable : Countable point.
Proof.
  apply (inj_countable' (λ x, (pt_name x, pt_pol x, pt_off x)) (λ '(p, q, b), MkPt p q b)).
  by intros [].
Qed.

(** x + n, x[i], the variable a, and the constant a at offset 0. *)
Definition pt_shift (n : nat) (x : point) : point :=
  MkPt (pt_name x) (pt_pol x) (pt_off x + n).
(** The payload point x[i] names the i-th carried end. It is the same
    point from both ends of the carrier, so it ignores the polarity of
    x and is positive itself: x̄[i] = x[i]. *)
Definition pt_payload (x : point) (i : nat) : point :=
  Pt (NPayload (pt_name x) (pt_off x) i) 0.
(** The dual point x̄, the point of the other end. *)
Definition pt_dual (x : point) : point :=
  MkPt (pt_name x) (negb (pt_pol x)) (pt_off x).
(** The point y read at polarity b: y itself for [true], ȳ for [false]. *)
Definition pt_polar (b : bool) (y : point) : point := if b then y else pt_dual y.

Lemma pt_dual_dual x : pt_dual (pt_dual x) = x.
Proof. destruct x as [p b o]. unfold pt_dual. simpl. by rewrite negb_involutive. Qed.
Lemma pt_dual_shift n x : pt_dual (pt_shift n x) = pt_shift n (pt_dual x).
Proof. done. Qed.
Lemma pt_payload_dual x i : pt_payload (pt_dual x) i = pt_payload x i.
Proof. done. Qed.
Lemma pt_dual_inj x y : pt_dual x = pt_dual y → x = y.
Proof. intros H. by rewrite <-(pt_dual_dual x), H, pt_dual_dual. Qed.
Lemma pt_dual_neq x : pt_dual x ≠ x.
Proof. destruct x as [p [] o]; unfold pt_dual; simpl; congruence. Qed.
Lemma pt_polar_shift b n y : pt_polar b (pt_shift n y) = pt_shift n (pt_polar b y).
Proof. by destruct b. Qed.
Lemma pt_polar_dual b y : pt_polar b (pt_dual y) = pt_dual (pt_polar b y).
Proof. by destruct b. Qed.
Lemma pt_polar_payload b y i : pt_payload (pt_polar b y) i = pt_payload y i.
Proof. by destruct b. Qed.
(** The payload point p[j] and the offset p + k, written x ·[ j ] and
    x +ₚ k, the paper's p[j] and p+k. *)
Notation "x ·[ j ]" := (pt_payload x j) (at level 2, j at level 200, left associativity, format "x ·[ j ]").
Notation "x +ₚ k" := (pt_shift k x) (at level 50, left associativity).
(** The index j of x[j] for branch i: x[0] for the first branch ([false]),
    x[1] for the second ([true]) (K11). *)
Definition bidx (i : bool) : nat := if i then 1 else 0.
(** Where a choice continues (end points): the selecting end at
    (x[i])‾, the branching end at x[i]. The two are dual. *)
Definition sel_pt (x : point) (i : bool) : point := pt_dual (pt_payload x (bidx i)).
Definition bra_pt (x : point) (i : bool) : point := pt_payload x (bidx i).

Definition pvar (a : nat) : point := Pt (NVar a) 0.
Definition pconst (a : nat) : point := Pt (NConst a) 0.

(** Instantiation of point variables. A name denotes the point at
    offset 0; the offset of a point adds on top. *)
Fixpoint pn_inst (σ : nat → point) (p : pname) : point :=
  match p with
  | NConst a => Pt (NConst a) 0
  | NVar a => σ a
  | NPayload p b i => pt_payload (pt_shift b (pn_inst σ p)) i
  end.

Definition pt_inst (σ : nat → point) (x : point) : point :=
  pt_polar (pt_pol x) (pt_shift (pt_off x) (pn_inst σ (pt_name x))).

(** Lifting an instantiation under a binder of m point variables. *)
Definition pup (m : nat) (σ : nat → point) : nat → point :=
  λ a, if decide (a < m) then pvar a
       else pt_inst (λ a', pvar (a' + m)) (σ (a - m)).

(** The instantiation that sends the variable i to the i-th point of
    a list, and shifts the variables beyond it down. *)
Definition plist (xs : list point) : nat → point :=
  λ a, match xs !! a with Some x => x | None => pvar (a - length xs) end.

(** The points x[0], …, x[m-1] of a point x. *)
Definition payload_pts (x : point) (m : nat) : list point :=
  (λ i, pt_payload x i) <$> seq 0 m.

(** Facts of a constraint: x ≺ y and x ≡ y (sharp edges 65). *)
Inductive fact := FLt (x y : point) | FEq (x y : point).

Definition fact_map (f : point → point) (g : fact) : fact :=
  match g with FLt x y => FLt (f x) (f y) | FEq x y => FEq (f x) (f y) end.

(** g holds when its ≺ holds in [lt] and its ≡ in [eq]. *)
Definition fact_holds (eq lt : point → point → Prop) (g : fact) : Prop :=
  match g with FLt x y => lt x y | FEq x y => eq x y end.

(** Two facts of the same kind with related points. *)
Definition fact_rel (R : point → point → Prop) (g g' : fact) : Prop :=
  match g, g' with
  | FLt x y, FLt x' y' | FEq x y, FEq x' y' => R x x' ∧ R y y'
  | _, _ => False
  end.

(** The root of a name is a variable below k. *)
Fixpoint pn_vb (k : nat) (p : pname) : Prop :=
  match p with
  | NConst _ => False | NVar a => a < k | NPayload q _ _ => pn_vb k q
  end.

Definition fact_scoped (k : nat) (g : fact) : Prop :=
  match g with FLt x y | FEq x y => pn_vb k (pt_name x) ∧ pn_vb k (pt_name y) end.

(** The constraint of a box (sharp edges 65): any set of positive facts,
    finite or infinite. It is a closure: the facts [bc_facts] speak of
    variables only, 0, …, n-1 for the box's ιs and n + j for the j-th
    point of [bc_env], which lives outside the binder and carries the
    outer point variables and constants. Substitution and renaming act
    on [bc_env] alone and never touch the predicate, so their equations
    hold by computation on lists, without functional extensionality.
    The roots of a constraint are the finitely many roots of [bc_env].
    A fact whose variables lie beyond n + |bc_env| is not part of C. *)
Record bcs := BCs { bc_env : list point; bc_facts : fact → Prop }.

(** The lower bound of an existential (sharp edges 97, 103, 149).
    [LNone] is no bound, the value holds no channel. [LBot] is ⊥, the
    unknown point: the value holds channels at points not known from
    outside, and no point lies below ⊥. [LPt x] says that every
    channel of the value lies at or above x. ⊥ is no point. It occurs
    only here, and a future that holds such a value carries a flag
    instead (static/FactTheory.v). The lower bound of an arrow is an
    optional point, [None] when the closure holds no channel, and its
    upper bound is an optional point, [None] when a call never blocks. *)
Inductive lbound := LNone | LBot | LPt (x : point).

Definition lb_map (f : point → point) (lb : lbound) : lbound :=
  match lb with LPt x => LPt (f x) | LNone => LNone | LBot => LBot end.

Lemma lb_map_ext f g lb : (∀ x, f x = g x) → lb_map f lb = lb_map g lb.
Proof. intros H. destruct lb; simpl; by rewrite ?H. Qed.

Lemma lb_map_comp f g lb : lb_map f (lb_map g lb) = lb_map (f ∘ g) lb.
Proof. by destruct lb. Qed.

Lemma lb_map_id f lb : (∀ x, f x = x) → lb_map f lb = lb.
Proof. intros H. destruct lb; simpl; by rewrite ?H. Qed.

(** ** Types

    The arrow carries an optional upper point β ([None]: the call
    never blocks) and an optional lower point λ ([None]: the closure
    holds nothing). □ binds n point variables, so ∀ occurs only directly
    under □ (sharp edges 109). ∃ binds n, and a
    payload binds m. Session types are unannotated: the only points
    inside them are those of payloads, all bound by the payload's ∃, so
    point instantiation never enters a session type. *)

Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (ub lb : option point) (T U : ty)
                                   (* T ⊸^ub_lb U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSum (T U : ty)                (* T ⊕ U *)
  | TBox (n k : nat) (C : bcs) (T : ty)
                                   (* □(∀ι₀ … ιₙ₋₁ α₀ … αₖ₋₁. C. T) — unlimited
                                      (replicable) values. T is a thunk
                                      type ∗ ⊸^u U, so the upper point
                                      u lives on the arrow under the
                                      binder (sharp edges 52, 63); the
                                      constraint C is a set of facts
                                      x ≺ y and x ≡ y over the ιs and
                                      outer points (sharp edges 65).
                                      The αs are the session variables
                                      0, …, k-1 of T (K6, sharp edges 73) *)

  | TSess (S : sty) (x : point)   (* S@x *)
  | TEx (lb : lbound) (n : nat) (C : bcs) (T : ty)
                                   (* ∃^ℓ ι₀ … ιₙ₋₁. C. T — existential
                                      points (sharp edges 97, 103): the
                                      value lies in T at some known
                                      instance meeting C, and its
                                      channels lie at or above the lower
                                      bound ℓ, which is absent, ⊥ or a point *)
with sty :=
  | SRcv (m : nat) (T : ty)        (* ?(∃ι₀ … ιₘ₋₁. T), no continuation *)
  | SSnd (m : nat) (T : ty)        (* !(∃ι₀ … ιₘ₋₁. T), no continuation *)
  | SEnd                           (* Close *)
  | SMu (S : sty)                  (* µα.S — binds one session variable *)
  | SVar (a : nat)                 (* α — de Bruijn *)
  | SVarD (a : nat)                (* α̅ — the dual of what α stands for;
                                      never written in source types, it
                                      enters only through [dual] *)
  | SSkip                          (* Skip *)
  | SSeq (S1 S2 : sty)             (* S₁;S₂ *)
  | SPlus (S1 S2 : sty)            (* ⊕(S₁, S₂): select a branch *)
  | SWith (S1 S2 : sty).           (* &(S₁, S₂): offer both branches *)

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

(** ** Point instantiation

    T[σ]: instantiate the free point variables of T. Session types are
    left alone (see above), so this is a plain recursion on [ty]. *)

(** C[σ]: the outer points of C instantiated. *)
Definition bcs_inst (σ : nat → point) (C : bcs) : bcs :=
  BCs (pt_inst σ <$> bc_env C) (bc_facts C).

(** The facts of C under its binder of n point variables: the ιs are
    the variables 0, …, n-1 and the outer points are shifted past them. *)
Definition bcs_open (n : nat) (C : bcs) (g : fact) : Prop :=
  ∃ f, bc_facts C f ∧ fact_scoped (n + length (bc_env C)) f ∧
    g = fact_map (pt_inst (pup n (plist (bc_env C)))) f.

(** C holds at the instance xs: every fact of C[xs/ιs] holds, ≺ in [lt]
    and ≡ in [eq] (sharp edges 65). *)
Definition bcs_hold (eq lt : point → point → Prop) (C : bcs) (xs : list point) : Prop :=
  ∀ g, bcs_open (length xs) C g → fact_holds eq lt (fact_map (pt_inst (plist xs)) g).

Lemma bcs_hold_mono (eq eq' lt lt' : point → point → Prop) C xs :
  (∀ x y, eq x y → eq' x y) → (∀ x y, lt x y → lt' x y) →
  bcs_hold eq lt C xs → bcs_hold eq' lt' C xs.
Proof. intros He Hl H g Hg. specialize (H g Hg). destruct g; simpl in *; auto. Qed.

Lemma fact_map_ext (f f' : point → point) g :
  (∀ x, f x = f' x) → fact_map f g = fact_map f' g.
Proof. intros H. destruct g; simpl; by rewrite !H. Qed.

Lemma fact_map_comp (f f' : point → point) g :
  fact_map f (fact_map f' g) = fact_map (f ∘ f') g.
Proof. by destruct g. Qed.

(** Substitution of the outer points is the image of the open facts
    under the lifted substitution. *)
Section bcs_open.
  Local Lemma bpt_shift_0 x : pt_shift 0 x = x.
  Proof. destruct x as [p b o]. unfold pt_shift. simpl. f_equal. lia. Qed.

  Local Lemma bpt_inst_pvar σ a : pt_inst σ (pvar a) = σ a.
  Proof. unfold pt_inst, pvar. simpl. apply bpt_shift_0. Qed.

  Local Lemma bpt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
  Proof.
    destruct x as [p b o]. unfold pt_inst, pt_shift. simpl.
    destruct (pn_inst σ p). destruct b; unfold pt_polar, pt_dual; simpl; f_equal; lia.
  Qed.

  Local Lemma bpt_inst_dual σ x : pt_inst σ (pt_dual x) = pt_dual (pt_inst σ x).
  Proof.
    destruct x as [p b o]. unfold pt_inst. simpl.
    destruct b; simpl; [done|by rewrite pt_dual_dual].
  Qed.

  Local Lemma bpn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
  Proof.
    induction p as [a|a|p IH b i]; simpl; [done|done|].
    assert (∀ x, pt_inst τ (pt_payload x i) = pt_payload (pt_inst τ x) i) as Hs
      by (intros [q [] o]; reflexivity).
    by rewrite Hs, bpt_inst_shift, IH.
  Qed.

  Local Lemma bpt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
  Proof.
    destruct x as [n b o]. unfold pt_inst at 2 3. simpl.
    destruct b; simpl; [|rewrite bpt_inst_dual]; by rewrite bpt_inst_shift, bpn_inst_comp.
  Qed.

  Local Lemma bpt_inst_ext_vb k σ τ x :
    pn_vb k (pt_name x) → (∀ a, a < k → σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros Hx H. destruct x as [p bb o]. unfold pt_inst. simpl in *. do 2 f_equal.
    induction p as [a|a|p IH b i]; simpl in *; [done|by apply H|by rewrite IH..].
  Qed.

  Local Lemma bpt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros H. destruct x as [p bb o]. unfold pt_inst. simpl. do 2 f_equal.
    induction p as [a|a|p IH b i]; simpl; [done|apply H|by rewrite IH..].
  Qed.

  Local Lemma bpup_plist σ n env a :
    a < n + length env →
    pup n (plist (pt_inst σ <$> env)) a = pt_inst (pup n σ) (pup n (plist env) a).
  Proof.
    intros Ha. unfold pup at 1 3. destruct (decide (a < n)).
    - rewrite bpt_inst_pvar. unfold pup. by rewrite decide_True.
    - unfold plist. rewrite list_lookup_fmap.
      destruct (lookup_lt_is_Some_2 env (a - n)) as [e He]; [lia|]. rewrite He. simpl.
      rewrite !bpt_inst_comp. apply bpt_inst_ext. intros b. simpl.
      rewrite bpt_inst_pvar. unfold pup. rewrite decide_False by lia.
      by replace (b + n - n) with b by lia.
  Qed.

  Lemma bcs_open_inst σ n C g :
    bcs_open n (bcs_inst σ C) g ↔ ∃ g0, bcs_open n C g0 ∧ g = fact_map (pt_inst (pup n σ)) g0.
  Proof.
    destruct C as [env P]. unfold bcs_open, bcs_inst; simpl. rewrite length_fmap.
    assert (∀ f, fact_scoped (n + length env) f →
              fact_map (pt_inst (pup n (plist (pt_inst σ <$> env)))) f
              = fact_map (pt_inst (pup n σ)) (fact_map (pt_inst (pup n (plist env))) f)) as E.
    { intros f Hf. rewrite fact_map_comp.
      assert (∀ x, pn_vb (n + length env) (pt_name x) →
                pt_inst (pup n (plist (pt_inst σ <$> env))) x
                = (pt_inst (pup n σ) ∘ pt_inst (pup n (plist env))) x) as Ex.
      { intros x Hx. simpl. rewrite bpt_inst_comp. apply (bpt_inst_ext_vb _ _ _ _ Hx).
        intros a Ha. by apply bpup_plist. }
      destruct f; simpl in *; destruct Hf; f_equal; auto. }
    split.
    - intros (f & Hf & Hs & ->). exists (fact_map (pt_inst (pup n (plist env))) f).
      split; [by exists f|]. by apply E.
    - intros (g0 & (f & Hf & Hs & ->) & ->). exists f. split_and!; [done|done|].
      symmetry. by apply E.
  Qed.
End bcs_open.

Fixpoint pinst_ty (σ : nat → point) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U =>
      TLolli (pt_inst σ <$> ub) (pt_inst σ <$> lb)
        (pinst_ty σ T1) (pinst_ty σ U)
  | TProd T1 U => TProd (pinst_ty σ T1) (pinst_ty σ U)
  | TSum T1 U => TSum (pinst_ty σ T1) (pinst_ty σ U)
  | TBox n k C T1 =>
      TBox n k (bcs_inst σ C) (pinst_ty (pup n σ) T1)
  | TSess s x => TSess s (pt_inst σ x)
  | TEx lb n C T1 =>
      TEx (lb_map (pt_inst σ) lb) n (bcs_inst σ C) (pinst_ty (pup n σ) T1)
  end.

(** T[xs/ιs]: instantiate the ∀ of a □ (or the ∃ of a payload) with a
    list of points. *)
Definition ty_inst (xs : list point) (T : ty) : ty := pinst_ty (plist xs) T.

(** The payload ∃ι₀ … ιₘ₋₁. T at the point x: P[x] = T[x[i]/ιᵢ]. *)
Definition payload_at (m : nat) (T : ty) (x : point) : ty :=
  ty_inst (payload_pts x m) T.

(** Composition and identity of point instantiation on types. The
    relation instantiates the ∃ of [TEx] by composing substitutions
    (relation/LogicalRelation.v, sharp edges 73). *)
Section tinst.
  Local Lemma tpt_shift_0 x : pt_shift 0 x = x.
  Proof. destruct x as [p b o]. unfold pt_shift. simpl. f_equal. lia. Qed.

  Lemma tpt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
  Proof. unfold pt_inst, pvar. simpl. apply tpt_shift_0. Qed.

  Local Lemma tpt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
  Proof.
    destruct x as [p b o]. unfold pt_inst, pt_shift. simpl.
    destruct (pn_inst σ p). destruct b; unfold pt_polar, pt_dual; simpl; f_equal; lia.
  Qed.

  Lemma tpt_inst_dual σ x : pt_inst σ (pt_dual x) = pt_dual (pt_inst σ x).
  Proof.
    destruct x as [p b o]. unfold pt_inst. simpl.
    destruct b; simpl; [done|by rewrite pt_dual_dual].
  Qed.

  Local Lemma tpn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
  Proof.
    induction p as [a|a|p IH b i]; simpl; [done|done|].
    assert (∀ x, pt_inst τ (pt_payload x i) = pt_payload (pt_inst τ x) i) as Hs
      by (intros [q [] o]; reflexivity).
    by rewrite Hs, tpt_inst_shift, IH.
  Qed.

  Lemma tpt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
  Proof.
    destruct x as [n b o]. unfold pt_inst at 2 3. simpl.
    destruct b; simpl; [|rewrite tpt_inst_dual]; by rewrite tpt_inst_shift, tpn_inst_comp.
  Qed.

  Lemma tpt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros H. destruct x as [p bb o]. unfold pt_inst. simpl. do 2 f_equal.
    induction p as [a|a|p IH b i]; simpl; [done|apply H|by rewrite IH..].
  Qed.

  Lemma tpt_inst_pvar x : pt_inst pvar x = x.
  Proof.
    destruct x as [p bb o]. unfold pt_inst. simpl.
    assert (pn_inst pvar p = Pt p 0) as ->;
      [|destruct bb; unfold pt_polar, pt_shift, pt_dual; simpl; f_equal; lia].
    induction p as [a|a|p IH b i]; simpl; [done|done|by rewrite IH..].
  Qed.

  Lemma tpup_ext n σ τ a : (∀ b, σ b = τ b) → pup n σ a = pup n τ a.
  Proof. intros H. unfold pup. by rewrite H. Qed.

  Lemma tpup_pvar n a : pup n pvar a = pvar a.
  Proof.
    unfold pup. destruct (decide (a < n)); [done|].
    rewrite tpt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia.
  Qed.

  Lemma tpup_comp τ σ n a : pt_inst (pup n τ) (pup n σ a) = pup n (pt_inst τ ∘ σ) a.
  Proof.
    unfold pup at 2 3. destruct (decide (a < n)).
    - rewrite tpt_inst_pvar_at. unfold pup. by rewrite decide_True.
    - change ((pt_inst τ ∘ σ) (a - n)) with (pt_inst τ (σ (a - n))).
      rewrite !tpt_inst_comp. apply tpt_inst_ext. intros b. simpl.
      rewrite tpt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
      by replace (b + n - n) with b by lia.
  Qed.

  Lemma tbcs_ext σ τ C : (∀ a, σ a = τ a) → bcs_inst σ C = bcs_inst τ C.
  Proof.
    intros H. destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
    apply list_fmap_ext. intros _ x _. by apply tpt_inst_ext.
  Qed.

  Lemma tbcs_comp τ σ C : bcs_inst τ (bcs_inst σ C) = bcs_inst (pt_inst τ ∘ σ) C.
  Proof.
    destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
    rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply tpt_inst_comp.
  Qed.

  Lemma tbcs_pvar C : bcs_inst pvar C = C.
  Proof.
    destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
    rewrite <-(list_fmap_id env) at 2. apply list_fmap_ext. intros _ x _. apply tpt_inst_pvar.
  Qed.

  Lemma tinst_ext T : ∀ σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
  Proof.
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n k C T1 IH | s x
                   | lb n C T1 IH]; intros σ τ H; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_ext
               |destruct lb; simpl; f_equal; auto using tpt_inst_ext|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; [by apply tbcs_ext|]. apply IH. intros a. by apply tpup_ext.
    - f_equal. by apply tpt_inst_ext.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_ext|by apply tbcs_ext|].
      apply IH. intros a. by apply tpup_ext.
  Qed.

  Lemma tinst_comp T : ∀ τ σ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
  Proof.
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n k C T1 IH | s x
                   | lb n C T1 IH]; intros τ σ; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_comp
               |destruct lb; simpl; f_equal; auto using tpt_inst_comp|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; [apply tbcs_comp|]. rewrite IH. apply tinst_ext. intros a. apply tpup_comp.
    - f_equal. apply tpt_inst_comp.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_comp|apply tbcs_comp|].
      rewrite IH. apply tinst_ext. intros a. apply tpup_comp.
  Qed.

  Lemma tinst_pvar T : pinst_ty pvar T = T.
  Proof.
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n k C T1 IH | s x
                   | lb n C T1 IH]; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_pvar
               |destruct lb; simpl; f_equal; auto using tpt_inst_pvar|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; [apply tbcs_pvar|]. rewrite (tinst_ext _ _ pvar); [done|apply tpup_pvar].
    - f_equal. apply tpt_inst_pvar.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_pvar|apply tbcs_pvar|].
      rewrite (tinst_ext _ _ pvar); [done|apply tpup_pvar].
  Qed.
End tinst.

(** Induction on types in which the body of an existential is available
    at every instance (sharp edges 73): the value relation reads an
    existential at the instance of its witness. *)
Fixpoint tsize (T : ty) : nat :=
  match T with
  | TUnit | TSess _ _ => 1
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U => S (tsize T1 + tsize U)
  | TBox _ _ _ T1 | TEx _ _ _ T1 => S (tsize T1)
  end.

Lemma tsize_pinst T : ∀ σ, tsize (pinst_ty σ T) = tsize T.
Proof. induction T; intros σ; simpl; auto. Qed.

Lemma ty_ind_ex (P : ty → Prop) :
  P TUnit →
  (∀ ub lb T, P T → ∀ U, P U → P (TLolli ub lb T U)) →
  (∀ T, P T → ∀ U, P U → P (TProd T U)) →
  (∀ T, P T → ∀ U, P U → P (TSum T U)) →
  (∀ n k C T, P T → P (TBox n k C T)) →
  (∀ s x, P (TSess s x)) →
  (∀ lb n C T, (∀ σ, P (pinst_ty σ T)) → P (TEx lb n C T)) →
  ∀ T, P T.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7.
  enough (∀ m T, tsize T < m → P T) as H by (intros T; apply (H (S (tsize T))); lia).
  induction m as [|m IH]; intros T HT; [lia|].
  destruct T; simpl in HT.
  - done.
  - apply H2; apply IH; lia.
  - apply H3; apply IH; lia.
  - apply H4; apply IH; lia.
  - apply H5; apply IH; lia.
  - apply H6.
  - apply H7. intros σ. apply IH. rewrite tsize_pinst. lia.
Qed.

(** ** Heads

    The points at which a value of the type is next used:
    heads(S@ι) = {ῑ}, heads(T ⊸^β_λ U) = {λ} (∅ without λ), ∅ for ∗ and □.
    The head of an end is the point of its partner end (end points,
    docs/extensions/end-points.md): a thread blocked at u that holds an
    end at v owes u ≺ v̄. Lower bounds λ and ℓ already live among these
    partner points. *)

Definition opt_heads (o : option point) : gset point :=
  match o with Some x => {[x]} | None => ∅ end.

Definition lb_heads (lb : lbound) : gset point :=
  match lb with LPt x => {[x]} | _ => ∅ end.

Fixpoint heads (T : ty) : gset point :=
  match T with
  | TUnit | TBox _ _ _ _ => ∅
  | TLolli _ lb _ _ => opt_heads lb
  | TProd T1 U | TSum T1 U => heads T1 ∪ heads U
  | TSess _ x => {[pt_dual x]}
  | TEx lb _ _ _ => lb_heads lb
  end.

(** The ⊥ flag of a type (sharp edges 103): a value of the type may
    hold an unopened existential with lower bound ⊥, whose channels lie
    at points not known from outside. heads(T) is the set of points of
    the heads of T, and the flag is the rest. *)
Fixpoint hbot (T : ty) : bool :=
  match T with
  | TProd T1 U | TSum T1 U => hbot T1 || hbot U
  | TEx LBot _ _ _ => true
  | _ => false
  end.

Lemma hbot_pinst σ T : hbot (pinst_ty σ T) = hbot T.
Proof. induction T; simpl; try done; try congruence. by destruct lb. Qed.

(** ** Session-type substitution (§4.3)

    Equi-recursive types identify µα.S with its unfolding S[µα.S/α],
    so the unfolding has to be computed. A session variable may occur
    anywhere a session type may, including inside the payload of a
    communication, so renaming and substitution traverse [ty] and
    [sty] mutually. Term variables and session variables live in
    separate namespaces; [upren] from Syntax.v is reused for the
    latter's shifts. *)

Fixpoint sren_ty (r : nat → nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (sren_ty r T1) (sren_ty r U)
  | TProd T1 U => TProd (sren_ty r T1) (sren_ty r U)
  | TSum T1 U => TSum (sren_ty r T1) (sren_ty r U)
  | TBox n k C T1 => TBox n k C (sren_ty (Nat.iter k upren r) T1)
  | TSess s x => TSess (sren r s) x
  | TEx lb n C T1 => TEx lb n C (sren_ty r T1)
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sren_ty r T)
  | SSnd m T => SSnd m (sren_ty r T)
  | SEnd => SEnd
  | SMu s' => SMu (sren (upren r) s')
  | SVar a => SVar (r a)
  | SVarD a => SVarD (r a)
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sren r s1) (sren r s2)
  | SPlus s1 s2 => SPlus (sren r s1) (sren r s2)
  | SWith s1 s2 => SWith (sren r s1) (sren r s2)
  end.

(** ** Polarity flip

    [sflip k] swaps α ↔ α̅ at de Bruijn level k and leaves every other
    variable alone. Duality uses it to fix up the variable a µ binds:
    in [dual (SMu s)] the binder's meaning changes from the protocol
    to its dual, so occurrences that kept denoting the original
    protocol must switch polarity. *)

Fixpoint sflip_ty (k : nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (sflip_ty k T1) (sflip_ty k U)
  | TProd T1 U => TProd (sflip_ty k T1) (sflip_ty k U)
  | TSum T1 U => TSum (sflip_ty k T1) (sflip_ty k U)
  | TBox n kk C T1 => TBox n kk C (sflip_ty (kk + k) T1)
  | TSess s x => TSess (sflip k s) x
  | TEx lb n C T1 => TEx lb n C (sflip_ty k T1)
  end
with sflip (k : nat) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sflip_ty k T)
  | SSnd m T => SSnd m (sflip_ty k T)
  | SEnd => SEnd
  | SMu s' => SMu (sflip (S k) s')
  | SVar a => if decide (a = k) then SVarD a else SVar a
  | SVarD a => if decide (a = k) then SVar a else SVarD a
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sflip k s1) (sflip k s2)
  | SPlus s1 s2 => SPlus (sflip k s1) (sflip k s2)
  | SWith s1 s2 => SWith (sflip k s1) (sflip k s2)
  end.

(** ** Session duality: swaps the direction of communication.

    Polarized duality after Gay, Thiemann and Vasconcelos, "Duality of
    Session Types: The Final Cut". Payloads are left alone — ?T.S and
    !T.S carry the same T — and variables carry a polarity:

      dual α = α̅    dual α̅ = α    dual (µα.S) = µα. flip₀ (dual S)
      dual Skip = Skip    dual (S₁;S₂) = dual S₁; dual S₂
      dual ⊕(S₁, S₂) = &(dual S₁, dual S₂)    dual &(S₁, S₂) = ⊕(dual S₁, dual S₂)

    The flip at the binder makes tail occurrences ("continue as
    myself") come out as α again, while payload occurrences come out
    as α̅ and keep denoting the *original* protocol. The naive
    dual α = α is unsound here: for µα.!(α).α, unrolling then
    dualizing gives payload µα.!(α).α, dualizing then unrolling gives
    payload µα.?(α).α. With polarities the two orders agree —
    [dual_unfoldS] below, unconditionally. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv m T => SSnd m T
  | SSnd m T => SRcv m T
  | SEnd => SEnd
  | SMu s' => SMu (sflip 0 (dual s'))
  | SVar a => SVarD a
  | SVarD a => SVar a
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (dual s1) (dual s2)
  | SPlus s1 s2 => SWith (dual s1) (dual s2)
  | SWith s1 s2 => SPlus (dual s1) (dual s2)
  end.

(** Substituting under α̅ dualizes the substituend, matching its
    reading as "the dual of what α stands for". *)

Definition sty_up (σ : nat → sty) : nat → sty := SVar 0 .: (sren S ∘ σ).

Fixpoint sinst_ty (σ : nat → sty) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (sinst_ty σ T1) (sinst_ty σ U)
  | TProd T1 U => TProd (sinst_ty σ T1) (sinst_ty σ U)
  | TSum T1 U => TSum (sinst_ty σ T1) (sinst_ty σ U)
  | TBox n k C T1 => TBox n k C (sinst_ty (Nat.iter k sty_up σ) T1)
  | TSess s x => TSess (sinst σ s) x
  | TEx lb n C T1 => TEx lb n C (sinst_ty σ T1)
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sinst_ty σ T)
  | SSnd m T => SSnd m (sinst_ty σ T)
  | SEnd => SEnd
  | SMu s' => SMu (sinst (sty_up σ) s')
  | SVar a => σ a
  | SVarD a => dual (σ a)
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sinst σ s1) (sinst σ s2)
  | SPlus s1 s2 => SPlus (sinst σ s1) (sinst σ s2)
  | SWith s1 s2 => SWith (sinst σ s1) (sinst σ s2)
  end.

(** One-step unrolling: µα.s ↦ s[µα.s/α]. *)
Definition unroll (s : sty) : sty := sinst (SMu s .: SVar) s.

(** ** Head normal form (K3 of docs/extensions/context-free.md)

    The relation reads a session type only through its head normal
    form unr(S) (Thiemann and Vasconcelos 2016, §3.3 and Lemma 3.8),
    whose cases are

      Skip | !P;S′ | ?P;S′ | α;S′ | α̅;S′ | ⊕(S₁, S₂) | &(S₁, S₂) | Close

    A lone !P, ?P or variable is read as itself followed by Skip, a
    choice followed by S distributes S into its branches, and Close;S
    is Close (K2: after a close the entry leaves the environment, so S
    is never read). unr unrolls µ and descends into the left of ;
    until such a head appears.

    unr terminates on contractive types only, so [unrN] counts fuel and
    returns [None] when it runs out. [unfoldS] runs it with the fuel
    [sfuel S] and returns S itself when no head appears. A stuck type is
    never in head form ([unrN_shape]), so the relation's clauses, which
    all match on a head, relate nothing at it. We call S contractive when
    [unfoldS S] is a head ([contractive]), which is "unr(S) is defined"
    of Lemma 3.8. On a closed type that is contractive in the sense of
    Fig. 3 of the paper, unr never reaches a recursion variable, so it
    explores only the syntax of S and the fuel suffices. That
    characterization is not mechanized. *)

(** S₁;S₂ for a head S₁ other than Skip: the continuation joins the
    head's own, and a choice takes it into both branches. *)
Definition hseq (h s2 : sty) : sty :=
  match h with
  | SSeq o SSkip => SSeq o s2
  | SSeq o r => SSeq o (SSeq r s2)
  | SPlus a b => SPlus (SSeq a s2) (SSeq b s2)
  | SWith a b => SWith (SSeq a s2) (SSeq b s2)
  | _ => h
  end.

Fixpoint unrN (k : nat) (s : sty) : option sty :=
  match k with
  | 0 => None
  | S k' =>
      match s with
      | SSkip => Some SSkip
      | SSeq s1 s2 =>
          match unrN k' s1 with
          | Some SSkip => unrN k' s2
          | Some h => Some (hseq h s2)
          | None => None
          end
      | SRcv m T => Some (SSeq (SRcv m T) SSkip)
      | SSnd m T => Some (SSeq (SSnd m T) SSkip)
      | SVar a => Some (SSeq (SVar a) SSkip)
      | SVarD a => Some (SSeq (SVarD a) SSkip)
      | SMu b => unrN k' (unroll b)
      | SEnd => Some SEnd
      | SPlus a b => Some (SPlus a b)
      | SWith a b => Some (SWith a b)
      end
  end.

(** The fuel: one per ; and µ on the spine of the type. *)
Fixpoint sfuel (s : sty) : nat :=
  match s with
  | SSeq a b => S (sfuel a + sfuel b)
  | SMu b => S (sfuel b)
  | _ => 1
  end.

Definition unfoldS (s : sty) : sty :=
  match unrN (sfuel s) s with Some h => h | None => s end.

(** The heads. *)
Definition satom (o : sty) : Prop :=
  match o with SRcv _ _ | SSnd _ _ | SVar _ | SVarD _ => True | _ => False end.

Definition hnf_shape (h : sty) : Prop :=
  match h with
  | SSkip | SEnd | SPlus _ _ | SWith _ _ => True
  | SSeq o _ => satom o
  | _ => False
  end.

Definition contractive (s : sty) : Prop := hnf_shape (unfoldS s).

Lemma hseq_shape h s2 : hnf_shape h → h ≠ SSkip → hnf_shape (hseq h s2).
Proof.
  destruct h as [| | | | | | |o r| |]; simpl; try done.
  destruct r; done.
Qed.

Lemma unrN_shape k : ∀ s h, unrN k s = Some h → hnf_shape h.
Proof.
  induction k as [|k IH]; intros s h Hs; [done|].
  destruct s; simpl in Hs; try (injection Hs as <-; done); [by eapply IH|].
  destruct (unrN k s1) as [h1|] eqn:E1; [|done].
  pose proof (IH _ _ E1) as Hh1.
  destruct h1 as [| | | | | | |o r| |]; try (exact (IH _ _ Hs)); simpl in Hh1; try done;
    injection Hs as <-; simpl; try done; destruct r; done.
Qed.

Lemma unrN_mono k : ∀ k' s h, unrN k s = Some h → k ≤ k' → unrN k' s = Some h.
Proof.
  induction k as [|k IH]; intros k' s h Hs Hk; [done|].
  destruct k' as [|k']; [lia|]. destruct s; simpl in *; try done.
  - apply IH; [done|lia].
  - destruct (unrN k s1) as [h1|] eqn:E1; [|done].
    rewrite (IH k' _ _ E1) by lia.
    destruct h1; try done. apply IH; [done|lia].
Qed.

(** A head is its own normal form. *)
Lemma sfuel_pos s : 1 ≤ sfuel s.
Proof. destruct s; simpl; lia. Qed.

Lemma unrN_hd k s : hnf_shape s → sfuel s ≤ k → unrN k s = Some s.
Proof.
  intros Hs Hk. destruct s as [| | | | | | |o r| |]; simpl in *; try done;
    destruct k as [|k]; try lia; try done.
  pose proof (sfuel_pos o). destruct k as [|k]; [lia|].
  destruct o; simpl; try done; destruct r; done.
Qed.

Lemma unrN_hd_fuel u : hnf_shape u → unrN (sfuel u) u = Some u.
Proof.
  intros Hu. by apply unrN_hd.
Qed.

Lemma unfoldS_hd u : hnf_shape u → unfoldS u = u.
Proof. intros Hu. unfold unfoldS. by rewrite unrN_hd_fuel. Qed.

Lemma unfoldS_rcv m T s : unfoldS (SSeq (SRcv m T) s) = SSeq (SRcv m T) s.
Proof. by apply unfoldS_hd. Qed.

Lemma unfoldS_snd m T s : unfoldS (SSeq (SSnd m T) s) = SSeq (SSnd m T) s.
Proof. by apply unfoldS_hd. Qed.

Lemma unfoldS_plus a b : unfoldS (SPlus a b) = SPlus a b.
Proof. by apply unfoldS_hd. Qed.

Lemma unfoldS_with a b : unfoldS (SWith a b) = SWith a b.
Proof. by apply unfoldS_hd. Qed.

Lemma unfoldS_end : unfoldS SEnd = SEnd.
Proof. done. Qed.

(** [unfoldS] either reaches a head or leaves the type alone. *)
Lemma unfoldS_cases s : (unrN (sfuel s) s = Some (unfoldS s) ∧ hnf_shape (unfoldS s)) ∨
                        (unrN (sfuel s) s = None ∧ unfoldS s = s).
Proof.
  unfold unfoldS. destruct (unrN (sfuel s) s) as [h|] eqn:E; [left|by right].
  split; [done|]. by eapply unrN_shape.
Qed.

(** A head that [unfoldS] returns is the one every larger fuel gives. *)
Lemma unfoldS_unrN s k : hnf_shape (unfoldS s) → sfuel s ≤ k → unrN k s = Some (unfoldS s).
Proof.
  intros Hh Hk. destruct (unfoldS_cases s) as [[E _]|[E Es]].
  - by eapply unrN_mono.
  - exfalso. rewrite Es in Hh. by rewrite unrN_hd_fuel in E.
Qed.

(** The view of a head and hereditary contractiveness (SessionEquiv.v
    reads ≈ through them; konst_ty asks force's session instances to be
    hereditarily contractive, K6). *)

Inductive hview :=
  | HSkip
  | HRcv (m : nat) (T : ty) (s : sty)
  | HSnd (m : nat) (T : ty) (s : sty)
  | HVar (a : nat) (s : sty)
  | HVarD (a : nat) (s : sty)
  | HPlus (s1 s2 : sty)
  | HWith (s1 s2 : sty)
  | HEnd
  | HStuck (u : sty).

Definition view (u : sty) : hview :=
  match u with
  | SSkip => HSkip
  | SSeq (SRcv m T) s => HRcv m T s
  | SSeq (SSnd m T) s => HSnd m T s
  | SSeq (SVar a) s => HVar a s
  | SSeq (SVarD a) s => HVarD a s
  | SPlus a b => HPlus a b
  | SWith a b => HWith a b
  | SEnd => HEnd
  | u => HStuck u
  end.

Definition unview (h : hview) : sty :=
  match h with
  | HSkip => SSkip
  | HRcv m T s => SSeq (SRcv m T) s
  | HSnd m T s => SSeq (SSnd m T) s
  | HVar a s => SSeq (SVar a) s
  | HVarD a s => SSeq (SVarD a) s
  | HPlus a b => SPlus a b
  | HWith a b => SWith a b
  | HEnd => SEnd
  | HStuck u => u
  end.

Lemma unview_view u : unview (view u) = u.
Proof. destruct u as [| | | | | | |o r| |]; try done. by destruct o. Qed.

(** The head of S. *)
Definition hd (s : sty) : hview := view (unfoldS s).

Lemma unfoldS_unview s : unfoldS s = unview (hd s).
Proof. unfold hd. by rewrite unview_view. Qed.

Lemma hd_of s u : unfoldS s = u → hd s = view u.
Proof. unfold hd. by intros ->. Qed.

Definition hc_step (τ : sty → Prop) (s : sty) : Prop :=
  match hd s with
  | HSkip | HEnd => True
  | HRcv _ _ s' | HSnd _ _ s' | HVar _ s' | HVarD _ s' => τ s'
  | HPlus a b | HWith a b => τ a ∧ τ b
  | HStuck _ => False
  end.

Fixpoint ahc (n : nat) (s : sty) : Prop :=
  match n with 0 => True | S n' => hc_step (ahc n') s end.

Definition hcontractive (s : sty) : Prop := ∀ n, ahc n s.

(** ** Closedness of session variables *)

Fixpoint sclosed_ty (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U =>
      sclosed_ty k T1 ∧ sclosed_ty k U
  | TBox _ kk _ T1 => sclosed_ty (kk + k) T1
  | TSess s _ => sclosed k s
  | TEx _ _ _ T1 => sclosed_ty k T1
  end
with sclosed (k : nat) (s : sty) : Prop :=
  match s with
  | SRcv _ T | SSnd _ T => sclosed_ty k T
  | SEnd | SSkip => True
  | SMu s' => sclosed (S k) s'
  | SVar a | SVarD a => a < k
  | SSeq s1 s2 | SPlus s1 s2 | SWith s1 s2 => sclosed k s1 ∧ sclosed k s2
  end.

(** A box binds k session variables: the session substitutions lift
    under it k times, as under k µ's. *)
Lemma sty_up_ext σ σ' : (∀ a, σ a = σ' a) → ∀ a, sty_up σ a = sty_up σ' a.
Proof. intros H [|a]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma iter_sty_up_ext k σ σ' :
  (∀ a, σ a = σ' a) → ∀ a, Nat.iter k sty_up σ a = Nat.iter k sty_up σ' a.
Proof. revert σ σ'. induction k as [|k IH]; intros σ σ' H; simpl; [done|]. by apply sty_up_ext, IH. Qed.

Lemma sinst_ext_mut :
  (∀ T σ σ', (∀ a, σ a = σ' a) → sinst_ty σ T = sinst_ty σ' T) ∧
  (∀ s σ σ', (∀ a, σ a = σ' a) → sinst σ s = sinst σ' s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - apply H. by apply iter_sty_up_ext.
  - apply H. by apply sty_up_ext.
Qed.

Definition sinst_ext := proj2 sinst_ext_mut.

(** The identity substitution leaves a type alone. *)
Lemma sinst_id_mut :
  (∀ T σ, (∀ a, σ a = SVar a) → sinst_ty σ T = T) ∧
  (∀ s σ, (∀ a, σ a = SVar a) → sinst σ s = s).
Proof.
  assert (∀ σ, (∀ a, σ a = SVar a) → ∀ a, sty_up σ a = SVar a) as Hup
    by (intros σ H [|a]; simpl; [done|]; unfold compose; by rewrite H).
  assert (∀ k σ, (∀ a, σ a = SVar a) → ∀ a, Nat.iter k sty_up σ a = SVar a) as Hit.
  { induction k as [|k IH]; intros σ H; simpl; [done|]. apply Hup. by apply IH. }
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  all: by rewrite H.
Qed.

(** ** The flip algebra

    [sflip k] is an involution, distinct levels commute, and it
    commutes with [dual] — everything a polarity swap should be. *)

Lemma sflip_sflip_mut :
  (∀ T k, sflip_ty k (sflip_ty k T) = T) ∧
  (∀ s k, sflip k (sflip k s) = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto;
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_sflip := proj2 sflip_sflip_mut.

Lemma sflip_comm_mut :
  (∀ T j k, j ≠ k → sflip_ty j (sflip_ty k T) = sflip_ty k (sflip_ty j T)) ∧
  (∀ s j k, j ≠ k → sflip j (sflip k s) = sflip k (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; auto with lia; done);
    try (f_equal; apply H; lia);
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_comm := proj2 sflip_comm_mut.

Lemma sflip_dual s : ∀ j, sflip j (dual s) = dual (sflip j s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros j; simpl; f_equal;
    auto.
  - rewrite <-IH. apply sflip_comm. lia.
  - repeat (case_decide; simpl); congruence.
  - repeat (case_decide; simpl); congruence.
Qed.

Lemma sfuel_sflip s : ∀ k, sfuel (sflip k s) = sfuel s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros k; simpl; auto;
    try case_decide; done.
Qed.

Lemma dual_involutive s : dual (dual s) = s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; simpl; f_equal; auto.
  rewrite <-sflip_dual, sflip_sflip. exact IH.
Qed.

Lemma sfuel_dual s : sfuel (dual s) = sfuel s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; simpl; auto.
  by rewrite sfuel_sflip, IH.
Qed.

(** ** Flip versus renaming and substitution

    [sflip k ∘ sren r] pushes through as [sren r ∘ sflip j] when r
    maps exactly the preimage of k to k ([sflip_sren_iff_mut]) and
    vanishes when nothing maps to k ([sflip_sren_ne_mut]). *)

Lemma upren_iff r j k : (∀ a, r a = k ↔ a = j) → ∀ a, upren r a = S k ↔ a = S j.
Proof.
  intros H0 [|a]; simpl; unfold compose.
  - split; intros Heq; exfalso; lia.
  - destruct (H0 a) as [Hf Hb]. split; intros Heq.
    + f_equal. apply Hf. lia.
    + f_equal. apply Hb. lia.
Qed.

Lemma iter_upren_iff kk r j k :
  (∀ a, r a = k ↔ a = j) → ∀ a, Nat.iter kk upren r a = kk + k ↔ a = kk + j.
Proof.
  revert r. induction kk as [|kk IH]; intros r H; simpl; [done|].
  apply (upren_iff (Nat.iter kk upren r) (kk + j) (kk + k)). by apply IH.
Qed.

Lemma upren_ne r k : (∀ a, r a ≠ k) → ∀ a, upren r a ≠ S k.
Proof. intros H0 [|a]; simpl; [lia|]. unfold compose. specialize (H0 a). lia. Qed.

Lemma iter_upren_ne kk r k : (∀ a, r a ≠ k) → ∀ a, Nat.iter kk upren r a ≠ kk + k.
Proof.
  revert r. induction kk as [|kk IH]; intros r H; simpl; [done|].
  apply (upren_ne (Nat.iter kk upren r) (kk + k)). by apply IH.
Qed.

Lemma sflip_sren_iff_mut :
  (∀ T j k r, (∀ a, r a = k ↔ a = j) →
     sflip_ty k (sren_ty r T) = sren_ty r (sflip_ty j T)) ∧
  (∀ s j k r, (∀ a, r a = k ↔ a = j) →
     sflip k (sren r s) = sren r (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. by apply iter_upren_iff.
  - apply H. by apply upren_iff.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
Qed.

Lemma sflip_sren_ne_mut :
  (∀ T k r, (∀ a, r a ≠ k) → sflip_ty k (sren_ty r T) = sren_ty r T) ∧
  (∀ s k r, (∀ a, r a ≠ k) → sflip k (sren r s) = sren r s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. by apply iter_upren_ne.
  - apply H. by apply upren_ne.
  - case_decide; [naive_solver|done].
  - case_decide; [naive_solver|done].
Qed.

Lemma dual_sren s : ∀ r, dual (sren r s) = sren r (dual s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros r; simpl; f_equal;
    auto.
  rewrite IH. apply (proj2 sflip_sren_iff_mut).
  intros [|a]; simpl; unfold compose; split; intros; simplify_eq; done.
Qed.

(** [sflip k] slides through a substitution that is the identity at k
    and flip-invariant elsewhere — [sty_up]-lifted substitutions are. *)

Lemma sty_up_flip σ k :
  σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
  sty_up σ (S k) = SVar (S k) ∧ ∀ a, a ≠ S k → sflip (S k) (sty_up σ a) = sty_up σ a.
Proof.
  intros H0 H1. split.
  - simpl. unfold compose. by rewrite H0.
  - intros [|a] Ha; simpl; [done|]. unfold compose.
    rewrite (proj2 sflip_sren_iff_mut _ k) by (intros; lia).
    rewrite H1; [done|lia].
Qed.

Lemma iter_sty_up_flip kk σ k :
  σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
  Nat.iter kk sty_up σ (kk + k) = SVar (kk + k) ∧
  ∀ a, a ≠ kk + k → sflip (kk + k) (Nat.iter kk sty_up σ a) = Nat.iter kk sty_up σ a.
Proof.
  intros H0 H1. induction kk as [|kk [IH0 IH1]]; simpl; [done|].
  exact (sty_up_flip _ _ IH0 IH1).
Qed.

Lemma sflip_sinst_mut :
  (∀ T k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip_ty k (sinst_ty σ T) = sinst_ty σ (sflip_ty k T)) ∧
  (∀ s k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip k (sinst σ s) = sinst σ (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - destruct (iter_sty_up_flip k σ k0 H0 H1). by apply H.
  - destruct (sty_up_flip σ k H0 H1). by apply H.
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + rewrite sflip_dual. by rewrite H0.
Qed.

(** ** Duality versus substitution and unfolding

    With polarized variables, duality commutes with substitution on
    the nose — same σ on both sides, no closedness needed. *)

Lemma dual_sinst s : ∀ σ, dual (sinst σ s) = sinst σ (dual s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros σ; simpl; f_equal;
    auto.
  - rewrite IH. apply (proj2 sflip_sinst_mut); [done|].
    intros [|a] Ha; simpl; [lia|]. unfold compose.
    apply (proj2 sflip_sren_ne_mut). intros; lia.
  - apply dual_involutive.
Qed.

(** Flipping the head variable of the term matches dualizing what the
    substitution feeds it. *)

Lemma sty_up_dual σ σ' k :
  σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
  sty_up σ' (S k) = dual (sty_up σ (S k)) ∧ ∀ a, a ≠ S k → sty_up σ' a = sty_up σ a.
Proof.
  intros H0 H1. split.
  - simpl. unfold compose. by rewrite H0, dual_sren.
  - intros [|a] Ha; simpl; [done|]. unfold compose. rewrite H1; [done|lia].
Qed.

Lemma iter_sty_up_dual kk σ σ' k :
  σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
  Nat.iter kk sty_up σ' (kk + k) = dual (Nat.iter kk sty_up σ (kk + k)) ∧
  ∀ a, a ≠ kk + k → Nat.iter kk sty_up σ' a = Nat.iter kk sty_up σ a.
Proof.
  intros H0 H1. induction kk as [|kk [IH0 IH1]]; simpl; [done|].
  exact (sty_up_dual _ _ _ IH0 IH1).
Qed.

Lemma sinst_sflip_dual_mut :
  (∀ T k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst_ty σ T = sinst_ty σ' (sflip_ty k T)) ∧
  (∀ s k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst σ s = sinst σ' (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - destruct (iter_sty_up_dual k σ σ' k0 H0 H1). by apply H.
  - destruct (sty_up_dual σ σ' k H0 H1). by apply H.
  - case_decide; simplify_eq; simpl.
    + by rewrite H, dual_involutive.
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + by rewrite H.
    + by rewrite H0.
Qed.

(** The two ends of a µ unroll in lockstep: unrolling substitutes
    µα.s at α and dual (µα.s) at α̅, which is exactly the reading
    [dual] gave the two polarities. *)

Lemma dual_unroll s : dual (unroll s) = unroll (sflip 0 (dual s)).
Proof.
  unfold unroll. rewrite dual_sinst.
  apply (proj2 sinst_sflip_dual_mut); [done|].
  intros [|a] Ha; [lia|done].
Qed.

Lemma dual_hseq h s2 : dual (hseq h s2) = hseq (dual h) (dual s2).
Proof. destruct h as [| | | | | | |o r| |]; simpl; try done. by destruct r. Qed.

Lemma dual_skip_iff h : dual h = SSkip ↔ h = SSkip.
Proof. split; [|by intros ->]. by destruct h. Qed.

Lemma dual_unrN k : ∀ s, unrN k (dual s) = dual <$> unrN k s.
Proof.
  induction k as [|k IH]; intros s; simpl; [done|].
  destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; simpl; try done.
  - by rewrite <-dual_unroll, IH.
  - rewrite IH. destruct (unrN k s1) as [h|]; simpl; [|done].
    destruct h as [| | | | | | |h1 h2| |]; simpl; try apply IH; try done.
    destruct h2; done.
Qed.

(** The property CONNECT needs: the two ends of a session unfold in
    lockstep — unconditionally, thanks to the polarized dual. *)
Lemma dual_unfoldS s : dual (unfoldS s) = unfoldS (dual s).
Proof.
  unfold unfoldS. rewrite sfuel_dual, dual_unrN.
  by destruct (unrN (sfuel s) s).
Qed.

Lemma hnf_shape_dual h : hnf_shape (dual h) ↔ hnf_shape h.
Proof. destruct h as [| | | | | | |o r| |]; simpl; try done. by destruct o. Qed.

Lemma contractive_dual s : contractive (dual s) ↔ contractive s.
Proof. unfold contractive. by rewrite <-dual_unfoldS, hnf_shape_dual. Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V)
  | prim_box n k C ub U : prim U → prim (TBox n k C (TLolli ub None TUnit U)).

(** ** Unlimited types

    The types whose variables admit contraction and weakening. The
    structural rules of Fig. 4 ([lsplit_unl], [lwk_drop]) and the
    relevance conjunct of semantic typing are stated against this
    predicate rather than against a single modality, so that adding
    one is a matter of extending the match below. *)

Definition unlimited (T : ty) : Prop :=
  match T with TBox _ _ _ _ => True | _ => False end.

(** ** Session environments: finite maps from channels to session
    types at points, c : S@x, x the channel's current point. Each
    action on c moves x to x + 1.
    This is the process-level Σ, one end per channel.

    Splitting Σ = Σ1, Σ2 is disjoint union of the underlying maps. *)

(** A notation rather than a definition, so that stdpp's map lemmas
    apply by keyed unification without unfolding. *)
Notation senv := (gmap chan (sty * point)).

(** Σ assigns c a session type whose *unfolding* is u, at point k,
    over the rest Σ1. Every clause of the logical relation that inspects a session
    type goes through this, which is what makes the relation respect
    µα.S = S[µα.S/α] without ever comparing environments up to that
    equation: the stored type is whatever it is, and only its head
    normal form is matched. On a non-contractive type [unfoldS] leaves
    a µ or a variable in head position, so no clause applies. *)
Definition senv_hd (Σ : senv) (c : chan) (u : sty) (k : point)
    (Σ1 : senv) : Prop :=
  ∃ s, Σ = <[c := (s, k)]> Σ1 ∧ unfoldS s = u.

(** An empty environment assigns nothing. *)
Lemma senv_hd_not_empty c u k Σ1 : ¬ senv_hd ∅ c u k Σ1.
Proof. intros (s & Heq & _). exact (insert_non_empty _ _ _ (eq_sym Heq)). Qed.

Lemma senv_hd_dom Σ c u k Σ1 :
  senv_hd Σ c u k Σ1 → dom Σ = {[c]} ∪ dom Σ1.
Proof. intros (s & -> & _). by rewrite dom_insert_L. Qed.

(** ** Term-level environments

    Θ may hold both ends of a channel (both carry the channel's one
    name): after [new], and after receiving the other end of a channel
    the thread already holds. An entry of Θ is a channel with one end
    ([One]) or two ([Both]); the two ends of a [Both] are unordered,
    and that they are dual at the same point is stated where it is needed
    ([Coequal.tenv_dual]). The process-level Σ embeds as [One]s. *)

Inductive ends :=
  | One (e : sty * point)
  | Both (e1 e2 : sty * point).

Notation tenv := (gmap chan ends).

Definition tenv_of (Σ : senv) : tenv := One <$> Σ.

(** Entries, one per end, keyed by the channel and a side bit (the
    second end of a [Both] is side [true]). Keys keep two equal ends of
    a channel apart: ready counts entries, not names. *)
Notation ekey := (chan * bool)%type.

Definition tenv_entry (Θ : tenv) (k : ekey) : option (sty * point) :=
  match Θ !! k.1, k.2 with
  | Some (One e), false => Some e
  | Some (Both e _), false => Some e
  | Some (Both _ e), true => Some e
  | _, _ => None
  end.

(** The point of the entry c : S@x, x. *)
Definition entry_head (k : ekey) (e : sty * point) : point := e.2.

(** The heads of an entry are partner points: heads(c : S@x) = {x̄}. *)
Definition ends_heads (c : chan) (o : ends) : gset point :=
  match o with
  | One e => {[pt_dual e.2]}
  | Both e1 e2 => {[pt_dual e1.2; pt_dual e2.2]}
  end.

Definition tenv_heads (Θ : tenv) : gset point :=
  map_fold (λ c o X, ends_heads c o ∪ X) ∅ Θ.

(** Θ = Θ1, c : e. *)
Definition tenv_ext (Θ1 : tenv) (c : chan) (e : sty * point) (Θ : tenv)
    : Prop :=
  (Θ1 !! c = None ∧ Θ = <[c := One e]> Θ1) ∨
  (∃ e', Θ1 !! c = Some (One e') ∧
     (Θ = <[c := Both e e']> Θ1 ∨ Θ = <[c := Both e' e]> Θ1)).

(** The term-level [senv_hd]: Θ = Θ1, c : S@x with S unfolding to u. *)
Definition tenv_hd (Θ : tenv) (c : chan) (u : sty) (k : point) (Θ1 : tenv)
    : Prop :=
  ∃ s, tenv_ext Θ1 c (s, k) Θ ∧ unfoldS s = u.

(** Θ = Θ1, Θ2: pointwise, and only defined where the overlap is one
    end on each side. *)
Inductive ends_join : option ends → option ends → option ends → Prop :=
  | ends_join_none : ends_join None None None
  | ends_join_l o : ends_join (Some o) None (Some o)
  | ends_join_r o : ends_join None (Some o) (Some o)
  | ends_join_both e1 e2 :
      ends_join (Some (One e1)) (Some (One e2)) (Some (Both e1 e2))
  | ends_join_both' e1 e2 :
      ends_join (Some (One e1)) (Some (One e2)) (Some (Both e2 e1)).

Definition tenv_join (Θ Θ1 Θ2 : tenv) : Prop :=
  ∀ c, ends_join (Θ1 !! c) (Θ2 !! c) (Θ !! c).

Lemma tenv_join_dom Θ Θ1 Θ2 :
  tenv_join Θ Θ1 Θ2 → dom Θ = dom Θ1 ∪ dom Θ2.
Proof.
  intros H. apply set_eq. intros c. rewrite elem_of_union, !elem_of_dom.
  pose proof (H c) as Hc.
  destruct (Θ1 !! c), (Θ2 !! c), (Θ !! c); inversion Hc;
    split; intros; try (by left); try (by right); try done;
    destruct_or?; by destruct select (is_Some None).
Qed.

Lemma tenv_join_empty Θ : tenv_join Θ ∅ ∅ → Θ = ∅.
Proof.
  intros H. apply map_empty. intros c. specialize (H c).
  rewrite !lookup_empty in H. by inversion H.
Qed.

(** The root name of a point: ι[i] belongs to the name of ι
    (relation/Worlds.v uses it for the support of a world). *)
Fixpoint pn_root (p : pname) : pname :=
  match p with
  | NPayload q _ _ => pn_root q
  | _ => p
  end.

Definition pt_root (x : point) : pname := pn_root (pt_name x).

(** ** Constraints of a fresh point (sharp edges 93, 97)

    A constraint C of one variable ι (the variable 0) whose every fact
    relates a point of the fresh channel to an outer point. A point of
    the fresh channel has the root ι, so it is ι+k, (ι+b)[i]+k and so on.
    [fresh_lo C u p] is the fact u ≺ p with p on the fresh channel,
    [fresh_hi C q v] the fact q ≺ v. [fresh_outer C u] reads an outer
    point in the context of the rule. C may be infinite. [ple p q]: p
    and q have one name and the offset of p is at most that of q. *)

Definition fresh_lo (C : bcs) (u p : point) : Prop :=
  bc_facts C (FLt u p) ∧ fact_scoped (S (length (bc_env C))) (FLt u p) ∧
  pt_root p = NVar 0 ∧ pt_root u ≠ NVar 0.

Definition fresh_hi (C : bcs) (q v : point) : Prop :=
  bc_facts C (FLt q v) ∧ fact_scoped (S (length (bc_env C))) (FLt q v) ∧
  pt_root q = NVar 0 ∧ pt_root v ≠ NVar 0.

Definition fresh_lt (C : bcs) : Prop :=
  ∀ f, bc_facts C f → fact_scoped (S (length (bc_env C))) f →
    (∃ u p, f = FLt u p ∧ fresh_lo C u p) ∨ (∃ q v, f = FLt q v ∧ fresh_hi C q v).

Definition fresh_outer (C : bcs) (u : point) : point := pt_inst (plist (pvar 0 :: bc_env C)) u.

(** ** Program order

    x ≺ x+1, closed under transitivity. It holds in every world, and a
    size that rises along successors makes it irreflexive. *)
Inductive ppo : point → point → Prop :=
  | ppo_po x : ppo x (pt_shift 1 x)
  | ppo_dpo x : ppo x (pt_shift 1 (pt_dual x))     (* x ≺ x̄+1, end points *)
  | ppo_trans x y z : ppo x y → ppo y z → ppo x z.

Fixpoint pn_size (p : pname) : nat :=
  match p with
  | NConst _ | NVar _ => 0
  | NPayload q b _ => pn_size q + b + 1
  end.

Definition pt_size (x : point) : nat := pn_size (pt_name x) + pt_off x.

Lemma ppo_size x y : ppo x y → pt_size x < pt_size y.
Proof.
  unfold pt_size. induction 1; simpl; [lia|lia|lia].
Qed.

Lemma ppo_irrefl x : ¬ ppo x x.
Proof. intros H%ppo_size. lia. Qed.

Lemma ppo_root x y : ppo x y → pt_root x = pt_root y.
Proof. induction 1; [done|done|congruence]. Qed.

Lemma ppo_same x y : pt_name x = pt_name y → pt_off x < pt_off y → ppo x y.
Proof.
  intros Hn Ho. destruct x as [p c a], y as [q c' b]; simpl in *. subst q.
  assert (∀ d a0 k, ppo (MkPt p d a0) (MkPt p d (a0 + S k))) as Hsame.
  { intros d a0 k. induction k as [|k IH].
    - exact (ppo_po (MkPt p d a0)).
    - eapply ppo_trans; [exact IH|].
      replace (a0 + S (S k)) with (a0 + S k + 1) by lia. exact (ppo_po (MkPt p d (a0 + S k))). }
  destruct (decide (c = c')) as [<-|Hc].
  - replace b with (a + S (b - a - 1)) by lia. apply Hsame.
  - assert (c' = negb c) as -> by (destruct c, c'; done).
    assert (ppo (MkPt p c a) (MkPt p (negb c) (a + 1))) as H1 by exact (ppo_dpo (MkPt p c a)).
    destruct (decide (b = a + 1)) as [->|Hb]; [done|].
    eapply ppo_trans; [exact H1|]. replace b with (a + 1 + S (b - a - 2)) by lia. apply Hsame.
Qed.

(** A map on points that commutes with successor preserves program
    order. *)
Lemma ppo_map (f : point → point) x y :
  (∀ z, f (pt_shift 1 z) = pt_shift 1 (f z)) →
  (∀ z, f (pt_dual z) = pt_dual (f z)) →
  ppo x y → ppo (f x) (f y).
Proof.
  intros Hs Hd. induction 1 as [z|z|];
    [rewrite Hs; apply ppo_po|rewrite Hs, Hd; apply ppo_dpo|by eapply ppo_trans].
Qed.

(** p at or before v in program order. *)
Definition ple (p v : point) : Prop := p = v ∨ ppo p v.

Lemma ple_same p v : pt_name p = pt_name v → pt_pol p = pt_pol v → pt_off p ≤ pt_off v → ple p v.
Proof.
  intros Hn Hp Ho. destruct (decide (pt_off p = pt_off v)) as [E|E].
  - left. destruct p, v. simpl in *. by subst.
  - right. apply ppo_same; [done|lia].
Qed.

(** ** The alias of a fresh point (sharp edges 104)

    [fresh_eq C w] is the fact ι ≡ w of C, with w an outer point. C is
    of the allowed form ([fresh_ok]) when its facts are ≺ facts of the
    form above ([fresh_lt]), or when they are such facts and one alias
    ι ≡ w. Which of the two cases holds is part of the evidence, so the
    semantic proof can build its world by cases without excluded
    middle. [fresh_at C w p] reads a point p of the fresh channel with
    the alias in place of ι, so ι+k becomes w+k and ι[i] becomes w[i].

    [fresh_between plt C] is the condition on the context. Without an
    alias it is the betweenness of sharp edges 94. With the alias
    ι ≡ w, the point ι has every fact of w, and a fresh extension adds
    no fact between known points. So every ≺ fact of C must already hold
    of w, that is u ≺ p[w/ι] for every u ≺ p and q[w/ι] ≺ v for every
    q ≺ v of C. That condition is necessary in every world that holds
    the alias, and it implies the betweenness of sharp edges 94. For
    C = {ι ≡ w} it is empty, and w known is all that new asks. *)

Definition fresh_eq (C : bcs) (w : point) : Prop :=
  bc_facts C (FEq (pvar 0) w) ∧ pn_vb (S (length (bc_env C))) (pt_name w) ∧ pt_root w ≠ NVar 0.

Definition fresh_ok (C : bcs) : Prop :=
  fresh_lt C ∨
  ∃ w, fresh_eq C w ∧
    ∀ f, bc_facts C f → fact_scoped (S (length (bc_env C))) f →
      (∃ u p, f = FLt u p ∧ fresh_lo C u p) ∨ (∃ q v, f = FLt q v ∧ fresh_hi C q v) ∨
      f = FEq (pvar 0) w.

Definition fresh_at (C : bcs) (w p : point) : point := pt_inst (λ _, fresh_outer C w) p.

Definition fresh_between (plt : point → point → Prop) (C : bcs) : Prop :=
  (fresh_lt C → ∀ u p q v, fresh_lo C u p → fresh_hi C q v → ple p q →
     plt (fresh_outer C u) (fresh_outer C v)) ∧
  (∀ w u p, fresh_eq C w → fresh_lo C u p → plt (fresh_outer C u) (fresh_at C w p)) ∧
  (∀ w q v, fresh_eq C w → fresh_hi C q v → plt (fresh_at C w q) (fresh_outer C v)).

(** The form of C reads only its facts and the length of its
    environment, so renaming and instantiating the outer points keeps it. *)
Section fresh_shape.
  Context (C C' : bcs) (Hf : bc_facts C = bc_facts C') (Hl : length (bc_env C) = length (bc_env C')).

  Lemma fresh_lo_shape u p : fresh_lo C u p ↔ fresh_lo C' u p.
  Proof. unfold fresh_lo. by rewrite Hf, Hl. Qed.

  Lemma fresh_hi_shape q v : fresh_hi C q v ↔ fresh_hi C' q v.
  Proof. unfold fresh_hi. by rewrite Hf, Hl. Qed.

  Lemma fresh_eq_shape w : fresh_eq C w ↔ fresh_eq C' w.
  Proof. unfold fresh_eq. by rewrite Hf, Hl. Qed.

  Lemma fresh_lt_shape : fresh_lt C → fresh_lt C'.
  Proof.
    intros H f Hf' Hs. rewrite <-Hf in Hf'. rewrite <-Hl in Hs.
    destruct (H f Hf' Hs) as [(u & p & -> & Hu)|(q & v & -> & Hv)].
    - left. exists u, p. split; [done|]. by apply fresh_lo_shape.
    - right. exists q, v. split; [done|]. by apply fresh_hi_shape.
  Qed.

  Lemma fresh_ok_shape : fresh_ok C → fresh_ok C'.
  Proof.
    intros [H|(w & Hw & H)]; [left; by apply fresh_lt_shape|right].
    exists w. split; [by apply fresh_eq_shape|]. intros f Hf' Hs. rewrite <-Hf in Hf'. rewrite <-Hl in Hs.
    destruct (H f Hf' Hs) as [(u & p & -> & Hu)|[(q & v & -> & Hv)| ->]].
    - left. exists u, p. split; [done|]. by apply fresh_lo_shape.
    - right; left. exists q, v. split; [done|]. by apply fresh_hi_shape.
    - by right; right.
  Qed.
End fresh_shape.

Lemma fresh_lt_no_eq C w : fresh_lt C → ¬ fresh_eq C w.
Proof.
  intros H (Hf & Hs & _).
  destruct (H _ Hf) as [(? & ? & E & _)|(? & ? & E & _)]; [split; [cbn; lia|done]|discriminate|discriminate].
Qed.

(** Without an alias, [fresh_between] is the betweenness of sharp
    edges 94. *)
Lemma fresh_between_lt (plt : point → point → Prop) C :
  fresh_lt C →
  (∀ u p q v, fresh_lo C u p → fresh_hi C q v → ple p q → plt (fresh_outer C u) (fresh_outer C v)) →
  fresh_between plt C.
Proof.
  intros HC Hbt. split_and!; [done|..]; intros w ? ? Hw; exfalso; by apply (fresh_lt_no_eq C w).
Qed.

Lemma fresh_between_mono (plt plt' : point → point → Prop) C :
  (∀ x y, plt x y → plt' x y) → fresh_between plt C → fresh_between plt' C.
Proof. intros H (H1 & H2 & H3). split_and!; eauto. Qed.

(** ** The closure of a set of facts

    [geq E] is the least congruence for successor and x ↦ x[i] that
    contains E, and [glt E L] the least transitive relation that
    contains L and program order and is closed under [geq E]. They are
    the fact theory read as a closure. relation/Worlds.v builds the
    world [wgen] from them. *)

Inductive geq (E : point → point → Prop) : point → point → Prop :=
  | geq_base x y : E x y → geq E x y
  | geq_refl x : geq E x x
  | geq_sym x y : geq E x y → geq E y x
  | geq_trans x y z : geq E x y → geq E y z → geq E x z
  | geq_shift x y : geq E x y → geq E (pt_shift 1 x) (pt_shift 1 y)
  | geq_payload x y i : geq E x y → geq E (pt_payload x i) (pt_payload y i)
  | geq_dual x y : geq E x y → geq E (pt_dual x) (pt_dual y).

Inductive glt (E L : point → point → Prop) : point → point → Prop :=
  | glt_base x y : L x y → glt E L x y
  | glt_po x : glt E L x (pt_shift 1 x)
  | glt_eq x x' y y' : geq E x x' → glt E L x' y' → geq E y' y → glt E L x y
  | glt_trans x y z : glt E L x y → glt E L y z → glt E L x z
  | glt_dpo x : glt E L x (pt_shift 1 (pt_dual x)).

(** ** Creation constraints (static-system.md §5, sharp edges 105)

    The constraint C of [new] is a box constraint of one variable ι, the
    variable 0. Its facts relate points of ι to each other and to outer
    points, by ≺ and by ≡, finitely or infinitely many. [cc_up R] reads
    the facts of the context Γ under the binder of ι, so the outer points
    shift past it. [cc_eq] and [cc_lt] add the facts of C, which is
    Γ + C. The judgment Γ ⊢ … is the closure [geq], [glt].

    [cc_ok] asks two things. Acyclic: every cycle of Γ + C comes from a
    cycle of Γ, so Γ + C ⊬ p ≺ p whenever Γ is acyclic. Conservative:
    Γ + C derives a fact between two points without root ι only when Γ
    derives it. The semantic proof extends a world by the facts of C at
    the fresh name, and conservativity is what makes that a fresh
    extension ⊑ₒ (relation/Creation.v). *)

(** The definitions take the number n of fresh variables. [new] creates
    one (n = 1), and a program starts under a creation constraint C₀
    over its n top-level variables, read against the empty context
    (static/Fundamental.v, sharp edges 148). *)
Definition cc_up_at (n : nat) (R : point → point → Prop) : point → point → Prop :=
  λ x y, ∃ x0 y0, R x0 y0 ∧ x = pt_inst (λ a, pvar (a + n)) x0 ∧ y = pt_inst (λ a, pvar (a + n)) y0.

Definition cc_eq_at (n : nat) (peq : point → point → Prop) (C : bcs) : point → point → Prop :=
  λ x y, cc_up_at n peq x y ∨ bcs_open n C (FEq x y).

Definition cc_lt_at (n : nat) (plt : point → point → Prop) (C : bcs) : point → point → Prop :=
  λ x y, cc_up_at n plt x y ∨ bcs_open n C (FLt x y).

Definition cc_acyclic_at (n : nat) (peq plt : point → point → Prop) (C : bcs) : Prop :=
  ∀ p, glt (cc_eq_at n peq C) (cc_lt_at n plt C) p p →
    ∃ x, glt (cc_up_at n peq) (cc_up_at n plt) x x.

Definition cc_conservative_at (n : nat) (peq plt : point → point → Prop) (C : bcs) : Prop :=
  (∀ x y, ¬ pn_vb n (pt_name x) → ¬ pn_vb n (pt_name y) →
     geq (cc_eq_at n peq C) x y → geq (cc_up_at n peq) x y) ∧
  (∀ x y, ¬ pn_vb n (pt_name x) → ¬ pn_vb n (pt_name y) →
     glt (cc_eq_at n peq C) (cc_lt_at n plt C) x y → glt (cc_up_at n peq) (cc_up_at n plt) x y).

Definition cc_ok_at (n : nat) (peq plt : point → point → Prop) (C : bcs) : Prop :=
  cc_acyclic_at n peq plt C ∧ cc_conservative_at n peq plt C.

Notation cc_up := (cc_up_at 1).
Notation cc_eq := (cc_eq_at 1).
Notation cc_lt := (cc_lt_at 1).
Notation cc_acyclic := (cc_acyclic_at 1).

Definition cc_conservative (peq plt : point → point → Prop) (C : bcs) : Prop :=
  (∀ x y, pt_root x ≠ NVar 0 → pt_root y ≠ NVar 0 →
     geq (cc_eq peq C) x y → geq (cc_up peq) x y) ∧
  (∀ x y, pt_root x ≠ NVar 0 → pt_root y ≠ NVar 0 →
     glt (cc_eq peq C) (cc_lt plt C) x y → glt (cc_up peq) (cc_up plt) x y).

Definition cc_ok (peq plt : point → point → Prop) (C : bcs) : Prop :=
  cc_acyclic peq plt C ∧ cc_conservative peq plt C.

(** The root of a point is variable 0 exactly when its name lies below 1. *)
Lemma pn_vb_1 p : pn_vb 1 p ↔ pn_root p = NVar 0.
Proof.
  induction p as [a|a|q IH o i]; simpl; [split; [done|discriminate]| |done].
  split; [intros ?; f_equal; lia|intros [= ->]; lia].
Qed.

(** A creation constraint over n fresh variables in a context whose
    order is [peq], [plt] and whose known points are [pk]: [cc_ok_at]
    and every outer point known. new asks it at n = 1
    ([creation_ok_1]), a program asks it for C₀ against the empty
    context (static/Fundamental.v). *)
Definition creation_ok (n : nat) (peq plt : point → point → Prop) (pk : point → Prop)
    (C : bcs) : Prop :=
  cc_ok_at n peq plt C ∧ Forall pk (bc_env C).

(** [cc_ok] is the case of one fresh variable. *)
Lemma cc_ok_at_1 peq plt C : cc_ok_at 1 peq plt C ↔ cc_ok peq plt C.
Proof.
  assert (∀ x, ¬ pn_vb 1 (pt_name x) ↔ pt_root x ≠ NVar 0) as E.
  { intros x. unfold pt_root. rewrite pn_vb_1. done. }
  unfold cc_ok_at, cc_ok, cc_conservative_at, cc_conservative.
  split; intros (Ha & He & Hl); (split; [done|split]); intros x y Hx Hy;
    [apply He|apply Hl|apply He|apply Hl]; by apply E.
Qed.

Lemma creation_ok_1 peq plt pk C :
  creation_ok 1 peq plt pk C ↔ cc_ok peq plt C ∧ Forall pk (bc_env C).
Proof. unfold creation_ok. by rewrite cc_ok_at_1. Qed.

(** T[ss/αs]: the session variable i goes to the i-th session type of a
    list, the variables beyond it shift down (K6). *)
Definition slist (ss : list sty) : nat → sty :=
  λ a, match ss !! a with Some s => s | None => SVar (a - length ss) end.

Lemma sinst_slist_nil T : sinst_ty (slist []) T = T.
Proof. apply sinst_id_mut. intros a. unfold slist. simpl. f_equal. lia. Qed.

(** The branch a selection or a branch label picks: S₁ for false. *)
Definition sbranch (b : bool) (S1 S2 : sty) : sty := if b then S2 else S1.

Lemma sbranch_map (f : sty → sty) b S1 S2 : f (sbranch b S1 S2) = sbranch b (f S1) (f S2).
Proof. by destruct b. Qed.

(** ** Constants as constrained type-indexed schemes (sharp edges 147)

    An instance of a constant's signature is a type, a constraint and a
    list of points that must be known ([konst_sig]). The constraint is a
    set of point facts that the meta level computes from the type, in
    the language of box constraints (≺ and ≡ only). E-Const proves it
    from the fact context, exactly as force proves its box's constraint
    at the instance. No constant reads the order in its signature. *)

(** Every fact of G holds, ≺ in [lt] and ≡ in [eq]. *)
Definition facts_hold (eq lt : point → point → Prop) (G : fact → Prop) : Prop :=
  ∀ g, G g → fact_holds eq lt g.

Lemma facts_hold_mono (eq eq' lt lt' : point → point → Prop) G :
  (∀ x y, eq x y → eq' x y) → (∀ x y, lt x y → lt' x y) →
  facts_hold eq lt G → facts_hold eq' lt' G.
Proof. intros He Hl H g Hg. specialize (H g Hg). destruct g; simpl in *; auto. Qed.

(** C[xs/ιs], the facts of C at the instance xs. *)
Definition bcs_at (C : bcs) (xs : list point) : fact → Prop :=
  λ g, ∃ g0, bcs_open (length xs) C g0 ∧ g = fact_map (pt_inst (plist xs)) g0.

Lemma facts_hold_bcs_at eq lt C xs : facts_hold eq lt (bcs_at C xs) ↔ bcs_hold eq lt C xs.
Proof.
  split.
  - intros H g Hg. apply H. by exists g.
  - intros H g (g0 & Hg0 & ->). by apply H.
Qed.

(** {x} ≺ H as a set of facts. *)
Definition below_all (x : point) (H : gset point) : fact → Prop :=
  λ g, ∃ h, h ∈ H ∧ g = FLt x h.

(** The signatures (spec §9; arrows without a bound leave it out).

    spawn  : (∗ ⊸^β_λ ∗) ⊸ ∗
    send   : (P[ι] ⊗ (!P;S)@ι) ⊸^ι S@(ι+1)       {ι ≺ h ∣ h ∈ heads(P[ι])}, no instance at the ⊥ flag
    recv   : (?P;S)@ι ⊸^ι P[ι] ⊗ S@(ι+1)
    close  : Close@ι ⊸^ι ∗
    selectᵢ : ⊕(S₁, S₂)@ι ⊸^ι Sᵢ@(ι[i])‾         {ι ≺ ι[i]}           (K11, end points)
    branch : &(S₁, S₂)@ι ⊸^ι S₁@ι[0] + S₂@ι[1]   {ι ≺ (ι[0])‾, ι ≺ (ι[1])‾}
    link   : S@ι ⊗ dual S@ι′ ⊸ ∗                  {ι ≡ (ι′)‾}   (never blocks, sharp edges 68)

    With end points the selecting end continues at the dual payload
    point (ι[i])‾ and the branching end at ι[i], so the two ends stay at
    dual points. This is the placement of the encoding of choice, where
    the brancher receives the end at ι[i] and the selector keeps its
    partner (examples/ChoiceEnc.v).
    force  : □(∀ιs αs. C. ∗ ⊸^u T) ⊸^{u[ιs′/ιs]} T[ιs′/ιs][ss/αs]
             C[ιs′/ιs], ιs′ known, every s ∈ ss hereditarily contractive   (52, 58, 63, 73) *)
Inductive konst_sig : konst → ty → (fact → Prop) → list point → Prop :=
  | KSSpawn ub lb :
      konst_sig KSpawn (TLolli None None (TLolli ub lb TUnit TUnit) TUnit) (λ _, False) []
  | KSSend m T S x :
      hbot T = false →
      konst_sig KSend
        (TLolli (Some x) None
           (TProd (payload_at m T x) (TSess (SSeq (SSnd m T) S) x))
           (TSess S (pt_shift 1 x)))
        (below_all x (heads (payload_at m T x))) []
  | KSRecv m T S x :
      konst_sig KRecv
        (TLolli (Some x) None
           (TSess (SSeq (SRcv m T) S) x)
           (TProd (payload_at m T x) (TSess S (pt_shift 1 x))))
        (λ _, False) []
  | KSClos x :
      konst_sig KClos (TLolli (Some x) None (TSess SEnd x) TUnit) (λ _, False) []
  | KSSel1 S1 S2 x :
      konst_sig KSel1
        (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S1 (pt_dual (pt_payload x 0))))
        (λ g, g = FLt x (pt_payload x 0)) []
  | KSSel2 S1 S2 x :
      konst_sig KSel2
        (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S2 (pt_dual (pt_payload x 1))))
        (λ g, g = FLt x (pt_payload x 1)) []
  | KSBra S1 S2 x :
      konst_sig KBra
        (TLolli (Some x) None (TSess (SWith S1 S2) x)
           (TSum (TSess S1 (pt_payload x 0)) (TSess S2 (pt_payload x 1))))
        (λ g, g = FLt x (pt_dual (pt_payload x 0)) ∨ g = FLt x (pt_dual (pt_payload x 1))) []
  | KSLink S x x' :
      konst_sig KLink
        (TLolli None None (TProd (TSess S x) (TSess (dual S) x')) TUnit)
        (λ g, g = FEq x (pt_dual x')) []
  | KSForce n k C ub T xs ss :
      length xs = n → length ss = k → Forall hcontractive ss →
      konst_sig KForce
        (TLolli (pt_inst (plist xs) <$> ub) None (TBox n k C (TLolli ub None TUnit T))
           (sinst_ty (slist ss) (ty_inst xs T)))
        (bcs_at C xs) xs.

(** E-Const reads a constant at an instance whose constraint holds and
    whose points are known. new is the one constant outside the
    schemes. It introduces a fresh point and no witness, so its premise
    is that C is a creation constraint ([cc_ok]) over known outer
    points (97, 103, 105):

    new    : ∗ ⊸ ∃^⊥ι. C. S@ι ⊗ dual S@ῑ

    The order is given as two relations, the world G generates for
    typing and a world W for the logical relation. [pk] says which
    points the order knows. force asks its instance known (sharp edges
    65), and new its outer points, so that the world of a run can state
    the facts of C about them (sharp edges 49, 105). *)
Inductive konst_ty (peq plt : point → point → Prop) (pk : point → Prop)
    : konst → ty → Prop :=
  | KTSig k T G xs :
      konst_sig k T G xs → facts_hold peq plt G → Forall pk xs →
      konst_ty peq plt pk k T
  | KTNewEx S C :
      cc_ok peq plt C → Forall pk (bc_env C) →
      konst_ty peq plt pk KNew
        (TLolli None None TUnit
           (TEx LBot 1 C (TProd (TSess S (pvar 0)) (TSess (dual S) (pt_dual (pvar 0)))))).

(** The instances one constant at a time. *)
Section konst_intro.
  Context (peq plt : point → point → Prop) (pk : point → Prop).

  Lemma KTSpawn ub lb :
    konst_ty peq plt pk KSpawn (TLolli None None (TLolli ub lb TUnit TUnit) TUnit).
  Proof. eapply KTSig; [constructor|by intros ?|constructor]. Qed.

  Lemma KTSend m T S x :
    (if hbot T then False else ∀ h, h ∈ heads (payload_at m T x) → plt x h) →
    konst_ty peq plt pk KSend
      (TLolli (Some x) None
         (TProd (payload_at m T x) (TSess (SSeq (SSnd m T) S) x))
         (TSess S (pt_shift 1 x))).
  Proof.
    intros H. destruct (hbot T) eqn:Hb; [done|].
    eapply KTSig; [by constructor| |constructor]. intros g (h & Hh & ->). by apply H.
  Qed.

  Lemma KTRecv m T S x :
    konst_ty peq plt pk KRecv
      (TLolli (Some x) None
         (TSess (SSeq (SRcv m T) S) x)
         (TProd (payload_at m T x) (TSess S (pt_shift 1 x)))).
  Proof. eapply KTSig; [constructor|by intros ?|constructor]. Qed.

  Lemma KTClos x : konst_ty peq plt pk KClos (TLolli (Some x) None (TSess SEnd x) TUnit).
  Proof. eapply KTSig; [constructor|by intros ?|constructor]. Qed.

  Lemma KTSel1 S1 S2 x :
    plt x (pt_payload x 0) →
    konst_ty peq plt pk KSel1
      (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S1 (pt_dual (pt_payload x 0)))).
  Proof. intros H. eapply KTSig; [constructor| |constructor]. by intros g ->. Qed.

  Lemma KTSel2 S1 S2 x :
    plt x (pt_payload x 1) →
    konst_ty peq plt pk KSel2
      (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S2 (pt_dual (pt_payload x 1)))).
  Proof. intros H. eapply KTSig; [constructor| |constructor]. by intros g ->. Qed.

  Lemma KTBra S1 S2 x :
    plt x (pt_dual (pt_payload x 0)) → plt x (pt_dual (pt_payload x 1)) →
    konst_ty peq plt pk KBra
      (TLolli (Some x) None (TSess (SWith S1 S2) x)
         (TSum (TSess S1 (pt_payload x 0)) (TSess S2 (pt_payload x 1)))).
  Proof. intros H0 H1. eapply KTSig; [constructor| |constructor]. by intros g [->| ->]. Qed.

  Lemma KTLink S x x' :
    peq x (pt_dual x') →
    konst_ty peq plt pk KLink
      (TLolli None None (TProd (TSess S x) (TSess (dual S) x')) TUnit).
  Proof. intros H. eapply KTSig; [constructor| |constructor]. by intros g ->. Qed.

  Lemma KTForce n k C ub T xs ss :
    length xs = n → bcs_hold peq plt C xs → Forall pk xs →
    length ss = k → Forall hcontractive ss →
    konst_ty peq plt pk KForce
      (TLolli (pt_inst (plist xs) <$> ub) None (TBox n k C (TLolli ub None TUnit T))
         (sinst_ty (slist ss) (ty_inst xs T))).
  Proof.
    intros Hn HC HK Hk Hs. eapply KTSig; [by constructor|by apply facts_hold_bcs_at|done].
  Qed.
End konst_intro.

(** Case analysis on a typed constant, one case per constant. *)
Lemma konst_ty_case (peq plt : point → point → Prop) (pk : point → Prop)
    (P : konst → ty → Prop) :
  (∀ ub lb, P KSpawn (TLolli None None (TLolli ub lb TUnit TUnit) TUnit)) →
  (∀ m T S x, (if hbot T then False else ∀ h, h ∈ heads (payload_at m T x) → plt x h) →
     P KSend (TLolli (Some x) None
                (TProd (payload_at m T x) (TSess (SSeq (SSnd m T) S) x))
                (TSess S (pt_shift 1 x)))) →
  (∀ m T S x, P KRecv (TLolli (Some x) None
                         (TSess (SSeq (SRcv m T) S) x)
                         (TProd (payload_at m T x) (TSess S (pt_shift 1 x))))) →
  (∀ x, P KClos (TLolli (Some x) None (TSess SEnd x) TUnit)) →
  (∀ S1 S2 x, plt x (pt_payload x 0) →
     P KSel1 (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S1 (pt_dual (pt_payload x 0))))) →
  (∀ S1 S2 x, plt x (pt_payload x 1) →
     P KSel2 (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S2 (pt_dual (pt_payload x 1))))) →
  (∀ S1 S2 x, plt x (pt_dual (pt_payload x 0)) → plt x (pt_dual (pt_payload x 1)) →
     P KBra (TLolli (Some x) None (TSess (SWith S1 S2) x)
               (TSum (TSess S1 (pt_payload x 0)) (TSess S2 (pt_payload x 1))))) →
  (∀ S x x', peq x (pt_dual x') → P KLink (TLolli None None (TProd (TSess S x) (TSess (dual S) x')) TUnit)) →
  (∀ n k C ub T xs ss, length xs = n → bcs_hold peq plt C xs → Forall pk xs →
     length ss = k → Forall hcontractive ss →
     P KForce (TLolli (pt_inst (plist xs) <$> ub) None (TBox n k C (TLolli ub None TUnit T))
                 (sinst_ty (slist ss) (ty_inst xs T)))) →
  (∀ S C, cc_ok peq plt C → Forall pk (bc_env C) →
     P KNew (TLolli None None TUnit
               (TEx LBot 1 C (TProd (TSess S (pvar 0)) (TSess (dual S) (pt_dual (pvar 0))))))) →
  ∀ k T, konst_ty peq plt pk k T → P k T.
Proof.
  intros Hsp Hsd Hrv Hcl Hs1 Hs2 Hbr Hln Hfo Hnw k T [k' T' G xs Hsig HG HK|S C HC HK]; [|by apply Hnw].
  destruct Hsig as [| m T0 S x Hb| | | | | | |n kk C ub T0 xs ss Hn Hk Hs]; auto.
  - apply Hsd. rewrite Hb. intros h Hh. apply (HG (FLt x h)). by exists h.
  - apply Hs1. by apply (HG (FLt _ _)).
  - apply Hs2. by apply (HG (FLt _ _)).
  - apply Hbr; [apply (HG (FLt _ _)); by left|apply (HG (FLt _ _)); by right].
  - apply Hln. by apply (HG (FEq _ _)).
  - eapply Hfo; [done|by apply facts_hold_bcs_at|done|done|done].
Qed.
