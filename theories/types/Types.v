(** * Types, session types, duality, environments (§2.2, Fig. 5 top)

    T, U ::= ∗ | T ⊸^β_λ U | T ⊗ U | T ⊕ U | S@ι | □T | ∀ιs. C. T | ∃^ℓ ιs. C. T
    S    ::= ?P.S | !P.S | Close | µα.S | α | α̅      P ::= ∃ιs. T
    β    ::= ι | ⊥        λ ::= ι | ⊤
    ι    ::= (p, b)       p ::= a | point variable | p[b][i]   (no channels) *)

From stdpp Require Import base strings gmap countable.
From LRGV Require Export lang.Syntax.

(** ** Points

    One sort of names (decision N). A point (p, b) is a name p with an
    offset b. A name is a point constant, a point variable (de Bruijn,
    bound by ∀ under □ or by ∃ in a payload), or the slot p[b][i], "the
    i-th point carried at (p, b)". Worlds and environments use ground
    points (constants and their slots), static types also use
    variables. No point mentions a channel, so renaming channels
    changes no type and no world.

    A slot writes the name and offset of its base unpacked, so that
    names are not mutual with points. *)

Inductive pname :=
  | NConst (a : nat)
  | NVar (a : nat)
  | NSlot (p : pname) (b : nat) (i : nat).   (* (p, b)[i] *)

Record point := Pt { pt_name : pname; pt_off : nat }.

Global Instance pname_eq_dec : EqDecision pname.
Proof. solve_decision. Defined.

Global Instance pname_countable : Countable pname.
Proof.
  set (enc := fix go p : gen_tree nat :=
    match p with
    | NConst a => GenNode 1 [GenLeaf a]
    | NVar a => GenLeaf a
    | NSlot p b i => GenNode 0 [go p; GenLeaf b; GenLeaf i]
    end).
  set (dec := fix go t : pname :=
    match t with
    | GenNode 1 [GenLeaf a] => NConst a
    | GenLeaf a => NVar a
    | GenNode 0 [t; GenLeaf b; GenLeaf i] => NSlot (go t) b i
    | _ => NVar 0
    end).
  apply (inj_countable' enc dec).
  intros p; induction p; simpl; congruence.
Qed.

Global Instance point_eq_dec : EqDecision point.
Proof. solve_decision. Defined.

Global Instance point_countable : Countable point.
Proof.
  apply (inj_countable' (λ x, (pt_name x, pt_off x)) (λ '(p, b), Pt p b)).
  by intros [].
Qed.

(** x + n, x[i], the variable a, and the constant a at offset 0. *)
Definition pt_shift (n : nat) (x : point) : point :=
  Pt (pt_name x) (pt_off x + n).
Definition pt_slot (x : point) (i : nat) : point :=
  Pt (NSlot (pt_name x) (pt_off x) i) 0.
Definition pvar (a : nat) : point := Pt (NVar a) 0.
Definition pconst (a : nat) : point := Pt (NConst a) 0.

(** Instantiation of point variables. A name denotes the point at
    offset 0; the offset of a point adds on top. *)
Fixpoint pn_inst (σ : nat → point) (p : pname) : point :=
  match p with
  | NConst a => Pt (NConst a) 0
  | NVar a => σ a
  | NSlot p b i => pt_slot (pt_shift b (pn_inst σ p)) i
  end.

Definition pt_inst (σ : nat → point) (x : point) : point :=
  pt_shift (pt_off x) (pn_inst σ (pt_name x)).

(** Lifting an instantiation under a binder of m point variables. *)
Definition pup (m : nat) (σ : nat → point) : nat → point :=
  λ a, if decide (a < m) then pvar a
       else pt_inst (λ a', pvar (a' + m)) (σ (a - m)).

(** The instantiation that sends the variable i to the i-th point of
    a list, and shifts the variables beyond it down. *)
Definition plist (xs : list point) : nat → point :=
  λ a, match xs !! a with Some x => x | None => pvar (a - length xs) end.

(** The slots x[0], …, x[m-1] of a point. *)
Definition slots (x : point) (m : nat) : list point :=
  (λ i, pt_slot x i) <$> seq 0 m.

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
  match p with NConst _ => False | NVar a => a < k | NSlot q _ _ => pn_vb k q end.

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

(** ** Types

    The arrow carries an upper point β ([None] = ⊥: the call never
    blocks) and a lower point λ ([None] = ⊤: the closure holds
    nothing). ∀ binds n point variables, and □ is a modality over any
    type (sharp edges 101). ∃ binds n, and a payload binds m. Session types are unannotated: the only points
    inside them are those of payloads, all bound by the payload's ∃, so
    point instantiation never enters a session type. *)

Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (ub lb : option point) (T U : ty)
                                   (* T ⊸^ub_lb U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSum (T U : ty)                (* T ⊕ U *)
  | TBoxM (T : ty)                 (* □T — unlimited (replicable)
                                      values. A box stands for its thunk,
                                      and the thunk lies in T. The boxes
                                      of the static system have type
                                      □(∀ιs. C. ∗ ⊸^u_⊤ U), so the upper
                                      point u lives on the arrow under
                                      the binder (sharp edges 52, 63,
                                      101) *)

  | TSess (S : sty) (x : point)   (* S@x *)
  | TEx (lb : option point) (n : nat) (C : bcs) (T : ty)
                                   (* ∃^ℓ ι₀ … ιₙ₋₁. C. T — existential
                                      points (sharp edges 97): the value
                                      lies in T at some known instance
                                      meeting C, and its channels lie at
                                      or above the lower point ℓ ([None]
                                      = ⊤: it holds nothing) *)
  | TAll (n : nat) (C : bcs) (T : ty)
                                   (* ∀ι₀ … ιₙ₋₁. C. T — the value lies
                                      in T at every known instance of
                                      the ιs that meets C, in every later
                                      world, and holds no channel. The
                                      constraint C is a set of facts
                                      x ≺ y and x ≡ y over the ιs and
                                      outer points (sharp edges 65,
                                      101) *)
with sty :=
  | SRcv (m : nat) (T : ty) (S : sty)
                                   (* ?(∃ι₀ … ιₘ₋₁. T).S *)
  | SSnd (m : nat) (T : ty) (S : sty)
                                   (* !(∃ι₀ … ιₘ₋₁. T).S *)
  | SEnd                           (* Close *)
  | SMu (S : sty)                  (* µα.S — binds one session variable *)
  | SVar (a : nat)                 (* α — de Bruijn *)
  | SVarD (a : nat).               (* α̅ — the dual of what α stands for;
                                      never written in source types, it
                                      enters only through [dual] *)

(** The boxes of the static system, □(∀ιs. C. T). *)
Notation TBox n C T := (TBoxM (TAll n C T)).

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
  Proof. destruct x as [p o]. unfold pt_shift. simpl. f_equal. lia. Qed.

  Local Lemma bpt_inst_pvar σ a : pt_inst σ (pvar a) = σ a.
  Proof. unfold pt_inst, pvar. simpl. apply bpt_shift_0. Qed.

  Local Lemma bpt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
  Proof.
    destruct x as [p o]. unfold pt_inst, pt_shift. simpl.
    destruct (pn_inst σ p). simpl. f_equal. lia.
  Qed.

  Local Lemma bpn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
  Proof.
    induction p as [a|a|p IH b i]; simpl; [done|done|].
    assert (∀ x, pt_inst τ (pt_slot x i) = pt_slot (pt_inst τ x) i) as Hs
      by (intros [q o]; done).
    by rewrite Hs, bpt_inst_shift, IH.
  Qed.

  Local Lemma bpt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
  Proof. unfold pt_inst at 2 3. by rewrite bpt_inst_shift, bpn_inst_comp. Qed.

  Local Lemma bpt_inst_ext_vb k σ τ x :
    pn_vb k (pt_name x) → (∀ a, a < k → σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros Hx H. destruct x as [p o]. unfold pt_inst. simpl in *. f_equal.
    induction p as [a|a|p IH b i]; simpl in *; [done|by apply H|by rewrite IH].
  Qed.

  Local Lemma bpt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros H. destruct x as [p o]. unfold pt_inst. simpl. f_equal.
    induction p as [a|a|p IH b i]; simpl; [done|apply H|by rewrite IH].
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
  | TBoxM T1 => TBoxM (pinst_ty σ T1)
  | TAll n C T1 =>
      TAll n (bcs_inst σ C) (pinst_ty (pup n σ) T1)
  | TSess s x => TSess s (pt_inst σ x)
  | TEx lb n C T1 =>
      TEx (pt_inst σ <$> lb) n (bcs_inst σ C) (pinst_ty (pup n σ) T1)
  end.

(** T[xs/ιs]: instantiate the ∀ of a □ (or the ∃ of a payload) with a
    list of points. *)
Definition ty_inst (xs : list point) (T : ty) : ty := pinst_ty (plist xs) T.

(** The payload ∃ι₀ … ιₘ₋₁. T at the point x: P[x] = T[x[i]/ιᵢ]. *)
Definition payload_at (m : nat) (T : ty) (x : point) : ty :=
  ty_inst (slots x m) T.

(** Composition and identity of point instantiation on types. The
    relation instantiates the ∃ of [TEx] by composing substitutions
    (relation/LogicalRelation.v, sharp edges 97). *)
Section tinst.
  Local Lemma tpt_shift_0 x : pt_shift 0 x = x.
  Proof. destruct x as [p o]. unfold pt_shift. simpl. f_equal. lia. Qed.

  Lemma tpt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
  Proof. unfold pt_inst, pvar. simpl. apply tpt_shift_0. Qed.

  Local Lemma tpt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
  Proof.
    destruct x as [p o]. unfold pt_inst, pt_shift. simpl.
    destruct (pn_inst σ p). simpl. f_equal. lia.
  Qed.

  Local Lemma tpn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
  Proof.
    induction p as [a|a|p IH b i]; simpl; [done|done|].
    assert (∀ x, pt_inst τ (pt_slot x i) = pt_slot (pt_inst τ x) i) as Hs
      by (intros [q o]; done).
    by rewrite Hs, tpt_inst_shift, IH.
  Qed.

  Lemma tpt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
  Proof. unfold pt_inst at 2 3. by rewrite tpt_inst_shift, tpn_inst_comp. Qed.

  Lemma tpt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
  Proof.
    intros H. destruct x as [p o]. unfold pt_inst. simpl. f_equal.
    induction p as [a|a|p IH b i]; simpl; [done|apply H|by rewrite IH].
  Qed.

  Lemma tpt_inst_pvar x : pt_inst pvar x = x.
  Proof.
    destruct x as [p o]. unfold pt_inst. simpl. f_equal.
    assert (pn_inst pvar p = Pt p 0) as ->; [|unfold pt_shift; simpl; f_equal; lia].
    induction p as [a|a|p IH b i]; simpl; [done|done|]. by rewrite IH.
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
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH0 | s x
                   | lb n C T1 IH | n C T1 IH]; intros σ τ H; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_ext
               |destruct lb; simpl; f_equal; auto using tpt_inst_ext|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; auto.
    - f_equal. by apply tpt_inst_ext.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_ext|by apply tbcs_ext|].
      apply IH. intros a. by apply tpup_ext.
    - f_equal; [by apply tbcs_ext|]. apply IH. intros a. by apply tpup_ext.
  Qed.

  Lemma tinst_comp T : ∀ τ σ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
  Proof.
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH0 | s x
                   | lb n C T1 IH | n C T1 IH]; intros τ σ; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_comp
               |destruct lb; simpl; f_equal; auto using tpt_inst_comp|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; auto.
    - f_equal. apply tpt_inst_comp.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_comp|apply tbcs_comp|].
      rewrite IH. apply tinst_ext. intros a. apply tpup_comp.
    - f_equal; [apply tbcs_comp|]. rewrite IH. apply tinst_ext. intros a. apply tpup_comp.
  Qed.

  Lemma tinst_pvar T : pinst_ty pvar T = T.
  Proof.
    induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH0 | s x
                   | lb n C T1 IH | n C T1 IH]; simpl.
    - done.
    - f_equal; [destruct ub; simpl; f_equal; auto using tpt_inst_pvar
               |destruct lb; simpl; f_equal; auto using tpt_inst_pvar|auto|auto].
    - f_equal; auto.
    - f_equal; auto.
    - f_equal; auto.
    - f_equal. apply tpt_inst_pvar.
    - f_equal; [destruct lb; simpl; f_equal; auto using tpt_inst_pvar|apply tbcs_pvar|].
      rewrite (tinst_ext _ _ pvar); [done|apply tpup_pvar].
    - f_equal; [apply tbcs_pvar|]. rewrite (tinst_ext _ _ pvar); [done|apply tpup_pvar].
  Qed.
End tinst.

(** Induction on types in which the body of an existential is available
    at every instance (sharp edges 97). The value relation reads an
    existential at the instance of its witness. *)
Fixpoint tsize (T : ty) : nat :=
  match T with
  | TUnit | TSess _ _ => 1
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U => S (tsize T1 + tsize U)
  | TBoxM T1 | TAll _ _ T1 | TEx _ _ _ T1 => S (tsize T1)
  end.

Lemma tsize_pinst T : ∀ σ, tsize (pinst_ty σ T) = tsize T.
Proof. induction T; intros σ; simpl; auto. Qed.

Lemma ty_ind_ex (P : ty → Prop) :
  P TUnit →
  (∀ ub lb T, P T → ∀ U, P U → P (TLolli ub lb T U)) →
  (∀ T, P T → ∀ U, P U → P (TProd T U)) →
  (∀ T, P T → ∀ U, P U → P (TSum T U)) →
  (∀ T, P T → P (TBoxM T)) →
  (∀ s x, P (TSess s x)) →
  (∀ lb n C T, (∀ σ, P (pinst_ty σ T)) → P (TEx lb n C T)) →
  (∀ n C T, (∀ σ, P (pinst_ty σ T)) → P (TAll n C T)) →
  ∀ T, P T.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  enough (∀ m T, tsize T < m → P T) as H by (intros T; apply (H (S (tsize T))); lia).
  induction m as [|m IH]; intros T HT; [lia|].
  destruct T; simpl in HT.
  - done.
  - apply H2; apply IH; lia.
  - apply H3; apply IH; lia.
  - apply H4; apply IH; lia.
  - apply H5. apply IH. lia.
  - apply H6.
  - apply H7. intros σ. apply IH. rewrite tsize_pinst. lia.
  - apply H8. intros σ. apply IH. rewrite tsize_pinst. lia.
Qed.

(** ** Heads

    The points at which a value of the type is next used:
    heads(S@ι) = {ι}, heads(T ⊸^β_λ U) = {λ} ∖ {⊤}, ∅ for ∗ and □. *)

Definition opt_heads (o : option point) : gset point :=
  match o with Some x => {[x]} | None => ∅ end.

Fixpoint heads (T : ty) : gset point :=
  match T with
  | TUnit | TBoxM _ | TAll _ _ _ => ∅
  | TLolli _ lb _ _ => opt_heads lb
  | TProd T1 U | TSum T1 U => heads T1 ∪ heads U
  | TSess _ x => {[x]}
  | TEx lb _ _ _ => opt_heads lb
  end.

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
  | TBoxM T1 => TBoxM (sren_ty r T1)
  | TAll n C T1 => TAll n C (sren_ty r T1)
  | TEx lb n C T1 => TEx lb n C (sren_ty r T1)
  | TSess s x => TSess (sren r s) x
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sren_ty r T) (sren r s')
  | SSnd m T s' => SSnd m (sren_ty r T) (sren r s')
  | SEnd => SEnd
  | SMu s' => SMu (sren (upren r) s')
  | SVar a => SVar (r a)
  | SVarD a => SVarD (r a)
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
  | TBoxM T1 => TBoxM (sflip_ty k T1)
  | TAll n C T1 => TAll n C (sflip_ty k T1)
  | TEx lb n C T1 => TEx lb n C (sflip_ty k T1)
  | TSess s x => TSess (sflip k s) x
  end
with sflip (k : nat) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sflip_ty k T) (sflip k s')
  | SSnd m T s' => SSnd m (sflip_ty k T) (sflip k s')
  | SEnd => SEnd
  | SMu s' => SMu (sflip (S k) s')
  | SVar a => if decide (a = k) then SVarD a else SVar a
  | SVarD a => if decide (a = k) then SVar a else SVarD a
  end.

(** ** Session duality: swaps the direction of communication.

    Polarized duality after Gay, Thiemann and Vasconcelos, "Duality of
    Session Types: The Final Cut". Payloads are left alone — ?T.S and
    !T.S carry the same T — and variables carry a polarity:

      dual α = α̅    dual α̅ = α    dual (µα.S) = µα. flip₀ (dual S)

    The flip at the binder makes tail occurrences ("continue as
    myself") come out as α again, while payload occurrences come out
    as α̅ and keep denoting the *original* protocol. The naive
    dual α = α is unsound here: for µα.!(α).α, unrolling then
    dualizing gives payload µα.!(α).α, dualizing then unrolling gives
    payload µα.?(α).α. With polarities the two orders agree —
    [dual_unfoldS] below, unconditionally. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv m T s' => SSnd m T (dual s')
  | SSnd m T s' => SRcv m T (dual s')
  | SEnd => SEnd
  | SMu s' => SMu (sflip 0 (dual s'))
  | SVar a => SVarD a
  | SVarD a => SVar a
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
  | TBoxM T1 => TBoxM (sinst_ty σ T1)
  | TAll n C T1 => TAll n C (sinst_ty σ T1)
  | TEx lb n C T1 => TEx lb n C (sinst_ty σ T1)
  | TSess s x => TSess (sinst σ s) x
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (sinst_ty σ T) (sinst σ s')
  | SSnd m T s' => SSnd m (sinst_ty σ T) (sinst σ s')
  | SEnd => SEnd
  | SMu s' => SMu (sinst (sty_up σ) s')
  | SVar a => σ a
  | SVarD a => dual (σ a)
  end.

(** One-step unrolling: µα.s ↦ s[µα.s/α]. *)
Definition unroll (s : sty) : sty := sinst (SMu s .: SVar) s.

(** ** Head normal form

    Under contractive definitions the leading µ's are finitely many,
    so unfolding until a communication constructor appears terminates.
    [unfoldS] is total: on a non-contractive type such as µα.α it
    simply stops, leaving a µ or a variable in head position, and the
    logical relation's clauses — which all match on the *unfolding* —
    are then unsatisfiable. Ill-formed types therefore need no
    well-formedness side condition; they just relate nothing. *)

Fixpoint mu_depth (s : sty) : nat :=
  match s with SMu s' => S (mu_depth s') | _ => 0 end.

Fixpoint unfoldN (k : nat) (s : sty) : sty :=
  match k with
  | 0 => s
  | S k' => match s with SMu s' => unfoldN k' (unroll s') | _ => s end
  end.

Definition unfoldS (s : sty) : sty := unfoldN (mu_depth s) s.

(** A type already in head normal form is its own unfolding. *)
Lemma unfoldS_hd u : mu_depth u = 0 → unfoldS u = u.
Proof. unfold unfoldS. by intros ->. Qed.

Lemma mu_depth_rcv m T s : mu_depth (SRcv m T s) = 0.
Proof. done. Qed.

Lemma mu_depth_snd m T s : mu_depth (SSnd m T s) = 0.
Proof. done. Qed.

(** ** Closedness of session variables *)

Fixpoint sclosed_ty (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U =>
      sclosed_ty k T1 ∧ sclosed_ty k U
  | TBoxM T1 | TAll _ _ T1 => sclosed_ty k T1
  | TEx _ _ _ T1 => sclosed_ty k T1
  | TSess s _ => sclosed k s
  end
with sclosed (k : nat) (s : sty) : Prop :=
  match s with
  | SRcv _ T s' | SSnd _ T s' => sclosed_ty k T ∧ sclosed k s'
  | SEnd => True
  | SMu s' => sclosed (S k) s'
  | SVar a | SVarD a => a < k
  end.

Lemma sinst_ext_mut :
  (∀ T σ σ', (∀ a, σ a = σ' a) → sinst_ty σ T = sinst_ty σ' T) ∧
  (∀ s σ σ', (∀ a, σ a = σ' a) → sinst σ s = sinst σ' s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  apply H. intros [|a]; simpl; [done|]. unfold compose. by rewrite H0.
Qed.

Definition sinst_ext := proj2 sinst_ext_mut.

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
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; auto; done);
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_comm := proj2 sflip_comm_mut.

Lemma sflip_dual s : ∀ j, sflip j (dual s) = dual (sflip j s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros j; simpl; f_equal;
    auto.
  - rewrite <-IH. apply sflip_comm. lia.
  - repeat (case_decide; simpl); congruence.
  - repeat (case_decide; simpl); congruence.
Qed.

Lemma sflip_mu_depth s : ∀ k, mu_depth (sflip k s) = mu_depth s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros k; simpl; auto;
    case_decide; done.
Qed.

Lemma dual_involutive s : dual (dual s) = s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; simpl; f_equal; auto.
  rewrite <-sflip_dual, sflip_sflip. exact IH.
Qed.

Lemma dual_mu_depth s : mu_depth (dual s) = mu_depth s.
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; simpl; auto.
  by rewrite sflip_mu_depth, IH.
Qed.

(** ** Flip versus renaming and substitution

    [sflip k ∘ sren r] pushes through as [sren r ∘ sflip j] when r
    maps exactly the preimage of k to k ([sflip_sren_iff_mut]) and
    vanishes when nothing maps to k ([sflip_sren_ne_mut]). *)

Lemma sflip_sren_iff_mut :
  (∀ T j k r, (∀ a, r a = k ↔ a = j) →
     sflip_ty k (sren_ty r T) = sren_ty r (sflip_ty j T)) ∧
  (∀ s j k r, (∀ a, r a = k ↔ a = j) →
     sflip k (sren r s) = sren r (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. intros [|a]; simpl; unfold compose.
    + split; intros Heq; exfalso; lia.
    + destruct (H0 a) as [Hf Hb]. split; intros Heq.
      * f_equal. apply Hf. lia.
      * f_equal. apply Hb. lia.
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
  - apply H. intros [|a]; simpl; [lia|]. unfold compose.
    specialize (H0 a). lia.
  - case_decide; [naive_solver|done].
  - case_decide; [naive_solver|done].
Qed.

Lemma dual_sren s : ∀ r, dual (sren r s) = sren r (dual s).
Proof.
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros r; simpl; f_equal;
    auto.
  rewrite IH. apply (proj2 sflip_sren_iff_mut).
  intros [|a]; simpl; unfold compose; split; intros; simplify_eq; done.
Qed.

(** [sflip k] slides through a substitution that is the identity at k
    and flip-invariant elsewhere — [sty_up]-lifted substitutions are. *)

Lemma sflip_sinst_mut :
  (∀ T k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip_ty k (sinst_ty σ T) = sinst_ty σ (sflip_ty k T)) ∧
  (∀ s k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip k (sinst σ s) = sinst σ (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H.
    + simpl. unfold compose. by rewrite H0.
    + intros [|a] Ha; simpl.
      * done.
      * unfold compose.
        rewrite (proj2 sflip_sren_iff_mut _ k) by (intros; lia).
        rewrite H1; [done|lia].
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
  induction s as [m T s IH|m T s IH| |s IH|a|a]; intros σ; simpl; f_equal;
    auto.
  - rewrite IH. apply (proj2 sflip_sinst_mut); [done|].
    intros [|a] Ha; simpl; [lia|]. unfold compose.
    apply (proj2 sflip_sren_ne_mut). intros; lia.
  - apply dual_involutive.
Qed.

(** Flipping the head variable of the term matches dualizing what the
    substitution feeds it. *)

Lemma sinst_sflip_dual_mut :
  (∀ T k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst_ty σ T = sinst_ty σ' (sflip_ty k T)) ∧
  (∀ s k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst σ s = sinst σ' (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H.
    + simpl. unfold compose. by rewrite H0, dual_sren.
    + intros [|a] Ha; simpl; [done|]. unfold compose.
      rewrite H1; [done|lia].
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

Lemma dual_unfoldN k : ∀ s, dual (unfoldN k s) = unfoldN k (dual s).
Proof.
  induction k as [|k IH]; intros s; simpl; [done|].
  destruct s as [m T s'|m T s'| |s'|a|a]; simpl; try done.
  by rewrite IH, dual_unroll.
Qed.

(** The property CONNECT needs: the two ends of a session unfold in
    lockstep — unconditionally, thanks to the polarized dual. *)
Lemma dual_unfoldS s : dual (unfoldS s) = unfoldS (dual s).
Proof. unfold unfoldS. rewrite dual_mu_depth. apply dual_unfoldN. Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V)
  | prim_box n C ub U : prim U → prim (TBox n C (TLolli ub None TUnit U)).

(** ** Unlimited types

    The types whose variables admit contraction and weakening. The
    structural rules of Fig. 4 ([lsplit_unl], [lwk_drop]) and the
    relevance conjunct of semantic typing are stated against this
    predicate rather than against a single modality, so that adding
    one is a matter of extending the match below. *)

Definition unlimited (T : ty) : Prop :=
  match T with TBoxM _ => True | _ => False end.

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

(** head(c : S@x) = x. *)
Definition entry_head (k : ekey) (e : sty * point) : point := e.2.

Definition ends_heads (c : chan) (o : ends) : gset point :=
  match o with
  | One e => {[e.2]}
  | Both e1 e2 => {[e1.2; e2.2]}
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

(** The root name of a point: a slot ι[i] belongs to the name of ι
    (relation/Worlds.v uses it for the support of a world). *)
Fixpoint pn_root (p : pname) : pname :=
  match p with
  | NSlot q _ _ => pn_root q
  | _ => p
  end.

Definition pt_root (x : point) : pname := pn_root (pt_name x).

(** ** Constraints of a fresh point (sharp edges 93, 97)

    A constraint C of one variable ι (the variable 0) whose every fact
    relates a point of the fresh channel to an outer point. A point of
    the fresh channel has the root ι, so it is ι+k, (ι+b).i+k and so on.
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

Definition fresh_ok (C : bcs) : Prop :=
  ∀ f, bc_facts C f → fact_scoped (S (length (bc_env C))) f →
    (∃ u p, f = FLt u p ∧ fresh_lo C u p) ∨ (∃ q v, f = FLt q v ∧ fresh_hi C q v).

Definition fresh_outer (C : bcs) (u : point) : point := pt_inst (plist (pvar 0 :: bc_env C)) u.

Definition ple (p v : point) : Prop := pt_name p = pt_name v ∧ pt_off p ≤ pt_off v.

(** ** Type-indexed families of type signatures for constants
    (§9)

    new    : ∗ ⊸^⊥_⊤ S@ι ⊗ dual S@ι
    new    : ∗ ⊸^⊥_⊤ ∃ι≽ℓ. C. S@ι ⊗ dual S@ι   C fresh, betweenness, ℓ ≺ ι in C (97)
    spawn  : (∗ ⊸^β_λ ∗) ⊸^⊥_⊤ ∗
    send   : (P[ι] ⊗ (!P.S)@ι) ⊸^ι_⊤ S@(ι+1)     {ι} ≺ heads(P[ι])
    recv   : (?P.S)@ι ⊸^ι_⊤ P[ι] ⊗ S@(ι+1)
    close  : Close@ι ⊸^ι_⊤ ∗
    link   : S@ι ⊗ dual S@ι′ ⊸^⊥_⊤ ∗       ι ≡ ι′   (never blocks, sharp edges 68)
    force  : □(∀ιs. C. ∗ ⊸^u_⊤ T) ⊸^{u[ιs′/ιs]}_⊤ T[ιs′/ιs]   C[ιs′/ιs]   (52, 58, 63)

    The side conditions on points are read in an order given as two
    relations: the world G generates for typing, a world W for the
    logical relation. Freshness of ι in [new] is a typing condition
    (static/). [pk] says which points the order knows: the point of
    [new] must be one, so that the created point can be aliased to it
    (sharp edges 49). force asks its instance known and every
    fact of the box's constraint at the instance (sharp edges 65). *)

Inductive konst_ty (peq plt : point → point → Prop) (pk : point → Prop)
    : konst → ty → Prop :=
  | KTNew S x :
      pk x →
      konst_ty peq plt pk KNew
        (TLolli None None TUnit (TProd (TSess S x) (TSess (dual S) x)))
  | KTSpawn ub lb :
      konst_ty peq plt pk KSpawn
        (TLolli None None (TLolli ub lb TUnit TUnit) TUnit)
  | KTSend m T S x :
      (∀ h, h ∈ heads (payload_at m T x) → plt x h) →
      konst_ty peq plt pk KSend
        (TLolli (Some x) None
           (TProd (payload_at m T x) (TSess (SSnd m T S) x))
           (TSess S (pt_shift 1 x)))
  | KTRecv m T S x :
      konst_ty peq plt pk KRecv
        (TLolli (Some x) None
           (TSess (SRcv m T S) x)
           (TProd (payload_at m T x) (TSess S (pt_shift 1 x))))
  | KTClos x :
      konst_ty peq plt pk KClos (TLolli (Some x) None (TSess SEnd x) TUnit)
  | KTLink S x x' :
      peq x x' →
      konst_ty peq plt pk KLink
        (TLolli None None (TProd (TSess S x) (TSess (dual S) x')) TUnit)
  | KTForce n C ub T xs :
      length xs = n → bcs_hold peq plt C xs → Forall pk xs →
      konst_ty peq plt pk KForce
        (TLolli (pt_inst (plist xs) <$> ub) None (TBox n C (TLolli ub None TUnit T))
           (ty_inst xs T))
  | KTNewEx S C u :
      fresh_ok C → Forall pk (bc_env C) →
      (∀ u' p q v, fresh_lo C u' p → fresh_hi C q v → ple p q →
         plt (fresh_outer C u') (fresh_outer C v)) →
      fresh_lo C u (pvar 0) →
      konst_ty peq plt pk KNew
        (TLolli None None TUnit
           (TEx (Some (fresh_outer C u)) 1 C (TProd (TSess S (pvar 0)) (TSess (dual S) (pvar 0))))).
