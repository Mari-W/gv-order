(** * Points (stage S2, proposal §2.3)

    root   r ::= a | g_ℓ | ι        a constant, a generated root of the
                                    family ℓ, a point variable
    point  x ::= r | x⁺ | x·κ | x‾

    A point is a name with a polarity and an offset. A name is a root or
    the field (p, b)·κ of the name p at offset b. The dual x‾ flips the
    polarity, the shift x⁺ raises the offset and keeps the polarity, and
    the field x·κ ignores the polarity of x (x‾·κ = x·κ) and is positive
    at offset 0. Point variables occur only in types, bound by □∀ and by
    a payload ∃ or the ∃ of [new_ℓ]. No point mentions a channel.

    An action moves an end from x to x⁺, a select of branch i to
    (x·κ_i)‾ and a branch to x·κ_i. The ends a message on x carries sit
    at the fields x·0, x·1, …, and [new_κ o] creates at x·κ for the point
    x of o. The continuation of choice i and the i-th payload field share
    a point by design (proposal §2.3). *)

From stdpp Require Export base gmap countable relations.
From GV Require Export lang.Notations.

Inductive pname :=
  | NConst (a : nat)                         (* a constant a *)
  | NGen (ℓ : family) (g : nat)              (* the generated root g of family ℓ *)
  | NVar (a : nat)                           (* a point variable, de Bruijn *)
  | NField (p : pname) (b : nat) (κ : field). (* (p, b)·κ *)

Record point := MkPt { pt_name : pname; pt_pol : bool; pt_off : nat }.

Global Instance pname_eq_dec : EqDecision pname.
Proof. solve_decision. Defined.

Global Instance pname_countable : Countable pname.
Proof.
  set (enc := fix go p : gen_tree nat :=
    match p with
    | NConst a => GenNode 0 [GenLeaf a]
    | NGen ℓ g => GenNode 1 [GenLeaf ℓ; GenLeaf g]
    | NVar a => GenNode 2 [GenLeaf a]
    | NField p b κ => GenNode 3 [go p; GenLeaf b; GenLeaf κ]
    end).
  set (dec := fix go t : pname :=
    match t with
    | GenNode 0 [GenLeaf a] => NConst a
    | GenNode 1 [GenLeaf ℓ; GenLeaf g] => NGen ℓ g
    | GenNode 2 [GenLeaf a] => NVar a
    | GenNode 3 [t; GenLeaf b; GenLeaf κ] => NField (go t) b κ
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

Declare Scope point_scope.
Delimit Scope point_scope with pt.
Bind Scope point_scope with point.

(** ** The algebra *)

(** x + n. The shift x⁺ is x + 1. *)
Definition pt_shift (n : nat) (x : point) : point :=
  MkPt (pt_name x) (pt_pol x) (pt_off x + n).

(** x‾, the point of the other end. *)
Definition pt_dual (x : point) : point :=
  MkPt (pt_name x) (negb (pt_pol x)) (pt_off x).

(** x·κ, positive, offset 0, the same from both ends of x. *)
Definition pt_field (x : point) (κ : field) : point :=
  MkPt (NField (pt_name x) (pt_off x) κ) true 0.

Notation "x ⁺" := (pt_shift 1 x) (at level 1, left associativity, format "x ⁺") : point_scope.
Notation "x ‾" := (pt_dual x) (at level 1, left associativity, format "x ‾") : point_scope.
Notation "x · κ" := (pt_field x κ) (at level 2, left associativity, format "x · κ") : point_scope.

Open Scope point_scope.

(** y read at polarity b: y for [true], y‾ for [false]. *)
Definition pt_polar (b : bool) (y : point) : point := if b then y else y‾.

(** The root of a point and the point of a root at offset 0. *)
Fixpoint pn_root (p : pname) : pname :=
  match p with NField q _ _ => pn_root q | r => r end.
Definition pt_root (x : point) : pname := pn_root (pt_name x).

Definition pgen (ℓ : family) (g : nat) : point := MkPt (NGen ℓ g) true 0.
Definition pvar (a : nat) : point := MkPt (NVar a) true 0.

(** The field where branch i continues: κ_0 = 0 for [false], κ_1 = 1
    for [true]. The selecting end continues at (x·κ_i)‾ and the
    branching end at x·κ_i. *)
Definition bfield (i : bool) : field := if i then 1 else 0.
Definition sel_pt (x : point) (i : bool) : point := (x·(bfield i))‾.
Definition bra_pt (x : point) (i : bool) : point := x·(bfield i).

(** The laws of today: fields ignore polarity, shift keeps it. *)
Lemma pt_dual_dual x : x‾‾ = x.
Proof. destruct x as [p b o]. unfold pt_dual. simpl. by rewrite negb_involutive. Qed.
Lemma pt_field_dual x κ : x‾·κ = x·κ.
Proof. done. Qed.
Lemma pt_dual_shift n x : pt_shift n x‾ = (pt_shift n x)‾.
Proof. done. Qed.
Lemma pt_shift_0 x : pt_shift 0 x = x.
Proof. destruct x as [p b o]. unfold pt_shift. simpl. f_equal. lia. Qed.
Lemma pt_root_shift n x : pt_root (pt_shift n x) = pt_root x.
Proof. done. Qed.
Lemma pt_root_dual x : pt_root x‾ = pt_root x.
Proof. done. Qed.
Lemma pt_root_field x κ : pt_root (x·κ) = pt_root x.
Proof. done. Qed.
Lemma pt_root_polar b x : pt_root (pt_polar b x) = pt_root x.
Proof. by destruct b. Qed.
(** ** Point instantiation

    x[σ] instantiates the point variables of x. A variable denotes the
    point σ a at offset 0, positive; the offset and polarity of x apply
    on top. *)
Fixpoint pn_inst (σ : nat → point) (p : pname) : point :=
  match p with
  | NConst a => MkPt (NConst a) true 0
  | NGen ℓ g => MkPt (NGen ℓ g) true 0
  | NVar a => σ a
  | NField p b κ => (pt_shift b (pn_inst σ p))·κ
  end.

Definition pt_inst (σ : nat → point) (x : point) : point :=
  pt_polar (pt_pol x) (pt_shift (pt_off x) (pn_inst σ (pt_name x))).

(** Lifting under a binder of m point variables. *)
Definition pup (m : nat) (σ : nat → point) : nat → point :=
  λ a, if decide (a < m) then pvar a
       else pt_inst (λ a', pvar (a' + m)) (σ (a - m)).

(** The variable i goes to the i-th point of xs, later variables down. *)
Definition plist (xs : list point) : nat → point :=
  λ a, match xs !! a with Some x => x | None => pvar (a - length xs) end.

(** Variables shifted past m new binders. *)
Definition pshift (m : nat) : nat → point := λ a, pvar (a + m).

(** The fields x·0, …, x·(m−1), where the ends of a message sit. *)
Definition payload_pts (x : point) (m : nat) : list point :=
  (λ i, x·i) <$> seq 0 m.

Lemma pt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
Proof. unfold pt_inst, pvar. simpl. apply pt_shift_0. Qed.

Lemma pt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
Proof.
  destruct x as [p b o]. unfold pt_inst, pt_shift. simpl.
  destruct (pn_inst σ p). destruct b; unfold pt_polar, pt_dual; simpl; f_equal; lia.
Qed.

Lemma pt_inst_dual σ x : pt_inst σ x‾ = (pt_inst σ x)‾.
Proof.
  destruct x as [p b o]. unfold pt_inst. simpl.
  destruct b; simpl; [done|by rewrite pt_dual_dual].
Qed.

Lemma pt_inst_field σ x κ : pt_inst σ (x·κ) = (pt_inst σ x)·κ.
Proof.
  destruct x as [p [] o]; unfold pt_inst; simpl; rewrite pt_shift_0; done.
Qed.

Lemma pt_inst_polar σ b x : pt_inst σ (pt_polar b x) = pt_polar b (pt_inst σ x).
Proof. destruct b; simpl; [done|apply pt_inst_dual]. Qed.

Lemma pn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
Proof.
  induction p as [a|ℓ g|a|p IH b κ]; simpl; try done.
  by rewrite pt_inst_field, pt_inst_shift, IH.
Qed.

Lemma pt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
Proof.
  destruct x as [n b o]. unfold pt_inst at 2 3. simpl.
  by rewrite pt_inst_polar, pt_inst_shift, pn_inst_comp.
Qed.

Lemma pn_inst_ext σ τ p : (∀ a, σ a = τ a) → pn_inst σ p = pn_inst τ p.
Proof. intros H. induction p; simpl; rewrite ?IHp; auto. Qed.

Lemma pt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. unfold pt_inst. by rewrite (pn_inst_ext σ τ). Qed.

(** Only the variables of the root matter. *)
Lemma pn_inst_ext_root σ τ p :
  (∀ a, pn_root p = NVar a → σ a = τ a) → pn_inst σ p = pn_inst τ p.
Proof. intros H. induction p; simpl in *; rewrite ?IHp; auto. Qed.

Lemma pt_inst_ext_root σ τ x :
  (∀ a, pt_root x = NVar a → σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. unfold pt_inst. by rewrite (pn_inst_ext_root σ τ). Qed.

Lemma pn_inst_pvar p : pn_inst pvar p = MkPt p true 0.
Proof.
  induction p; simpl; try done. rewrite IHp. unfold pt_field, pt_shift. done.
Qed.

Lemma pt_inst_pvar x : pt_inst pvar x = x.
Proof.
  destruct x as [p bb o]. unfold pt_inst. simpl. rewrite pn_inst_pvar.
  destruct bb; unfold pt_polar, pt_shift, pt_dual; simpl; f_equal; lia.
Qed.

Lemma pt_inst_novar σ x : (∀ a, pt_root x ≠ NVar a) → pt_inst σ x = x.
Proof.
  intros H. rewrite (pt_inst_ext_root σ pvar); [apply pt_inst_pvar|].
  intros a Ha. by destruct (H a).
Qed.

(** The root of an instance is the root of the instance of the root. *)
Lemma pn_root_inst σ p :
  pt_root (pn_inst σ p) = pt_root (pn_inst σ (pn_root p)).
Proof. induction p; simpl; try done; by rewrite <-IHp. Qed.

Lemma pt_root_inst_var σ x :
  pt_root (pt_inst σ x) = pt_root (pn_inst σ (pt_root x)).
Proof.
  unfold pt_inst. rewrite pt_root_polar, pt_root_shift.
  apply pn_root_inst.
Qed.

Lemma pup_ext n σ τ a : (∀ b, σ b = τ b) → pup n σ a = pup n τ a.
Proof. intros H. unfold pup. by rewrite H. Qed.

Lemma pup_pvar n a : pup n pvar a = pvar a.
Proof.
  unfold pup. destruct (decide (a < n)); [done|].
  rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma pup_comp τ σ n a : pt_inst (pup n τ) (pup n σ a) = pup n (pt_inst τ ∘ σ) a.
Proof.
  unfold pup at 2 3. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True.
  - change ((pt_inst τ ∘ σ) (a - n)) with (pt_inst τ (σ (a - n))).
    rewrite !pt_inst_comp. apply pt_inst_ext. intros b. simpl.
    rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
    by replace (b + n - n) with b by lia.
Qed.

Lemma pup_pshift m σ a : pup m σ (a + m) = pt_inst (pshift m) (σ a).
Proof.
  unfold pup. rewrite decide_False by lia. by replace (a + m - m) with a by lia.
Qed.

Lemma plist_shift xs m b : length xs = m → plist xs (b + m) = pvar b.
Proof.
  intros <-. unfold plist. rewrite lookup_ge_None_2 by lia. f_equal. lia.
Qed.

Lemma plist_lookup xs i x : xs !! i = Some x → plist xs i = x.
Proof. unfold plist. by intros ->. Qed.

(** ** Renamings of generated roots

    [pn_gmap r] renames every generated root (ℓ, g) to r (ℓ, g) and
    leaves constants, variables and the rest of the name alone. A
    renaming of families is the instance r (ℓ, g) = (f ℓ, g), and a
    renaming of the roots of one family keeps ℓ. *)
Fixpoint pn_gmap (r : family * nat → family * nat) (p : pname) : pname :=
  match p with
  | NGen ℓ g => NGen (r (ℓ, g)).1 (r (ℓ, g)).2
  | NField q b κ => NField (pn_gmap r q) b κ
  | q => q
  end.

Definition pt_gmap (r : family * nat → family * nat) (x : point) : point :=
  MkPt (pn_gmap r (pt_name x)) (pt_pol x) (pt_off x).

(** ** Facts *)

Inductive fact := FLt (x y : point).

Global Instance fact_eq_dec : EqDecision fact.
Proof. solve_decision. Defined.

Definition fact_map (f : point → point) (g : fact) : fact :=
  match g with FLt x y => FLt (f x) (f y) end.

Lemma fact_map_comp (f f' : point → point) g : fact_map f (fact_map f' g) = fact_map (f ∘ f') g.
Proof. by destruct g. Qed.

Lemma fact_map_ext (f f' : point → point) g : (∀ x, f x = f' x) → fact_map f g = fact_map f' g.
Proof. intros H. destruct g; simpl; by rewrite !H. Qed.

(** The root of a name is a variable below k. *)
Fixpoint pn_vb (k : nat) (p : pname) : Prop :=
  match p with
  | NVar a => a < k
  | NField q _ _ => pn_vb k q
  | _ => False
  end.

Definition fact_scoped (k : nat) (g : fact) : Prop :=
  match g with FLt x y => pn_vb k (pt_name x) ∧ pn_vb k (pt_name y) end.

Lemma pn_vb_root k p : pn_vb k p ↔ ∃ a, pn_root p = NVar a ∧ a < k.
Proof. induction p; simpl; naive_solver. Qed.

(** ** Box constraints

    The constraint of a box or an existential: any set of facts, finite
    or infinite. The facts speak of variables only, 0, …, n−1 for the
    bound ιs and n + j for the j-th point of [bc_env], which lives
    outside the binder. Instantiation acts on [bc_env] alone. *)
Record bcs := BCs { bc_env : list point; bc_facts : fact → Prop }.

Definition bcs_inst (σ : nat → point) (C : bcs) : bcs :=
  BCs (pt_inst σ <$> bc_env C) (bc_facts C).

Definition bcs_gmap (r : family * nat → family * nat) (C : bcs) : bcs :=
  BCs (pt_gmap r <$> bc_env C) (bc_facts C).

(** The facts of C under its binder of n variables. *)
Definition bcs_open (n : nat) (C : bcs) (g : fact) : Prop :=
  ∃ f, bc_facts C f ∧ fact_scoped (n + length (bc_env C)) f ∧
    g = fact_map (pt_inst (pup n (plist (bc_env C)))) f.

(** C[xs/ιs], the facts of C at the instance xs. *)
Definition bcs_at (C : bcs) (xs : list point) : fact → Prop :=
  λ g, ∃ g0, bcs_open (length xs) C g0 ∧ g = fact_map (pt_inst (plist xs)) g0.

(** A constraint without outer points. *)
Definition bcs_of (P : fact → Prop) : bcs := BCs [] P.

Lemma bcs_inst_ext σ τ C : (∀ a, σ a = τ a) → bcs_inst σ C = bcs_inst τ C.
Proof.
  intros H. destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  apply list_fmap_ext. intros _ x _. by apply pt_inst_ext.
Qed.

Lemma bcs_inst_comp τ σ C : bcs_inst τ (bcs_inst σ C) = bcs_inst (pt_inst τ ∘ σ) C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_inst_comp.
Qed.

Lemma bcs_inst_pvar C : bcs_inst pvar C = C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-(list_fmap_id env) at 2. apply list_fmap_ext. intros _ x _. apply pt_inst_pvar.
Qed.

(** ** Lower bounds of existentials

    [LNone]: the value holds no end. [LBot]: its ends sit at points not
    known from outside, the ⊥ flag. [LPt x]: every end lies at or above
    x. *)
Inductive lbound := LNone | LBot | LPt (x : point).

Global Instance lbound_eq_dec : EqDecision lbound.
Proof. solve_decision. Defined.

Definition lb_map (f : point → point) (lb : lbound) : lbound :=
  match lb with LPt x => LPt (f x) | LNone => LNone | LBot => LBot end.

Lemma lb_map_ext f g lb : (∀ x, f x = g x) → lb_map f lb = lb_map g lb.
Proof. intros H. destruct lb; simpl; by rewrite ?H. Qed.

Lemma lb_map_comp f g lb : lb_map f (lb_map g lb) = lb_map (f ∘ g) lb.
Proof. by destruct lb. Qed.

Lemma lb_map_id f lb : (∀ x, f x = x) → lb_map f lb = lb.
Proof. intros H. destruct lb; simpl; by rewrite ?H. Qed.
