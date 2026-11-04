(** * An algorithmic judgment for the non-recursive core (docs/extensions/algorithmic-bidir.md)

    [synth n Φ Δ F a] is the synthesis half of the bidirectional system
    of algorithmic-bidir.md, run on annotated terms [aexpr]. It is a
    function. It returns the synthesized type and a constraint
    ([constr]), a finite tree of atoms over the fact theory with one
    binder for the fresh point of every [new]. The constraint collects
    everything the declarative rules of static/Source.v read from the
    fact context: the ≺ facts of the gates ({u} ≺ F), the ≡ facts of
    conversion, the lower bounds of closures, knownness, and the
    creation constraints of [new]. [csat Ψ c] says that c holds in the
    fact theory of the hypotheses Ψ. Soundness.v proves that every
    hypothesis context Ψ with [csat Ψ c] gives a derivation of
    [styped Φ Ψ Δ F (erase a) T].

    The fragment. Variables, unit, the constants spawn, send, recv,
    close, select, branch and link applied to an argument, λ with its
    bounds and argument type annotated, application, pairs, let, sums
    with the other arm annotated, case, and [new] with its session type
    and creation constraint annotated, encoded as [let_new]. No box,
    no force, no pack beyond the one of new, no bare constant. Linear
    environments split by occurrence ([lp], [sok] of
    examples/ExampleTools.v). Session types are compared on the nose
    ([sty_eqb]); the head of a session type is read through [hd], which
    is the only conversion the fragment performs.

    Effects. The future F is an input of every mode (inherited), the
    upper point of an arrow is checked against it at every application
    ([ub_constr]), and the lower point of a λ is checked against the
    heads of the captured environment. The frame variable φ of a λ body
    is the counter n, so no freshness oracle is needed. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** Atoms and constraints *)

Inductive atom :=
  | ALt (x y : point)                                (* x ≺ y *)
  | AEq (x y : point)                                (* x ≡ y *)
  | ALe (x y : point)                                (* x ≼ y *)
  | ALtF (u : point) (P : gset point)                (* u ≺ every point of P *)
  | ALbH (lb : option point) (H : gset point) (b : bool)   (* ℓ ≼ H, the flag b off *)
  | AKnown (x : point)                               (* x known *)
  | ACc (C : bcs)                                    (* C a creation constraint *)
  | AFalse.

Definition asat (Ψ : hyps) (a : atom) : Prop :=
  match a with
  | ALt x y => hlt Ψ x y
  | AEq x y => heqs Ψ x y
  | ALe x y => hle Ψ x y
  | ALtF u P => ∀ y, y ∈ P → hlt Ψ u y
  | ALbH lb H b => hlb_below_hb Ψ lb H b
  | AKnown x => hyp_known Ψ x
  | ACc C => cc_ok (heqs Ψ) (hlt Ψ) C
  | AFalse => False
  end.

(** A constraint: atoms, conjunction, and the binder of the fresh point
    of a [new], under which the hypothesis (C, ι) is in scope. *)
Inductive constr :=
  | CTrue
  | CAtom (a : atom)
  | CAnd (c1 c2 : constr)
  | COpen (C : bcs) (c : constr).

Fixpoint csat (Ψ : hyps) (c : constr) : Prop :=
  match c with
  | CTrue => True
  | CAtom a => asat Ψ a
  | CAnd c1 c2 => csat Ψ c1 ∧ csat Ψ c2
  | COpen C c => csat (hyps_inst (pshift 1) Ψ ++ [(bcs_inst (pshift 1) C, ids 1)]) c
  end.

Definition cands (cs : list constr) : constr := foldr CAnd CTrue cs.

Lemma csat_cands Ψ cs : csat Ψ (cands cs) ↔ Forall (csat Ψ) cs.
Proof.
  induction cs as [|c cs IH]; simpl.
  - split; [constructor|done].
  - rewrite Forall_cons. by rewrite IH.
Qed.

(** {u} ≺ F, resolved against the frame hypotheses Φ: u below every
    point of F, and u ≼ u′ for the hypothesis u′ ≺ φ of the frame
    variable φ of F. A frame with the ⊥ flag, or whose frame variable
    has no hypothesis, admits no call with an upper point. *)
Definition ub_constr (Φ : fhyps) (ub : option point) (F : sframe) : constr :=
  match ub with
  | None => CTrue
  | Some u =>
      CAnd (CAtom (ALtF u F.1))
        (match F.2 with
         | None => CTrue
         | Some (FVar φ) =>
             match Φ !! φ with
             | Some (Some u') => CAtom (ALe u u')
             | _ => CAtom AFalse
             end
         | Some (FBot _) => CAtom AFalse
         end)
  end.

(** ** Decidable equality of types without constraints *)

Definition opt_point_eqb (o o' : option point) : bool := bool_decide (o = o').

Fixpoint ty_eqb (T U : ty) : bool :=
  match T, U with
  | TUnit, TUnit => true
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      opt_point_eqb ub ub' && opt_point_eqb lb lb' && ty_eqb T1 U1 && ty_eqb T2 U2
  | TProd T1 T2, TProd U1 U2 => ty_eqb T1 U1 && ty_eqb T2 U2
  | TSum T1 T2, TSum U1 U2 => ty_eqb T1 U1 && ty_eqb T2 U2
  | TSess s x, TSess r y => sty_eqb s r && bool_decide (x = y)
  | _, _ => false
  end
with sty_eqb (s r : sty) : bool :=
  match s, r with
  | SRcv m T, SRcv m' U => Nat.eqb m m' && ty_eqb T U
  | SSnd m T, SSnd m' U => Nat.eqb m m' && ty_eqb T U
  | SEnd, SEnd => true
  | SMu s', SMu r' => sty_eqb s' r'
  | SVar a, SVar b => Nat.eqb a b
  | SVarD a, SVarD b => Nat.eqb a b
  | SSkip, SSkip => true
  | SSeq s1 s2, SSeq r1 r2 => sty_eqb s1 r1 && sty_eqb s2 r2
  | SPlus s1 s2, SPlus r1 r2 => sty_eqb s1 r1 && sty_eqb s2 r2
  | SWith s1 s2, SWith r1 r2 => sty_eqb s1 r1 && sty_eqb s2 r2
  | _, _ => false
  end.

Lemma ty_sty_eqb_sound :
  (∀ T U, ty_eqb T U = true → T = U) ∧ (∀ s r, sty_eqb s r = true → s = r).
Proof.
  apply ty_sty_mut_ind; intros; try (destruct U; simpl in *; try done);
    try (destruct r; simpl in *; try done).
  - apply andb_true_iff in H1 as [[[H1 H2]%andb_true_iff H3]%andb_true_iff H4].
    unfold opt_point_eqb in *. apply bool_decide_eq_true in H1, H2. subst. f_equal; auto.
  - apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
  - apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
  - apply andb_true_iff in H as [H1 H2]. apply bool_decide_eq_true in H2. subst. f_equal; auto.
  - apply andb_true_iff in H0 as [H1 H2]. apply Nat.eqb_eq in H1. subst. f_equal; auto.
  - apply andb_true_iff in H0 as [H1 H2]. apply Nat.eqb_eq in H1. subst. f_equal; auto.
  - f_equal; auto.
  - apply Nat.eqb_eq in H. by subst.
  - apply Nat.eqb_eq in H. by subst.
  - apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
  - apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
  - apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
Qed.

Definition ty_eqb_sound := proj1 ty_sty_eqb_sound.
Definition sty_eqb_sound := proj2 ty_sty_eqb_sound.

(** ** Matching two types up to the points of channels and bounds

    [tmatch T U] succeeds when T and U agree except at points, and
    returns the ≡ atoms between the points. It fails on boxes and
    existentials. Soundness: the atoms give [hsteq Ψ T U], the premise
    of E-Conv. *)

Definition omatch (o o' : option point) : option constr :=
  match o, o' with
  | Some x, Some y => Some (CAtom (AEq x y))
  | None, None => Some CTrue
  | _, _ => None
  end.

Fixpoint tmatch (T U : ty) : option constr :=
  match T, U with
  | TUnit, TUnit => Some CTrue
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      match omatch ub ub', omatch lb lb', tmatch T1 U1, tmatch T2 U2 with
      | Some c0, Some c1, Some c2, Some c3 => Some (cands [c0; c1; c2; c3])
      | _, _, _, _ => None
      end
  | TProd T1 T2, TProd U1 U2 | TSum T1 T2, TSum U1 U2 =>
      match tmatch T1 U1, tmatch T2 U2 with
      | Some c1, Some c2 => Some (CAnd c1 c2)
      | _, _ => None
      end
  | TSess s x, TSess r y => if sty_eqb s r then Some (CAtom (AEq x y)) else None
  | _, _ => None
  end.

(** ** Linear environments by occurrence *)

Fixpoint lenv_emptyb (Δ : lenv) : bool :=
  match Δ with
  | [] => true
  | None :: Δ' => lenv_emptyb Δ'
  | Some _ :: _ => false
  end.

Fixpoint lenv_onlyb (x : nat) (Δ : lenv) : option ty :=
  match Δ, x with
  | Some T :: Δ', 0 => if lenv_emptyb Δ' then Some T else None
  | None :: Δ', S x' => lenv_onlyb x' Δ'
  | _, _ => None
  end.

(** ** Annotated terms *)

Inductive aexpr :=
  | AVar (x : nat)
  | AUnit
  | AKonst (k : konst)
  | ALam (ub lb : option point) (T : ty) (e : aexpr)     (* λx:T. e with the bounds of its arrow *)
  | AApp (e1 e2 : aexpr)
  | APair (e1 e2 : aexpr)
  | ALetU (e1 e2 : aexpr)
  | ALetP (e1 e2 : aexpr)
  | AInj1 (U : ty) (e : aexpr)                          (* inj₁ e at T + U *)
  | AInj2 (T : ty) (e : aexpr)                          (* inj₂ e at T + U *)
  | ACase (e e1 e2 : aexpr)
  | ANew (S : sty) (C : bcs) (e : aexpr).              (* let (a, b) = new ∗ in e, the fresh point under C *)

Fixpoint erase (a : aexpr) : expr :=
  match a with
  | AVar x => Var x
  | AUnit => EUnit
  | AKonst k => Konst k
  | ALam _ _ _ e => Lam (erase e)
  | AApp e1 e2 => App (erase e1) (erase e2)
  | APair e1 e2 => Pair (erase e1) (erase e2)
  | ALetU e1 e2 => LetU (erase e1) (erase e2)
  | ALetP e1 e2 => LetP (erase e1) (erase e2)
  | AInj1 _ e => Inj1 (erase e)
  | AInj2 _ e => Inj2 (erase e)
  | ACase e e1 e2 => Case (erase e) (erase e1) (erase e2)
  | ANew _ _ e => let_new (erase e)
  end.

(** ** Decidable scoping of a payload (kscoped) *)

Definition pt_scopedb (k : nat) (x : point) : bool :=
  match pt_root x with NVar a => Nat.ltb a k | _ => true end.

Definition opt_scopedb (k : nat) (o : option point) : bool :=
  match o with Some x => pt_scopedb k x | None => true end.

Definition lb_scopedb (k : nat) (lb : lbound) : bool :=
  match lb with LPt x => pt_scopedb k x | _ => true end.

Definition bcs_scopedb (k : nat) (C : bcs) : bool := forallb (pt_scopedb k) (bc_env C).

Fixpoint pscopedb (k : nat) (T : ty) : bool :=
  match T with
  | TUnit => true
  | TLolli ub lb T1 U => opt_scopedb k ub && opt_scopedb k lb && pscopedb k T1 && pscopedb k U
  | TProd T1 U | TSum T1 U => pscopedb k T1 && pscopedb k U
  | TBox n _ C T1 => bcs_scopedb k C && pscopedb (n + k) T1
  | TSess _ x => pt_scopedb k x
  | TEx lb n C T1 => lb_scopedb k lb && bcs_scopedb k C && pscopedb (n + k) T1
  end.

(** ** The constants applied to an argument of type A

    The scheme of the constant is read off A (spec §9). The head of the
    session type is its head normal form [hd]. *)
Definition konst_app (Φ : fhyps) (F : sframe) (k : konst) (A : ty) : option (ty * constr) :=
  match k, A with
  | KSpawn, TLolli _ _ TUnit TUnit => Some (TUnit, CTrue)
  | KSend, TProd P (TSess s x) =>
      match hd s with
      | HSnd m T s' =>
          if hbot T || negb (pscopedb m T) then None else
          match tmatch P (payload_at m T x) with
          | Some c =>
              Some (TSess s' (pt_shift 1 x),
                    cands [c; CAtom (ALtF x (heads (payload_at m T x))); ub_constr Φ (Some x) F])
          | None => None
          end
      | _ => None
      end
  | KRecv, TSess s x =>
      match hd s with
      | HRcv m T s' =>
          if negb (pscopedb m T) then None else
          Some (TProd (payload_at m T x) (TSess s' (pt_shift 1 x)), ub_constr Φ (Some x) F)
      | _ => None
      end
  | KClos, TSess s x =>
      match hd s with
      | HEnd => Some (TUnit, ub_constr Φ (Some x) F)
      | _ => None
      end
  | KSel1, TSess s x =>
      match hd s with
      | HPlus s1 s2 =>
          Some (TSess s1 (pt_slot x 0), CAnd (CAtom (ALt x (pt_slot x 0))) (ub_constr Φ (Some x) F))
      | _ => None
      end
  | KSel2, TSess s x =>
      match hd s with
      | HPlus s1 s2 =>
          Some (TSess s2 (pt_slot x 1), CAnd (CAtom (ALt x (pt_slot x 1))) (ub_constr Φ (Some x) F))
      | _ => None
      end
  | KBra, TSess s x =>
      match hd s with
      | HWith s1 s2 =>
          Some (TSum (TSess s1 (pt_slot x 0)) (TSess s2 (pt_slot x 1)),
                cands [CAtom (ALt x (pt_slot x 0)); CAtom (ALt x (pt_slot x 1)); ub_constr Φ (Some x) F])
      | _ => None
      end
  | KLink, TProd (TSess s x) (TSess r y) =>
      if sty_eqb r (dual s) then Some (TUnit, CAtom (AEq x y)) else None
  | _, _ => None
  end.

(** The result type of a [new] body must not mention the fresh point. *)
Definition unshift_ty (U : ty) : ty := pinst_ty (λ a, pvar (a - 1)) U.

(** ** Synthesis

    n is the next free frame variable: every frame variable of Φ is
    below n. *)
Fixpoint synth (n : nat) (Φ : fhyps) (Δ : lenv) (F : sframe) (a : aexpr) : option (ty * constr) :=
  match a with
  | AVar x =>
      match lenv_onlyb x Δ with Some T => Some (T, CTrue) | None => None end
  | AUnit => if lenv_emptyb Δ then Some (TUnit, CTrue) else None
  | AKonst _ => None
  | ALam ub lb T e =>
      match synth (S n) (<[n := ub]> Φ) (Some T :: Δ) (∅, Some (FVar n)) e with
      | Some (U, c) =>
          Some (TLolli ub lb T U, CAnd (CAtom (ALbH lb (lenv_heads Δ) (lenv_bot Δ))) c)
      | None => None
      end
  | AApp (AKonst k) e2 =>
      match synth n Φ Δ F e2 with
      | Some (A, c2) =>
          match konst_app Φ F k A with
          | Some (U, c) => Some (U, CAnd c2 c)
          | None => None
          end
      | None => None
      end
  | AApp e1 e2 =>
      if sok (erase e1) 0 (erase e2) 0 Δ then
        let Δ1 := lp (erase e1) 0 Δ in
        let Δ2 := lp (erase e2) 0 Δ in
        match synth n Φ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 with
        | Some (TLolli ub lb T U, c1) =>
            match synth n Φ Δ2 (sf_union F (opt_heads lb)) e2 with
            | Some (T', c2) =>
                match tmatch T' T with
                | Some c3 => Some (U, cands [c1; c2; c3; ub_constr Φ ub F])
                | None => None
                end
            | None => None
            end
        | _ => None
        end
      else None
  | APair e1 e2 =>
      if sok (erase e1) 0 (erase e2) 0 Δ then
        let Δ1 := lp (erase e1) 0 Δ in
        let Δ2 := lp (erase e2) 0 Δ in
        match synth n Φ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 with
        | Some (T, c1) =>
            match synth n Φ Δ2 (sf_unionb F (heads T) (hbot T)) e2 with
            | Some (U, c2) => Some (TProd T U, CAnd c1 c2)
            | None => None
            end
        | None => None
        end
      else None
  | ALetU e1 e2 =>
      if sok (erase e1) 0 (erase e2) 0 Δ then
        let Δ1 := lp (erase e1) 0 Δ in
        let Δ2 := lp (erase e2) 0 Δ in
        match synth n Φ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 with
        | Some (TUnit, c1) =>
            match synth n Φ Δ2 F e2 with
            | Some (T, c2) => Some (T, CAnd c1 c2)
            | None => None
            end
        | _ => None
        end
      else None
  | ALetP e1 e2 =>
      if sok (erase e1) 0 (erase e2) 2 Δ then
        let Δ1 := lp (erase e1) 0 Δ in
        let Δ2 := lp (erase e2) 2 Δ in
        match synth n Φ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 with
        | Some (TProd T1 T2, c1) =>
            match synth n Φ (Some T2 :: Some T1 :: Δ2) F e2 with
            | Some (T, c2) => Some (T, CAnd c1 c2)
            | None => None
            end
        | _ => None
        end
      else None
  | AInj1 U e =>
      match synth n Φ Δ F e with
      | Some (T, c) => Some (TSum T U, c)
      | None => None
      end
  | AInj2 T e =>
      match synth n Φ Δ F e with
      | Some (U, c) => Some (TSum T U, c)
      | None => None
      end
  | ACase e e1 e2 =>
      if sok (erase e) 0 (Lam (Pair (erase e1) (erase e2))) 0 Δ then
        let Δ1 := lp (erase e) 0 Δ in
        let Δ2 := lp (Lam (Pair (erase e1) (erase e2))) 0 Δ in
        match synth n Φ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e with
        | Some (TSum T1 T2, c) =>
            match synth n Φ (Some T1 :: Δ2) F e1, synth n Φ (Some T2 :: Δ2) F e2 with
            | Some (T, c1), Some (T', c2) =>
                match tmatch T' T with
                | Some c3 => Some (T, cands [c; c1; c2; c3])
                | None => None
                end
            | _, _ => None
            end
        | _ => None
        end
      else None
  | ANew S C e =>
      match synth n (fhyps_pinst (pshift 1) Φ)
              (Some (TSess (dual S) (pvar 0)) :: Some (TSess S (pvar 0)) :: None :: None ::
                 lenv_pinst (pshift 1) Δ)
              (sf_pinst (pshift 1) F) e with
      | Some (U', c) =>
          let T := unshift_ty U' in
          if ty_eqb (pinst_ty (pshift 1) T) U' then
            Some (T, cands [CAtom (ACc C);
                            cands (CAtom ∘ AKnown <$> bc_env C);
                            COpen C c])
          else None
      | None => None
      end
  end.
