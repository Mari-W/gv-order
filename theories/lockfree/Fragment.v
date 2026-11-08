(** * The static rules of the lock-free fragment (lock-freedom-plan.md §10.2)

    Stage 3a. The rules are checks next to the guard of liveness/Guard.v.
    No relation changes.

    - [pcall_target]: a force is a potentially recursive call when it
      forces a box literal whose body forces, or anything else (a box
      variable, a parameter, a received box).
    - R1 ([r1]): a potentially recursive call sits in tail position of
      its thread. Threads are the root term, the body of a spawned λ and
      the body of a box under its one λ. Let, let pair and case pass
      tail position to their continuation and branches, and an applied
      λ passes it to its body. Every other frame is a frame that still
      holds or uses something, the call's results included, so the call
      is rejected there. This is the plan's R1 and not R1′.
    - R2′ ([r2]): inside a box body (a round) the argument of every
      potentially recursive call and of every link is fresh. Fresh
      means built from variables that the round bound to the result of
      an action or of new, from send, select, branch, new, unit,
      constants and boxes. The parameter, the self and a received
      payload are not fresh.
    - R4′ ([r4_ok]): a forwarding hop is a send, inside a box body, of a
      payload received in the same body and not acted on. Its two
      carriers are traced back to the box parameter as paths into its
      product type. The session types at those paths come from a type
      of the box that the typing judgment derives ([ann]), and an edge
      runs from the receiving carrier's type to the dual of the sending
      carrier's type, both with points and constraints erased. The
      graph of all hops is acyclic. Expressions carry no types, so this
      rule reads its types off typings of the boxes, not off the term.
    - Rank ([wf_world]): ≺ of the world is well founded.
    - R2-recv ([r2r], stage 3c, plan §13) replaces R2′ in the fragment.
      A received payload passed to a call of the self counts as
      advanced, and every slot it feeds must be acted on before the
      round passes it on. [r2] stays as the stricter rule.

    [lfptyped] is [gptyped] with R1, R2-recv, R4′ and Rank. [lfsource] is
    the same for a source program under a top-level constraint, the
    form in which the CFST scheduler is typed. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.Guard.
From LRGV Require Import static.Fundamental examples.ExampleTools examples.LitTools.
From LRGV Require examples.Forwarder examples.TailCall examples.KobForwarder
  examples.cfst.CfstTools examples.cfst.CfstScheduler examples.cfst.TreeSum
  examples.ReceivedChain examples.GrowRing examples.ABP.

(** ** Potentially recursive calls *)

Fixpoint has_force (e : expr) : bool :=
  match e with
  | Konst KForce => true
  | Var _ | EUnit | Konst _ | Chan _ => false
  | Lam e | EBox e | Inj1 e | Inj2 e => has_force e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => has_force e1 || has_force e2
  | Case e e1 e2 => has_force e || has_force e1 || has_force e2
  end.

(** force f is potentially recursive unless f is a box literal whose
    body never forces. *)
Definition pcall_target (f : expr) : bool :=
  match f with EBox b => has_force b | _ => true end.

(** The term is a potentially recursive call, applied or not. *)
Definition pcall (e : expr) : bool :=
  match e with
  | App (App (Konst KForce) f) _ => pcall_target f
  | App (Konst KForce) f => pcall_target f
  | _ => false
  end.

(** ** R1, empty future at a potentially recursive call

    [tl] holds when the subterm is in tail position of its thread. *)
Fixpoint r1 (tl : bool) (e : expr) : bool :=
  match e with
  | App (App (Konst KForce) f) a => (negb (pcall_target f) || tl) && r1 false f && r1 false a
  | App (Konst KForce) f => (negb (pcall_target f) || tl) && r1 false f
  | App (Konst KSpawn) (Lam b) => r1 true b
  | App (Lam b) a => r1 false a && r1 tl b
  | App e1 e2 => r1 false e1 && r1 false e2
  | Lam b => r1 false b
  | EBox (Lam b) => r1 true b
  | EBox b => r1 false b
  | LetU e1 e2 | LetP e1 e2 => r1 false e1 && r1 tl e2
  | Case e e1 e2 => r1 false e && r1 tl e1 && r1 tl e2
  | Pair e1 e2 => r1 false e1 && r1 false e2
  | Inj1 e | Inj2 e => r1 false e
  | Var _ | EUnit | Konst _ | Chan _ => true
  end.

Definition lf_r1 (e : expr) : bool := r1 true e.

(** ** R2′, advance before recursion and before link *)

(** The result of these constants is fresh: the continuation of an end
    acted on, a pair of new ends, or unit. *)
Definition kfresh (k : konst) : bool :=
  match k with
  | KSend | KSel1 | KSel2 | KBra | KNew | KClos | KLink | KSpawn => true
  | KRecv | KForce => false
  end.

(** [S !! x = Some true]: the variable x was bound in this round to
    something acted on or created. *)
Fixpoint fresh (S : list bool) (e : expr) : bool :=
  match e with
  | Var x => default false (S !! x)
  | EUnit | Konst _ | EBox _ => true
  | Pair a b => fresh S a && fresh S b
  | Inj1 a | Inj2 a => fresh S a
  | App (Konst k) _ => kfresh k
  | _ => false
  end.

(** The freshness of the two variables a let pair binds, index 0 first.
    After recv the continuation is fresh and the payload is not. *)
Definition pfresh (S : list bool) (e : expr) : list bool :=
  match e with
  | App (Konst KRecv) _ => [true; false]
  | Pair a b => [fresh S b; fresh S a]
  | _ => let f := fresh S e in [f; f]
  end.

(** [rnd] holds inside a box body. A box starts a new round in which no
    outer variable, no parameter and not the self is fresh. *)
Fixpoint r2 (rnd : bool) (S : list bool) (e : expr) : bool :=
  match e with
  | App (App (Konst KForce) f) a =>
      (negb rnd || negb (pcall_target f) || fresh S a) && r2 rnd S f && r2 rnd S a
  | App (Konst KLink) a => (negb rnd || fresh S a) && r2 rnd S a
  | App (Lam b) a => r2 rnd S a && r2 rnd (fresh S a :: S) b
  | App e1 e2 => r2 rnd S e1 && r2 rnd S e2
  | Lam b => r2 rnd (false :: S) b
  | EBox b => r2 true [] b
  | LetU e1 e2 => r2 rnd S e1 && r2 rnd S e2
  | LetP e1 e2 => r2 rnd S e1 && r2 rnd (pfresh S e1 ++ S) e2
  | Case e e1 e2 => r2 rnd S e && r2 rnd (fresh S e :: S) e1 && r2 rnd (fresh S e :: S) e2
  | Pair e1 e2 => r2 rnd S e1 && r2 rnd S e2
  | Inj1 e | Inj2 e => r2 rnd S e
  | Var _ | EUnit | Konst _ | Chan _ => true
  end.

Definition lf_r2 (e : expr) : bool := r2 false [] e.

(** ** R4′, bounded forwarding *)

(** Session types up to points, as words. Points, bounds and
    constraints are dropped, and every constructor has a fixed arity, so
    two erased types are equal exactly when the types agree up to
    points and constraints. *)
Fixpoint er_ty (T : ty) : list nat :=
  match T with
  | TUnit => [0]
  | TLolli _ _ T U => 1 :: er_ty T ++ er_ty U
  | TProd T U => 2 :: er_ty T ++ er_ty U
  | TSum T U => 3 :: er_ty T ++ er_ty U
  | TBox n k _ T => 4 :: n :: k :: er_ty T
  | TSess s _ => 5 :: er_sty s
  | TEx _ n _ T => 6 :: n :: er_ty T
  end
with er_sty (s : sty) : list nat :=
  match s with
  | SRcv m T => 10 :: m :: er_ty T
  | SSnd m T => 11 :: m :: er_ty T
  | SEnd => [12]
  | SMu s => 13 :: er_sty s
  | SVar a => [14; a]
  | SVarD a => [15; a]
  | SSkip => [16]
  | SSeq s1 s2 => 17 :: er_sty s1 ++ er_sty s2
  | SPlus s1 s2 => 18 :: er_sty s1 ++ er_sty s2
  | SWith s1 s2 => 19 :: er_sty s1 ++ er_sty s2
  end.

(** What a variable of a box body is, for forwarding: a carrier that
    descends from the parameter at a path into its product type (false
    for the left component), a payload received on such a carrier and
    not acted on (None when the carrier is unknown), or neither. *)
Inductive car := CNo | CPar (π : list bool) | CRcv (o : option (list bool)).

Definition car_of (G : list car) (x : nat) : car := default CNo (G !! x).

Definition is_rcv (c : car) : bool := match c with CRcv _ => true | _ => false end.

Definition keep_par (c : car) : car := match c with CPar π => CPar π | _ => CNo end.

(** The carrier an expression denotes. Send and select continue their
    carrier. *)
Fixpoint ecar (G : list car) (e : expr) : car :=
  match e with
  | Var x => car_of G x
  | App (Konst KSend) (Pair _ c) => keep_par (ecar G c)
  | App (Konst KSel1) c | App (Konst KSel2) c => keep_par (ecar G c)
  | _ => CNo
  end.

(** The carriers a let pair binds, index 0 first. *)
Definition pcar (G : list car) (e : expr) : list car :=
  match e with
  | App (Konst KRecv) c =>
      match ecar G c with CPar π => [CPar π; CRcv (Some π)] | _ => [CNo; CRcv None] end
  | Var x =>
      match car_of G x with
      | CPar π => [CPar (π ++ [true]); CPar (π ++ [false])]
      | CRcv o => [CRcv o; CRcv o]
      | CNo => [CNo; CNo]
      end
  | Pair a b => [ecar G b; ecar G a]
  | _ => [CNo; CNo]
  end.

(** The carrier a case branch binds. *)
Definition ccar (G : list car) (e : expr) : car :=
  match e with
  | App (Konst KBra) c => keep_par (ecar G c)
  | Var x => match car_of G x with CRcv o => CRcv o | _ => CNo end
  | _ => CNo
  end.

(** A received payload occurs free. *)
Fixpoint mentions (G : list car) (e : expr) : bool :=
  match e with
  | Var x => is_rcv (car_of G x)
  | EUnit | Konst _ | Chan _ => false
  | Lam b | EBox b => mentions (CNo :: G) b
  | App a b | Pair a b | LetU a b => mentions G a || mentions G b
  | LetP a b => mentions G a || mentions (CNo :: CNo :: G) b
  | Inj1 a | Inj2 a => mentions G a
  | Case a b c => mentions G a || mentions (CNo :: G) b || mentions (CNo :: G) c
  end.

Definition ocat {A} (a b : option (list A)) : option (list A) :=
  match a, b with Some x, Some y => Some (x ++ y) | _, _ => None end.

(** The hops of a box body, as pairs of carrier paths (receiving,
    sending). None when a received payload is sent in a form whose
    carriers cannot be traced. Nested boxes are boxes of their own. *)
Fixpoint hops (G : list car) (e : expr) : option (list (list bool * list bool)) :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ | EBox _ => Some []
  | App (Konst KSend) (Pair p c) =>
      let rest := ocat (hops G p) (hops G c) in
      if mentions G p then
        match ecar G p, ecar G c with
        | CRcv (Some π1), CPar π2 => ocat (Some [(π1, π2)]) rest
        | _, _ => None
        end
      else rest
  | Lam b => hops (CNo :: G) b
  | App (Lam b) a => ocat (hops G a) (hops (ecar G a :: G) b)
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => ocat (hops G e1) (hops G e2)
  | LetP e1 e2 => ocat (hops G e1) (hops (pcar G e1 ++ G) e2)
  | Inj1 e | Inj2 e => hops G e
  | Case e e1 e2 =>
      ocat (hops G e) (ocat (hops (ccar G e :: G) e1) (hops (ccar G e :: G) e2))
  end.

(** In EBox (Lam b) the parameter is variable 0 of b and the self is 1. *)
Definition box_hops (b : expr) : option (list (list bool * list bool)) :=
  match b with Lam b' => hops [CPar []; CNo] b' | _ => hops [CNo] b end.

(** The box literals of a term, nested ones included. *)
Fixpoint boxes (e : expr) : list expr :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => []
  | EBox b => EBox b :: boxes b
  | Lam b | Inj1 b | Inj2 b => boxes b
  | App a b | Pair a b | LetU a b | LetP a b => boxes a ++ boxes b
  | Case a b c => boxes a ++ boxes b ++ boxes c
  end.

Fixpoint ty_at (π : list bool) (T : ty) : option ty :=
  match π, T with
  | [], _ => Some T
  | false :: π', TProd T1 _ => ty_at π' T1
  | true :: π', TProd _ T2 => ty_at π' T2
  | _, _ => None
  end.

Definition node := list nat.

(** The edge of a hop in a box whose parameter has type P. *)
Definition edge_of (P : ty) (h : list bool * list bool) : option (node * node) :=
  match ty_at h.1 P, ty_at h.2 P with
  | Some (TSess s1 _), Some (TSess s2 _) => Some (er_sty s1, er_sty (dual s2))
  | _, _ => None
  end.

Fixpoint omap {A B} (f : A → option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: l => match f x, omap f l with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

Fixpoint ann_lookup (b : expr) (ann : list (expr * ty)) : option ty :=
  match ann with
  | [] => None
  | (b', T) :: ann => if bool_decide (b = b') then Some T else ann_lookup b ann
  end.

(** The edges of one box. A box with hops needs a type in [ann] without
    session variables, so that erased types are not instances of one
    another. *)
Definition box_edges (ann : list (expr * ty)) (e : expr) : option (list (node * node)) :=
  match e with
  | EBox b =>
      match box_hops b with
      | None => None
      | Some [] => Some []
      | Some hs =>
          match ann_lookup e ann with
          | Some (TBox _ 0 _ (TLolli _ _ _ (TLolli _ _ P _))) => omap (edge_of P) hs
          | _ => None
          end
      end
  | _ => Some []
  end.

Definition thread_edges (ann : list (expr * ty)) (e : expr) : option (list (node * node)) :=
  foldr (λ b acc, ocat (box_edges ann b) acc) (Some []) (boxes e).

(** A path of 1 to n edges from x to y. *)
Fixpoint reach (n : nat) (E : list (node * node)) (x y : node) : bool :=
  match n with
  | 0 => false
  | S n' => existsb (λ ab, bool_decide (ab.1 = x) && (bool_decide (ab.2 = y) || reach n' E ab.2 y)) E
  end.

Definition acyclic (E : list (node * node)) : bool :=
  forallb (λ ab, negb (bool_decide (ab.1 = ab.2) || reach (length E) E ab.2 ab.1)) E.

(** R4′ for the threads [ts], with box types derived by [tyd]. *)
Definition r4_ok (tyd : expr → ty → Prop) (ts : expr → Prop) : Prop :=
  ∃ (ann : list (expr * ty)) (E : list (node * node)),
    (∀ b T, (b, T) ∈ ann → tyd b T) ∧ acyclic E = true ∧
    ∀ e, ts e → ∃ E', thread_edges ann e = Some E' ∧ ∀ ab, ab ∈ E' → ab ∈ E.

(** ** R2-recv, advance with fed slots (plan §13)

    R2-recv relaxes R2′ for received payloads. Inside a round, the
    argument of a potentially recursive call is advanced when every
    component of its pair structure is fresh, or is a received payload
    not acted on and the call forces the self of the round's box. A
    link still asks a fresh argument, so a received payload counts as
    advanced when it goes to recursion and not when it is linked.

    A received payload that goes to the self lands in a parameter slot
    of the next round, a path into the parameter's product type. These
    are the fed slots of the box ([feds]). Within a round, a fed slot
    not yet acted on may occur only as the carrier of an action, as the
    pair a let pair takes apart, or as the value a let binds. Each of
    those keeps track of the slot. Any other occurrence, and in
    particular a send of the slot as payload, is rejected. A slot whose
    path is a prefix of a fed path, or extends one, counts as fed.

    The environment records for each variable whether it is fresh, its
    carrier ([car], shared with R4′), and whether it is the self. In
    EBox (Lam b) the parameter is variable 0 of b, at slot path [], and
    the self is variable 1. The flag [ff] switches the fed-slot clause
    on. Without it the starving server below passes. *)

Record rent := RE { re_fr : bool; re_car : car; re_self : bool }.

Definition rno : rent := RE false CNo false.
Definition rget (G : list rent) (x : nat) : rent := default rno (G !! x).
Definition rfr (G : list rent) : list bool := re_fr <$> G.
Definition rcr (G : list rent) : list car := re_car <$> G.

(** A received payload not acted on. *)
Definition rrcv (G : list rent) (e : expr) : bool := is_rcv (ecar (rcr G) e).

Definition rself (G : list rent) (f : expr) : bool :=
  match f with Var x => re_self (rget G x) | _ => false end.

(** Every component is fresh or a received payload. *)
Fixpoint adv (G : list rent) (e : expr) : bool :=
  match e with
  | Pair a b => adv G a && adv G b
  | _ => fresh (rfr G) e || rrcv G e
  end.

(** The slots that the received components of a call argument feed. *)
Fixpoint fedp (G : list rent) (π : list bool) (e : expr) : list (list bool) :=
  match e with
  | Pair a b => fedp G (π ++ [false]) a ++ fedp G (π ++ [true]) b
  | _ => if rrcv G e then [π] else []
  end.

(** The entries a let, a let pair and a case branch bind. *)
Definition rbind1 (G : list rent) (a : expr) : rent := RE (fresh (rfr G) a) (ecar (rcr G) a) false.
Definition rbindp (G : list rent) (e : expr) : list rent :=
  zip_with (λ f c, RE f c false) (pfresh (rfr G) e) (pcar (rcr G) e).
Definition rbindc (G : list rent) (e : expr) : rent := RE (fresh (rfr G) e) (ccar (rcr G) e) false.

(** The fed slots of a box body. Nested boxes are boxes of their own. *)
Fixpoint feds (G : list rent) (e : expr) : list (list bool) :=
  match e with
  | App (App (Konst KForce) f) a => (if rself G f then fedp G [] a else []) ++ feds G f ++ feds G a
  | App (Lam b) a => feds G a ++ feds (rbind1 G a :: G) b
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => feds G e1 ++ feds G e2
  | Lam b => feds (rno :: G) b
  | EBox _ => []
  | LetP e1 e2 => feds G e1 ++ feds (rbindp G e1 ++ G) e2
  | Case e e1 e2 => feds G e ++ feds (rbindc G e :: G) e1 ++ feds (rbindc G e :: G) e2
  | Inj1 e | Inj2 e => feds G e
  | Var _ | EUnit | Konst _ | Chan _ => []
  end.

Fixpoint pref (π ρ : list bool) : bool :=
  match π, ρ with
  | [], _ => true
  | b :: π', c :: ρ' => Bool.eqb b c && pref π' ρ'
  | _ :: _, [] => false
  end.

(** A parameter slot not acted on whose path meets a fed slot. *)
Definition rfed (fd : list (list bool)) (r : rent) : bool :=
  negb (re_fr r) &&
  match re_car r with CPar π => existsb (λ ρ, pref π ρ || pref ρ π) fd | _ => false end.

(** The constants that act on a carrier given as a variable. *)
Definition act_konst (k : konst) : bool :=
  match k with KRecv | KClos | KSel1 | KSel2 | KBra => true | _ => false end.

Definition bbox_env (b : expr) : list rent :=
  match b with
  | Lam _ => [RE false (CPar []) false; RE false CNo true]
  | _ => [RE false CNo true]
  end.

Definition bbox_body (b : expr) : expr := match b with Lam b' => b' | _ => b end.

Fixpoint r2r (ff rnd : bool) (fd : list (list bool)) (G : list rent) (e : expr) : bool :=
  match e with
  | Var x => negb (ff && rnd && rfed fd (rget G x))
  | App (App (Konst KForce) f) a =>
      (negb rnd || negb (pcall_target f) || fresh (rfr G) a || (rself G f && adv G a)) &&
      r2r ff rnd fd G f && r2r ff rnd fd G a
  | App (Konst k) a =>
      (negb rnd || negb (bool_decide (k = KLink)) || fresh (rfr G) a) &&
      match a with
      | Var _ => act_konst k || r2r ff rnd fd G a
      | Pair p (Var _) => if bool_decide (k = KSend) then r2r ff rnd fd G p else r2r ff rnd fd G a
      | _ => r2r ff rnd fd G a
      end
  | App (Lam b) a =>
      match a with Var _ => true | _ => r2r ff rnd fd G a end &&
      r2r ff rnd fd (rbind1 G a :: G) b
  | App e1 e2 => r2r ff rnd fd G e1 && r2r ff rnd fd G e2
  | Lam b => r2r ff rnd fd (rno :: G) b
  | EBox b =>
      let G' := bbox_env b in let b' := bbox_body b in r2r ff true (feds G' b') G' b'
  | LetU e1 e2 => r2r ff rnd fd G e1 && r2r ff rnd fd G e2
  | LetP e1 e2 =>
      match e1 with Var _ => true | _ => r2r ff rnd fd G e1 end &&
      r2r ff rnd fd (rbindp G e1 ++ G) e2
  | Case e e1 e2 =>
      r2r ff rnd fd G e && r2r ff rnd fd (rbindc G e :: G) e1 && r2r ff rnd fd (rbindc G e :: G) e2
  | Pair e1 e2 => r2r ff rnd fd G e1 && r2r ff rnd fd G e2
  | Inj1 e | Inj2 e => r2r ff rnd fd G e
  | EUnit | Konst _ | Chan _ => true
  end.

Definition lf_r2r (e : expr) : bool := r2r true false [] [] e.

(** ** Rank *)

Definition wf_world (W : world) : Prop := well_founded (w_lt W).

(** ** The lock-free fragment *)

Definition lf_r4 (W : world) (p : proc) : Prop :=
  r4_ok (λ b T, ∃ Φ Ψ Δ F, typed W Φ Ψ ∅ Δ F b T) (λ e, e ∈ p.2).

Definition lfptyped (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  gptyped W Σ p T ∧ (∀ e, e ∈ p.2 → lf_r1 e = true) ∧ (∀ e, e ∈ p.2 → lf_r2r e = true) ∧
  lf_r4 W p ∧ wf_world W.

Lemma lfptyped_gptyped W Σ p T : lfptyped W Σ p T → gptyped W Σ p T.
Proof. by intros [? _]. Qed.

(** A source program under the top-level constraint C₀ over n point
    variables (the premises of [live_soundness_source]). Its world is
    [wc0 n C₀]. *)
Definition lfsource (n : nat) (C0 : bcs) (t : expr) (T : ty) : Prop :=
  creation_ok n nofact nofact (λ _, False) C0 ∧ prim T ∧
  gstyped ∅ [(C0, ids n)] [] (∅, None) t T ∧ lf_r1 t = true ∧ lf_r2r t = true ∧
  r4_ok (λ b T, ∃ Φ Ψ Δ F, styped Φ Ψ Δ F b T) (λ e, e = t) ∧ wf_world (wc0 n C0).

Lemma lfsource_gstyped n C0 t T : lfsource n C0 t T → gstyped ∅ [(C0, ids n)] [] (∅, None) t T.
Proof. by intros (_ & _ & ? & _). Qed.

(** ** Rank, general facts *)

(** A world generated without facts orders only by program order. *)
Lemma glt_empty (E L : prel) :
  (∀ x y, ¬ E x y) → (∀ x y, ¬ L x y) → ∀ x y, glt E L x y → pt_off x < pt_off y.
Proof.
  intros HE HL.
  assert (∀ x y, geq E x y → x = y) as Hq.
  { induction 1 as [x y H| | | | | |]; [by destruct (HE x y H)|..]; subst; done. }
  intros x0 y0.
  induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
  - by destruct (HL x y H).
  - unfold pt_shift. simpl. lia.
  - apply Hq in Hx, Hy. by subst.
  - lia.
  - unfold pt_shift, pt_dual. simpl. lia.
Qed.

Lemma wgen_empty_wf N (E L : prel) :
  (∀ x y, ¬ E x y) → (∀ x y, ¬ L x y) → wf_world (wgen N E L).
Proof.
  intros HE HL. apply (Wf_nat.well_founded_lt_compat _ pt_off). intros x y. by apply glt_empty.
Qed.

Lemma Wpo_wf cs : wf_world (Wpo cs).
Proof. unfold Wpo. apply wgen_empty_wf; by intros ? ? []. Qed.

Lemma wc0_top_wf n : wf_world (wc0 n CfstTools.top_C0).
Proof.
  apply wgen_empty_wf.
  - intros x y (? & ? & [] & _).
  - intros x y (? & ? & (f & [] & _) & _).
Qed.

(** Rank from a rank into a well-founded order. A world generated
    without ≡ facts is well founded when the rank rises along program
    order, along x ≺ x̄+1 and along its ≺ facts. The facts may form
    infinite ascending chains. *)
Lemma wgen_rank_wf {A} (R : A → A → Prop) N (E L : prel) (r : point → A) :
  well_founded R → (∀ a b c, R a b → R b c → R a c) →
  (∀ x y, ¬ E x y) → (∀ x y, L x y → R (r x) (r y)) →
  (∀ x, R (r x) (r (pt_shift 1 x))) → (∀ x, R (r x) (r (pt_shift 1 (pt_dual x)))) →
  wf_world (wgen N E L).
Proof.
  intros Hwf Htr HE HL Hs Hd.
  assert (∀ x y, geq E x y → x = y) as Hq.
  { induction 1 as [x y H| | | | | |]; [by destruct (HE x y H)|..]; subst; done. }
  assert (∀ x y, glt E L x y → R (r x) (r y)) as Hlt.
  { induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
    - by apply HL.
    - apply Hs.
    - apply Hq in Hx, Hy. by subst.
    - by eapply Htr.
    - apply Hd. }
  assert (∀ a, Acc R a → ∀ x, r x = a → Acc (glt E L) x) as H.
  { induction 1 as [a _ IH]. intros x <-. constructor. intros y Hy. exact (IH (r y) (Hlt y x Hy) y eq_refl). }
  intros x. exact (H (r x) (Hwf (r x)) x eq_refl).
Qed.

(** The run of a source program starts in [wc0 n C₀]. Its ≺ facts are
    the facts of C₀ read at the constants. *)
Lemma wc0_rank_wf {A} (R : A → A → Prop) n C (r : point → A) :
  well_founded R → (∀ a b c, R a b → R b c → R a c) →
  (∀ x y, bcs_open n C (FLt x y) → R (r (c0_pt n x)) (r (c0_pt n y))) →
  (∀ x, R (r x) (r (pt_shift 1 x))) → (∀ x, R (r x) (r (pt_shift 1 (pt_dual x)))) →
  wf_world (wc0 n C).
Proof.
  intros Hwf Htr HL Hs Hd. apply (wgen_rank_wf R _ _ _ r Hwf Htr); [| |done|done].
  - intros x y (x0 & y0 & [] & _).
  - intros x y (x0 & y0 & H & -> & ->). exact (HL x0 y0 H).
Qed.

Lemma lexlt_wf : well_founded lexlt.
Proof.
  assert (∀ a b, Acc lexlt (a, b)) as H.
  { intros a. induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
    intros b. induction b as [b IHb] using (well_founded_induction Wf_nat.lt_wf).
    constructor. intros [a' b'] [Hlt|[Heq Hlt]]; cbn in *; [by apply IHa|subst; by apply IHb]. }
  intros [a b]. apply H.
Qed.

(** A descending chain refutes Rank. *)
Lemma chain_not_wf W (f : nat → point) : (∀ n, w_lt W (f (S n)) (f n)) → ¬ wf_world W.
Proof.
  intros Hf Hwf.
  assert (∀ x, Acc (w_lt W) x → ∀ n, f n = x → False) as H.
  { induction 1 as [x _ IH]. intros n <-. exact (IH (f (S n)) (Hf n) (S n) eq_refl). }
  exact (H (f 0) (Hwf (f 0)) 0 eq_refl).
Qed.

(** ** Examples *)

Lemma elem_of_single (e t : expr) : e ∈ ({[+ t +]} : gmultiset expr) → e = t.
Proof. apply gmultiset_elem_of_singleton. Qed.

(** The forwarder. fwd forwards the payload it receives on a (Si) to b
    (So), one hop, from Si to the dual of So, which no hop leaves. *)
Definition fw_ann : list (expr * ty) :=
  [(Forwarder.fwd, TBox 2 0 Forwarder.fw_C (TLolli None None TUnit Forwarder.fwd_body))].

Definition fw_E : list (node * node) :=
  default [] (thread_edges fw_ann Forwarder.fw_main).

Lemma fw_E_one : length fw_E = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem fw_lfptyped : lfptyped (Wpo []) ∅ (∅, {[+ Forwarder.fw_main +]}) TUnit.
Proof.
  pose proof (proj1 Wpo_nil_strict') as HW.
  split_and!.
  - split; [apply ptyped_closed_s; [constructor|apply Forwarder.fw_typed]|].
    intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - exists fw_ann, fw_E. split_and!.
    + intros b T Hin. apply list_elem_of_singleton in Hin. injection Hin as -> ->.
      exists ∅, [], [], (∅, None). by apply Forwarder.fwd_typed.
    + vm_compute. reflexivity.
    + intros e ->%elem_of_single. exists fw_E. split; [vm_compute; reflexivity|done].
  - apply Wpo_wf.
Qed.

(** The tail call. No hop. *)
Theorem tc_lfptyped : lfptyped (Wpo []) ∅ (∅, {[+ TailCall.tc_main +]}) TUnit.
Proof.
  split_and!.
  - split; [apply ptyped_closed_s; [constructor|apply TailCall.tc_typed]|].
    intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->%elem_of_single. exists []. split; [vm_compute; reflexivity|done].
  - apply Wpo_wf.
Qed.

(** The recursive CFST scheduler, a source program under the ceiling
    constraint. Rounds of six steps, every end passed on is acted on in
    the round, no hop. *)
Theorem sch_lfsource : lfsource 1 CfstTools.top_C0 CfstScheduler.sch_main TUnit.
Proof.
  split_and!.
  - apply c0_acyclic_creation, CfstTools.top_acyclic.
  - constructor.
  - split; [apply CfstScheduler.sch_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply wc0_top_wf.
Qed.

(** Kobayashi's forwarder server. The guard rejects it. R1, R2′ and R4′
    accept it, because the spawned call takes the fresh end p. *)
Theorem kob_checks :
  lf_r1 KobForwarder.fw_main = true ∧ lf_r2 KobForwarder.fw_main = true ∧
  thread_edges [] KobForwarder.fw_main = Some [].
Proof. vm_compute. auto. Qed.

Theorem kob_not_lfptyped W Σ T : ¬ lfptyped W Σ (∅, {[+ KobForwarder.fw_main +]}) T.
Proof.
  intros [[_ Hg] _]. specialize (Hg _ (proj2 (gmultiset_elem_of_singleton _ _) eq_refl)).
  revert Hg. unfold guarded. vm_compute. discriminate.
Qed.

(** Under the constant world (plan §10.4) the creation facts of the
    reply channels are facts of W, at a constant a. Then Rank fails. *)
Theorem kob_rank_fails W a :
  (∀ x y, KobForwarder.fw_P (FLt x y) →
     w_lt W (pt_inst (plist [pconst a]) x) (pt_inst (plist [pconst a]) y)) →
  ¬ wf_world W.
Proof.
  intros H. apply (chain_not_wf W (λ n, pt_inst (plist [pconst a]) (Pt (payloadv n) 0))).
  intros n. apply H. exists n, true, true. left. reflexivity.
Qed.

(** C1 of plan §10.1, the spawner chain.

      c1 = !(f = λ⟨prev, chat⟩. let (a, b) = new ∗ in
                 let () = spawn (λw. let () = w in let () = recvclose a in close prev) in
                 (force f) ⟨b, send ⟨∗, chat⟩⟩)

    a and b are created at κ[0] when prev sits at κ, and the call is at
    κ[0]. The spawned thread blocks on a while it holds prev. *)
Definition c1_box : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (recvclose (Var 2)) (App EClos (Var 4))))))
      (App (App EForce (Var 5)) (Pair (Var 0) (App ESend (Pair EUnit (Var 2))))))))).

(** C1 passes the guard, R1, R2′ and R4′. The body is harmless. *)
Theorem c1_checks :
  guarded c1_box ∧ lf_r1 c1_box = true ∧ lf_r2 c1_box = true ∧ thread_edges [] c1_box = Some [].
Proof. unfold guarded. vm_compute. auto. Qed.

(** The gate of C1 needs κ[0]ⁿ⁺¹ ≺ κ[0]ⁿ for every n. *)
Definition c1_P (g : fact) : Prop := ∃ n, g = FLt (Pt (payloadv (S n)) 0) (Pt (payloadv n) 0).

(** Rank rejects C1 once these facts are facts of W, at a constant a. *)
Theorem c1_rank_fails W a :
  (∀ x y, c1_P (FLt x y) →
     w_lt W (pt_inst (plist [pconst a]) x) (pt_inst (plist [pconst a]) y)) →
  ¬ wf_world W.
Proof.
  intros H. apply (chain_not_wf W (λ n, pt_inst (plist [pconst a]) (Pt (payloadv n) 0))).
  intros n. apply H. by exists n.
Qed.

(** C3 of plan §10.1, link refresh with a chatter step.

      c3 = !(f = λ⟨y, d⟩. let (a, b) = new ∗ in let () = link ⟨y, a⟩ in
                 (force f) ⟨b, send ⟨∗, d⟩⟩)

    y holds the partner of C. Every round links it to a fresh end and
    goes on with the other fresh end b, so C is never served. *)
Definition c3_box : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ELink (Pair (Var 3) (Var 1)))
      (App (App EForce (Var 5)) (Pair (Var 0) (App ESend (Pair EUnit (Var 2))))))))).

(** The guard and R1 accept C3. R2′ rejects it, because y is linked
    before the round acts on it. *)
Theorem c3_checks : guarded c3_box ∧ lf_r1 c3_box = true ∧ lf_r2 c3_box = false.
Proof. unfold guarded. vm_compute. auto. Qed.

Theorem c3_not_lfptyped W Σ T : ¬ lfptyped W Σ (∅, {[+ c3_box +]}) T.
Proof.
  intros (_ & _ & H2 & _). specialize (H2 _ (proj2 (gmultiset_elem_of_singleton _ _) eq_refl)).
  revert H2. vm_compute. discriminate.
Qed.

(** TreeSum (plan §10.5): R1 rejects it, because the left call's result
    is still used by the frame of the right call. *)
Theorem tsum_r1_fails : lf_r1 TreeSum.tsum = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Stage 3c: R2-recv (plan §13) *)

(** The starving server. Each round receives an end x on c, sends back
    the end h that the previous round received, and recurs with ⟨c, x⟩.

      starve = !(f = λp. let (c, h) = p in let (x, c) = recv c in
                   let (c, u) = ⟨send ⟨h, c⟩, ∗⟩ in let () = u in (force f) ⟨c, x⟩)

    x feeds the slot of h, and the next round sends h on before it acts
    on it. An end can bounce between the server and a client forever,
    and its partner waits. The guard, R1 and R4′ accept it, and so does
    R2-recv without the fed-slot clause. With the clause it fails. *)
Definition starve_body : expr :=
  LetP (Var 0) (LetP (App ERecv (Var 1))
    (LetP (Pair (App ESend (Pair (Var 2) (Var 0))) EUnit) (LetU (Var 0)
      (App (App EForce (Var 7)) (Pair (Var 1) (Var 3)))))).

Definition starve_box : expr := EBox (Lam starve_body).

Theorem starve_checks :
  guarded starve_box ∧ lf_r1 starve_box = true ∧ thread_edges [] starve_box = Some [] ∧
  r2r false false [] [] starve_box = true ∧ lf_r2r starve_box = false ∧ lf_r2 starve_box = false.
Proof. unfold guarded. split_and!; vm_compute; reflexivity. Qed.

(** The slot it feeds is the second component of the parameter. *)
Theorem starve_feds : feds (bbox_env (Lam starve_body)) starve_body = [[true]].
Proof. vm_compute. reflexivity. Qed.

Theorem starve_not_lfptyped W Σ T : ¬ lfptyped W Σ (∅, {[+ starve_box +]}) T.
Proof.
  intros (_ & _ & H2 & _). specialize (H2 _ (proj2 (gmultiset_elem_of_singleton _ _) eq_refl)).
  revert H2. vm_compute. discriminate.
Qed.

(** R2-recv on the earlier examples. Kobayashi's forwarder and C1 pass
    it and stay out by the guard and by Rank. C3 still fails it, by the
    link clause alone. TreeSum fails it as it fails R2′, besides R1. *)
Theorem r2r_earlier :
  lf_r2r KobForwarder.fw_main = true ∧ lf_r2r c1_box = true ∧
  lf_r2r c3_box = false ∧ r2r false false [] [] c3_box = false ∧
  lf_r2r TreeSum.tsum = false.
Proof. split_and!; vm_compute; reflexivity. Qed.

(** ReceivedChain.v: R2′ rejects it, R2-recv accepts it. The received
    payload d goes to the self inside a spawn and feeds the parameter
    slot, which the next round acts on first. *)
Theorem rc_r2_fails : lf_r2 ReceivedChain.ch_main = false.
Proof. vm_compute. reflexivity. Qed.

Theorem rc_lfptyped : lfptyped (Wpo []) ∅ (∅, {[+ ReceivedChain.ch_main +]}) TUnit.
Proof.
  split_and!.
  - split; [apply ptyped_closed_s; [constructor|apply ReceivedChain.ch_typed]|].
    intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - intros e ->%elem_of_single. vm_compute. reflexivity.
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->%elem_of_single. exists []. split; [vm_compute; reflexivity|done].
  - apply Wpo_wf.
Qed.

(** The growing ring (GrowRing.v, Padovani III.7). R2′ rejects it,
    because the received z goes to the self. Under the constant world
    the facts of e are facts of W. They climb without end, and the rank
    2·depth + offset still makes W well founded. *)
Theorem rg_r2_fails : lf_r2 GrowRing.rg_main = false.
Proof. vm_compute. reflexivity. Qed.

Lemma rg_wf : wf_world (wc0 1 GrowRing.rg0_C).
Proof.
  apply (wc0_rank_wf lt 1 _ GrowRing.rg_rank Wf_nat.lt_wf); [intros a b c; lia| | |].
  - intros x y H. rewrite !GrowRing.rg_rank_c0. apply bcs_open_nil in H as [H _].
    by apply GrowRing.rg0_rank.
  - intros x. unfold GrowRing.rg_rank, pt_shift. cbn. lia.
  - intros x. unfold GrowRing.rg_rank, pt_shift, pt_dual. cbn. lia.
Qed.

Theorem rg_lfsource : lfsource 1 GrowRing.rg0_C GrowRing.rg_main TUnit.
Proof.
  split_and!.
  - apply c0_acyclic_creation, GrowRing.rg0_acyclic.
  - constructor.
  - split; [apply GrowRing.rg_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply rg_wf.
Qed.

(** The alternating bit protocol (ABP.v, Padovani III.8). No end
    travels, so R2′ already accepts it. The world has the ceiling θ
    above three interleaved ascending chains, and the pair rank makes it
    well founded. *)
Theorem abp_r2 : lf_r2 ABP.abp_main = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abp_wf : wf_world (wc0 4 ABP.abp0_C).
Proof.
  apply (wc0_rank_wf lexlt 4 _ ABP.abp_rank lexlt_wf); [unfold lexlt; intros a b c; lia| | |].
  - intros x y H. rewrite !ABP.abp_rank_c0. apply bcs_open_nil in H as [H _].
    by apply ABP.abp_rank_facts.
  - apply ABP.abp_rank_shift.
  - intros x. exact (ABP.abp_rank_shift x).
Qed.

Theorem abp_lfsource : lfsource 4 ABP.abp0_C ABP.abp_main TUnit.
Proof.
  split_and!.
  - apply c0_acyclic_creation, ABP.abp0_acyclic.
  - constructor.
  - split; [apply ABP.abp_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply abp_wf.
Qed.
