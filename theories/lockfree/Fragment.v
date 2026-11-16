(** * The static rules of the lock-free fragment (lock-freedom-plan.md §10.2)

    Stage 3a. The rules are checks next to the guard of liveness/Guard.v.
    No relation changes.

    - [pcall_target]: a force is a potentially recursive call when it
      forces a box literal whose body forces, or anything else (a box
      variable, a parameter, a received box).
    - R1 ([r1]): a potentially recursive call sits in tail position of
      its thread. Threads are the root term, the body of a spawned λ and
      the body of a box under its λs. A call is force f applied to the
      point values of the box and then to its argument ([fhead]). Let, let pair and case pass
      tail position to their continuation and branches, and an applied
      λ passes it to its body. Every other frame is a frame that still
      holds or uses something, the call's results included, so the call
      is rejected there. This is the plan's R1 and not R1′.
    - R2′ ([r2]): inside a box body (a round) the argument of every
      potentially recursive call and of every link is fresh. Fresh
      means built from variables that the round bound to the result of
      an action or of new, from send, select, branch, new, unit,
      constants, boxes and point values. The point parameters of a box
      are fresh. The parameter, the self and a received payload are
      not.
    - R4′ ([r4_ok]): a forwarding hop is a send, inside a box body, of a
      payload received in the same body and not acted on. Its two
      carriers are traced back to the box parameter as paths into its
      product type. The session types at those paths come from a type
      of the box that the typing judgment derives ([ann]), and an edge
      runs from the receiving carrier's type to the dual of the sending
      carrier's type, both with points and constraints erased. The
      graph of all hops is acyclic. Expressions carry no types, so this
      rule reads its types off typings of the boxes, not off the term.
      Under §17.6 a link inside a box body adds edges to the same graph,
      the hand-off graph, and replaces the link clause of R2′.
    - Rank ([wf_world]): ≺ of the world is well founded.
    - R2-recv ([r2r], stage 3c, plan §13) replaces R2′ in the fragment.
      A received payload passed to a call of the self counts as
      advanced, and every slot it feeds must be acted on before the
      round passes it on. [r2] stays as the stricter rule. The fragment
      asks [lf_r2h], R2-recv without the link clause.
    - Budgets ([with_budgets], [src_world], plan §17.6, §17.8, revised
      after stage L6a). The refill w_bud and the floor w_pay of the
      world come from the root graph ([root_edges]) and from the
      stretch bound L ([stretch_len]). The root graph bounds the
      hand-offs of payloads by the roots of their carriers, inside
      boxes and outside, and it is read off the term. No session type
      enters the budgets, so there is no map from points to types to
      check.

    Syntactic points (sharp edges 173): a box that creates a channel
    takes its points as leading λs, and the hypotheses of a closed
    program name constants. R2-recv reads a leading λ as a point
    parameter only when the box type in its annotation says TPt.

    [lfptyped] is [gptyped] with R1, R2-recv, the hand-off graph and
    Rank. [lfsource] is
    the same for a closed source program over the hypotheses of its
    top-level channels, the form in which the examples are typed under
    the constant world (sharp edges 172). Its Rank is asked of the world
    where the run starts, which has the creation facts ([cworld]), and
    it asks an acyclic root graph ([root_ok]). *)

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
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => false
  | Lam e | EBox e | Inj1 e | Inj2 e => has_force e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => has_force e1 || has_force e2
  | Case e e1 e2 => has_force e || has_force e1 || has_force e2
  end.

(** force f is potentially recursive unless f is a box literal whose
    body never forces. *)
Definition pcall_target (f : expr) : bool :=
  match f with EBox b => has_force b | _ => true end.

(** The forced value of a force applied to any number of arguments. A
    box that creates a channel takes its point values first and its
    channels last (sharp edges 173), so a call is force f applied to
    the point values and then to the channel argument. *)
Fixpoint fhead (e : expr) : option expr :=
  match e with
  | App (Konst KForce) f => Some f
  | App e1 _ => fhead e1
  | _ => None
  end.

(** The term is a potentially recursive call, applied or not. *)
Definition pcall (e : expr) : bool :=
  match fhead e with Some f => pcall_target f | None => false end.

(** ** R1, empty future at a potentially recursive call

    [tl] holds when the subterm is in tail position of its thread. The
    forced value and every argument of a call are checked outside tail
    position, and the leading λs of a box, which take point values,
    keep the tail position for the body. *)
Fixpoint r1 (tl : bool) (e : expr) : bool :=
  match e with
  | App e1 e2 =>
      match fhead e with
      | Some f =>
          (negb (pcall_target f) || tl) &&
          (fix sp (a : expr) : bool := match a with App a1 a2 => sp a1 && r1 false a2 | _ => true end) e1 &&
          r1 false e2
      | None =>
          match e1, e2 with
          | Konst KSpawn, Lam b => r1 true b
          | Lam b, _ => r1 false e2 && r1 tl b
          | _, _ => r1 false e1 && r1 false e2
          end
      end
  | Lam b => r1 false b
  | EBox b =>
      match b with
      | Lam _ => (fix lams (a : expr) : bool := match a with Lam a' => lams a' | _ => r1 true a end) b
      | _ => r1 false b
      end
  | LetU e1 e2 | LetP e1 e2 => r1 false e1 && r1 tl e2
  | Case e e1 e2 => r1 false e && r1 tl e1 && r1 tl e2
  | Pair e1 e2 => r1 false e1 && r1 false e2
  | Inj1 e | Inj2 e => r1 false e
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => true
  end.

Definition lf_r1 (e : expr) : bool := r1 true e.

(** ** R2′, advance before recursion and before link *)

(** The result of these constants is fresh: the continuation of an end
    acted on, a pair of new ends, unit, or a point value. *)
Definition kfresh (k : konst) : bool :=
  match k with
  | KSend | KSel1 | KSel2 | KBra | KNew | KClos | KLink | KSpawn | KPay _ | KSucc => true
  | KRecv | KForce => false
  end.

(** [S !! x = Some true]: the variable x was bound in this round to
    something acted on or created, or it is a point parameter of the
    round's box. A point value holds no channel and counts as fresh. *)
Fixpoint fresh (S : list bool) (e : expr) : bool :=
  match e with
  | Var x => default false (S !! x)
  | EUnit | Konst _ | EBox _ | EPt _ => true
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
    outer variable, no parameter and not the self is fresh. The leading
    λs of a box are parameters as well. A point value built by EPt,
    KPay or KSucc is fresh, a point parameter passed on unchanged is
    not, because [r2] reads no type that would tell a point parameter
    from a channel. Every argument of a
    potentially recursive call is checked, the point values and the
    parameter, because a call applied to k arguments contains the call
    applied to the first k - 1. *)
Fixpoint r2 (rnd : bool) (S : list bool) (e : expr) : bool :=
  match e with
  | App e1 e2 =>
      match fhead e, e1 with
      | Some _, Konst _ => r2 rnd S e2
      | Some f, _ => (negb rnd || negb (pcall_target f) || fresh S e2) && r2 rnd S e1 && r2 rnd S e2
      | None, Konst KLink => (negb rnd || fresh S e2) && r2 rnd S e2
      | None, Lam b => r2 rnd S e2 && r2 rnd (fresh S e2 :: S) b
      | None, _ => r2 rnd S e1 && r2 rnd S e2
      end
  | Lam b => r2 rnd (false :: S) b
  | EBox b =>
      (fix lams (S' : list bool) (a : expr) : bool :=
         match a with
         | Lam a' => lams (false :: S') a'
         | _ => r2 true S' a
         end) [] b
  | LetU e1 e2 => r2 rnd S e1 && r2 rnd S e2
  | LetP e1 e2 => r2 rnd S e1 && r2 rnd (pfresh S e1 ++ S) e2
  | Case e e1 e2 => r2 rnd S e && r2 rnd (fresh S e :: S) e1 && r2 rnd (fresh S e :: S) e2
  | Pair e1 e2 => r2 rnd S e1 && r2 rnd S e2
  | Inj1 e | Inj2 e => r2 rnd S e
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => true
  end.
Definition lf_r2 (e : expr) : bool := r2 false [] e.

(** ** The hand-off graph: R4′ and the link clause of R2′ (plan §17.6)

    R4′ bounded forwarding by a graph over session types up to points,
    and R2′ asked the arguments of a link inside a round to be fresh.
    Under §17.6 both are edges of one graph, the hand-off graph, which
    must be acyclic. Its nodes are session types up to points. A
    forward, a send inside a box body of a payload received in the same
    body and not acted on, adds the edge of R4′, from the type of the
    receiving carrier to the dual of the type of the sending carrier. A
    link ⟨u, v⟩ inside a box body hands the partner of u over to the
    partner of v and the partner of v over to the partner of u. It adds
    edges from the type of u to the type of the partner of v, and from
    the type of v to the type of the partner of u. C3 closes a cycle in
    one round: y is linked to a fresh a, and b, the partner of a, is
    the next round's y. *)

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
  | TPt _ => [7]
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

(** What a variable of a box body is, for hand-offs: a carrier that
    descends from the parameter at a path into its product type (false
    for the left component), a payload received on such a carrier and
    not acted on (None when the carrier is unknown), the pair that the
    new with id i returned, one end of it (false for the first
    component), the self, or none of these. The id of a new is the
    length of the environment where its pair is bound, so two news on
    one path have different ids. *)
Inductive car := CNo | CPar (π : list bool) | CRcv (o : option (list bool))
  | CNewP (i : nat) | CNew (i : nat) (s : bool) | CSelf.

Definition car_of (G : list car) (x : nat) : car := default CNo (G !! x).

Definition is_rcv (c : car) : bool := match c with CRcv _ => true | _ => false end.

(** An action keeps the carrier it acts on. *)
Definition keep_par (c : car) : car :=
  match c with CPar π => CPar π | CNew i s => CNew i s | _ => CNo end.

(** The carrier an expression denotes. Send and select continue their
    carrier. *)
Fixpoint ecar (G : list car) (e : expr) : car :=
  match e with
  | Var x => car_of G x
  | App (Konst KSend) (Pair _ c) => keep_par (ecar G c)
  | App (Konst KSel1) c | App (Konst KSel2) c => keep_par (ecar G c)
  | App (Konst KNew) _ => CNewP (length G)
  | _ => CNo
  end.

(** The carriers a let pair binds, index 0 first. *)
Definition pcar (G : list car) (e : expr) : list car :=
  match e with
  | App (Konst KRecv) c =>
      match ecar G c with
      | CPar π => [CPar π; CRcv (Some π)]
      | CNew i s => [CNew i s; CRcv None]
      | _ => [CNo; CRcv None]
      end
  | Var x =>
      match car_of G x with
      | CPar π => [CPar (π ++ [true]); CPar (π ++ [false])]
      | CRcv o => [CRcv o; CRcv o]
      | CNewP i => [CNew i true; CNew i false]
      | _ => [CNo; CNo]
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
  | EUnit | Konst _ | Chan _ _ | EPt _ => false
  | Lam b | EBox b => mentions (CNo :: G) b
  | App a b | Pair a b | LetU a b => mentions G a || mentions G b
  | LetP a b => mentions G a || mentions (CNo :: CNo :: G) b
  | Inj1 a | Inj2 a => mentions G a
  | Case a b c => mentions G a || mentions (CNo :: G) b || mentions (CNo :: G) c
  end.

Definition ocat {A} (a b : option (list A)) : option (list A) :=
  match a, b with Some x, Some y => Some (x ++ y) | _, _ => None end.

(** An end that a link names: a parameter slot, or an end of a new. *)
Inductive ref := RPar (π : list bool) | RNew (i : nat) (s : bool).

Definition ref_of (c : car) : option ref :=
  match c with CPar π => Some (RPar π) | CNew i s => Some (RNew i s) | _ => None end.

(** The items of a box body: a forward between two carrier paths
    (receiving, sending), a link of two ends, and an end s of the new i
    passed to the self at the parameter slot π. *)
Inductive hitem :=
  | HFwd (π1 π2 : list bool)
  | HLink (r1 r2 : ref)
  | HBind (i : nat) (s : bool) (π : list bool).

Definition handoff (h : hitem) : bool := match h with HBind _ _ _ => false | _ => true end.

(** The ends of news that an argument of the self passes at slots. *)
Fixpoint binds (G : list car) (π : list bool) (e : expr) : list hitem :=
  match e with
  | Pair a b => binds G (π ++ [false]) a ++ binds G (π ++ [true]) b
  | _ => match ecar G e with CNew i s => [HBind i s π] | _ => [] end
  end.

Definition is_self (G : list car) (f : expr) : bool :=
  match f with Var x => match car_of G x with CSelf => true | _ => false end | _ => false end.

(** The items of a box body. None when a received payload is sent in a
    form whose carriers cannot be traced, or when a link names an end
    that is neither a parameter slot nor an end of a new. Nested boxes
    are boxes of their own. *)
Fixpoint hops (G : list car) (e : expr) : option (list hitem) :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => Some []
  | App (Konst KSend) (Pair p c) =>
      let rest := ocat (hops G p) (hops G c) in
      if mentions G p then
        match ecar G p, ecar G c with
        | CRcv (Some π1), CPar π2 => ocat (Some [HFwd π1 π2]) rest
        | _, _ => None
        end
      else rest
  | App (Konst KLink) (Pair u v) =>
      match ref_of (ecar G u), ref_of (ecar G v) with
      | Some r1, Some r2 => ocat (Some [HLink r1 r2]) (ocat (hops G u) (hops G v))
      | _, _ => None
      end
  | App (Konst KLink) _ => None
  | Lam b => hops (CNo :: G) b
  | App (Lam b) a => ocat (hops G a) (hops (ecar G a :: G) b)
  | App e1 e2 =>
      let bd := match fhead e, e1 with
                | Some f, App _ _ => if is_self G f then binds G [] e2 else []
                | _, _ => []
                end in
      ocat (Some bd) (ocat (hops G e1) (hops G e2))
  | Pair e1 e2 | LetU e1 e2 => ocat (hops G e1) (hops G e2)
  | LetP e1 e2 => ocat (hops G e1) (hops (pcar G e1 ++ G) e2)
  | Inj1 e | Inj2 e => hops G e
  | Case e e1 e2 =>
      ocat (hops G e) (ocat (hops (ccar G e :: G) e1) (hops (ccar G e :: G) e2))
  end.

(** A box body sits under the λs of the box. The leading λs take point
    values and the innermost takes the parameter (sharp edges 173). The
    environment of the body has the parameter at 0, the point
    parameters above it and the self last. *)
Fixpoint nlams (e : expr) : nat := match e with Lam e' => S (nlams e') | _ => 0 end.
Fixpoint bbody (e : expr) : expr := match e with Lam e' => bbody e' | _ => e end.

Definition benv {A} (par pt self : A) (n : nat) : list A :=
  match n with 0 => [self] | S m => par :: repeat pt m ++ [self] end.

Definition box_hops (b : expr) : option (list hitem) :=
  hops (benv (CPar []) CNo CSelf (nlams b)) (bbody b).

(** The box literals of a term, nested ones included. *)
Fixpoint boxes (e : expr) : list expr :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => []
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

(** The node of the session type at path π of the parameter type P,
    dualized when d holds. *)
Definition node_at (P : ty) (π : list bool) (d : bool) : option node :=
  match ty_at π P with Some (TSess s _) => Some (er_sty (if d then dual s else s)) | _ => None end.

Fixpoint omap {A B} (f : A → option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: l => match f x, omap f l with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

(** The slots at which the next round holds the end s of the new i, with
    true when the slot holds its partner, so that its type is the dual. *)
Definition new_slots (hs : list hitem) (i : nat) (s : bool) : list (list bool * bool) :=
  hs ≫= (λ h, match h with
              | HBind j t π => if bool_decide (j = i) then [(π, negb (Bool.eqb t s))] else []
              | _ => []
              end).

(** The slots that give the type of an end and of its partner. *)
Definition ref_slots (hs : list hitem) (r : ref) : list (list bool * bool) :=
  match r with RPar π => [(π, false)] | RNew i s => new_slots hs i s end.
Definition peer_slots (hs : list hitem) (r : ref) : list (list bool * bool) :=
  match r with RPar π => [(π, true)] | RNew i s => new_slots hs i (negb s) end.

(** The types at the slots. An end that reaches no slot has no type the
    check can read, and the box is rejected. *)
Definition nodes_of (P : ty) (sl : list (list bool * bool)) : option (list node) :=
  match sl with [] => None | _ => omap (λ pd, node_at P pd.1 pd.2) sl end.

Definition pairs {A} (xs ys : list A) : list (A * A) := xs ≫= (λ x, (λ y, (x, y)) <$> ys).

(** The edges of one item in a box whose parameter has type P. *)
Definition item_edges (P : ty) (hs : list hitem) (h : hitem) : option (list (node * node)) :=
  match h with
  | HFwd π1 π2 =>
      match node_at P π1 false, node_at P π2 true with Some a, Some b => Some [(a, b)] | _, _ => None end
  | HLink r1 r2 =>
      match nodes_of P (ref_slots hs r1), nodes_of P (peer_slots hs r2),
            nodes_of P (ref_slots hs r2), nodes_of P (peer_slots hs r1) with
      | Some a1, Some b2, Some a2, Some b1 => Some (pairs a1 b2 ++ pairs a2 b1)
      | _, _, _, _ => None
      end
  | HBind _ _ _ => Some []
  end.

Fixpoint ann_lookup (b : expr) (ann : list (expr * ty)) : option ty :=
  match ann with
  | [] => None
  | (b', T) :: ann => if bool_decide (b = b') then Some T else ann_lookup b ann
  end.

(** The parameter type under n point parameters. *)
Fixpoint peel (n : nat) (T : ty) : option ty :=
  match n, T with
  | 0, TLolli _ _ P _ => Some P
  | S n', TLolli _ _ (TPt _) T' => peel n' T'
  | _, _ => None
  end.

(** The edges of one box. A box with hand-offs needs a type in [ann]
    without session variables, so that erased types are not instances
    of one another. *)
Definition box_edges (ann : list (expr * ty)) (e : expr) : option (list (node * node)) :=
  match e with
  | EBox b =>
      match box_hops b with
      | None => None
      | Some hs =>
          if existsb handoff hs then
            match ann_lookup e ann, nlams b with
            | Some (TBox _ 0 _ (TLolli _ _ _ T)), S n =>
                match peel n T with
                | Some P => match omap (item_edges P hs) hs with Some ls => Some (concat ls) | None => None end
                | None => None
                end
            | _, _ => None
            end
          else Some []
      end
  | _ => Some []
  end.

Definition thread_edges (ann : list (expr * ty)) (e : expr) : option (list (node * node)) :=
  foldr (λ b acc, ocat (box_edges ann b) acc) (Some []) (boxes e).

(** A path of 1 to n edges from x to y. Graphs are over any type with
    decidable equality. Here the nodes are session types up to points,
    and in the budgets below they are root names. *)
Fixpoint reach {A} `{EqDecision A} (n : nat) (E : list (A * A)) (x y : A) : bool :=
  match n with
  | 0 => false
  | S n' => existsb (λ ab, bool_decide (ab.1 = x) && (bool_decide (ab.2 = y) || reach n' E ab.2 y)) E
  end.

Definition acyclic {A} `{EqDecision A} (E : list (A * A)) : bool :=
  forallb (λ ab, negb (bool_decide (ab.1 = ab.2) || reach (length E) E ab.2 ab.1)) E.

(** The hand-off graph of the threads [ts] is acyclic, with box types
    derived by [tyd]. The name stays from R4′. *)
Definition r4_ok (tyd : expr → ty → Prop) (ts : expr → Prop) : Prop :=
  ∃ (ann : list (expr * ty)) (E : list (node * node)),
    (∀ b T, (b, T) ∈ ann → tyd b T) ∧ acyclic E = true ∧
    ∀ e, ts e → ∃ E', thread_edges ann e = Some E' ∧ ∀ ab, ab ∈ E' → ab ∈ E.

(** ** R2-recv, advance with fed slots (plan §13)

    R2-recv relaxes R2′ for received payloads. Inside a round, the
    argument of a potentially recursive call is advanced when every
    component of its pair structure is fresh, or is a received payload
    not acted on and the call forces the self of the round's box. The
    point values a call takes before its argument are fresh. In [r2r]
    a link still asks a fresh argument, so a received payload counts as
    advanced when it goes to recursion and not when it is linked. Under
    §17.6 the link clause moves into the hand-off graph, and the
    fragment asks [lf_r2h], R2-recv without it.

    A received payload that goes to the self lands in a parameter slot
    of the next round, a path into the parameter's product type. These
    are the fed slots of the box ([feds]). Within a round, a fed slot
    not yet acted on may occur only as the carrier of an action, as the
    pair a let pair takes apart, or as the value a let binds. Each of
    those keeps track of the slot. Any other occurrence, and in
    particular a send of the slot as payload, is rejected. A slot whose
    path is a prefix of a fed path, or extends one, counts as fed.

    The environment records for each variable whether it is fresh, its
    carrier ([car], shared with the hand-off graph), and whether it is
    the self. In a box body the parameter is variable 0, at slot path
    [], the other leading λs follow, and the self is last
    ([bbox_envk]). A leading λ is a point parameter, and fresh, only
    when the box type says that it takes TPt ([box_npt]). The flag [ff] switches the fed-slot clause on.
    Without it the starving server below passes. The flag [lk]
    switches the link clause on. *)

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
  | App e1 e2 =>
      match fhead e, e1 with
      | Some f, App _ _ => if rself G f then fedp G [] e2 else []
      | _, _ => []
      end ++
      match e1 with
      | Lam b => feds G e2 ++ feds (rbind1 G e2 :: G) b
      | _ => feds G e1 ++ feds G e2
      end
  | Pair e1 e2 | LetU e1 e2 => feds G e1 ++ feds G e2
  | Lam b => feds (rno :: G) b
  | EBox _ => []
  | LetP e1 e2 => feds G e1 ++ feds (rbindp G e1 ++ G) e2
  | Case e e1 e2 => feds G e ++ feds (rbindc G e :: G) e1 ++ feds (rbindc G e :: G) e2
  | Inj1 e | Inj2 e => feds G e
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => []
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

(** The environment of a box body whose k outermost λs take point
    values. Those are fresh. The other leading λs are ordinary
    parameters and are not fresh. *)
Definition bbox_envk (k : nat) (b : expr) : list rent :=
  match nlams b with
  | 0 => [RE false CNo true]
  | S m => RE false (CPar []) false :: repeat rno (m - k) ++ repeat (RE true CNo false) k ++ [RE false CNo true]
  end.

Definition bbox_env (b : expr) : list rent := bbox_envk 0 b.

(** The number of leading point parameters that a box type states:
    □(∀…. ∗ ⊸ TPt x₁ ⊸ … ⊸ TPt xₖ ⊸ …). *)
Fixpoint npt (T : ty) : nat := match T with TLolli _ _ (TPt _) T' => S (npt T') | _ => 0 end.

Definition box_npt (ann : list (expr * ty)) (e : expr) : nat :=
  match ann_lookup e ann with Some (TBox _ _ _ (TLolli _ _ _ T)) => npt T | _ => 0 end.

Definition bbox_body (b : expr) : expr := bbody b.

Fixpoint r2x (lk : bool) (pts : expr → nat) (ff rnd : bool) (fd : list (list bool)) (G : list rent) (e : expr) : bool :=
  match e with
  | Var x => negb (ff && rnd && rfed fd (rget G x))
  | App e1 e2 =>
      match fhead e, e1 with
      | Some f, App _ _ =>
          (negb rnd || negb (pcall_target f) || fresh (rfr G) e2 || (rself G f && adv G e2)) &&
          r2x lk pts ff rnd fd G e1 && r2x lk pts ff rnd fd G e2
      | _, Konst k =>
          (negb rnd || negb lk || negb (bool_decide (k = KLink)) || fresh (rfr G) e2) &&
          match e2 with
          | Var _ => act_konst k || r2x lk pts ff rnd fd G e2
          | Pair p (Var _) => if bool_decide (k = KSend) then r2x lk pts ff rnd fd G p else r2x lk pts ff rnd fd G e2
          | _ => r2x lk pts ff rnd fd G e2
          end
      | _, Lam b =>
          match e2 with Var _ => true | _ => r2x lk pts ff rnd fd G e2 end &&
          r2x lk pts ff rnd fd (rbind1 G e2 :: G) b
      | _, _ => r2x lk pts ff rnd fd G e1 && r2x lk pts ff rnd fd G e2
      end
  | Lam b => r2x lk pts ff rnd fd (rno :: G) b
  | EBox b =>
      let k := match nlams b with 0 => 0 | S m => Nat.min m (pts (EBox b)) end in
      let G' := bbox_envk k b in
      (fix lams (a : expr) : bool :=
         match a with Lam a' => lams a' | _ => r2x lk pts ff true (feds G' a) G' a end) b
  | LetU e1 e2 => r2x lk pts ff rnd fd G e1 && r2x lk pts ff rnd fd G e2
  | LetP e1 e2 =>
      match e1 with Var _ => true | _ => r2x lk pts ff rnd fd G e1 end &&
      r2x lk pts ff rnd fd (rbindp G e1 ++ G) e2
  | Case e e1 e2 =>
      r2x lk pts ff rnd fd G e && r2x lk pts ff rnd fd (rbindc G e :: G) e1 && r2x lk pts ff rnd fd (rbindc G e :: G) e2
  | Pair e1 e2 => r2x lk pts ff rnd fd G e1 && r2x lk pts ff rnd fd G e2
  | Inj1 e | Inj2 e => r2x lk pts ff rnd fd G e
  | EUnit | Konst _ | Chan _ _ | EPt _ => true
  end.

(** R2-recv with the link clause, as stage 3c stated it. *)
Definition r2r (ff rnd : bool) (fd : list (list bool)) (G : list rent) (e : expr) : bool :=
  r2x true (λ _, 0) ff rnd fd G e.

Definition lf_r2r (e : expr) : bool := r2r true false [] [] e.

(** R2-recv without the link clause, which the hand-off graph replaces
    (plan §17.6). A leading λ of a box counts as a point parameter, and
    so as fresh, only when the box type in the annotation [ann] says
    that its argument is TPt. *)
Definition lf_r2h (ann : list (expr * ty)) (e : expr) : bool := r2x false (box_npt ann) true false [] [] e.

(** R2-recv for the threads [ts], with box types derived by [tyd]. *)
Definition r2h_ok (tyd : expr → ty → Prop) (ts : expr → Prop) : Prop :=
  ∃ ann : list (expr * ty), (∀ b T, (b, T) ∈ ann → tyd b T) ∧ ∀ e, ts e → lf_r2h ann e = true.

(** ** The root graph (stage L6a, the floors of the budgets)

    The floor w_pay k must drop by a stretch at every hand-off of a
    payload that its receiver passes on without acting on it, and it
    must not drop elsewhere. §17.6 read the floor off the session type
    of the end at k, given as a map from points to types. That map is
    not checked, and no check can read it off a derivation, because the
    derivation instantiates the points of a box at its calls and the
    term does not record the instances. Under syntactic points the term
    records the root of every point instead. A new takes a point value
    built from literals by x ↦ x[i] and x ↦ x + 1, and every point a run
    reaches has the root of a literal (shift, payload, select, branch
    and dual keep the root). So the floors are keyed on roots, and the
    graph that bounds the hand-offs is a graph over roots.

    An edge r₁ → r₂ means that a payload received on a carrier with root
    r₁ is passed on, not acted on, along a carrier with root r₂. Three
    kinds of hand-off give edges.
    - A forward inside a box body ([HFwd] of [hops]) between two
      parameter slots. Every call of the box from outside a box must
      pass ends of top-level news at both slots, and every call of the
      self must pass at each of the two slots the continuation of the
      same slot ([stab]), so that the slot keeps its root from round to
      round. One edge per call site.
    - A forward outside boxes, in the code of a thread ([troots]): a
      send of a received payload, not acted on, along an end of a
      top-level new.
    - A link outside boxes of a received payload, not acted on, with an
      end of a top-level new. A link is accounted like a send of the
      one end along the other (decision of 2026-11-16).
    A received payload not acted on may occur only as the payload of a
    send, as the carrier of an action, as the value a let, a let pair, a
    case or an applied λ binds, inside a spawned or applied λ, and,
    inside a box, as a component of the argument of the self (R2-recv).
    Any other occurrence would hand it on along a path the graph does
    not see, and the program is rejected ([troots], [bleak]). Links
    inside boxes stay with the hand-off graph above, whose link edges
    are self-loops. Links outside boxes are not rejected. *)

(** The root of a point value. *)
Fixpoint proot (e : expr) : option pname :=
  match e with
  | EPt x => Some (pt_root x)
  | App (Konst (KPay _)) a | App (Konst KSucc) a => proot a
  | _ => None
  end.

(** What a variable of the code of a thread denotes. It is a box
    literal, the pair of a top-level new with its root, an end of one, a
    payload received and not acted on (with the root of its carrier when
    known), a pair of these, or none of these. *)
Inductive tcar := TCNo | TCBox (b : expr) | TCNewP (r : pname) | TCEnd (r : pname)
  | TCRcv (o : option pname) | TCPair (c1 c2 : tcar).

Definition tcar_of (G : list tcar) (x : nat) : tcar := default TCNo (G !! x).
Definition tc_rcv (c : tcar) : bool := match c with TCRcv _ => true | _ => false end.
Definition tc_keep (c : tcar) : tcar := match c with TCEnd r => TCEnd r | _ => TCNo end.

Fixpoint tecar (G : list tcar) (e : expr) : tcar :=
  match e with
  | Var x => tcar_of G x
  | EBox _ => TCBox e
  | Pair a b => TCPair (tecar G a) (tecar G b)
  | App (Konst KSend) (Pair _ c) => tc_keep (tecar G c)
  | App (Konst KSel1) c | App (Konst KSel2) c => tc_keep (tecar G c)
  | App (Konst KNew) v => match proot v with Some r => TCNewP r | None => TCNo end
  | _ => TCNo
  end.

(** The carriers a let pair binds, index 0 first. *)
Definition tpcar (G : list tcar) (e : expr) : list tcar :=
  match e with
  | App (Konst KRecv) c =>
      match tecar G c with TCEnd r => [TCEnd r; TCRcv (Some r)] | _ => [TCNo; TCRcv None] end
  | _ =>
      match tecar G e with
      | TCPair c1 c2 => [c2; c1]
      | TCNewP r => [TCEnd r; TCEnd r]
      | TCRcv o => [TCRcv o; TCRcv o]
      | _ => [TCNo; TCNo]
      end
  end.

Definition tccar (G : list tcar) (e : expr) : tcar :=
  match e with
  | App (Konst KBra) c => tc_keep (tecar G c)
  | Var x => match tcar_of G x with TCRcv o => TCRcv o | _ => TCNo end
  | _ => TCNo
  end.

Fixpoint tmentions (G : list tcar) (e : expr) : bool :=
  match e with
  | Var x => tc_rcv (tcar_of G x)
  | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => false
  | Lam b => tmentions (TCNo :: G) b
  | App a b | Pair a b | LetU a b => tmentions G a || tmentions G b
  | LetP a b => tmentions G a || tmentions (TCNo :: TCNo :: G) b
  | Inj1 a | Inj2 a => tmentions G a
  | Case a b c => tmentions G a || tmentions (TCNo :: G) b || tmentions (TCNo :: G) c
  end.

(** A call is force f applied to its arguments, the point values first. *)
Fixpoint spine (e : expr) : option (expr * list expr) :=
  match e with
  | App (Konst KForce) f => Some (f, [])
  | App e1 e2 => match spine e1 with Some (f, args) => Some (f, args ++ [e2]) | None => None end
  | _ => None
  end.

(** The call site of a call is the box it forces with the carrier of
    its argument, or an unknown box. *)
Definition call_site (G : list tcar) (f : expr) (args : list expr) : list (option expr * tcar) :=
  match tecar G f with
  | TCBox (EBox b) =>
      if bool_decide (length args = nlams b) then [(Some (EBox b), default TCNo (tecar G <$> last args))]
      else [(None, TCNo)]
  | _ => [(None, TCNo)]
  end.

Abbreviation tres := (option (list (pname * pname) * list (option expr * tcar))).

Definition oapp (a b : tres) : tres :=
  match a, b with Some (x1, y1), Some (x2, y2) => Some (x1 ++ x2, y1 ++ y2) | _, _ => None end.

(** The root edges and the call sites of the code of a thread. Box
    bodies are left to [hops]. A spawned or applied λ is code of the
    same thread. *)
Fixpoint troots (G : list tcar) (e : expr) : tres :=
  match e with
  | Var x => if tc_rcv (tcar_of G x) then None else Some ([], [])
  | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => Some ([], [])
  | Lam b => troots (TCNo :: G) b
  | App (Lam b) a =>
      oapp (match a with Var _ => Some ([], []) | _ => troots G a end) (troots (tecar G a :: G) b)
  | App (Konst KSend) (Pair p c) =>
      oapp
        (match p with
         | Var x =>
             match tcar_of G x, tecar G c with
             | TCRcv (Some r1), TCEnd r2 => Some ([(r1, r2)], [])
             | TCRcv _, _ => None
             | _, _ => Some ([], [])
             end
         | _ => troots G p
         end)
        (match c with Var _ => Some ([], []) | _ => troots G c end)
  | App (Konst KLink) (Pair u v) =>
      oapp
        (match u with
         | Var x =>
             match tcar_of G x, tecar G v with
             | TCRcv (Some r1), TCEnd r2 => Some ([(r1, r2)], [])
             | TCRcv _, _ => None
             | _, _ => Some ([], [])
             end
         | _ => troots G u
         end)
        (match v with
         | Var x =>
             match tcar_of G x, tecar G u with
             | TCRcv (Some r1), TCEnd r2 => Some ([(r1, r2)], [])
             | TCRcv _, _ => None
             | _, _ => Some ([], [])
             end
         | _ => troots G v
         end)
  | App (Konst KForce) f => if tmentions G f then None else Some ([], [(None, TCNo)])
  | App (Konst k) a =>
      if act_konst k then match a with Var _ => Some ([], []) | _ => troots G a end else troots G a
  | App e1 e2 =>
      match spine e with
      | Some (f, args) =>
          if tmentions G e then None else
          oapp (Some ([], call_site G f args))
            (oapp ((fix sp (a : expr) : tres :=
                      match a with App a1 a2 => oapp (sp a1) (troots G a2) | _ => Some ([], []) end) e1)
                  (troots G e2))
      | None => oapp (troots G e1) (troots G e2)
      end
  | Pair e1 e2 => oapp (troots G e1) (troots G e2)
  | LetU e1 e2 => oapp (match e1 with Var _ => Some ([], []) | _ => troots G e1 end) (troots G e2)
  | LetP e1 e2 =>
      oapp (match e1 with Var _ => Some ([], []) | _ => troots G e1 end) (troots (tpcar G e1 ++ G) e2)
  | Inj1 e | Inj2 e => troots G e
  | Case e e1 e2 =>
      oapp (match e with Var _ => Some ([], []) | _ => troots G e end)
        (oapp (troots (tccar G e :: G) e1) (troots (tccar G e :: G) e2))
  end.

(** Inside a box body, a received payload not acted on escapes. A
    component of the argument of the self is allowed (R2-recv), and so
    are the forms that [hops] traces. *)
Fixpoint bleak (G : list car) (e : expr) : bool :=
  match e with
  | Var x => is_rcv (car_of G x)
  | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => false
  | Lam b => bleak (CNo :: G) b
  | App (Lam b) a => (match a with Var _ => false | _ => bleak G a end) || bleak (ecar G a :: G) b
  | App (Konst KSend) (Pair p c) =>
      (match p with Var _ => false | _ => bleak G p end) || (match c with Var _ => false | _ => bleak G c end)
  | App (Konst k) a => if act_konst k then match a with Var _ => false | _ => bleak G a end else bleak G a
  | App e1 e2 =>
      match spine e with
      | Some (f, _) =>
          if is_self G f then
            (fix sp (a : expr) : bool := match a with App a1 a2 => sp a1 || bleak G a2 | _ => false end) e1 ||
            (fix adl (a : expr) : bool :=
               match a with Pair a1 a2 => adl a1 || adl a2 | Var _ => false | _ => bleak G a end) e2
          else bleak G e1 || bleak G e2
      | None => bleak G e1 || bleak G e2
      end
  | Pair e1 e2 => bleak G e1 || bleak G e2
  | LetU e1 e2 => (match e1 with Var _ => false | _ => bleak G e1 end) || bleak G e2
  | LetP e1 e2 => (match e1 with Var _ => false | _ => bleak G e1 end) || bleak (pcar G e1 ++ G) e2
  | Inj1 e | Inj2 e => bleak G e
  | Case e e1 e2 =>
      (match e with Var _ => false | _ => bleak G e end) || bleak (ccar G e :: G) e1 || bleak (ccar G e :: G) e2
  end.

(** A force inside a box body whose target is not the self. *)
Fixpoint foreign (G : list car) (e : expr) : bool :=
  match e with
  | App (Konst KForce) f => negb (is_self G f)
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => false
  | Lam b => foreign (CNo :: G) b
  | App (Lam b) a => foreign G a || foreign (ecar G a :: G) b
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => foreign G e1 || foreign G e2
  | LetP e1 e2 => foreign G e1 || foreign (pcar G e1 ++ G) e2
  | Inj1 e | Inj2 e => foreign G e
  | Case e e1 e2 => foreign G e || foreign (ccar G e :: G) e1 || foreign (ccar G e :: G) e2
  end.

(** The carrier at slot π of the argument of a call. *)
Fixpoint arg_at (G : list car) (π : list bool) (e : expr) {struct e} : car :=
  match π, e with
  | b :: π', Pair e1 e2 => arg_at G π' (if b then e2 else e1)
  | _, _ => match ecar G e with CPar ρ => CPar (ρ ++ π) | c => if bool_decide (π = []) then c else CNo end
  end.

Definition stable_arg (G : list car) (π : list bool) (e : expr) : bool :=
  match arg_at G π e with CPar ρ => bool_decide (ρ = π) | _ => false end.

(** Every call of the self, with n arguments, passes at slot π the
    continuation of slot π. *)
Fixpoint stab (n : nat) (π : list bool) (G : list car) (e : expr) : bool :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ | EBox _ => true
  | Lam b => stab n π (CNo :: G) b
  | App (Lam b) a => stab n π G a && stab n π (ecar G a :: G) b
  | App e1 e2 =>
      match spine e with
      | Some (f, args) =>
          (negb (is_self G f) || (bool_decide (length args = n) && stable_arg G π e2)) &&
          (fix sp (a : expr) : bool := match a with App a1 a2 => sp a1 && stab n π G a2 | _ => true end) e1 &&
          stab n π G e2
      | None => stab n π G e1 && stab n π G e2
      end
  | Pair e1 e2 | LetU e1 e2 => stab n π G e1 && stab n π G e2
  | LetP e1 e2 => stab n π G e1 && stab n π (pcar G e1 ++ G) e2
  | Inj1 e | Inj2 e => stab n π G e
  | Case e e1 e2 => stab n π G e && stab n π (ccar G e :: G) e1 && stab n π (ccar G e :: G) e2
  end.

Fixpoint slot_root (c : tcar) (π : list bool) : option pname :=
  match π, c with
  | [], TCEnd r => Some r
  | b :: π', TCPair c1 c2 => slot_root (if b then c2 else c1) π'
  | _, _ => None
  end.

Definition box_env (b : expr) : list car := benv (CPar []) CNo CSelf (nlams b).

Definition is_fwd (h : hitem) : bool := match h with HFwd _ _ => true | _ => false end.

(** The edges of the forward h of the box B, one per call site of B. *)
Definition fwd_edges (sites : list (option expr * tcar)) (B : expr) (h : hitem) : option (list (pname * pname)) :=
  match B, h with
  | EBox b, HFwd π1 π2 =>
      if stab (nlams b) π1 (box_env b) (bbody b) && stab (nlams b) π2 (box_env b) (bbody b) then
        omap (λ s, match slot_root s.2 π1, slot_root s.2 π2 with
                   | Some r1, Some r2 => Some (r1, r2)
                   | _, _ => None
                   end)
          (filter (λ s : option expr * tcar, s.1 = Some B) sites)
      else None
  | _, _ => Some []
  end.

Definition box_ok (B : expr) : bool :=
  match B with
  | EBox b => match box_hops b with Some _ => negb (bleak (box_env b) (bbody b)) | None => false end
  | _ => true
  end.

Definition box_local (B : expr) : bool :=
  match B with EBox b => negb (foreign (box_env b) (bbody b)) | _ => true end.

(** The root graph of a closed program. None when a payload is handed on
    along a path the graph does not see, or when a box that forwards has
    a call site whose roots are not known. *)
Definition root_edges (t : expr) : option (list (pname * pname)) :=
  match troots [] t with
  | None => None
  | Some (Et, sites) =>
      let bs := boxes t in
      let fw := bs ≫= (λ B, match B with
                            | EBox b => (λ h, (B, h)) <$> filter (λ h, is_fwd h = true) (default [] (box_hops b))
                            | _ => []
                            end) in
      if forallb box_ok bs &&
         (bool_decide (fw = []) ||
          (forallb box_local bs && forallb (λ s, match s.1 with Some _ => true | None => false end) sites))
      then match omap (λ Bh, fwd_edges sites Bh.1 Bh.2) fw with
           | Some ls => Some (concat ls ++ Et)
           | None => None
           end
      else None
  end.

(** The root graph exists and is acyclic. *)
Definition root_ok (t : expr) : Prop := ∃ E, root_edges t = Some E ∧ acyclic E = true.

Lemma root_ok_intro t :
  match root_edges t with Some E => acyclic E | None => false end = true → root_ok t.
Proof. destruct (root_edges t) as [E|] eqn:H; [|done]. intros Ha. by exists E. Qed.

(** ** Rank *)

Definition wf_world (W : world) : Prop := well_founded (w_lt W).

(** ** The lock-free fragment *)

Definition lf_r4 (W : world) (p : proc) : Prop :=
  r4_ok (λ b T, ∃ Φ Ψ Δ F, typed W Φ Ψ ∅ Δ F b T) (λ e, e ∈ p.2).

Definition lf_r2w (W : world) (p : proc) : Prop :=
  r2h_ok (λ b T, ∃ Φ Ψ Δ F, typed W Φ Ψ ∅ Δ F b T) (λ e, e ∈ p.2).

Definition lfptyped (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  gptyped W Σ p T ∧ (∀ e, e ∈ p.2 → lf_r1 e = true) ∧ lf_r2w W p ∧
  lf_r4 W p ∧ wf_world W.

Lemma lfptyped_gptyped W Σ p T : lfptyped W Σ p T → gptyped W Σ p T.
Proof. by intros [? _]. Qed.

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

(** ** Rank under the constant world (sharp edges 172, 173)

    A closed program creates its channels at its top level, at the
    constants of its hypotheses Ψ ([created]). Its run starts in
    [cworld Ψ], which supports these constants and has exactly the
    facts of Ψ, closed under program order. The creation facts are
    facts of this world, and Rank asks that its ≺ be well founded. A
    descending chain in a creation constraint, as in Kobayashi's
    forwarder, refutes it ([kob_cworld_not_wf]). Under syntactic points
    the hypotheses name constants already, so no instantiation sits
    between Ψ and the world. *)

(** The ≺ facts that the hypotheses Ψ state at their instances. *)
Definition hyps_lt (Ψ : hyps) : prel := λ x y, hyp_fact Ψ (FLt x y).

(** The root names of the instances of Ψ. *)
Definition hroots (Ψ : hyps) : gset pname := list_to_set (Ψ ≫= (λ g, pt_root <$> g.2)).

Definition cworld (Ψ : hyps) : world := wgen (hroots Ψ) (λ _ _, False) (hyps_lt Ψ).

Lemma hroots_elem Ψ p : p ∈ hroots Ψ ↔ ∃ C xs y, (C, xs) ∈ Ψ ∧ y ∈ xs ∧ p = pt_root y.
Proof.
  unfold hroots. rewrite elem_of_list_to_set, list_elem_of_bind. split.
  - intros ([C xs] & Hp & Hin). apply list_elem_of_fmap in Hp as (y & -> & Hy). by exists C, xs, y.
  - intros (C & xs & y & Hin & Hy & ->). exists (C, xs). split; [|done]. apply list_elem_of_fmap. by exists y.
Qed.

(** The instances of created hypotheses are constants. *)
Lemma created_consts W Ψ : created W Ψ → ∀ C xs y, (C, xs) ∈ Ψ → y ∈ xs → ∃ a, y = pconst a.
Proof.
  induction 1 as [|Ψ C a HΨ IH _ _ _]; intros C' xs y Hin Hy; [by apply elem_of_nil in Hin|].
  apply elem_of_app in Hin as [Hin|Hin]; [by eapply IH|].
  apply list_elem_of_singleton in Hin. injection Hin as -> ->. apply list_elem_of_singleton in Hy as ->.
  by exists a.
Qed.

(** A world contains the world its facts generate. *)
Lemma glt_into (W : world) (L : prel) :
  world_wf W → (∀ x y, L x y → w_lt W x y) → ∀ x y, glt (λ _ _, False) L x y → w_lt W x y.
Proof.
  intros HW HL.
  assert (∀ x y, geq (λ _ _ : point, False) x y → x = y) as Hq.
  { induction 1 as [x y []| | | | | |]; subst; done. }
  induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
  - by apply HL.
  - apply (wf_lt_po _ HW).
  - apply Hq in Hx, Hy. by subst.
  - by eapply (wf_lt_trans _ HW).
  - apply (wf_lt_dpo _ HW).
Qed.

(** [cworld Ψ] is strict and realizes Ψ. *)
Lemma cworld_hold Ψ : created (Wpo []) Ψ →
  strict (cworld Ψ) ∧ hyps_hold (w_eq (cworld Ψ)) (w_lt (cworld Ψ)) (pt_known (cworld Ψ)) Ψ.
Proof.
  intros HΨ. destruct (created_world_names (Wpo []) Ψ Wpo_nil_strict' HΨ) as (W1 & HW1 & Hh & Hkn).
  destruct (proj2 (proj2 (proj2 HW1))) as [HW1wf HW1irr].
  assert (∀ x y, hyps_lt Ψ x y → w_lt W1 x y) as HL.
  { intros x y (C & xs & Hin & g & Hg & E). destruct (Hh C xs Hin) as [Hb _].
    specialize (Hb g Hg). rewrite <-E in Hb. exact Hb. }
  assert (w_names W1 ⊆ hroots Ψ) as HN.
  { intros p Hp. destruct (wf_names_const _ HW1wf p Hp) as [a ->].
    destruct (Hkn (pconst a) Hp) as [Hk|(C & xs & y & Hin & Hy & E)].
    - unfold pt_known in Hk. rewrite Wpo_nil_names in Hk. set_solver.
    - apply hroots_elem. exists C, xs, y. split_and!; [done|done|]. by rewrite <-E. }
  pose proof (glt_into W1 _ HW1wf HL) as Hin.
  split; [split|].
  - apply wgen_wf.
    + intros p Hp. apply hroots_elem in Hp as (C & xs & y & HC & Hy & ->).
      destruct (created_consts _ _ HΨ C xs y HC Hy) as [a ->]. by exists a.
    + by intros ? ? [].
    + intros x y H. destruct (wf_lt_supp _ HW1wf x y (HL x y H)) as [Hp|[Hx Hy]]; [by left|].
      right. split; by apply HN.
  - intros x Hx. apply (HW1irr x). by apply Hin.
  - intros C xs Hc. split.
    + intros g Hg. destruct (fact_map (pt_inst (plist xs)) g) as [x y] eqn:E. cbn [fact_holds].
      apply glt_base. exists C, xs. split; [done|]. exists g. split; [done|]. by rewrite E.
    + destruct (Hh C xs Hc) as [_ Hk]. eapply Forall_impl; [exact Hk|]. intros x Hx.
      unfold pt_known in *. apply HN. exact Hx.
Qed.

(** The process of a closed program over Ψ is typed in every strict
    world that realizes Ψ. *)
Lemma world_ptyped W Ψ t T :
  strict W → hyps_hold (w_eq W) (w_lt W) (pt_known W) Ψ → prim T →
  styped ∅ Ψ [] (∅, None) t T → ptyped W ∅ (∅, {[+ t +]}) T.
Proof.
  intros HS Hh HT Ht. apply ptyped_closed; [done|].
  pose proof (typed_pinst W ∅ Ψ ∅ [] (∅, None) t T HS (styped_typed W _ _ _ _ _ _ Ht) pvar []) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  unfold fhyps_pinst in H. rewrite fmap_empty in H. apply H; [|apply tenv_pol_pvar].
  rewrite hyps_inst_pvar.
  apply (hyps_hold_mono (w_eq W) _ (w_lt W) _ (pt_known W)); [| | |exact Hh].
  - intros ? ? ?. by apply se_w.
  - intros ? ? ?. by apply sl_w.
  - intros ? ?. by left.
Qed.

Lemma cworld_ptyped Ψ t T :
  created (Wpo []) Ψ → prim T → styped ∅ Ψ [] (∅, None) t T →
  ptyped (cworld Ψ) ∅ (∅, {[+ t +]}) T.
Proof. intros HΨ. destruct (cworld_hold Ψ HΨ) as [HS Hh]. by apply world_ptyped. Qed.

(** *** The facts of Ψ

    A hypothesis (C, [a]) whose constraint has constants as outer
    points states its facts at the constants. The variable 0 becomes a
    and the variable j + 1 the j-th outer point ([pt_open]). *)

Fixpoint pn_open (xs : list point) (p : pname) : pname :=
  match p with
  | NVar j => match xs !! j with Some z => pt_name z | None => NVar j end
  | NConst a => NConst a
  | NPayload q b i => NPayload (pn_open xs q) b i
  end.

Definition pt_open (xs : list point) (x : point) : point :=
  MkPt (pn_open xs (pt_name x)) (pt_pol x) (pt_off x).

Lemma pn_inst_open σ xs p :
  (∀ a, pn_root p = NVar a → ∃ c, xs !! a = Some (pconst c) ∧ σ a = pconst c) →
  pn_inst σ p = Pt (pn_open xs p) 0.
Proof.
  induction p as [a|a|q IH b i]; intros H; cbn [pn_inst pn_open].
  - done.
  - destruct (H a eq_refl) as (c & -> & ->). done.
  - rewrite IH by exact H. unfold pt_payload, pt_shift. done.
Qed.

Lemma pt_inst_open σ xs x :
  (∀ a, pt_root x = NVar a → ∃ c, xs !! a = Some (pconst c) ∧ σ a = pconst c) →
  pt_inst σ x = pt_open xs x.
Proof.
  intros H. destruct x as [p b o]. unfold pt_inst, pt_open. cbn [pt_name pt_pol pt_off].
  rewrite (pn_inst_open σ xs p H). destruct b; unfold pt_polar, pt_shift, pt_dual; done.
Qed.

Definition all_const (env : list point) : Prop := Forall (λ z, ∃ c, z = pconst c) env.

Lemma open_sub a env j :
  all_const env → j < S (length env) →
  ∃ c, (pconst a :: env) !! j = Some (pconst c) ∧
    (pt_inst (plist [pconst a]) ∘ pup 1 (plist env)) j = pconst c.
Proof.
  intros Henv Hj. destruct j as [|j].
  - exists a. split; [done|]. unfold compose, pup. rewrite decide_True by lia. done.
  - destruct (lookup_lt_is_Some_2 env j) as [z Hz]; [lia|].
    destruct (proj1 (Forall_lookup _ _) Henv j z Hz) as [c ->]. exists c. split; [done|].
    unfold compose, pup. rewrite decide_False by lia. cbn. unfold plist at 2. rewrite Nat.sub_0_r, Hz. done.
Qed.

Lemma hyps_lt_nil x y : ¬ hyps_lt [] x y.
Proof. intros (C & xs & Hin & _). by apply elem_of_nil in Hin. Qed.

Lemma hyps_lt_snoc Ψ env P a x y :
  all_const env → hyps_lt (Ψ ++ [(BCs env P, [pconst a])]) x y →
  hyps_lt Ψ x y ∨ ∃ x0 y0, P (FLt x0 y0) ∧ fact_scoped (S (length env)) (FLt x0 y0) ∧
    x = pt_open (pconst a :: env) x0 ∧ y = pt_open (pconst a :: env) y0.
Proof.
  intros Henv (C & xs & Hin & g & Hg & E). apply elem_of_app in Hin as [Hin|Hin].
  - left. exists C, xs. split; [done|]. by exists g.
  - right. apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    destruct Hg as (f & Hf & Hs & ->). destruct f as [x0 y0]. cbn [bc_facts bc_env length] in Hf, Hs, E.
    cbn [fact_map] in E. injection E as -> ->. exists x0, y0. split_and!; [done|done| |];
      rewrite pt_inst_comp; apply pt_inst_open; intros j Hj; apply open_sub; [done| |done|];
      destruct Hs as [Hx Hy]; [exact (pn_vb_root _ _ _ Hx Hj)|exact (pn_vb_root _ _ _ Hy Hj)].
Qed.

Lemma hyps_lt_snoc_intro Ψ env P a x0 y0 :
  all_const env → P (FLt x0 y0) → fact_scoped (S (length env)) (FLt x0 y0) →
  hyps_lt (Ψ ++ [(BCs env P, [pconst a])]) (pt_open (pconst a :: env) x0) (pt_open (pconst a :: env) y0).
Proof.
  intros Henv Hf Hs. exists (BCs env P), [pconst a]. split; [apply elem_of_app; right; by left|].
  exists (FLt (pt_inst (pup 1 (plist env)) x0) (pt_inst (pup 1 (plist env)) y0)). split.
  - exists (FLt x0 y0). split_and!; [done|exact Hs|done].
  - cbn [fact_map]. destruct Hs as [Hx Hy]. rewrite !pt_inst_comp.
    f_equal; symmetry; apply pt_inst_open; intros j Hj; apply open_sub;
      [done|exact (pn_vb_root _ _ _ Hx Hj)|done|exact (pn_vb_root _ _ _ Hy Hj)].
Qed.

(** *** Ranks *)

(** Rank holds when a rank into a well-founded order rises along program
    order, along x ≺ x̄+1 and along the facts of Ψ. *)
Lemma cworld_rank_wf {A} (R : A → A → Prop) Ψ (r : point → A) :
  well_founded R → (∀ a b c, R a b → R b c → R a c) →
  (∀ x y, hyps_lt Ψ x y → R (r x) (r y)) →
  (∀ x, R (r x) (r (pt_shift 1 x))) → (∀ x, R (r x) (r (pt_shift 1 (pt_dual x)))) →
  wf_world (cworld Ψ).
Proof. intros Hwf Htr HL Hs Hd. apply (wgen_rank_wf R _ _ _ r Hwf Htr); [by intros ? ? []|done|done|done]. Qed.

(** The rank of depth and offset, read lexicographically. *)
Definition drank (x : point) : nat * nat := (sdepth (pt_name x), pt_off x).

Lemma cworld_depth_wf Ψ : (∀ x y, hyps_lt Ψ x y → lexlt (drank x) (drank y)) → wf_world (cworld Ψ).
Proof.
  intros HL. apply (cworld_rank_wf lexlt Ψ drank lexlt_wf); [unfold lexlt; intros ? ? ?; lia|done| |].
  - intros x. unfold drank, lexlt, pt_shift. cbn. lia.
  - intros x. unfold drank, lexlt, pt_shift. cbn. lia.
Qed.

(** *** The shared constant ladder

    CfstScheduler.v and ABP.v create a ceiling z = N without facts,
    then channels 0, …, a-1, channel b at the constant N - 1 - b
    ([CfstTools.cl_Ψ]). The constraint of channel a relates its instants
    to those of each earlier channel by a rank rkf and puts them below
    z. The world is well founded under the rank that reads channel b at
    rkf b and puts z above all of them. *)
Section ladder_rank.
  Context (rkf : nat → nat → nat) (Hrk : ∀ b k, rkf b k < rkf b (S k)) (N : nat).

  Definition lad_rel (a : nat) (x y : point) : Prop :=
    ∃ v, v < a ∧ pt_name x = NConst (N - 1 - v) ∧
      ((∃ w, w < a ∧ pt_name y = NConst (N - 1 - w) ∧ rkf v (pt_off x) < rkf w (pt_off y)) ∨
       pt_name y = NConst N).

  Lemma cl_env_const a : all_const (CfstTools.cl_env N a).
  Proof. unfold CfstTools.cl_env. apply Forall_fmap, Forall_forall. intros i _. by eexists. Qed.

  Lemma cl_open_name a v x : pt_name x = NVar (S v) → v ≤ a →
    pt_name (pt_open (pconst (N - 1 - a) :: CfstTools.cl_env N a) x) = NConst (N - a + v).
  Proof.
    intros Hx Hv. unfold pt_open. cbn [pt_name]. rewrite Hx. cbn [pn_open].
    change ((pconst (N - 1 - a) :: CfstTools.cl_env N a) !! S v) with (CfstTools.cl_env N a !! v).
    rewrite (CfstTools.cl_env_lookup rkf Hrk) by lia. done.
  Qed.

  Lemma ladder_lt a x y : a ≤ N → hyps_lt (CfstTools.cl_Ψ rkf N a) x y → lad_rel a x y.
  Proof.
    revert x y. induction a as [|a IH]; intros x y Ha H.
    - destruct H as (C & xs & Hin & g & Hg & _). apply list_elem_of_singleton in Hin.
      injection Hin as -> ->. destruct Hg as (f & Hf & _). destruct Hf.
    - cbn [CfstTools.cl_Ψ] in H. unfold CfstTools.cl_C in H.
      destruct (hyps_lt_snoc _ _ _ _ x y (cl_env_const a) H) as [H0|(x0 & y0 & Hf & _ & -> & ->)].
      + destruct (IH x y ltac:(lia) H0) as (v & Hv & Hx & Hy). exists v. split; [lia|]. split; [done|].
        destruct Hy as [(w & Hw & Hy & Hr)|Hy]; [left; exists w; split_and!; [lia|done|done]|by right].
      + destruct Hf as [(b & k & j & c & c' & Hb & Hr & E)|[(b & k & j & c & c' & Hb & Hr & E)|(j & c & E)]];
          injection E as -> ->.
        * exists b. split; [lia|]. split.
          -- rewrite (cl_open_name a (a - b - 1)); [f_equal; lia| |lia].
             destruct c; cbn; f_equal; lia.
          -- left. exists a. split; [lia|]. split; [by destruct c'|].
             replace (a - b) with (S (a - b - 1)) by lia. destruct c, c'; exact Hr.
        * exists a. split; [lia|]. split; [by destruct c|].
          left. exists b. split; [lia|]. split.
          -- rewrite (cl_open_name a (a - b - 1)); [f_equal; lia| |lia].
             destruct c'; cbn; f_equal; lia.
          -- destruct c, c'; exact Hr.
        * exists a. split; [lia|]. split; [by destruct c|]. right.
          rewrite (cl_open_name a a); [f_equal; lia|done|lia].
  Qed.

  Definition lad_rank (x : point) : nat * nat :=
    match pt_name x with
    | NConst v => if decide (v < N) then (0, rkf (N - 1 - v) (pt_off x))
                  else if decide (v = N) then (1, pt_off x) else (0, pt_off x)
    | _ => (0, pt_off x)
    end.

  Lemma lad_rank_shift x : lexlt (lad_rank x) (lad_rank (pt_shift 1 x)).
  Proof.
    unfold lad_rank, lexlt, pt_shift. cbn [pt_name pt_off].
    destruct (pt_name x) as [v|v|q b i]; [|cbn; lia|cbn; lia].
    repeat case_decide; cbn; try lia. right. split; [done|]. rewrite Nat.add_1_r. apply Hrk.
  Qed.

  Lemma ladder_wf a : a ≤ N → wf_world (cworld (CfstTools.cl_Ψ rkf N a)).
  Proof.
    intros Ha. apply (cworld_rank_wf lexlt _ lad_rank lexlt_wf); [unfold lexlt; intros ? ? ?; lia| |apply lad_rank_shift|].
    - intros x y H. destruct (ladder_lt a x y Ha H) as (v & Hv & Hx & [(w & Hw & Hy & Hr)|Hy]);
        unfold lad_rank, lexlt; rewrite Hx, Hy; repeat case_decide; cbn; try lia.
      right. split; [done|].
      replace (N - 1 - (N - 1 - v)) with v by lia. replace (N - 1 - (N - 1 - w)) with w by lia. exact Hr.
    - intros x. exact (lad_rank_shift (pt_dual x)).
  Qed.
End ladder_rank.

(** A closed source program over the hypotheses Ψ of its top-level
    channels (the premises of [soundness_created_s]), with the checks of
    the fragment. Its run starts in [cworld Ψ], and Rank is asked of
    that world. The root graph, from which its floors come, must
    exist and be acyclic. *)
Definition lfsource (Ψ : hyps) (t : expr) (T : ty) : Prop :=
  created (Wpo []) Ψ ∧ prim T ∧
  gstyped ∅ Ψ [] (∅, None) t T ∧ lf_r1 t = true ∧
  r2h_ok (λ b T, ∃ Φ Ψ Δ F, styped Φ Ψ Δ F b T) (λ e, e = t) ∧
  r4_ok (λ b T, ∃ Φ Ψ Δ F, styped Φ Ψ Δ F b T) (λ e, e = t) ∧ wf_world (cworld Ψ) ∧
  root_ok t.

Lemma lfsource_gstyped Ψ t T : lfsource Ψ t T → gstyped ∅ Ψ [] (∅, None) t T.
Proof. by intros (_ & _ & ? & _). Qed.

(** Budgets do not enter strictness. *)
Lemma strict_budgets W B P : strict W → strict (World (w_names W) (w_lt W) B P).
Proof. intros [[Ht Hp Hs Hn Hd] Hi]. split; [split|]; cbn; auto. Qed.

(** The process of such a program is in the fragment, in every world
    with the support and the order of the world where its run starts,
    whatever its budgets. *)
Theorem lfsource_lfptyped_at Ψ t T B P :
  lfsource Ψ t T →
  strict (World (hroots Ψ) (w_lt (cworld Ψ)) B P) ∧
  lfptyped (World (hroots Ψ) (w_lt (cworld Ψ)) B P) ∅ (∅, {[+ t +]}) T.
Proof.
  intros (HΨ & HT & [Ht Hg] & H1 & (ann2 & Hann2 & H2) & (ann & E & Hann & Hac & Hts) & Hwf & _).
  destruct (cworld_hold Ψ HΨ) as [HS Hh].
  pose proof (strict_budgets (cworld Ψ) B P HS) as HS'.
  split; [exact HS'|]. split_and!.
  - split; [by apply (world_ptyped _ Ψ)|]. by intros e ->%gmultiset_elem_of_singleton.
  - by intros e ->%gmultiset_elem_of_singleton.
  - exists ann2. split.
    + intros b U Hin. destruct (Hann2 b U Hin) as (Φ & Ψ' & Δ & F & Hb). exists Φ, Ψ', Δ, F.
      by apply styped_typed.
    + intros e ->%gmultiset_elem_of_singleton. by apply H2.
  - exists ann, E. split_and!; [|done|].
    + intros b U Hin. destruct (Hann b U Hin) as (Φ & Ψ' & Δ & F & Hb). exists Φ, Ψ', Δ, F.
      by apply styped_typed.
    + intros e ->%gmultiset_elem_of_singleton. by apply Hts.
  - exact Hwf.
Qed.

(** The world where the run starts, with its default budgets. *)
Theorem lfsource_lfptyped Ψ t T :
  lfsource Ψ t T → strict (cworld Ψ) ∧ lfptyped (cworld Ψ) ∅ (∅, {[+ t +]}) T.
Proof. intros H. exact (lfsource_lfptyped_at Ψ t T (λ _, None) (λ _, 0) H). Qed.

(** ** Budgets (plan §17.6, §17.8, revised after stage L6a)

    The stretch bound L. A stretch of an end is the run of its holder
    from the moment the end arrives (by new, by an action on it that
    refills it, by a receive, or as an argument) up to the action on it
    or the hand-over that ends it, with the hand-over counted. Each
    channel step on another end burns one unit (F-Tick), and a send, a
    spawn and a link cost the handed end one unit. L bounds the units
    of every stretch.

    A segment of a thread is its code up to its tail call, or a round
    of a box up to its tail call. [scost] counts the units on the
    longest path of a segment. A channel step, a spawn and a link cost
    one. A spawned or applied λ counts with the code that builds it, so
    a stretch that follows an end into a spawned thread stays inside
    the segment. A box literal forced in place whose body never forces
    runs inline and costs its body at each force. Any other force is a
    potentially recursive call (R1 puts it in tail position) and ends
    the segment. A stretch spans at most two segments. An end that a
    round holds at its start came in the argument, and R2-recv makes
    the round act on it or hand it over. Inside a round only fresh
    ends and fed slots go to a call, so the end does not reach a third
    segment. A thread's own code passes its ends to its first call,
    whose round is the second segment. Hence L = 2 · [seg_len].

    The budgets. d is the largest depth of the root graph, and the
    depth of a root is the length of the longest path that ends in it.
    Every end gets the refill and cap B = (d + 2)·L. A payload sent
    along a carrier at the point k is floored by
    w_pay k = (d − depth (root k) + 1)·L. The receiver of a payload with
    counter c ≥ w_pay k acts on it within its stretch (L ≤ c), or
    passes it on along a carrier of a root deeper by one at least, which
    asks c − L ≥ the next floor, true because the floors drop by L per
    level. A fresh end meets every floor, B − L = (d + 1)·L is the
    largest one. §17.6 had b_bud = (d − depth + 1)·2L, read at the
    session type of the end. A payload of a deep type sent along a
    carrier of a shallow type then misses the floor, so B is uniform.
    The fragment never uses ∞. *)

Fixpoint indepth {A} `{EqDecision A} (n : nat) (E : list (A * A)) (x : A) : nat :=
  match n with
  | 0 => 0
  | S n' => foldr max 0 ((λ ab, if bool_decide (ab.2 = x) then S (indepth n' E ab.1) else 0) <$> E)
  end.

(** In an acyclic graph a path has at most [length E] edges. *)
Definition depth {A} `{EqDecision A} (E : list (A * A)) (x : A) : nat := indepth (length E) E x.

Definition gdepth {A} `{EqDecision A} (E : list (A * A)) : nat := foldr max 0 ((λ ab, depth E ab.2) <$> E).

(** The constants that hand an end over without a channel step. *)
Definition hand_konst (k : konst) : bool := match k with KSpawn | KLink => true | _ => false end.

(** Units on the longest path through a segment. *)
Fixpoint scost (e : expr) : nat :=
  match e with
  | App (Konst KForce) (EBox b) => if has_force b then 0 else scost b
  | App (Konst k) a => (if prim_konst k || hand_konst k then 1 else 0) + scost a
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => scost e1 + scost e2
  | Lam b => scost b
  | Case e e1 e2 => scost e + max (scost e1) (scost e2)
  | Inj1 e | Inj2 e => scost e
  | EBox _ | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ => 0
  end.

(** The longest segment, in the code of the thread or in a round of a box. *)
Definition seg_len (e : expr) : nat :=
  foldr max (scost e) ((λ b, match b with EBox b' => scost b' | _ => 0 end) <$> boxes e).

(** L. *)
Definition stretch_len (e : expr) : nat := 2 * seg_len e.

Definition bud_at (E : list (pname * pname)) (L : nat) (x : point) : option nat :=
  Some ((gdepth E + 2) * L).

Definition pay_at (E : list (pname * pname)) (L : nat) (k : point) : nat :=
  (gdepth E - depth E (pt_root k) + 1) * L.

(** The world W with the budgets of the root graph E and the stretch
    bound L. *)
Definition with_budgets (W : world) (E : list (pname * pname)) (L : nat) : world :=
  World (w_names W) (w_lt W) (bud_at E L) (pay_at E L).

Lemma with_budgets_strict W E L : strict W → strict (with_budgets W E L).
Proof. apply strict_budgets. Qed.

Lemma with_budgets_wf W E L : wf_world W → wf_world (with_budgets W E L).
Proof. done. Qed.

Lemma with_budgets_bud W E L x : w_bud (with_budgets W E L) x = Some ((gdepth E + 2) * L).
Proof. done. Qed.

Lemma with_budgets_pay W E L k : w_pay (with_budgets W E L) k = (gdepth E - depth E (pt_root k) + 1) * L.
Proof. done. Qed.

(** The world where the run of a closed program starts, with the
    budgets of its root graph and of its stretch bound. The budgets are
    a function of the program, and no session type enters them. *)
Definition src_world (Ψ : hyps) (t : expr) : world :=
  with_budgets (cworld Ψ) (default [] (root_edges t)) (stretch_len t).

(** A program of the fragment is in the fragment at its budgets. *)
Theorem lfsource_budgets Ψ t T :
  lfsource Ψ t T → strict (src_world Ψ t) ∧ lfptyped (src_world Ψ t) ∅ (∅, {[+ t +]}) T.
Proof. apply lfsource_lfptyped_at. Qed.
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

(** In the world of the forwarder (Forwarder.v) a is the constant 1 and
    b the constant 0. Round k of both sits at 6k, a at 6k, b at 6k+1, and
    the payload points a[k], b[k] in between, at 6k+2 or 6k+3 by
    polarity. *)
Definition fw_k (p : pname) : nat :=
  match p with NPayload (NConst 1) k 0 | NPayload (NConst 0) k 0 => k | _ => 0 end.
Definition fw_b (p : pname) (c : bool) : nat :=
  match p with
  | NConst 0 => 1
  | NPayload (NConst 1) _ 0 => if c then 2 else 3
  | NPayload (NConst 0) _ 0 => if c then 3 else 2
  | _ => 0
  end.
Definition fw_rank (x : point) : nat := 6 * (pt_off x + fw_k (pt_name x)) + fw_b (pt_name x) (pt_pol x).

Lemma fw_b_le p c : fw_b p c ≤ 3.
Proof. unfold fw_b. repeat case_match; lia. Qed.

Lemma fw_wf : wf_world (cworld Forwarder.fw_Ψ).
Proof.
  apply (cworld_rank_wf lt _ fw_rank Wf_nat.lt_wf); [intros ? ? ?; lia| | |].
  - intros x y H.
    destruct (hyps_lt_snoc ([] ++ [(Forwarder.fpa_C, [pconst 1])]) [pconst 1] Forwarder.fwb_P 0 x y
      ltac:(by repeat econstructor) H) as [H0|(x0 & y0 & Hf & _ & -> & ->)].
    + destruct (hyps_lt_snoc [] [] Forwarder.fpa_P 1 x y ltac:(constructor) H0) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
        [by apply hyps_lt_nil in Hn|].
      destruct Hf as (k & b & b' & [E|E]); injection E as -> ->; destruct b, b'; cbn; lia.
    + destruct Hf as (k & E); repeat destruct E as [E|E]; injection E as -> ->; cbn; lia.
  - intros x. unfold fw_rank, pt_shift. cbn. lia.
  - intros x. unfold fw_rank, pt_shift, pt_dual. cbn. pose proof (fw_b_le (pt_name x) (pt_pol x)). lia.
Qed.

Theorem fw_lfsource : lfsource Forwarder.fw_Ψ Forwarder.fw_main TUnit.
Proof.
  split_and!.
  - apply Forwarder.fw_created.
  - constructor.
  - split; [apply Forwarder.fw_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists fw_ann, fw_E. split_and!.
    + intros b T Hin. apply list_elem_of_singleton in Hin. injection Hin as -> ->.
      exists ∅, [], [], (∅, None). apply Forwarder.fwd_typed, (proj1 wnil_strict).
    + vm_compute. reflexivity.
    + intros e ->. exists fw_E. split; [vm_compute; reflexivity|done].
  - apply fw_wf.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

Theorem fw_lfptyped : ∃ W, strict W ∧ lfptyped W ∅ (∅, {[+ Forwarder.fw_main +]}) TUnit.
Proof. exists (cworld Forwarder.fw_Ψ). exact (lfsource_lfptyped _ _ _ fw_lfsource). Qed.

(** The tail call. No hop. The facts ι+k ≺ ι[0] climb in depth. *)
Theorem tc_lfsource : lfsource TailCall.tc_Ψ TailCall.tc_main TUnit.
Proof.
  split_and!.
  - apply TailCall.tc_created.
  - constructor.
  - split; [apply TailCall.tc_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply cworld_depth_wf. intros x y H.
    destruct (hyps_lt_snoc [] [] TailCall.tcc_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
      [by apply hyps_lt_nil in Hn|].
    destruct Hf as (k & b & E). injection E as -> ->. destruct b; unfold drank, lexlt; cbn; lia.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

Theorem tc_lfptyped : ∃ W, strict W ∧ lfptyped W ∅ (∅, {[+ TailCall.tc_main +]}) TUnit.
Proof. exists (cworld TailCall.tc_Ψ). exact (lfsource_lfptyped _ _ _ tc_lfsource). Qed.

(** The recursive CFST scheduler, over its seven top-level points, the
    ceiling and the six channels of the ring. Rounds of six steps, every
    end passed on is acted on in the round, no hop. Its world is the
    shared constant ladder. *)

Theorem sch_lfsource : lfsource (CfstScheduler.sch_Ψ 6) CfstScheduler.sch_main TUnit.
Proof.
  split_and!.
  - apply CfstScheduler.sch_created. lia.
  - constructor.
  - split; [apply CfstScheduler.sch_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply (ladder_wf CfstScheduler.rk CfstScheduler.rk_S 6 6). lia.
  - apply root_ok_intro. vm_compute. reflexivity.
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

(** The world where the run of Kobayashi's forwarder starts has these
    facts at the constant 0, so Rank rejects it already there. *)
Lemma payloadv_vb n : pn_vb 1 (payloadv n).
Proof. induction n as [|n IH]; cbn; [lia|done]. Qed.

Theorem kob_cworld_not_wf : ¬ wf_world (cworld KobForwarder.kfw_Ψ).
Proof.
  apply (chain_not_wf _ (λ n, pt_open [pconst 0] (Pt (payloadv n) 0))). intros n.
  apply glt_base. apply (hyps_lt_snoc_intro [] [] KobForwarder.fw_P 0); [constructor| |].
  - exists n, true, true. by left.
  - split; apply payloadv_vb.
Qed.

(** C1 of plan §10.1, the spawner chain.

      c1 = !(f = λπ. λ⟨prev, chat⟩. let chat′ = send ⟨∗, chat⟩ in let (a, b) = new (π[0]) in
                 let () = spawn (λw. let () = w in let () = recvclose a in close prev) in
                 (force f) (π[0]) ⟨b, chat′⟩)

    Under syntactic points the box takes the point κ of prev as π, and
    a and b are created at κ[0], where the call places the next round.
    The chatter step comes first, because the call applies the forced
    self to a point value, which performs no primitive (Guard.v). The
    spawned thread blocks on a while it holds prev. *)
Definition c1_box : expr :=
  EBox (Lam (Lam (LetP (Var 0) (App (Lam (let_new_pair_at (App (Konst (KPay 0)) (Var 4))
    (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (recvclose (Var 2)) (App EClos (Var 5))))))
      (App (App (App EForce (Var 7)) (App (Konst (KPay 0)) (Var 6))) (Pair (Var 0) (Var 2))))))
    (App ESend (Pair EUnit (Var 0))))))).

(** C1 passes the guard, R1, R2′ and the hand-off graph. The body is
    harmless. *)

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

      c3 = !(f = λπ. λ⟨y, d⟩. let d′ = send ⟨∗, d⟩ in let (a, b) = new (π[0]) in
                 let () = link ⟨y, a⟩ in (force f) (π[0]) ⟨b, d′⟩)

    y holds the partner of C. Every round links it to a fresh end and
    goes on with the other fresh end b, so C is never served. The
    chatter step comes first, as in C1. *)
Definition c3_box : expr :=
  EBox (Lam (Lam (LetP (Var 0) (App (Lam (let_new_pair_at (App (Konst (KPay 0)) (Var 4))
    (LetU (App ELink (Pair (Var 4) (Var 1)))
      (App (App (App EForce (Var 7)) (App (Konst (KPay 0)) (Var 6))) (Pair (Var 0) (Var 2))))))
    (App ESend (Pair EUnit (Var 0))))))).

(** The guard and R1 accept C3. R2′ rejects it, because y is linked
    before the round acts on it. *)
Theorem c3_checks : guarded c3_box ∧ lf_r1 c3_box = true ∧ lf_r2 c3_box = false.
Proof. unfold guarded. vm_compute. auto. Qed.

(** A self-loop refutes acyclicity. *)
Lemma acyclic_loop (E : list (node * node)) n : acyclic E = true → (n, n) ∈ E → False.
Proof.
  unfold acyclic. intros H Hin. rewrite forallb_forall in H.
  specialize (H _ (proj1 (list_elem_of_In _ _) Hin)). cbn in H.
  rewrite bool_decide_true in H by done. discriminate.
Qed.

(** A box whose items give a self-loop at every parameter type has a
    self-loop in its edges, whatever type the annotation gives it. *)
Lemma box_loop ann b hs E :
  box_hops b = Some hs → existsb handoff hs = true →
  (∀ P ls, omap (item_edges P hs) hs = Some ls → ∃ n, (n, n) ∈ concat ls) →
  box_edges ann (EBox b) = Some E → ∃ n, (n, n) ∈ E.
Proof.
  intros Hb Hh Hl. unfold box_edges. rewrite Hb, Hh.
  repeat case_match; try discriminate. intros [= <-]. eapply Hl. eassumption.
Qed.

Lemma thread_loop ann b E' :
  boxes b = [] → (∀ E, box_edges ann (EBox b) = Some E → ∃ n, (n, n) ∈ E) →
  thread_edges ann (EBox b) = Some E' → ∃ n, (n, n) ∈ E'.
Proof.
  intros Hb H. unfold thread_edges. cbn [boxes]. rewrite Hb. cbn [foldr].
  destruct (box_edges ann (EBox b)) as [E|] eqn:HE; [|done]. cbn. rewrite app_nil_r.
  intros [= <-]. by apply H.
Qed.

Definition c3_body : expr := match c3_box with EBox b => b | _ => EUnit end.
Definition c3_hs : list hitem := default [] (box_hops c3_body).

(** The link of y to a hands the partner of y over to b, which sits at
    the slot of y in the next round. Both edges of the link are
    self-loops, at the type of y and at its dual. *)
Lemma c3_items P ls : omap (item_edges P c3_hs) c3_hs = Some ls → ∃ n, (n, n) ∈ concat ls.
Proof.
  assert (c3_hs = [HLink (RPar [false]) (RNew 6 false); HBind 6 true [false]]) as -> by (vm_compute; reflexivity).
  intros H. cbn in H. unfold node_at in H.
  destruct (ty_at [false] P) as [[]|] eqn:Hty; try discriminate H.
  rewrite !bool_decide_true in H by done. cbn in H. unfold node_at in H. rewrite Hty in H.
  injection H as <-. eexists. cbn. left.
Qed.

(** Under §17.6 C3 passes R2-recv without the link clause, and the
    hand-off graph rejects it, at every annotation. *)
Theorem c3_not_lfptyped W Σ T : ¬ lfptyped W Σ (∅, {[+ c3_box +]}) T.
Proof.
  intros (_ & _ & _ & (ann & E & _ & Hac & Hts) & _).
  destruct (Hts c3_box (proj2 (gmultiset_elem_of_singleton _ _) eq_refl)) as (E' & HE' & Hsub).
  destruct (thread_loop ann c3_body E' ltac:(vm_compute; reflexivity)
    (λ E0, box_loop ann c3_body c3_hs E0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c3_items)
    HE') as [n Hn].
  exact (acyclic_loop E n Hac (Hsub _ Hn)).
Qed.

Theorem c3_r2h : lf_r2h [] c3_box = true.
Proof. vm_compute. reflexivity. Qed.

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
  intros (_ & _ & (ann & _ & H2) & _). specialize (H2 _ (proj2 (gmultiset_elem_of_singleton _ _) eq_refl)).
  revert H2. vm_compute. discriminate.
Qed.

(** A box whose leading λ takes a channel c and passes it on unacted.

      lc = !(f = λc. λd. let d′ = send ⟨∗, d⟩ in (force f) c d′)

    Read as a point parameter c would count as fresh, and R2 would let
    the round hand c on forever. Only an annotation whose box type says
    TPt for c makes R2-recv accept it, and the typing premise of
    [lfptyped] asks a derivation of that type. Without an annotation,
    or with a channel type for c, R2-recv rejects it, and so does R2′. *)
Definition lc_box : expr :=
  EBox (Lam (Lam (App (Lam (App (App (App EForce (Var 3)) (Var 2)) (Var 0)))
    (App ESend (Pair EUnit (Var 0)))))).

Definition lc_ty (A : ty) : ty :=
  TBox 0 0 (BCs [] (λ _, False))
    (TLolli None None TUnit (TLolli None None A (TLolli None None (TSess SEnd (pvar 0)) TUnit))).

Theorem lc_r2_fails :
  guarded lc_box ∧ lf_r1 lc_box = true ∧ lf_r2 lc_box = false ∧ lf_r2h [] lc_box = false ∧
  lf_r2h [(lc_box, lc_ty (TSess SEnd (pvar 0)))] lc_box = false ∧
  lf_r2h [(lc_box, lc_ty (TPt (pvar 0)))] lc_box = true.
Proof. unfold guarded. split_and!; vm_compute; reflexivity. Qed.

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

Lemma sdepth_chv n : sdepth (ReceivedChain.chv n) = n.
Proof. induction n as [|n IH]; [done|]. cbn. by rewrite IH. Qed.

(** Opening at constants keeps the depth of a name. *)
Lemma sdepth_open xs p : all_const xs → sdepth (pn_open xs p) = sdepth p.
Proof.
  intros Hxs. induction p as [a|a|q IH b i]; cbn [pn_open sdepth]; [done| |by rewrite IH].
  destruct (xs !! a) as [z|] eqn:E; [|done].
  by destruct (proj1 (Forall_lookup _ _) Hxs a z E) as [c ->].
Qed.

Theorem rc_lfsource : lfsource ReceivedChain.ch_Ψ ReceivedChain.ch_main TUnit.
Proof.
  split_and!.
  - apply ReceivedChain.ch_created.
  - constructor.
  - split; [apply ReceivedChain.ch_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply cworld_depth_wf. intros x y H.
    destruct (hyps_lt_snoc [] [] ReceivedChain.chc_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
      [by apply hyps_lt_nil in Hn|].
    unfold drank. cbn [pt_open pt_name pt_off]. rewrite !sdepth_open by (repeat econstructor).
    destruct Hf as [(n & E)|(n & [E|E])]; injection E as -> ->; unfold lexlt;
      cbn [pt_name pt_off fst snd ReceivedChain.chv sdepth]; rewrite ?sdepth_chv; lia.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

Theorem rc_lfptyped : ∃ W, strict W ∧ lfptyped W ∅ (∅, {[+ ReceivedChain.ch_main +]}) TUnit.
Proof. exists (cworld ReceivedChain.ch_Ψ). exact (lfsource_lfptyped _ _ _ rc_lfsource). Qed.

(** The growing ring (GrowRing.v, Padovani III.7). R2′ rejects it,
    because the received z goes to the self. Under the constant world
    the facts of e are facts of W. They climb without end, and the rank
    2·depth + offset still makes W well founded. *)
Theorem rg_r2_fails : lf_r2 GrowRing.rg_main = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pdepth_open xs p : all_const xs → GrowRing.pdepth (pn_open xs p) = GrowRing.pdepth p.
Proof.
  intros Hxs. induction p as [a|a|q IH b i]; cbn [pn_open GrowRing.pdepth]; [done| |by rewrite IH].
  destruct (xs !! a) as [z|] eqn:E; [|done].
  by destruct (proj1 (Forall_lookup _ _) Hxs a z E) as [c ->].
Qed.

Lemma rg_wf : wf_world (cworld GrowRing.rg_Ψ).
Proof.
  apply (cworld_rank_wf lt _ GrowRing.rg_rank Wf_nat.lt_wf); [intros a b c; lia| | |].
  - intros x y H.
    destruct (hyps_lt_snoc [] [] GrowRing.rg0_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
      [by apply hyps_lt_nil in Hn|].
    pose proof (GrowRing.rg0_rank x0 y0 Hf) as Hr. unfold GrowRing.rg_rank in *.
    cbn [pt_open pt_name pt_off]. by rewrite !pdepth_open by (repeat econstructor).
  - intros x. unfold GrowRing.rg_rank, pt_shift. cbn. lia.
  - intros x. unfold GrowRing.rg_rank, pt_shift, pt_dual. cbn. lia.
Qed.

Theorem rg_lfsource : lfsource GrowRing.rg_Ψ GrowRing.rg_main TUnit.
Proof.
  split_and!.
  - apply GrowRing.rg_created.
  - constructor.
  - split; [apply GrowRing.rg_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply rg_wf.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

(** The alternating bit protocol (ABP.v, Padovani III.8). No end
    travels, so R2′ already accepts it. The world has the ceiling θ
    above three interleaved ascending chains, and the pair rank makes it
    well founded. *)
Theorem abp_r2 : lf_r2 ABP.abp_main = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abp_wf : wf_world (cworld ABP.abp_Ψ).
Proof. unfold ABP.abp_Ψ. apply (ladder_wf ABP.rkc ABP.rkc_S 3 3). lia. Qed.

Theorem abp_lfsource : lfsource ABP.abp_Ψ ABP.abp_main TUnit.
Proof.
  split_and!.
  - apply ABP.abp_created.
  - constructor.
  - split; [apply ABP.abp_typed|vm_compute; reflexivity].
  - vm_compute. reflexivity.
  - exists []. split; [intros b T Hin; by apply elem_of_nil in Hin|intros e ->; vm_compute; reflexivity].
  - exists [], []. split_and!.
    + intros b T Hin. by apply elem_of_nil in Hin.
    + reflexivity.
    + intros e ->. exists []. split; [vm_compute; reflexivity|done].
  - apply abp_wf.
  - apply root_ok_intro. vm_compute. reflexivity.
Qed.

(** ** The budgets of the examples (plan §17.6, §17.8)

    Each example world is [src_world Ψ t], [cworld Ψ] with the budgets
    of the root graph and of the stretch bound of t. Only the forwarder
    has an edge, so d = 1 there. In the other examples d = 0, every end
    gets 2L and every floor is L. *)

(** With no root edge every end gets 2L and every floor is L. *)
Lemma budgets_flat W L x :
  w_bud (with_budgets W [] L) x = Some (2 * L) ∧ w_pay (with_budgets W [] L) x = L.
Proof. rewrite with_budgets_bud, with_budgets_pay. cbn. split; [f_equal|]; lia. Qed.

(** The forwarder. fwd receives on its slot [false], which main fills
    with a at the constant 1, and forwards along its slot [true], which
    main fills with b at the constant 0. Both slots keep their roots from
    round to round, and the root graph is the one edge from 1 to 0.
    A round has 3 units (fwd receives, sends and spawns), so L = 6.
    Every end gets 3L = 18. A payload sent along a carrier of root 1 (by
    the producer) arrives with floor 2L = 12, and the same payload
    forwarded along b with floor L = 6. *)
Definition fw_W : world := src_world Forwarder.fw_Ψ Forwarder.fw_main.

Theorem fw_budgets :
  strict fw_W ∧ lfptyped fw_W ∅ (∅, {[+ Forwarder.fw_main +]}) TUnit ∧
  root_edges Forwarder.fw_main = Some [(NConst 1, NConst 0)] ∧ stretch_len Forwarder.fw_main = 6 ∧
  (∀ x, w_bud fw_W x = Some 18) ∧
  (∀ k, pt_root k = NConst 1 → w_pay fw_W k = 12) ∧
  (∀ k, pt_root k = NConst 0 → w_pay fw_W k = 6).
Proof.
  destruct (lfsource_budgets _ _ _ fw_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|vm_compute; reflexivity| | |].
  - intros x. unfold fw_W, src_world. rewrite with_budgets_bud. vm_compute. reflexivity.
  - intros k Hk. unfold fw_W, src_world. rewrite with_budgets_pay, Hk. vm_compute. reflexivity.
  - intros k Hk. unfold fw_W, src_world. rewrite with_budgets_pay, Hk. vm_compute. reflexivity.
Qed.

(** The examples without a root edge. *)
Lemma src_flat Ψ t L x :
  root_edges t = Some [] → stretch_len t = L →
  w_bud (src_world Ψ t) x = Some (2 * L) ∧ w_pay (src_world Ψ t) x = L.
Proof. intros HE HL. unfold src_world. rewrite HE, HL. apply budgets_flat. Qed.

Definition tc_W : world := src_world TailCall.tc_Ψ TailCall.tc_main.

Theorem tc_budgets :
  strict tc_W ∧ lfptyped tc_W ∅ (∅, {[+ TailCall.tc_main +]}) TUnit ∧
  stretch_len TailCall.tc_main = 2 ∧ ∀ x, w_bud tc_W x = Some 4 ∧ w_pay tc_W x = 2.
Proof.
  destruct (lfsource_budgets _ _ _ tc_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 2 x); vm_compute; reflexivity.
Qed.

(** The CFST scheduler. Its main spawns the six agents of the ring,
    whose top-level code counts with main, so a segment has 9 units. *)
Definition sch_W : world := src_world (CfstScheduler.sch_Ψ 6) CfstScheduler.sch_main.

Theorem sch_budgets :
  strict sch_W ∧ lfptyped sch_W ∅ (∅, {[+ CfstScheduler.sch_main +]}) TUnit ∧
  stretch_len CfstScheduler.sch_main = 18 ∧ ∀ x, w_bud sch_W x = Some 36 ∧ w_pay sch_W x = 18.
Proof.
  destruct (lfsource_budgets _ _ _ sch_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 18 x); vm_compute; reflexivity.
Qed.

Definition rc_W : world := src_world ReceivedChain.ch_Ψ ReceivedChain.ch_main.

Theorem rc_budgets :
  strict rc_W ∧ lfptyped rc_W ∅ (∅, {[+ ReceivedChain.ch_main +]}) TUnit ∧
  stretch_len ReceivedChain.ch_main = 6 ∧ ∀ x, w_bud rc_W x = Some 12 ∧ w_pay rc_W x = 6.
Proof.
  destruct (lfsource_budgets _ _ _ rc_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 6 x); vm_compute; reflexivity.
Qed.

Definition rg_W : world := src_world GrowRing.rg_Ψ GrowRing.rg_main.

Theorem rg_budgets :
  strict rg_W ∧ lfptyped rg_W ∅ (∅, {[+ GrowRing.rg_main +]}) TUnit ∧
  stretch_len GrowRing.rg_main = 14 ∧ ∀ x, w_bud rg_W x = Some 28 ∧ w_pay rg_W x = 14.
Proof.
  destruct (lfsource_budgets _ _ _ rg_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 14 x); vm_compute; reflexivity.
Qed.

Definition abp_W : world := src_world ABP.abp_Ψ ABP.abp_main.

Theorem abp_budgets :
  strict abp_W ∧ lfptyped abp_W ∅ (∅, {[+ ABP.abp_main +]}) TUnit ∧
  stretch_len ABP.abp_main = 8 ∧ ∀ x, w_bud abp_W x = Some 16 ∧ w_pay abp_W x = 8.
Proof.
  destruct (lfsource_budgets _ _ _ abp_lfsource) as [HS HL].
  split_and!; [exact HS|exact HL|vm_compute; reflexivity|].
  intros x. apply (src_flat _ _ 8 x); vm_compute; reflexivity.
Qed.

(** A forward outside boxes (stage L6a). The term creates a at the
    constant 1 and b at the constant 0, receives d on a and sends it on
    along b.
    The root graph has the edge from 1 to 0, so the floor along b lies
    a stretch below the floor along a. Passing d to a box instead hands
    it on along a path the graph does not see, and the term has no root
    graph. *)
Definition relay_main : expr :=
  let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
    (LetP (App ERecv (Var 3))
      (App EClos (App ESend (Pair (Var 1) (Var 3)))))).

Definition relay_call : expr :=
  let_new_pair_at (EPt (pconst 1))
    (LetP (App ERecv (Var 1)) (App (App EForce (EBox (Lam (App EClos (Var 0))))) (Var 1))).

Theorem relay_roots :
  root_edges relay_main = Some [(NConst 1, NConst 0)] ∧ root_edges relay_call = None.
Proof. split; vm_compute; reflexivity. Qed.
