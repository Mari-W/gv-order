(** * Fuel as a predicate on threads (lock-freedom plan §17.3, §17.8, §18, §19.3)

    [FuelE n W σ r π φ tk d e] is a step-indexed predicate on one
    thread e. It reads no type. π maps the ends the thread holds to
    their points, φ maps them to their counters, and tk is the
    thread's count of link tickets. σ is the cost type of the value e
    returns, r the tickets e must still hold then, and d the frame, the
    channel actions e may still perform before it returns (None is ∞).
    A thread runs at σ = [cany], r = 0 and d = None ([fsem]). The
    budgets are read in the world, [w_bud W] for the refill and cap of
    an end at a point, and [w_pc W] for the cost type of a payload sent
    on a carrier at a point (plan §19.3). The index counts every step,
    administrative ones included.

    A channel step of the holder on another end burns one unit (F-Tick)
    and one unit of the frame. Internal steps, new, spawn and links
    burn no counter. Acting on an end refills it to the budget of its
    next point. A send hands its payload on with the counter minus one,
    in [Vfuel] at the payload cost type of the carrier, and a spawn
    hands the ends of the closure to the child with the counter minus
    one. A link needs a ticket and spends it (plan §18.3). A spawn
    gives ⌈tk/2⌉ tickets to the child and keeps ⌊tk/2⌋. A thread acts
    only on ends whose partner has a finite budget (F-Wait), and no
    counter exceeds its budget (F-Cap). Receive is universal over the
    incoming values at the payload cost type of the carrier, whose
    ends sit at points the world knows ([fin_ok]). A value returned
    satisfies [Vfuel] at σ, at the level of the expression. No clause
    writes the counters of another thread.

    [Fdef] closes the predicate under injective renamings of channels
    ([kinj], plan §19.8 hole 1) and under extensions of the budgets.
    The new clause asks the new channel to be fresh against the
    thread's own map (§19.8 hole 2).

    [Vfuel n W σ π φ w] recurses on the value w and reads the cost
    type σ (plan §19.3). A closure of type [CArr c t h σ1 σ2] at credit
    a has captured counters at least h + a, and for every later world,
    lower level, counters at or above h and argument in [Vfuel] at σ1,
    its body after the β step satisfies [FuelE] at σ2 with frame c and
    every reserve and ticket count that meet t.

    A link loop (C3 of the plan, §10.1) spends a ticket per round, so it
    has no fuel at any finite ticket count ([link_tickets_fall]).

    [fupd] computes the counters of the successor from the label. *)

From stdpp Require Import base gmap.
From LRGV Require Import lang.Semantics relation.Worlds lockfree.Instr.
From LRGV Require Export relation.CostTypes.

(** Counters ([fuel], [fle], [ftick]) live in relation/CostTypes.v. *)

(** ** Maps of ends *)

(** The map without the ends of X, and the map on the ends of X. *)
Definition mrem {Y : Type} (X : gset cend) (m : gmap cend Y) : gmap cend Y :=
  filter (λ kv : cend * Y, kv.1 ∉ X) m.
Definition mres {Y : Type} (X : gset cend) (m : gmap cend Y) : gmap cend Y :=
  filter (λ kv : cend * Y, kv.1 ∈ X) m.

Lemma lookup_mrem_Some {Y : Type} (X : gset cend) (m : gmap cend Y) o a :
  mrem X m !! o = Some a ↔ m !! o = Some a ∧ o ∉ X.
Proof. unfold mrem. by rewrite map_lookup_filter_Some. Qed.

Lemma lookup_mres_Some {Y : Type} (X : gset cend) (m : gmap cend Y) o a :
  mres X m !! o = Some a ↔ m !! o = Some a ∧ o ∈ X.
Proof. unfold mres. by rewrite map_lookup_filter_Some. Qed.

Lemma dom_mrem {Y : Type} (X : gset cend) (m : gmap cend Y) : dom (mrem X m) = dom m ∖ X.
Proof.
  apply set_eq. intros o. rewrite elem_of_difference, !elem_of_dom.
  split.
  - intros [a Ha]. apply lookup_mrem_Some in Ha as [Ha Hx]. eauto.
  - intros [[a Ha] Hx]. exists a. by apply lookup_mrem_Some.
Qed.

Lemma dom_mres {Y : Type} (X : gset cend) (m : gmap cend Y) : dom (mres X m) = dom m ∩ X.
Proof.
  apply set_eq. intros o. rewrite elem_of_intersection, !elem_of_dom.
  split.
  - intros [a Ha]. apply lookup_mres_Some in Ha as [Ha Hx]. eauto.
  - intros [[a Ha] Hx]. exists a. by apply lookup_mres_Some.
Qed.

(** ** Anatomy of a session label, for fuel *)

(** The end a session action acts on. A link acts on none. *)
Definition sl_end (σ : slabel) : option cend :=
  match σ with
  | SRecv o _ | SSend o _ | SClos o | SSel o _ | SBra o _ => Some o
  | SLink _ => None
  end.

(** The end and point after the action, from the point k before it.
    Send and receive move to k + 1 and keep the bit. Select moves to
    (k[i])‾, which is negative, and branch to k[i], which is positive.
    Close and link leave nothing. *)
Definition sl_next (σ : slabel) (k : point) : option (cend * point) :=
  match σ with
  | SRecv o _ | SSend o _ => Some (o, pt_shift 1 k)
  | SSel o b => Some ((o.1, false), sel_pt k b)
  | SBra o b => Some ((o.1, true), bra_pt k b)
  | SClos _ | SLink _ => None
  end.

(** The ends a session action hands on: the payload of a send, both
    ends of a link. *)
Definition sl_out (σ : slabel) : gset cend :=
  match σ with
  | SSend _ w => fends w
  | SLink cd => cd
  | _ => ∅
  end.

(** ** The fuel update along a step *)

(** An action on its end: the other counters tick, the end refills to
    the budget of its next point. *)
Definition fact (W : world) (σ : slabel) (π : gmap cend point) (φ : gmap cend fuel)
    : gmap cend point * gmap cend fuel :=
  match sl_end σ with
  | None => (π, φ)
  | Some o =>
      match π !! o with
      | None => (π, φ)
      | Some k =>
          match sl_next σ k with
          | None => (delete o π, ftick <$> delete o φ)
          | Some (o', k') =>
              (<[o' := k']> (delete o π), <[o' := w_bud W k']> (ftick <$> delete o φ))
          end
      end
  end.

(** The successor's points and counters. At receive this is the part
    the receiver keeps, before the incoming ends join. *)
Definition fupd (W : world) (π : gmap cend point) (φ : gmap cend fuel) (α : tlabel)
    : gmap cend point * gmap cend fuel :=
  match α with
  | LBeta => (π, φ)
  | LNew c x =>
      (<[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π),
       <[(c, pt_pol x) := w_bud W x]> (<[(c, negb (pt_pol x)) := w_bud W (pt_dual x)]> φ))
  | LSpawn w => (mrem (fends w) π, mrem (fends w) φ)
  | LSess σ => fact W σ (mrem (sl_out σ) π) (mrem (sl_out σ) φ)
  end.

(** The points and counters a spawn hands to the child. *)
Definition fchild (π : gmap cend point) (φ : gmap cend fuel) (w : expr)
    : gmap cend point * gmap cend fuel :=
  (mres (fends w) π, ftick <$> mres (fends w) φ).

(** ** The clauses *)

(** F-Cap: every counter lies at or below the budget of its end's point. *)
Definition fcap (W : world) (π : gmap cend point) (φ : gmap cend fuel) : Prop :=
  ∀ o f, φ !! o = Some f → ∃ k, π !! o = Some k ∧ fle f (w_bud W k).

(** F-Wait: a thread acts only on a held end whose partner has a finite
    budget. *)
Definition fwait (W : world) (π : gmap cend point) (e : expr) : Prop :=
  ∀ σ e' o, tstep e (LSess σ) e' → sl_end σ = Some o →
    ∃ k, π !! o = Some k ∧ w_bud W (pt_dual k) ≠ None.

(** F-Tick: an action on o burns one unit of every other finite counter. *)
Definition ftick_ok (o : cend) (φ : gmap cend fuel) : Prop :=
  ∀ o' m, o' ≠ o → φ !! o' = Some (Some m) → 1 ≤ m.

(** Handing the ends X on: the counter minus one meets the floor fl. *)
Definition fhand (fl : nat) (X : gset cend) (φ : gmap cend fuel) : Prop :=
  ∀ o m, o ∈ X → φ !! o = Some (Some m) → fl + 1 ≤ m.

(** Only ends whose partner has a finite budget travel in a message.
    Acting on an end whose partner has budget ∞ breaks F-Wait anyway. *)
Definition ftravel (W : world) (π : gmap cend point) (X : gset cend) : Prop :=
  ∀ o k, o ∈ X → π !! o = Some k → w_bud W (pt_dual k) ≠ None.

(** Incoming ends: points and counters on exactly the ends of w, under
    the cap, at points W knows. An extension of W keeps the budgets only
    at the points W knows ([wext_bud]), so an incoming end at an unknown
    point could see its budget change (quirk A13c). The floor of §17.8
    is gone: the payload cost type [w_pc] carries it (plan §19.3). *)
Definition fin_ok (W : world) (w : expr)
    (πi : gmap cend point) (φi : gmap cend fuel) : Prop :=
  dom πi = fends w ∧ dom φi = fends w ∧ fcap W πi φi ∧
  (∀ o k, πi !! o = Some k → w_bud W (pt_dual k) ≠ None) ∧
  ∀ o k, πi !! o = Some k → pt_known W k.

(** ** Protocols in a world (plan §19.3) *)

Definition pfits (W : world) : point → cpro → Prop := pfits_at (pt_known W) (w_bud W) (w_pc W).
Definition pfitpt (W : world) : point → cprof → Prop := pfitpt_at (pt_known W) (w_bud W) (w_pc W).

(** ** The predicates, level by level *)

(** E reads the result type, the reserve, points, counters, the ticket
    count and the frame. V reads the cost type, points and counters. *)
Abbreviation epred :=
  (world → cta → nat → gmap cend point → gmap cend fuel → nat → fuel → expr → Prop).
Abbreviation vpred := (world → cta → gmap cend point → gmap cend fuel → expr → Prop).

(** The frame after a step: an action spends one unit. *)
Definition dupd (d : fuel) (α : tlabel) : fuel :=
  match α with
  | LSess s => match sl_end s with Some _ => ftick d | None => d end
  | _ => d
  end.

(** The thread holds no other end of the channel of o. A select or a
    branch changes the bit of its end, and the partner of a select or
    branch is never the same thread (plan §19.13). *)
Definition fsolo (π : gmap cend point) (o : cend) : Prop :=
  ∀ b, (o.1, b) ∈ dom π → (o.1, b) = o.

(** The obligation of a step e --α--> e' at index n' + 1, given the
    predicates E and V at the levels up to n'. An action needs a unit
    of the frame. A link needs a ticket and spends it. A spawn splits
    the tickets, ⌈tk/2⌉ to the child and ⌊tk/2⌋ to the parent (plan
    §18.3); the child runs as a thread. The new clause holds only for a
    channel the thread does not hold (plan §19.8). A send, a spawn and a
    link hand on only ends the thread holds, a send not its own subject,
    and a select or branch continues only when the thread holds no other
    end of its channel (plan §19.13). *)
Definition Fobl (E : nat → epred) (V : nat → vpred) (n' : nat) (W : world) (σ : cta) (r : nat)
    (π : gmap cend point) (φ : gmap cend fuel) (tk : nat) (d : fuel) (α : tlabel) (e' : expr)
    : Prop :=
  match α with
  | LBeta => E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 tk d e'
  | LNew c x =>
      (c, true) ∉ dom π → (c, false) ∉ dom π →
      E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 tk d e'
  | LSpawn w =>
      fends w ⊆ dom π ∧
      fhand 0 (fends w) φ ∧
      E n' W cany 0 (fchild π φ w).1 (fchild π φ w).2 (Nat.div2 (S tk)) None (App w EUnit) ∧
      E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 (Nat.div2 tk) d e'
  | LSess s =>
      (∀ o, sl_end s = Some o → ftick_ok o φ ∧ fle (Some 1) d) ∧
      match s with
      | SSend o w =>
          (* the thread holds what it sends, and not the end it sends on
             (plan §19.13) *)
          fends w ⊆ dom π ∖ {[o]} ∧
          ftravel W π (fends w) ∧
          (* the payload, at the counters the receiver gets (decision 2026-11-09),
             at the payload cost type of the carrier *)
          (∀ k, π !! o = Some k →
             V n' W (w_pc W k) (mres (fends w) π) (ftick <$> mres (fends w) φ) w) ∧
          E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 tk (ftick d) e'
      | SRecv o w =>
          (* the payload cost type is keyed by the carrier's point at the
             sender, the dual of the receiver's point *)
          ∀ k j πi φi, π !! o = Some k → j ≤ n' →
            dom πi ## dom (fupd W π φ α).1 →
            fin_ok W w πi φi →
            V j W (w_pc W (pt_dual k)) πi φi w →
            E j W σ r ((fupd W π φ α).1 ∪ πi) ((fupd W π φ α).2 ∪ φi) tk (ftick d) e'
      | SLink cd => cd ⊆ dom π ∧ 1 ≤ tk ∧ E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 (tk - 1) d e'
      | SSel o _ | SBra o _ =>
          (* only when the partner is not this thread (plan §19.13) *)
          fsolo π o → E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 tk (ftick d) e'
      | SClos _ => E n' W σ r (fupd W π φ α).1 (fupd W π φ α).2 tk (ftick d) e'
      end
  end.

(** [renk g m m']: m' is m with every end (c, b) renamed to (g c, b).
    Two ends with one image must carry one value. *)
Definition renk {Y : Type} (g : chan → chan) (m m' : gmap cend Y) : Prop :=
  (∀ o v, m !! o = Some v → m' !! (g o.1, o.2) = Some v) ∧
  (∀ o' v, m' !! o' = Some v → ∃ o, o' = (g o.1, o.2) ∧ m !! o = Some v).

Lemma renk_id {Y : Type} (m : gmap cend Y) : renk id m m.
Proof. split; [by intros [c b]|]. intros [c b] v H. by exists (c, b). Qed.

Lemma renk_compose {Y : Type} (g h : chan → chan) (m m1 m2 : gmap cend Y) :
  renk h m m1 → renk g m1 m2 → renk (g ∘ h) m m2.
Proof.
  intros [H1 H2] [G1 G2]. split.
  - intros o v Ho. apply (G1 (h o.1, o.2)). by apply H1.
  - intros o' v Ho'. destruct (G2 o' v Ho') as (o1 & -> & Ho1).
    destruct (H2 o1 v Ho1) as (o & -> & Ho). by exists o.
Qed.

(** g renames the ends of m injectively (plan §19.8, hole 1). *)
Definition kinj {Y : Type} (g : chan → chan) (m : gmap cend Y) : Prop :=
  ∀ o1 o2 v1 v2, m !! o1 = Some v1 → m !! o2 = Some v2 → (g o1.1, o1.2) = (g o2.1, o2.2) → o1 = o2.

Lemma kinj_id {Y : Type} (m : gmap cend Y) : kinj id m.
Proof. intros [c1 b1] [c2 b2] v1 v2 _ _ H. simpl in H. by simplify_eq. Qed.

Lemma kinj_compose {Y : Type} (g h : chan → chan) (m m1 : gmap cend Y) :
  renk h m m1 → kinj h m → kinj g m1 → kinj (g ∘ h) m.
Proof.
  intros [H1 _] Hh Hg o1 o2 v1 v2 Ho1 Ho2 Heq. apply (Hh o1 o2 v1 v2 Ho1 Ho2).
  apply (Hg (h o1.1, o1.2) (h o2.1, o2.2) v1 v2); [by apply H1|by apply H1|exact Heq].
Qed.

(** W′ extends W on budgets: it knows the names of W and keeps their
    budgets and payload cost types. The inclusion of names makes the
    relation transitive. *)
Definition wbext (W W' : world) : Prop := w_names W ⊆ w_names W' ∧ wext_bud W W'.

Lemma wbext_refl W : wbext W W.
Proof. done. Qed.

Lemma wbext_trans W1 W2 W3 : wbext W1 W2 → wbext W2 W3 → wbext W1 W3.
Proof.
  intros [H12 B12] [H23 B23]. split; [set_solver|]. by apply (wext_bud_trans W1 W2 W3).
Qed.

(** The cap in every extension of the world. *)
Definition fcap_ext (W : world) (π : gmap cend point) (φ : gmap cend fuel) : Prop :=
  ∀ W', wbext W W' → fcap W' π φ.

(** An argument of a closure: a value with counters on exactly its
    points, under the cap in every extension (plan §19.14). *)
Definition farg (W : world) (v : expr) (πa : gmap cend point) (φa : gmap cend fuel) : Prop :=
  is_val v = true ∧ dom φa = dom πa ∧ fcap_ext W πa φa.

(** Ends held by a value sit at points the world knows, and their
    partners have finite budgets, so they may travel (plan §19.14). *)
Definition fpts (W : world) (π : gmap cend point) : Prop :=
  ∀ o k, π !! o = Some k → pt_known W k ∧ w_bud W (pt_dual k) ≠ None.

(** The closure clause of [Vfdef], for the body [body v] after the β
    step (plan §19.3). The captured counters lie at or above h + a. For
    every later world, lower level, counters φ' at or above the floor h
    under the cap in every extension, and argument in V at σ1 under the
    cap in every extension, the body satisfies E at σ2 with frame c, for
    every reserve r and ticket count tk that meet the transformer t.
    Only the floor check reads the actual counters φ. The cap premises
    are what an application can supply (plan §19.14). *)
Definition farr (E : nat → epred) (V : nat → vpred) (n : nat) (W : world)
    (c : fuel) (t : tix) (h : nat) (σ1 σ2 : cta) (a : fuel)
    (π : gmap cend point) (φ : gmap cend fuel) (body : expr → expr) : Prop :=
  (∀ o f, φ !! o = Some f → fle (fadd (Some h) a) f) ∧
  ∀ W' j φ' v πa φa, wbext W W' → j < n → dom φ' = dom π → fcap_ext W' π φ' →
    (∀ o f, φ' !! o = Some f → fle (Some h) f) →
    dom πa ## dom π → farg W' v πa φa → V j W' σ1 πa φa v →
    ∀ r tk, meets t r tk → E j W' σ2 r (π ∪ πa) (φ' ∪ φa) tk c (body v).

(** Values at a cost type, by recursion on the value (plan §19.3). A
    primitive constant is not a value at an arrow type, and a box holds
    no end (plan §19.14). A pair adds its credit to both components and
    splits its points into two disjoint parts, one per component (plan
    §19.13). *)
Fixpoint Vfdef (E : nat → epred) (V : nat → vpred) (n : nat) (W : world) (σ : cta)
    (π : gmap cend point) (φ : gmap cend fuel) (w : expr) {struct w} : Prop :=
  match σ with
  | CTa τ a =>
      match τ with
      | CAny => True
      | CVal => w = EUnit ∧ π = ∅
      | CPt ρ => ∃ x, w = EPt x ∧ π = ∅ ∧ pt_known W x ∧ pfitpt W x ρ
      | CEnd P =>
          ∃ c b x f, w = Chan c b ∧ π = {[(c, b) := x]} ∧ pfits W x P ∧
            φ !! (c, b) = Some f ∧ fle a f ∧ fpts W π
      | CArr c t h σ1 σ2 =>
          match w with
          | Lam eb => dom π = fends w ∧ fpts W π ∧ farr E V n W c t h σ1 σ2 a π φ (λ v, subst1 v eb)
          | _ => False
          end
      | CBox c t σ' =>
          match w with
          | EBox eb =>
              π = ∅ ∧ fends eb = ∅ ∧ ∀ W' j r tk, wbext W W' → j < n → meets t r tk →
                E j W' σ' r ∅ ∅ tk c (subst1 (EBox eb) eb)
          | _ => False
          end
      | CProd σ1 σ2 =>
          match w with
          | Pair u v =>
              (* the points split into two disjoint parts, the counters
                 follow them (plan §19.13) *)
              ∃ π1 π2, π = π1 ∪ π2 ∧ dom π1 ## dom π2 ∧
                Vfdef E V n W (cadd a σ1) π1 (mres (dom π1) φ) u ∧
                Vfdef E V n W (cadd a σ2) π2 (mres (dom π2) φ) v
          | _ => False
          end
      | CSum σ1 σ2 =>
          match w with
          | Inj1 u => Vfdef E V n W (cadd a σ1) π φ u
          | Inj2 u => Vfdef E V n W (cadd a σ2) π φ u
          | _ => False
          end
      end
  end.

(** FuelE is closed under injective renamings of channels by definition:
    a link renames the peer of the removed end in the whole soup
    (decision 2026-11-09, under delegation; injectivity, plan §19.8). It
    is also closed under every extension of the budgets ([wbext]), so
    that a thread keeps its fuel in a joined world (decision 2026-11-16,
    under delegation). A value satisfies V at σ at the level of the
    expression and holds its reserve (plan §19.8, hole 3). *)
Definition Fdef (E : nat → epred) (V : nat → vpred) (n' : nat) (W : world) (σ : cta) (r : nat)
    (π : gmap cend point) (φ : gmap cend fuel) (tk : nat) (d : fuel) (e : expr) : Prop :=
  ∀ W' g π' φ', wbext W W' → kinj g π → renk g π π' → renk g φ φ' →
    fcap W' π' φ' ∧ fwait W' π' (emap g e) ∧
    (is_val (emap g e) = true → r ≤ tk ∧ Vfdef E V (S n') W' σ π' φ' (emap g e)) ∧
    ∀ α e', tstep (emap g e) α e' → Fobl E V n' W' σ r π' φ' tk d α e'.

Record flevel := FLevel { fE : epred; fV : vpred }.

Definition mk_flevel (below : nat → flevel) (n : nat) : flevel :=
  {| fE := match n with
           | 0 => λ _ _ _ _ _ _ _ _, True
           | S n' => Fdef (λ j, fE (below j)) (λ j, fV (below j)) n'
           end;
     fV := Vfdef (λ j, fE (below j)) (λ j, fV (below j)) n |}.

Definition dummy_flevel : flevel :=
  {| fE := λ _ _ _ _ _ _ _ _, False; fV := λ _ _ _ _ _, False |}.

(** [flevels n j] is level j for every j < n. *)
Fixpoint flevels (n : nat) : nat → flevel :=
  match n with
  | 0 => λ _, dummy_flevel
  | S n' => λ j, if decide (j < n') then flevels n' j else mk_flevel (flevels n') n'
  end.

Definition flevel_at (n : nat) : flevel := flevels (S n) n.

Definition FuelE (n : nat) : epred := fE (flevel_at n).
Definition Vfuel (n : nat) : vpred := fV (flevel_at n).

(** Every held end starts full (§17.4), at a ticket count fixed for
    every index (plan §18.3). A thread returns anything, holds no
    reserve and has no frame (plan §19.3). *)
Definition fsem (W : world) (π : gmap cend point) (t : expr) : Prop :=
  ∃ tk, ∀ n, FuelE n W cany 0 π (w_bud W <$> π) tk None t.

(** FuelE of a thread: result [cany], reserve 0, frame ∞. *)
Abbreviation FuelT n W π φ tk e := (FuelE n W cany 0 π φ tk None e).

(** ** Unfolding *)

Lemma flevel_at_eq n : flevel_at n = mk_flevel (flevels n) n.
Proof. unfold flevel_at. simpl. by destruct (decide (n < n)); [lia|]. Qed.

Lemma flevels_at n j : j < n → flevels n j = flevel_at j.
Proof.
  revert j. induction n as [|n' IH]; intros j Hj; [lia|].
  simpl. destruct (decide (j < n')) as [H|H].
  - by apply IH.
  - assert (j = n') as -> by lia. by rewrite flevel_at_eq.
Qed.

Lemma Fobl_ext (E1 E2 : nat → epred) (V1 V2 : nat → vpred) n' W σ r π φ tk d α e' :
  (∀ j, j ≤ n' → ∀ W σ r π φ tk d e, E1 j W σ r π φ tk d e ↔ E2 j W σ r π φ tk d e) →
  (∀ j, j ≤ n' → ∀ W σ π φ e, V1 j W σ π φ e ↔ V2 j W σ π φ e) →
  Fobl E1 V1 n' W σ r π φ tk d α e' ↔ Fobl E2 V2 n' W σ r π φ tk d α e'.
Proof.
  intros HE HV.
  assert (HE' : ∀ W σ r π φ tk d e, E1 n' W σ r π φ tk d e ↔ E2 n' W σ r π φ tk d e)
    by (apply HE; lia).
  assert (HV' : ∀ W σ π φ e, V1 n' W σ π φ e ↔ V2 n' W σ π φ e) by (apply HV; lia).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl.
  - apply HE'.
  - split; intros [H1 H2]; split; try done; intros k j πi φi Hk Hj Hd Hin Hv;
      apply (HE j Hj); apply (H2 k); try done; by apply (HV j Hj).
  - split; intros (H1 & H0 & H2 & H3 & H4); split_and!; try done;
      first [intros k Hk; apply HV'; by apply H3|by apply HE'].
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite !HE'.
Qed.

Lemma farr_ext (E1 E2 : nat → epred) (V1 V2 : nat → vpred) n W c t h σ1 σ2 a π φ body :
  (∀ j, j < n → ∀ W σ r π φ tk d e, E1 j W σ r π φ tk d e ↔ E2 j W σ r π φ tk d e) →
  (∀ j, j < n → ∀ W σ π φ e, V1 j W σ π φ e ↔ V2 j W σ π φ e) →
  farr E1 V1 n W c t h σ1 σ2 a π φ body ↔ farr E2 V2 n W c t h σ1 σ2 a π φ body.
Proof.
  intros HE HV. unfold farr.
  split; intros [Hf H]; split; try done;
    intros W' j φ' v πa φa Hb Hj Hd Hc Hh Hdis Hin Hv r0 tk0 Hm;
    [rewrite <-HE by done|rewrite HE by done];
    apply H; try done; [rewrite HV by done|rewrite <-HV by done]; done.
Qed.

Lemma Vfdef_ext (E1 E2 : nat → epred) (V1 V2 : nat → vpred) n W σ π φ w :
  (∀ j, j < n → ∀ W σ r π φ tk d e, E1 j W σ r π φ tk d e ↔ E2 j W σ r π φ tk d e) →
  (∀ j, j < n → ∀ W σ π φ e, V1 j W σ π φ e ↔ V2 j W σ π φ e) →
  Vfdef E1 V1 n W σ π φ w ↔ Vfdef E2 V2 n W σ π φ w.
Proof.
  intros HE HV.
  induction w in σ, π, φ |- *; destruct σ as [τ a]; destruct τ; simpl; try done;
    try (by rewrite (farr_ext E1 E2 V1 V2)); try (by rewrite IHw);
    try (split; intros (π1 & π2 & Hπ & Hd & H1 & H2); exists π1, π2; split_and!; try done;
         first [by apply IHw1|by apply IHw2]).
  all: split; intros (Hp & Hf & H); split_and!; try done; intros W' j r0 tk0 Hb Hj Hm;
    [rewrite <-HE by done|rewrite HE by done]; auto.
Qed.

Lemma Fdef_ext (E1 E2 : nat → epred) (V1 V2 : nat → vpred) n' W σ r π φ tk d e :
  (∀ j, j ≤ n' → ∀ W σ r π φ tk d e, E1 j W σ r π φ tk d e ↔ E2 j W σ r π φ tk d e) →
  (∀ j, j ≤ n' → ∀ W σ π φ e, V1 j W σ π φ e ↔ V2 j W σ π φ e) →
  Fdef E1 V1 n' W σ r π φ tk d e ↔ Fdef E2 V2 n' W σ r π φ tk d e.
Proof.
  intros HE HV. unfold Fdef.
  assert (HVf : ∀ W σ π φ e, Vfdef E1 V1 (S n') W σ π φ e ↔ Vfdef E2 V2 (S n') W σ π φ e).
  { intros. apply Vfdef_ext; intros j Hj; [apply HE|apply HV]; lia. }
  split; intros H W' g π' φ' Hb Hk Hr1 Hr2;
    destruct (H W' g π' φ' Hb Hk Hr1 Hr2) as (Hc & Hw & Hv & Hs); split_and!; try done.
  - intros Hval. destruct (Hv Hval) as [Hr Hv']. split; [done|]. by apply HVf.
  - intros α e' Hst. specialize (Hs α e' Hst). by rewrite <-(Fobl_ext E1 E2 V1 V2).
  - intros Hval. destruct (Hv Hval) as [Hr Hv']. split; [done|]. by apply HVf.
  - intros α e' Hst. specialize (Hs α e' Hst). by rewrite (Fobl_ext E1 E2 V1 V2).
Qed.

Lemma FuelE_0 W σ r π φ tk d e : FuelE 0 W σ r π φ tk d e.
Proof. unfold FuelE. rewrite flevel_at_eq. done. Qed.

Lemma FuelE_S n W σ r π φ tk d e :
  FuelE (S n) W σ r π φ tk d e ↔ Fdef FuelE Vfuel n W σ r π φ tk d e.
Proof.
  unfold FuelE at 1. rewrite flevel_at_eq.
  change (Fdef (λ j, fE (flevels (S n) j)) (λ j, fV (flevels (S n) j)) n W σ r π φ tk d e
    ↔ Fdef FuelE Vfuel n W σ r π φ tk d e).
  apply Fdef_ext; intros j Hj; intros; unfold FuelE, Vfuel; by rewrite flevels_at by lia.
Qed.

Lemma Vfuel_eq n W σ π φ w : Vfuel n W σ π φ w ↔ Vfdef FuelE Vfuel n W σ π φ w.
Proof.
  unfold Vfuel at 1. rewrite flevel_at_eq.
  change (Vfdef (λ j, fE (flevels n j)) (λ j, fV (flevels n j)) n W σ π φ w
    ↔ Vfdef FuelE Vfuel n W σ π φ w).
  apply Vfdef_ext; intros j Hj; intros; unfold FuelE, Vfuel; by rewrite flevels_at by lia.
Qed.

(** ** Monotonicity in the index *)

Lemma farr_down (E : nat → epred) (V : nat → vpred) m n W c t h σ1 σ2 a π φ body :
  m ≤ n → farr E V n W c t h σ1 σ2 a π φ body → farr E V m W c t h σ1 σ2 a π φ body.
Proof. intros Hmn [Hf H]. split; [done|]. intros W' j φ' v πa φa Hb Hj. apply H; [done|lia]. Qed.

Lemma Vfuel_down m n W σ π φ w : m ≤ n → Vfuel n W σ π φ w → Vfuel m W σ π φ w.
Proof.
  intros Hmn. rewrite !Vfuel_eq.
  induction w in σ, π, φ |- *; destruct σ as [τ a]; destruct τ; simpl; try done;
    try (intros (Hp & Hq & Hf); split_and!; [done|done|]; by apply (farr_down _ _ m n));
    try (intros (π1 & π2 & Hπ & Hd & H1 & H2); exists π1, π2; split_and!; auto; fail); auto.
  all: intros (Hp & Hf & H); split_and!; [done|done|]; intros W' j r0 tk0 Hb Hj; apply H; [done|lia].
Qed.

Lemma FuelE_S_down n W σ r π φ tk d e :
  FuelE (S n) W σ r π φ tk d e → FuelE n W σ r π φ tk d e.
Proof.
  revert W σ r π φ tk d e. induction n as [|n IH]; intros W σ r π φ tk d e H; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H. intros W' g π' φ' Hb Hk Hr1 Hr2.
  destruct (H W' g π' φ' Hb Hk Hr1 Hr2) as (Hc & Hw & Hv & Hs).
  split_and!; [done|done| |].
  { intros Hval. destruct (Hv Hval) as [Hr Hv']. split; [done|].
    apply Vfuel_eq. apply (Vfuel_down (S n) (S (S n))); [lia|]. by apply Vfuel_eq. }
  intros α e' Hst. specialize (Hs α e' Hst).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in Hs |- *.
  - by apply IH.
  - destruct Hs as [H1 H2]. split; [done|].
    intros k j πi φi Hk' Hj. apply (H2 k j πi φi Hk'). lia.
  - destruct Hs as (H1 & H0 & H2 & H3 & H4). split_and!; [done|done|done| |by apply IH].
    intros k Hk'. eapply Vfuel_down; [|exact (H3 k Hk')]. lia.
  - destruct Hs as [H1 H2]. auto.
  - destruct Hs as (H1 & H0 & H2 & H3). auto.
  - destruct Hs as [H1 H2]. split; [done|]. intros Hso. apply IH. by apply H2.
  - destruct Hs as [H1 H2]. split; [done|]. intros Hso. apply IH. by apply H2.
  - intros Hc1 Hc2. apply IH. by apply Hs.
  - destruct Hs as (H0 & H1 & H2 & H3). auto.
Qed.

Lemma FuelE_down m n W σ r π φ tk d e :
  m ≤ n → FuelE n W σ r π φ tk d e → FuelE m W σ r π φ tk d e.
Proof. induction 1; eauto using FuelE_S_down. Qed.

(** ** Monotonicity in the tickets *)

Lemma div2_mono a b : a ≤ b → Nat.div2 a ≤ Nat.div2 b.
Proof. intros H. rewrite !Nat.div2_div. by apply Nat.Div0.div_le_mono. Qed.

(** More tickets never hurt. A received value runs inside a thread that
    has more (plan §18.3). *)
Lemma FuelE_tk_mono n W σ r π φ tk tk' d e :
  tk ≤ tk' → FuelE n W σ r π φ tk d e → FuelE n W σ r π φ tk' d e.
Proof.
  revert W σ r π φ tk tk' d e. induction n as [n IH] using lt_wf_ind.
  intros W σ r π φ tk tk' d e Htk H. destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H. intros W' g π' φ' Hb Hk Hr1 Hr2.
  destruct (H W' g π' φ' Hb Hk Hr1 Hr2) as (Hc & Hw & Hv & Hs).
  split_and!; [done|done| |].
  { intros Hval. destruct (Hv Hval) as [Hr Hv']. split; [lia|done]. }
  intros α e' Hst. specialize (Hs α e' Hst).
  assert (IHn : ∀ W σ r π φ tk tk' d e,
    tk ≤ tk' → FuelE n W σ r π φ tk d e → FuelE n W σ r π φ tk' d e) by (apply IH; lia).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in Hs |- *.
  - by apply (IHn _ _ _ _ _ tk).
  - destruct Hs as [H1 H2]. split; [done|].
    intros k j πi φi Hk' Hj Hd Hin Hv0. apply (IH j ltac:(lia) _ _ _ _ _ tk); [done|].
    by apply (H2 k).
  - destruct Hs as (H1 & H0 & H2 & H3 & H4). split_and!; try done. by apply (IHn _ _ _ _ _ tk).
  - destruct Hs as [H1 H2]. split; [done|]. by apply (IHn _ _ _ _ _ tk).
  - destruct Hs as (H1 & H0 & H2 & H3). split_and!; [done|done|lia|].
    apply (IHn _ _ _ _ _ (tk - 1)); [lia|done].
  - destruct Hs as [H1 H2]. split; [done|]. intros Hso. apply (IHn _ _ _ _ _ tk); [done|by apply H2].
  - destruct Hs as [H1 H2]. split; [done|]. intros Hso. apply (IHn _ _ _ _ _ tk); [done|by apply H2].
  - intros Hc1 Hc2. apply (IHn _ _ _ _ _ tk); [done|]. by apply Hs.
  - destruct Hs as (H0 & H1 & H2 & H3). split_and!; [done|done| |].
    + apply (IHn _ _ _ _ _ (Nat.div2 (S tk))); [apply (div2_mono (S tk) (S tk')); lia|exact H2].
    + apply (IHn _ _ _ _ _ (Nat.div2 tk)); [by apply div2_mono|done].
Qed.

(** ** Renaming of channels (a link renames the peer of its removed end) *)

Lemma FuelE_rename n W σ r π φ tk d e (h : chan → chan) π1 φ1 :
  kinj h π → renk h π π1 → renk h φ φ1 →
  FuelE n W σ r π φ tk d e → FuelE n W σ r π1 φ1 tk d (emap h e).
Proof.
  destruct n as [|n]; [intros; apply FuelE_0|]. rewrite !FuelE_S.
  intros Hi H1 H2 HF W' g π' φ' Hb Hg G1 G2. rewrite emap_emap.
  apply HF; [done| |eapply renk_compose; eauto|eapply renk_compose; eauto].
  by apply (kinj_compose g h π π1).
Qed.

(** ** Extension of the budgets *)

Lemma FuelE_wbext n W W' σ r π φ tk d e :
  wbext W W' → FuelE n W σ r π φ tk d e → FuelE n W' σ r π φ tk d e.
Proof.
  destruct n as [|n]; [intros; apply FuelE_0|]. rewrite !FuelE_S.
  intros Hb HF W'' g π' φ' Hb' Hk G1 G2. apply HF; [|done|done|done].
  by apply (wbext_trans W W' W'').
Qed.

(** ** The clauses of a thread at index n + 1 *)

(** The parent's tickets after a step. A link spends one, a spawn keeps
    ⌊tk/2⌋. *)
Definition tkupd (tk : nat) (α : tlabel) : nat :=
  match α with
  | LSess (SLink _) => tk - 1
  | LSpawn _ => Nat.div2 tk
  | _ => tk
  end.

Lemma tkupd_act tk σ o : sl_end σ = Some o → tkupd tk (LSess σ) = tk.
Proof. by destruct σ. Qed.

Lemma dupd_None α : dupd None α = None.
Proof. destruct α as [|[]| |]; done. Qed.

(** The cost type, reserve and frame are implicit: they are read off the
    hypothesis. *)
Section clauses.
  Context (n : nat) (W : world) {sg : cta} {r : nat} (π : gmap cend point) (φ : gmap cend fuel)
    (tk : nat) {d : fuel} (e : expr).
  Context (HF : FuelE (S n) W sg r π φ tk d e).

  Lemma fuel_def : Fdef FuelE Vfuel n W sg r π φ tk d e.
  Proof. by apply FuelE_S. Qed.

  Local Lemma fuel_self :
    fcap W π φ ∧ fwait W π e ∧
    (is_val e = true → r ≤ tk ∧ Vfdef FuelE Vfuel (S n) W sg π φ e) ∧
    ∀ α e', tstep e α e' → Fobl FuelE Vfuel n W sg r π φ tk d α e'.
  Proof.
    pose proof (fuel_def W id π φ (wbext_refl W) (kinj_id π) (renk_id π) (renk_id φ)) as H.
    by rewrite emap_id in H.
  Qed.

  (** F-Cap: counters stay at or below the budget of their point. *)
  Lemma fuel_cap : fcap W π φ.
  Proof. by destruct fuel_self as (? & _ & _). Qed.

  (** F-Wait: the partner of an end the thread acts on has a finite
      budget, and the end is held. *)
  Lemma fuel_wait σ e' o :
    tstep e (LSess σ) e' → sl_end σ = Some o →
    ∃ k m, π !! o = Some k ∧ w_bud W (pt_dual k) = Some m.
  Proof.
    intros Hst Ho. destruct fuel_self as (_ & Hw & _).
    destruct (Hw σ e' o Hst Ho) as (k & Hk & Hb).
    destruct (w_bud W (pt_dual k)) as [m|] eqn:E; [|done]. eauto.
  Qed.

  (** A value returned holds the reserve and is in [Vfuel] at the
      result type, at the level of the expression. *)
  Lemma fuel_val : is_val e = true → r ≤ tk ∧ Vfuel (S n) W sg π φ e.
  Proof.
    intros Hv. destruct fuel_self as (_ & _ & H & _). destruct (H Hv) as [Hr H'].
    split; [done|]. by apply Vfuel_eq.
  Qed.

  Lemma fuel_obl α e' : tstep e α e' → Fobl FuelE Vfuel n W sg r π φ tk d α e'.
  Proof. intros Hst. destruct fuel_self as (_ & _ & _ & Hs). by apply Hs. Qed.

  (** F-Tick. *)
  Lemma fuel_tick σ e' o : tstep e (LSess σ) e' → sl_end σ = Some o → ftick_ok o φ.
  Proof.
    intros Hst Ho. pose proof (fuel_obl _ _ Hst) as [H _]. by destruct (H o Ho).
  Qed.

  (** An action spends a unit of the frame. *)
  Lemma fuel_frame σ e' o : tstep e (LSess σ) e' → sl_end σ = Some o → fle (Some 1) d.
  Proof.
    intros Hst Ho. pose proof (fuel_obl _ _ Hst) as [H _]. by destruct (H o Ho).
  Qed.

  (** The payload of a send has finite partner budgets. *)
  Lemma fuel_send_travel o w e' : tstep e (LSess (SSend o w)) e' → ftravel W π (fends w).
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & _ & H & _). Qed.

  (** The thread holds the ends it sends, and not the end it sends on. *)
  Lemma fuel_send_held o w e' : tstep e (LSess (SSend o w)) e' → fends w ⊆ dom π ∖ {[o]}.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H & _). Qed.

  (** The payload of a send at the counters the receiver gets, at the
      payload cost type of the carrier's point. *)
  Lemma fuel_send_val o w e' k :
    tstep e (LSess (SSend o w)) e' → π !! o = Some k →
    Vfuel n W (w_pc W k) (mres (fends w) π) (ftick <$> mres (fends w) φ) w.
  Proof. intros Hst Hk. pose proof (fuel_obl _ _ Hst) as (_ & _ & _ & H & _). by apply H. Qed.

  (** A link needs a ticket. *)
  Lemma fuel_link cd e' : tstep e (LSess (SLink cd)) e' → 1 ≤ tk.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & _ & H & _). Qed.

  (** A link forwards ends the thread holds. *)
  Lemma fuel_link_held cd e' : tstep e (LSess (SLink cd)) e' → cd ⊆ dom π.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H & _). Qed.

  (** A spawn hands on ends the thread holds. *)
  Lemma fuel_spawn_held w e' : tstep e (LSpawn w) e' → fends w ⊆ dom π.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (H & _ & _). Qed.

  (** The ends a spawn hands to the child have a unit to spare. *)
  Lemma fuel_spawn_hand w e' : tstep e (LSpawn w) e' → fhand 0 (fends w) φ.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H & _ & _). Qed.

  (** ** lffuel_step: the successor at the updated counters, tickets and frame *)

  (** Every step but a receive. A new step needs a channel the thread
      does not hold, a select or branch a thread that holds no other end
      of its channel. *)
  Lemma lffuel_step α e' :
    tstep e α e' → (∀ o w, α ≠ LSess (SRecv o w)) →
    (∀ c x, α = LNew c x → ((c, true) ∉ dom π) ∧ ((c, false) ∉ dom π)) →
    (∀ o b, α = LSess (SSel o b) ∨ α = LSess (SBra o b) → fsolo π o) →
    FuelE n W sg r (fupd W π φ α).1 (fupd W π φ α).2 (tkupd tk α) (dupd d α) e'.
  Proof.
    intros Hst Hr Hn Hso. pose proof (fuel_obl _ _ Hst) as H.
    destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in H |- *.
    - done.
    - by destruct (Hr o w).
    - by destruct H as (_ & _ & _ & _ & H).
    - by destruct H as [_ H].
    - by destruct H as (_ & _ & _ & H).
    - destruct H as [_ H]. apply H, (Hso o b). by left.
    - destruct H as [_ H]. apply H, (Hso o b). by right.
    - destruct (Hn c x eq_refl) as [H1 H2]. by apply H.
    - by destruct H as (_ & _ & _ & H).
  Qed.

  (** Receive: the receiver continues for every incoming value at the
      payload cost type of the carrier, read at the sender's point, whose
      ends sit at known points under the cap. *)
  Lemma lffuel_recv o w e' k j πi φi :
    tstep e (LSess (SRecv o w)) e' → π !! o = Some k → j ≤ n →
    dom πi ## dom (fupd W π φ (LSess (SRecv o w))).1 →
    fin_ok W w πi φi → Vfuel j W (w_pc W (pt_dual k)) πi φi w →
    FuelE j W sg r ((fupd W π φ (LSess (SRecv o w))).1 ∪ πi)
      ((fupd W π φ (LSess (SRecv o w))).2 ∪ φi) tk (ftick d) e'.
  Proof.
    intros Hst Hk Hj Hd Hin Hv. pose proof (fuel_obl _ _ Hst) as [_ H]. eauto.
  Qed.

  (** Spawn: the child at the handed-on counters and ⌈tk/2⌉ tickets, run
      as a thread, the parent without them. *)
  Lemma lffuel_spawn w e' :
    tstep e (LSpawn w) e' →
    FuelE n W cany 0 (fchild π φ w).1 (fchild π φ w).2 (Nat.div2 (S tk)) None (App w EUnit) ∧
    FuelE n W sg r (fupd W π φ (LSpawn w)).1 (fupd W π φ (LSpawn w)).2 (Nat.div2 tk) d e'.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & _ & H1 & H2). Qed.

  (** ** At counter 0 *)

  (** The holder's next channel step is on the end at 0. *)
  Lemma fuel_zero_act o σ e' o' :
    φ !! o = Some (Some 0) → tstep e (LSess σ) e' → sl_end σ = Some o' → o' = o.
  Proof.
    intros H0 Hst Ho'. destruct (decide (o = o')) as [|Hne]; [done|].
    pose proof (fuel_tick _ _ _ Hst Ho' o 0 Hne H0). lia.
  Qed.

  (** It does not spawn the end at 0 away. *)
  Lemma fuel_zero_nospawn o w e' :
    φ !! o = Some (Some 0) → tstep e (LSpawn w) e' → o ∉ fends w.
  Proof.
    intros H0 Hst Hin. pose proof (fuel_spawn_hand _ _ Hst o 0 Hin H0). lia.
  Qed.
End clauses.

(** ** Link loops exhaust the tickets

    A thread that links in every state of a family Q, and stays in Q
    after the link, has no fuel at tk tickets and index tk + 1. A link
    loop with chatter (C3) is of this shape between its chatter steps,
    so no finite ticket count gives it fuel at every index. *)
Lemma link_tickets_fall (W : world) (σ : cta) (r : nat) (d : fuel)
    (Q : gmap cend point → gmap cend fuel → expr → Prop) :
  (∀ π φ e, Q π φ e → ∃ cd e', tstep e (LSess (SLink cd)) e' ∧
     Q (fupd W π φ (LSess (SLink cd))).1 (fupd W π φ (LSess (SLink cd))).2 e') →
  ∀ tk π φ e, Q π φ e → ¬ FuelE (S tk) W σ r π φ tk d e.
Proof.
  intros HQ tk. induction tk as [|tk IH]; intros π φ e Hq HF;
    destruct (HQ π φ e Hq) as (cd & e' & Hst & Hq');
    pose proof (fuel_obl _ _ _ _ _ _ HF _ _ Hst) as (_ & _ & H1 & H2); [lia|].
  simpl in H2. rewrite Nat.sub_0_r in H2. exact (IH _ _ _ Hq' H2).
Qed.

(** ** Counters stay at or below the cap along fupd *)

Lemma fcap_mrem (W : world) (X : gset cend) π φ : fcap W π φ → fcap W (mrem X π) (mrem X φ).
Proof.
  intros H o f Hf. apply lookup_mrem_Some in Hf as [Hf Hx].
  destruct (H o f Hf) as (k & Hk & Hle). exists k. by rewrite lookup_mrem_Some.
Qed.

Lemma fcap_mres (W : world) (X : gset cend) π φ : fcap W π φ → fcap W (mres X π) (mres X φ).
Proof.
  intros H o f Hf. apply lookup_mres_Some in Hf as [Hf Hx].
  destruct (H o f Hf) as (k & Hk & Hle). exists k. by rewrite lookup_mres_Some.
Qed.

Lemma fcap_delete (W : world) π φ o : fcap W π φ → fcap W (delete o π) (delete o φ).
Proof.
  intros H o' f Hf. apply lookup_delete_Some in Hf as [Hne Hf].
  destruct (H o' f Hf) as (k & Hk & Hle). exists k. by rewrite lookup_delete_ne.
Qed.

Lemma fcap_tick (W : world) π φ : fcap W π φ → fcap W π (ftick <$> φ).
Proof.
  intros H o f Hf. apply lookup_fmap_Some in Hf as (f0 & <- & Hf).
  destruct (H o f0 Hf) as (k & Hk & Hle). exists k. split; [done|]. by apply fle_tick.
Qed.

Lemma fcap_insert (W : world) π φ o k : fcap W π φ → fcap W (<[o := k]> π) (<[o := w_bud W k]> φ).
Proof.
  intros H o' f Hf. destruct (decide (o = o')) as [<-|Hne].
  - rewrite lookup_insert_eq in Hf. simplify_eq. exists k.
    rewrite lookup_insert_eq. split; [done|apply fle_refl].
  - rewrite lookup_insert_ne in Hf by done.
    destruct (H o' f Hf) as (k' & Hk & Hle). exists k'. by rewrite lookup_insert_ne.
Qed.

Lemma fact_cap (W : world) σ π φ : fcap W π φ → fcap W (fact W σ π φ).1 (fact W σ π φ).2.
Proof.
  intros H. unfold fact. destruct (sl_end σ) as [o|]; [|done].
  destruct (π !! o) as [k|]; [|done].
  destruct (sl_next σ k) as [[o' k']|]; simpl.
  - apply fcap_insert, fcap_tick, fcap_delete, H.
  - apply fcap_tick, fcap_delete, H.
Qed.

(** The successor's counters stay at or below the cap, for every label. *)
Lemma fupd_cap (W : world) π φ α : fcap W π φ → fcap W (fupd W π φ α).1 (fupd W π φ α).2.
Proof.
  intros H. destruct α as [|σ|c x|w]; simpl.
  - done.
  - by apply fact_cap, fcap_mrem.
  - by apply fcap_insert, fcap_insert.
  - by apply fcap_mrem.
Qed.

(** ** Handing ends on *)

(** The ends handed on by a send or a spawn are admissible incoming
    ends for the receiver or the child: they sit at points W knows, under
    the cap, with finite partner budgets. *)
Lemma fchild_fin_ok (W : world) π φ w :
  fcap W π φ → dom φ = dom π → fends w ⊆ dom π →
  ftravel W π (fends w) → (∀ o k, o ∈ fends w → π !! o = Some k → pt_known W k) →
  fin_ok W w (fchild π φ w).1 (fchild π φ w).2.
Proof.
  intros Hc Hdom Hsub Ht Hk0. unfold fchild; simpl. split_and!.
  - rewrite dom_mres. set_solver.
  - rewrite dom_fmap_L, dom_mres, Hdom. set_solver.
  - by apply fcap_tick, fcap_mres.
  - intros o k Hk. apply lookup_mres_Some in Hk as [Hk Hx]. by apply (Ht o k).
  - intros o k Hk. apply lookup_mres_Some in Hk as [Hk Hx]. by apply (Hk0 o k).
Qed.

(** ** Finite counters *)

(** A counter under a finite budget is finite. With F-Wait this bounds
    the counter of the partner a thread waits on. *)
Lemma fcap_finite (W : world) π φ o k b f :
  fcap W π φ → π !! o = Some k → w_bud W k = Some b → φ !! o = Some f →
  ∃ m, f = Some m ∧ m ≤ b.
Proof.
  intros H Hk Hb Hf. destruct (H o f Hf) as (k' & Hk' & Hle).
  rewrite Hk in Hk'. simplify_eq. rewrite Hb in Hle.
  destruct f as [m|]; simpl in Hle; [eauto|done].
Qed.
