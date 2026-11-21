(** * Fuel (stage S6, proposal §2.10, §2.11, decisions Q4, Q5, Q10, Q11)

      e ∈ F^N _ n⟦σ ▷ c⟧(Π, φ)     [FuelE N n σ c Π φ e]
      v ∈ FV^N _ n⟦σ⟧(Π, φ)        [Vfuel N n σ Π φ v]

    A step-indexed predicate on one thread e. Π maps the ends the thread
    holds to their session types, and φ maps them to their counters and
    their tickets. σ is the type of the value e returns, with the credits
    of its ends and closures, or [RThread] for a thread, which returns
    holding no end. c is the frame, the channel actions e may still
    perform before it returns. N bounds the tickets of the two ends of a
    channel (decision of 2026-11-21). Counters, tickets, credits, the
    frame and N range over ℕ ∪ {∞}. Deadlock freedom is the instance
    N = ∞.

    The predicate reads no point, no world and no relation. Under the
    merged judgment (decision Q11) a cost protocol is a session type
    with its annotations, so Π is the session-type part of the
    environment of the live relation at the same index (stage S8). The
    payload of a send is read at the payload type of the session type of
    Π, whose ends carry their own credits.

    Counters evolve by one update at every index. An action on o sets
    the counter of o back to its tickets and ticks every other counter of
    the thread by one (truncated at 0). A send and a spawn hand the ends
    of the value they move on with their counters minus one. New ends
    start at their tickets m1 and m2, which the creation chooses with
    m1 + m2 ≤ N. A link moves no counter, and
    the counter of each linked end exceeds what the bound leaves the
    partner of the other ([lok]). The checks are F-Tick (an action asks
    every other counter at least 1, and the frame at least 1), the
    hand-over (every handed counter at least 1), F-Wait (no action on an
    idle end) and F-Link. An idle end is an end whose session type is
    Skip: no thread can act on it (decision Q5, the corrected form).
    Idleness only removes the checks "≥ 1" of F-Tick and of the hand-over
    for that end. It never changes how a counter evolves.

    Every step costs one level, β, new, spawn and link included (decision
    Q10 (b), see docs/redesign/progress.md for why one clock fails).

    FuelE^N is closed under injective renamings of ends (a link renames
    the partner of the removed end in another thread). [Vfuel] recurses
    on the type. A closure at (T ⊸[c] U)^a has captured counters at least
    a on the ends that are not idle, and for every lower level, counters
    at or above the counters at creation minus a at the same tickets
    (per-end capture, decision of 2026-11-20) and argument in [Vfuel] at
    T, its body satisfies [FuelE] at U with frame c. A box does the same
    per force, for every session instance of its variables.

    Decision Q15 adds the clause of Q14 in V. A closure holds exactly the
    ends its body mentions (dom Π = fends v), and a box mentions no end.
    So every value of [Vfuel] is exact ([Vfuel_exact]), and the ends a
    send or a spawn reads off its label are the ends of its map. *)

From GV Require Export lang.Semantics static.Contexts relation.Ord.

(** ** Maps of ends *)

Abbreviation penv := (gmap cend sty).
Abbreviation cenv := (gmap cend (fuel * fuel)).

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
  apply set_eq. intros o. rewrite elem_of_difference, !elem_of_dom. split.
  - intros [a Ha]. apply lookup_mrem_Some in Ha as [Ha Hx]. eauto.
  - intros [[a Ha] Hx]. exists a. by apply lookup_mrem_Some.
Qed.

Lemma dom_mres {Y : Type} (X : gset cend) (m : gmap cend Y) : dom (mres X m) = dom m ∩ X.
Proof.
  apply set_eq. intros o. rewrite elem_of_intersection, !elem_of_dom. split.
  - intros [a Ha]. apply lookup_mres_Some in Ha as [Ha Hx]. eauto.
  - intros [[a Ha] Hx]. exists a. by apply lookup_mres_Some.
Qed.

(** [renk g m m']: m' is m with every end o renamed to g o. *)
Definition renk {Y : Type} (g : cend → cend) (m m' : gmap cend Y) : Prop :=
  (∀ o v, m !! o = Some v → m' !! g o = Some v) ∧
  (∀ o' v, m' !! o' = Some v → ∃ o, o' = g o ∧ m !! o = Some v).

(** g renames the ends of m injectively. *)
Definition kinj {Y : Type} (g : cend → cend) (m : gmap cend Y) : Prop :=
  ∀ o1 o2 v1 v2, m !! o1 = Some v1 → m !! o2 = Some v2 → g o1 = g o2 → o1 = o2.

Lemma renk_id {Y : Type} (m : gmap cend Y) : renk id m m.
Proof. split; [done|]. intros o v H. by exists o. Qed.

Lemma kinj_id {Y : Type} (m : gmap cend Y) : kinj id m.
Proof. by intros o1 o2 v1 v2 _ _. Qed.

Lemma renk_compose {Y : Type} (g h : cend → cend) (m m1 m2 : gmap cend Y) :
  renk h m m1 → renk g m1 m2 → renk (g ∘ h) m m2.
Proof.
  intros [H1 H2] [G1 G2]. split.
  - intros o v Ho. apply G1. by apply H1.
  - intros o' v Ho'. destruct (G2 o' v Ho') as (o1 & -> & Ho1).
    destruct (H2 o1 v Ho1) as (o & -> & Ho). by exists o.
Qed.

Lemma kinj_compose {Y : Type} (g h : cend → cend) (m m1 : gmap cend Y) :
  renk h m m1 → kinj h m → kinj g m1 → kinj (g ∘ h) m.
Proof.
  intros [H1 _] Hh Hg o1 o2 v1 v2 Ho1 Ho2 Heq. apply (Hh o1 o2 v1 v2 Ho1 Ho2).
  apply (Hg (h o1) (h o2) v1 v2); [by apply H1|by apply H1|exact Heq].
Qed.

Lemma kinj_nil {Y : Type} (g : cend → cend) : kinj (Y := Y) g ∅.
Proof. intros ? ? ? ?; by rewrite lookup_empty. Qed.

Lemma kinj_union {Y : Type} (g : cend → cend) (m1 m2 : gmap cend Y) :
  kinj g m1 → kinj g m2 → (∀ o1 o2, o1 ∈ dom m1 → o2 ∈ dom m2 → g o1 ≠ g o2) →
  kinj g (m1 ∪ m2).
Proof.
  intros H1 H2 Hx o1 o2 v1 v2 Ho1 Ho2 Heq.
  apply lookup_union_Some_raw in Ho1 as [Ho1|[N1 Ho1]], Ho2 as [Ho2|[N2 Ho2]].
  - exact (H1 o1 o2 v1 v2 Ho1 Ho2 Heq).
  - exfalso. apply (Hx o1 o2); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
  - exfalso. apply (Hx o2 o1); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
  - exact (H2 o1 o2 v1 v2 Ho1 Ho2 Heq).
Qed.


(** ** Counters, idle ends and the update *)

(** One unit less, truncated at 0. ∞ stays ∞. *)
Definition ftick (f : fuel) : fuel := fsub f (Some 1).

(** An entry of φ is the counter of an end and its tickets. A tick lowers
    the counter and keeps the tickets. *)
Definition ctick (p : fuel * fuel) : fuel * fuel := (ftick p.1, p.2).

(** An idle end ([idle], types/Types.v): its session type is Skip. *)

Definition idle_at (Π : penv) (o : cend) : Prop := ∃ S, Π !! o = Some S ∧ idle S.

(** The ends X have a unit to spare: every counter on X of an end that is
    not idle is at least 1. F-Tick asks it of the other ends of an action,
    the hand-over of the ends of a sent or spawned value. *)
Definition fspare (Π : penv) (φ : cenv) (X : gset cend) : Prop :=
  ∀ o f, o ∈ X → φ !! o = Some f → ¬ idle_at Π o → fle (Some 1) f.1.

(** An action on o: o goes back to its tickets, the other counters tick. *)
Definition refill (o : cend) (φ : cenv) : cenv :=
  match φ !! o with
  | Some (_, m) => <[o := (m, m)]> (ctick <$> delete o φ)
  | None => ctick <$> φ
  end.

Lemma refill_lookup o φ f m : φ !! o = Some (f, m) → refill o φ = <[o := (m, m)]> (ctick <$> delete o φ).
Proof. intros H. unfold refill. by rewrite H. Qed.

(** The counters the ends M take with them: one unit less. *)
Definition fhand (M : gset cend) (φ : cenv) : cenv := ctick <$> mres M φ.

(** The ends c⁺ and c⁻ of a new channel, at S and its dual, each at its
    tickets. *)
Definition pnew (c : chan) (S : sty) (Π : penv) : penv := <[EPos c := S]> (<[ENeg c := dual S]> Π).
Definition cnew (m1 m2 : fuel) (c : chan) (φ : cenv) : cenv :=
  <[EPos c := (m1, m1)]> (<[ENeg c := (m2, m2)]> φ).

(** A new channel is fresh against the thread's own maps. *)
Definition ffresh (c : chan) (Π : penv) (φ : cenv) : Prop :=
  (EPos c ∉ dom Π) ∧ (ENeg c ∉ dom Π) ∧ (EPos c ∉ dom φ) ∧ (ENeg c ∉ dom φ).

(** The two ends of a link label, held at dual protocols. *)
Definition plink (Π : penv) (os : gset cend) : Prop :=
  ∃ o1 o2 S1 S2, os = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧ Π !! o1 = Some S1 ∧ Π !! o2 = Some S2 ∧
    sequiv S2 (dual S1).

(** The tickets of a link: the counter of each linked end exceeds what the
    bound leaves the partner of the other, a1 + m2 > N and a2 + m1 > N. *)
Definition lok (N : fuel) (φ : cenv) (os : gset cend) : Prop :=
  ∀ o1 o2 p1 p2, os = {[o1]} ∪ {[o2]} → o1 ≠ o2 → φ !! o1 = Some p1 → φ !! o2 = Some p2 →
    lgt N p1.1 p2.2 ∧ lgt N p2.1 p1.2.

(** ** Result types and readers *)

(** The type T of a returned value, or a thread, which returns any
    value and holds no end then. *)
Inductive rty := RTy (T : ty) | RThread.

(** FuelE at one level reads the bound, the result type, the frame,
    protocols, counters with tickets and the term. Vfuel reads the bound,
    the type, protocols, counters and the value. *)
Abbreviation epred := (fuel → rty → fuel → penv → cenv → expr → Prop).
Abbreviation vpred := (fuel → rty → penv → cenv → expr → Prop).

(** ** The obligations of a step (§2.10)

    One per label, for the step e --α--> e' at index n, given FuelE
    and Vfuel at every level below n. *)
Section obligations.
  Context (N : fuel) (El : Ix → epred) (Vl : Ix → vpred) (n : Ix)
    (σ : rty) (d : fuel) (Π : penv) (φ : cenv).

  (** An action on o. F-Wait: o is held and not idle. F-Tick: every other
      end that is not idle has a unit to spare, and so has the frame. *)
  Definition f_act (o : cend) : Prop :=
    ¬ idle_at Π o ∧ o ∈ dom φ ∧ fspare Π φ (dom φ ∖ {[o]}) ∧ fle (Some 1) d.

  Definition f_beta (e' : expr) : Prop := (∀ j, olt j n → El j N σ d Π φ e').

  (** A creation chooses the protocol and the tickets m1 and m2 of the
      two new ends, with m1 + m2 ≤ N. *)
  Definition f_new (c : chan) (e' : expr) : Prop :=
    ffresh c Π φ → ∃ S m1 m2, tsum_ok N m1 m2 ∧
      (∀ j, olt j n → El j N σ d (pnew c S Π) (cnew m1 m2 c φ) e').

  (** The child takes the ends of v with one unit less and runs as a
      thread. *)
  Definition f_spawn (v e' : expr) : Prop :=
    fends v ⊆ dom φ ∧ fspare Π φ (fends v) ∧
    (∀ j, olt j n → El j N RThread None (mres (fends v) Π) (fhand (fends v) φ) (App v EUnit)) ∧
    (∀ j, olt j n → El j N σ d (mrem (fends v) Π) (mrem (fends v) φ) e').

  (** A send hands on held ends other than its subject, at the payload
      type of the session type, with one unit less. *)
  Definition f_send (o : cend) (w e' : expr) : Prop :=
    f_act o ∧ ∃ S0 m T S, Π !! o = Some S0 ∧ unfoldS S0 = SSeq (SSnd m T) S ∧
      fends w ⊆ dom φ ∖ {[o]} ∧ fspare Π φ (fends w) ∧
      (∀ j, olt j n → Vl j N (RTy T) (mres (fends w) Π) (fhand (fends w) φ) w) ∧
      (∀ j, olt j n → El j N σ (ftick d) (<[o := S]> (mrem (fends w) Π)) (refill o (mrem (fends w) φ)) e').

  (** A receive continues for every incoming value at the payload type,
      with any protocols and counters it brings. *)
  Definition f_recv (o : cend) (w e' : expr) : Prop :=
    f_act o ∧ ∃ S0 m T S, Π !! o = Some S0 ∧ unfoldS S0 = SSeq (SRcv m T) S ∧
      ∀ j Πi φi, olt j n → Πi ##ₘ <[o := S]> Π → φi ##ₘ refill o φ →
        Vl j N (RTy T) Πi φi w →
        El j N σ (ftick d) (<[o := S]> Π ∪ Πi) (refill o φ ∪ φi) e'.

  Definition f_close (o : cend) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0, Π !! o = Some S0 ∧ unfoldS S0 = SEnd ∧
      (∀ j, olt j n → El j N σ (ftick d) (delete o Π) (ctick <$> delete o φ) e').

  Definition f_select (o : cend) (i : bool) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0 S1 S2, Π !! o = Some S0 ∧ unfoldS S0 = SPlus S1 S2 ∧
      (∀ j, olt j n → El j N σ (ftick d) (<[o := if i then S2 else S1]> Π) (refill o φ) e').

  Definition f_branch (o : cend) (i : bool) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0 S1 S2, Π !! o = Some S0 ∧ unfoldS S0 = SWith S1 S2 ∧
      (∀ j, olt j n → El j N σ (ftick d) (<[o := if i then S2 else S1]> Π) (refill o φ) e').

  (** A link forwards held ends whose protocols are dual, and the counter
      of each exceeds what the bound leaves the partner of the other. The
      soup reads the duality: after the link the partners of the two ends
      form one channel (stage S8). *)
  Definition f_link (os : gset cend) (e' : expr) : Prop :=
    plink Π os ∧ os ⊆ dom φ ∧ lok N φ os ∧ (∀ j, olt j n → El j N σ d (mrem os Π) (mrem os φ) e').

  Definition Fobl (α : tlabel) (e' : expr) : Prop :=
    match α with
    | LBeta => f_beta e'                                  (* F-Beta *)
    | LNew c => f_new c e'                                (* F-New *)
    | LSpawn v => f_spawn v e'                          (* F-Spawn *)
    | LSess (SSend o w) => f_send o w e'                (* F-Send *)
    | LSess (SRecv o w) => f_recv o w e'                  (* F-Recv *)
    | LSess (SClose o) => f_close o e'                    (* F-Close *)
    | LSess (SSel o i) => f_select o i e'                 (* F-Select *)
    | LSess (SBra o i) => f_branch o i e'                 (* F-Branch *)
    | LSess (SLink os) => f_link os e'                    (* F-Link *)
    end.
End obligations.

(** ** Values at a type (§2.11)

    By recursion on the type. Points, upper and lower points and box
    constraints are not read. An end reads its credit and its tickets, a
    closure its credit, and a product splits its ends into two disjoint
    parts. *)
Fixpoint Vty (N : fuel) (El : Ix → epred) (Vl : Ix → vpred) (n : Ix)
    (T : ty) (Π : penv) (φ : cenv) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => v = EUnit ∧ Π = ∅ ∧ φ = ∅
  | TSess s _ a m =>
      ∃ o S' f, v = Chan o ∧ Π = {[o := S']} ∧ φ = {[o := (f, m)]} ∧ sequiv S' s ∧ fle a f
  | TLolli _ _ c T1 U a =>
      ∃ e, v = Lam e ∧ fends e = dom Π ∧ dom Π = dom φ ∧
        (∀ o f, φ !! o = Some f → ¬ idle_at Π o → fle a f.1) ∧
        ∀ j φ' Πu φu u, olt j n → dom φ' = dom φ →
          (∀ o f f', φ !! o = Some f → φ' !! o = Some f' → f'.2 = f.2 ∧ fle (fsub f.1 a) f'.1) →
          Π ##ₘ Πu → φ' ##ₘ φu →
          Vl j N (RTy T1) Πu φu u →
          El j N (RTy U) c (Π ∪ Πu) (φ' ∪ φu) (subst1 u e)
  | TProd T1 T2 =>
      ∃ v1 v2 Π1 Π2 φ1 φ2, v = Pair v1 v2 ∧ Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧
        Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
        Vty N El Vl n T1 Π1 φ1 v1 ∧ Vty N El Vl n T2 Π2 φ2 v2
  | TSum T1 T2 =>
      (∃ v', v = Inj false v' ∧ Vty N El Vl n T1 Π φ v') ∨
      (∃ v', v = Inj true v' ∧ Vty N El Vl n T2 Π φ v')
  | TBox _ k _ _ c U =>
      ∃ e, v = EBox e ∧ fends e = ∅ ∧ Π = ∅ ∧ φ = ∅ ∧
        ∀ j ss, olt j n → length ss = k → sinsts N ss →
          El j N (RTy (sinst_ty (slist ss) U)) c ∅ ∅ (subst1 (EBox e) e)
  | TEx _ _ _ T1 => Vty N El Vl n T1 Π φ v
  end.

Definition Vres (N : fuel) (El : Ix → epred) (Vl : Ix → vpred) (n : Ix)
    (σ : rty) (Π : penv) (φ : cenv) (v : expr) : Prop :=
  match σ with
  | RTy T => Vty N El Vl n T Π φ v
  | RThread => Π = ∅ ∧ φ = ∅
  end.

(** ** One level of FuelE

    For every renaming g injective on the held ends, the renamed term
    returns a value in [Vfuel] at σ (val), and every step meets its
    obligation (step). *)
Definition Fdef (N : fuel) (El : Ix → epred) (Vl : Ix → vpred) (n : Ix)
    (σ : rty) (d : fuel) (Π : penv) (φ : cenv) (e : expr) : Prop :=
  ∀ g Π' φ', kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
    (is_val (emap g e) → Vres N El Vl n σ Π' φ' (emap g e)) ∧    (* (val) *)
    ∀ α e', tstep (emap g e) α e' → Fobl N El Vl n σ d Π' φ' α e'.  (* (step) *)

Record flevel := FLevel { fE : epred; fV : vpred }.

(** One level is one predicate on the arguments of FuelE and Vfuel, so
    that the fixpoint [osfix] of relation/Ord.v applies. *)
Inductive flarg :=
  | FAE (N : fuel) (σ : rty) (d : fuel) (Π : penv) (φ : cenv) (e : expr)
  | FAV (N : fuel) (σ : rty) (Π : penv) (φ : cenv) (v : expr).

Definition flvl_of (R : flarg → Prop) : flevel :=
  FLevel (λ N σ d Π φ e, R (FAE N σ d Π φ e)) (λ N σ Π φ v, R (FAV N σ Π φ v)).

Definition mk_flarg (R : Ix → flarg → Prop) (n : Ix) (a : flarg) : Prop :=
  match a with
  | FAE N σ d Π φ e => Fdef N (λ j, fE (flvl_of (R j))) (λ j, fV (flvl_of (R j))) n σ d Π φ e
  | FAV N σ Π φ v => Vres N (λ j, fE (flvl_of (R j))) (λ j, fV (flvl_of (R j))) n σ Π φ v
  end.

Definition FLevA : Ix → flarg → Prop := osfix mk_flarg.

Definition FuelE (N : fuel) (n : Ix) : rty → fuel → penv → cenv → expr → Prop :=
  λ σ d Π φ e, FLevA n (FAE N σ d Π φ e).
Definition Vfuel (N : fuel) (n : Ix) : rty → penv → cenv → expr → Prop :=
  λ σ Π φ v, FLevA n (FAV N σ Π φ v).

(** A thread: result [RThread], frame ∞. *)
Abbreviation FuelT N n Π φ e := (FuelE N n RThread None Π φ e).

(** A thread with the protocols Π and the counters and tickets φ, at
    every index. *)
Definition fsem (N : fuel) (Π : penv) (φ : cenv) (e : expr) : Prop :=
  ∀ n, FuelT N n Π φ e.

(** ** Notations (Appendix A) *)

Notation "e ∈ F^ N '_' n ⟦ σ ▷ c ⟧( Π , φ )" := (FuelE N n σ c Π φ e)
  (at level 70, N at level 0, n at level 0, σ at level 60, c at level 60,
   format "e  ∈  F^ N  '_'  n ⟦ σ  ▷  c ⟧( Π ,  φ )").
Notation "v ∈ FV^ N '_' n ⟦ σ ⟧( Π , φ )" := (Vfuel N n σ Π φ v)
  (at level 70, N at level 0, n at level 0, σ at level 60,
   format "v  ∈  FV^ N  '_'  n ⟦ σ ⟧( Π ,  φ )").

(** ** Unfolding *)

Section ext.
  Context (El1 El2 : Ix → epred) (Vl1 Vl2 : Ix → vpred).

  Lemma Fobl_ext_1 N n σ d Π φ α e' :
    (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
    (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Fobl N El1 Vl1 n σ d Π φ α e' → Fobl N El2 Vl2 n σ d Π φ α e'.
  Proof.
    intros HE HV.
    assert (HE' : ∀ N σ d Π φ e, (∀ j, olt j n → El1 j N σ d Π φ e) →
                                  ∀ j, olt j n → El2 j N σ d Π φ e)
      by (intros ? ? ? ? ? ? H j Hj; apply HE; [done|by apply H]).
    destruct α as [|c|v|[o w|o w|o|o i|o i|os]]; simpl;
      unfold f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link.
    - apply HE'.
    - intros H Hf. destruct (H Hf) as (S & m1 & m2 & Hm & HS). exists S, m1, m2. split; [done|]. by apply HE'.
    - intros (H1 & H2 & H3 & H4). split_and!; [done|done|by apply HE'|by apply HE'].
    - intros (Ha & S0 & m & T & S & H1 & H2 & H3 & H4 & H5 & H6).
      split; [done|]. exists S0, m, T, S. split_and!; try done; [intros j Hj; apply HV; [done|by apply H5]|by apply HE'].
    - intros (Ha & S0 & m & T & S & H1 & H2 & H3).
      split; [done|]. exists S0, m, T, S. split_and!; [done|done|].
      intros j Πi φi Hj Hd1 Hd2 Hv. apply HE; [done|]. apply H3; try done. by apply HV.
    - intros (Ha & S0 & H1 & H2 & H3). split; [done|]. exists S0. split_and!; [done|done|by apply HE'].
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|].
      exists S0, S1, S2. split_and!; [done|done|by apply HE'].
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|].
      exists S0, S1, S2. split_and!; [done|done|by apply HE'].
    - intros (H0 & H1 & H2 & H3). split_and!; [done|done|done|by apply HE'].
  Qed.

  Lemma Vty_ext_1 N n T Π φ v :
    (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
    (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Vty N El1 Vl1 n T Π φ v → Vty N El2 Vl2 n T Π φ v.
  Proof.
    intros HE HV. revert Π φ v.
    induction T as [|ub lb c T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c U IH|s x a mt|lb m C T1 IH];
      intros Π φ v; simpl; try done.
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done|done|].
      intros j φ' Πu φu u Hj Hd' Hh HΠ Hφ Hu.
      apply HE; [done|]. apply H; try done. by apply HV.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; auto.
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros j ss Hj Hl Hs. apply HE; [done|]. by apply H.
    - auto.
  Qed.

  Lemma Vres_ext_1 N n σ Π φ v :
    (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
    (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Vres N El1 Vl1 n σ Π φ v → Vres N El2 Vl2 n σ Π φ v.
  Proof. intros HE HV. destruct σ; simpl; [by apply Vty_ext_1|done]. Qed.

  Lemma Fdef_ext_1 N n σ d Π φ e :
    (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
    (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Fdef N El1 Vl1 n σ d Π φ e → Fdef N El2 Vl2 n σ d Π φ e.
  Proof.
    intros HE HV H g Π' φ' H1 H2 H3 H4.
    destruct (H g Π' φ' H1 H2 H3 H4) as [Hv Hs]. split.
    - intros Hval. eapply Vres_ext_1; [exact HE|exact HV|exact (Hv Hval)].
    - intros α e' Hst. eapply Fobl_ext_1; [exact HE|exact HV|by apply Hs].
  Qed.
End ext.

Lemma Fdef_ext El1 El2 Vl1 Vl2 N n σ d Π φ e :
  (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
  (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
  Fdef N El1 Vl1 n σ d Π φ e ↔ Fdef N El2 Vl2 n σ d Π φ e.
Proof.
  intros HE HV. split; apply Fdef_ext_1; try done; intros j Hj; intros; symmetry; auto.
Qed.

Lemma Vres_ext El1 El2 Vl1 Vl2 N n σ Π φ v :
  (∀ j, olt j n → ∀ N σ d Π φ e, El1 j N σ d Π φ e ↔ El2 j N σ d Π φ e) →
  (∀ j, olt j n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
  Vres N El1 Vl1 n σ Π φ v ↔ Vres N El2 Vl2 n σ Π φ v.
Proof.
  intros HE HV. split; apply Vres_ext_1; try done; intros j Hj; intros; symmetry; auto.
Qed.

Lemma FLev_unfold n a : FLevA n a ↔ mk_flarg FLevA n a.
Proof.
  apply (osfix_unfold mk_flarg). intros m R R' H [N σ d Π φ e|N σ Π φ v]; cbn [mk_flarg].
  - apply Fdef_ext; intros j Hj; intros; cbn; by apply H.
  - apply Vres_ext; intros j Hj; intros; cbn; by apply H.
Qed.

Lemma FuelE_eq N n σ d Π φ e :
  e ∈ F^N _ n⟦σ ▷ d⟧(Π, φ) ↔ Fdef N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d Π φ e.
Proof. unfold FuelE at 1. by rewrite FLev_unfold. Qed.

Lemma Vfuel_eq N n σ Π φ v : v ∈ FV^N _ n⟦σ⟧(Π, φ) ↔ Vres N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ Π φ v.
Proof. unfold Vfuel at 1. by rewrite FLev_unfold. Qed.

Global Opaque FuelE Vfuel.
