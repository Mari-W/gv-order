(** * Fuel (stage S6, proposal §2.10, §2.11, decisions Q4, Q5, Q10, Q11)

      e ∈ F^N _ n⟦σ ▷ c ; r⟧(Π, φ, tk)     [FuelE N n σ c r Π φ tk e]
      v ∈ FV^N _ n⟦σ⟧(Π, φ)               [Vfuel N n σ Π φ v]

    A step-indexed predicate on one thread e. Π maps the ends the thread
    holds to their session types, φ maps them to their counters, and tk
    is the thread's count of link tickets. σ is the credited type of the
    value e returns, or [RThread] for a thread, which returns holding no
    end. r is the reserve, the tickets e must still hold when it
    returns, and c the frame, the channel actions e may still perform
    before it returns. N is the refill, the counter of a fresh end and
    of an end after an action. Counters, credits, the frame and N range
    over ℕ ∪ {∞}. Deadlock freedom is the instance N = ∞.

    The predicate reads no point, no world and no relation. Under the
    merged judgment (decision Q11) a cost protocol is a session type
    with its annotations, so Π is the session-type part of the
    environment of the live relation at the same index (stage S8). The
    payload of a send is read at the payload type and its credit in the
    session type of Π.

    Counters evolve by one update at every index. An action on o
    refills o to N and ticks every other counter of the thread by one
    (truncated at 0). A send and a spawn hand the ends of the value they
    move on with their counters minus one. New ends start at N.
    A link spends a ticket and moves no counter. The checks are F-Tick
    (an action asks every other counter at least 1, and the frame at
    least 1), the hand-over (every handed counter at least 1), and
    F-Wait (no action on an idle end). An idle end is an end whose
    session type is Skip: no thread can act on it (decision Q5, the
    corrected form). Idleness only removes the checks "≥ 1" of F-Tick and
    of the hand-over for that end. It never changes how a counter evolves.

    Every step costs one level, β, new, spawn and link included (decision
    Q10 (b), see docs/redesign/progress.md for why one clock fails).

    FuelE^N holds for every refill N′ ≥ N and is closed under injective
    renamings of ends (a link renames the partner of the removed end in
    another thread). [Vfuel] recurses on the type. A closure at
    T ⊸[c ; ϑ ; h] U with credit a has captured counters at least h + a,
    and for every refill N′ ≥ N, lower level, counters at or above the
    floor h and argument in [Vfuel] at T, its body satisfies [FuelE] at U
    with frame c and every reserve and ticket count that meet ϑ. A box
    does the same per force, for every session instance of its
    variables.

    Decision Q15 adds the clause of Q14 in V. A closure holds exactly the
    ends its body mentions (dom Π = fends v), and a box mentions no end.
    So every value of [Vfuel] is exact ([Vfuel_exact]), and the ends a
    send or a spawn reads off its label are the ends of its map. *)

From GV Require Export lang.Semantics static.Contexts relation.Sfix.

(** ** Maps of ends *)

Abbreviation penv := (gmap cend sty).
Abbreviation cenv := (gmap cend fuel).

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

(** ** The order on refills

    Finite refills are ordered by ≤, and ∞ lies above ∞ only. FuelE and
    the closure and box clauses of [Vfuel] hold at every refill above N
    in this order. Under the order of ℕ ∪ {∞} a finite refill could jump
    to ∞, where a box promises its body only at the instances with the
    annotations of N = ∞ ([sinsts None]), and E-Force at a finite N has
    no instance to force (docs/redesign/progress.md, S7.5). *)
Definition rle (N N' : fuel) : Prop :=
  match N, N' with
  | Some m, Some m' => m ≤ m'
  | None, None => True
  | _, _ => False
  end.

Lemma rle_refl N : rle N N.
Proof. destruct N; simpl; lia. Qed.

Lemma rle_trans N1 N2 N3 : rle N1 N2 → rle N2 N3 → rle N1 N3.
Proof. destruct N1, N2, N3; simpl; lia || done. Qed.

Lemma rle_fle N N' : rle N N' → fle N N'.
Proof. destruct N, N'; simpl; lia || done. Qed.

Lemma rle_sinsts N N' ss : rle N N' → sinsts N' ss → sinsts N ss.
Proof. intros H [H1 H2]. split; [done|]. intros ->. destruct N'; [done|]. by apply H2. Qed.

(** ** Counters, idle ends and the update *)

(** One unit less, truncated at 0. ∞ stays ∞. *)
Definition ftick (f : fuel) : fuel := fsub f (Some 1).

(** An idle end ([idle], types/Types.v): its session type is Skip. *)

Definition idle_at (Π : penv) (o : cend) : Prop := ∃ S, Π !! o = Some S ∧ idle S.

(** The ends X have a unit to spare: every counter on X of an end that is
    not idle is at least 1. F-Tick asks it of the other ends of an action,
    the hand-over of the ends of a sent or spawned value. *)
Definition fspare (Π : penv) (φ : cenv) (X : gset cend) : Prop :=
  ∀ o f, o ∈ X → φ !! o = Some f → ¬ idle_at Π o → fle (Some 1) f.

(** An action on o: o refills to N, the other counters tick. *)
Definition refill (N : fuel) (o : cend) (φ : cenv) : cenv := <[o := N]> (ftick <$> delete o φ).

(** The counters the ends M take with them: one unit less. *)
Definition fhand (M : gset cend) (φ : cenv) : cenv := ftick <$> mres M φ.

(** The ends c⁺ and c⁻ of a new channel, at S and its dual, counters N. *)
Definition pnew (c : chan) (S : sty) (Π : penv) : penv := <[EPos c := S]> (<[ENeg c := dual S]> Π).
Definition cnew (N : fuel) (c : chan) (φ : cenv) : cenv := <[EPos c := N]> (<[ENeg c := N]> φ).

(** A new channel is fresh against the thread's own maps. *)
Definition ffresh (c : chan) (Π : penv) (φ : cenv) : Prop :=
  (EPos c ∉ dom Π) ∧ (ENeg c ∉ dom Π) ∧ (EPos c ∉ dom φ) ∧ (ENeg c ∉ dom φ).

(** The two ends of a link label, held at dual protocols. *)
Definition plink (Π : penv) (os : gset cend) : Prop :=
  ∃ o1 o2 S1 S2, os = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧ Π !! o1 = Some S1 ∧ Π !! o2 = Some S2 ∧
    sequiv S2 (dual S1).

(** ** Result types and readers *)

(** The credited type T^a of a returned value, or a thread, which
    returns any value and holds no end then. *)
Inductive rty := RTy (T : ty) (a : fuel) | RThread.

(** FuelE at one level reads the refill, the result type, the frame,
    the reserve, protocols, counters, tickets and the term. Vfuel reads
    the refill, the type, protocols, counters and the value. *)
Abbreviation epred := (fuel → rty → fuel → nat → penv → cenv → nat → expr → Prop).
Abbreviation vpred := (fuel → rty → penv → cenv → expr → Prop).

(** ** The obligations of a step (§2.10)

    One per label, for the step e --α--> e' at index n' + 1, given FuelE
    and Vfuel at the levels up to n'. *)
Section obligations.
  Context (N : fuel) (El : nat → epred) (Vl : nat → vpred) (n' : nat)
    (σ : rty) (d : fuel) (r : nat) (Π : penv) (φ : cenv) (tk : nat).

  (** An action on o. F-Wait: o is held and not idle. F-Tick: every other
      end that is not idle has a unit to spare, and so has the frame. *)
  Definition f_act (o : cend) : Prop :=
    ¬ idle_at Π o ∧ o ∈ dom φ ∧ fspare Π φ (dom φ ∖ {[o]}) ∧ fle (Some 1) d.

  Definition f_beta (e' : expr) : Prop := El n' N σ d r Π φ tk e'.

  (** new_ℓ and new_κ o. *)
  Definition f_new (c : chan) (e' : expr) : Prop :=
    ffresh c Π φ → ∃ S, El n' N σ d r (pnew c S Π) (cnew N c φ) tk e'.

  (** The child takes the ends of v with one unit less and ⌈tk/2⌉
      tickets, and runs as a thread. The parent keeps ⌊tk/2⌋. *)
  Definition f_spawn (v e' : expr) : Prop :=
    fends v ⊆ dom φ ∧ fspare Π φ (fends v) ∧
    El n' N RThread None 0 (mres (fends v) Π) (fhand (fends v) φ) (Nat.div2 (S tk)) (App v EUnit) ∧
    El n' N σ d r (mrem (fends v) Π) (mrem (fends v) φ) (Nat.div2 tk) e'.

  (** A send hands on held ends other than its subject, at the payload
      type and credit of the session type, with one unit less. *)
  Definition f_send (o : cend) (w e' : expr) : Prop :=
    f_act o ∧ ∃ S0 m T b S, Π !! o = Some S0 ∧ unfoldS S0 = SSeq (SSnd m T b) S ∧
      fends w ⊆ dom φ ∖ {[o]} ∧ fspare Π φ (fends w) ∧
      Vl n' N (RTy T b) (mres (fends w) Π) (fhand (fends w) φ) w ∧
      El n' N σ (ftick d) r (<[o := S]> (mrem (fends w) Π)) (refill N o (mrem (fends w) φ)) tk e'.

  (** A receive continues for every incoming value at the payload type,
      with any protocols and counters it brings. *)
  Definition f_recv (o : cend) (w e' : expr) : Prop :=
    f_act o ∧ ∃ S0 m T b S, Π !! o = Some S0 ∧ unfoldS S0 = SSeq (SRcv m T b) S ∧
      ∀ j Πi φi, j ≤ n' → Πi ##ₘ <[o := S]> Π → φi ##ₘ refill N o φ →
        Vl j N (RTy T b) Πi φi w →
        El j N σ (ftick d) r (<[o := S]> Π ∪ Πi) (refill N o φ ∪ φi) tk e'.

  Definition f_close (o : cend) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0, Π !! o = Some S0 ∧ unfoldS S0 = SEnd ∧
      El n' N σ (ftick d) r (delete o Π) (ftick <$> delete o φ) tk e'.

  Definition f_select (o : cend) (i : bool) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0 S1 S2, Π !! o = Some S0 ∧ unfoldS S0 = SPlus S1 S2 ∧
      El n' N σ (ftick d) r (<[o := if i then S2 else S1]> Π) (refill N o φ) tk e'.

  Definition f_branch (o : cend) (i : bool) (e' : expr) : Prop :=
    f_act o ∧ ∃ S0 S1 S2, Π !! o = Some S0 ∧ unfoldS S0 = SWith S1 S2 ∧
      El n' N σ (ftick d) r (<[o := if i then S2 else S1]> Π) (refill N o φ) tk e'.

  (** A link forwards held ends whose protocols are dual and spends a
      ticket. The soup reads the duality: after the link the partners of
      the two ends form one channel (stage S8). *)
  Definition f_link (os : gset cend) (e' : expr) : Prop :=
    plink Π os ∧ os ⊆ dom φ ∧ 1 ≤ tk ∧ El n' N σ d r (mrem os Π) (mrem os φ) (tk - 1) e'.

  Definition Fobl (α : tlabel) (e' : expr) : Prop :=
    match α with
    | LBeta => f_beta e'                                  (* F-Beta *)
    | LNew _ c | LNewAt _ _ c => f_new c e'               (* F-New *)
    | LSpawn v => f_spawn v e'                          (* F-Spawn *)
    | LSess (SSend o w) => f_send o w e'                (* F-Send *)
    | LSess (SRecv o w) => f_recv o w e'                  (* F-Recv *)
    | LSess (SClose o) => f_close o e'                    (* F-Close *)
    | LSess (SSel o i) => f_select o i e'                 (* F-Select *)
    | LSess (SBra o i) => f_branch o i e'                 (* F-Branch *)
    | LSess (SLink os) => f_link os e'                    (* F-Link *)
    end.
End obligations.

(** ** Values at a credited type (§2.11)

    By recursion on the type. Points, upper and lower points, box
    constraints and transformers of boxes are not read. A product and a
    sum add their credit to their parts, and a product splits its ends
    into two disjoint parts. *)
Fixpoint Vty (N : fuel) (El : nat → epred) (Vl : nat → vpred) (n : nat)
    (T : ty) (a : fuel) (Π : penv) (φ : cenv) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => v = EUnit ∧ Π = ∅ ∧ φ = ∅
  | TSess s _ =>
      ∃ o S' f, v = Chan o ∧ Π = {[o := S']} ∧ φ = {[o := f]} ∧ sequiv S' s ∧ fle a f
  | TLolli _ _ c t h T1 a1 U a2 =>
      ∃ e, v = Lam e ∧ fends e = dom Π ∧ dom Π = dom φ ∧ (∀ o f, φ !! o = Some f → fle (fadd h a) f) ∧
        ∀ N' j φ' Πu φu u r tk, rle N N' → j < n → dom φ' = dom φ →
          (∀ o f, φ' !! o = Some f → fle h f) → Π ##ₘ Πu → φ' ##ₘ φu →
          Vl j N' (RTy T1 a1) Πu φu u → meets t r tk →
          El j N' (RTy U a2) c r (Π ∪ Πu) (φ' ∪ φu) tk (subst1 u e)
  | TProd T1 a1 T2 a2 =>
      ∃ v1 v2 Π1 Π2 φ1 φ2, v = Pair v1 v2 ∧ Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧
        Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
        Vty N El Vl n T1 (fadd a a1) Π1 φ1 v1 ∧ Vty N El Vl n T2 (fadd a a2) Π2 φ2 v2
  | TSum T1 a1 T2 a2 =>
      (∃ v', v = Inj false v' ∧ Vty N El Vl n T1 (fadd a a1) Π φ v') ∨
      (∃ v', v = Inj true v' ∧ Vty N El Vl n T2 (fadd a a2) Π φ v')
  | TBox _ k _ _ c t U aU =>
      ∃ e, v = EBox e ∧ fends e = ∅ ∧ Π = ∅ ∧ φ = ∅ ∧
        ∀ N' j ss r tk, rle N N' → j < n → length ss = k → sinsts N' ss → meets t r tk →
          El j N' (RTy (sinst_ty (slist ss) U) aU) c r ∅ ∅ tk (subst1 (EBox e) e)
  | TEx _ _ _ T1 aT => Vty N El Vl n T1 (fadd a aT) Π φ v
  end.

Definition Vres (N : fuel) (El : nat → epred) (Vl : nat → vpred) (n : nat)
    (σ : rty) (Π : penv) (φ : cenv) (v : expr) : Prop :=
  match σ with
  | RTy T a => Vty N El Vl n T a Π φ v
  | RThread => Π = ∅ ∧ φ = ∅
  end.

(** ** One level of FuelE

    For every refill N′ ≥ N and every renaming g injective on the held
    ends, the renamed term returns a value in [Vfuel] at σ that holds the
    reserve (val), and every step meets its obligation (step). *)
Definition Fdef (N : fuel) (El : nat → epred) (Vl : nat → vpred) (n' : nat)
    (σ : rty) (d : fuel) (r : nat) (Π : penv) (φ : cenv) (tk : nat) (e : expr) : Prop :=
  ∀ N' g Π' φ', rle N N' → kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
    (is_val (emap g e) → r ≤ tk ∧ Vres N' El Vl (S n') σ Π' φ' (emap g e)) ∧    (* (val) *)
    ∀ α e', tstep (emap g e) α e' → Fobl N' El Vl n' σ d r Π' φ' tk α e'.        (* (step) *)

Record flevel := FLevel { fE : epred; fV : vpred }.

Definition mk_flevel (below : nat → flevel) (n : nat) : flevel :=
  FLevel
    (λ N σ d r Π φ tk e,
       match n with
       | 0 => True
       | S n' => Fdef N (λ j, fE (below j)) (λ j, fV (below j)) n' σ d r Π φ tk e
       end)
    (λ N σ Π φ v, Vres N (λ j, fE (below j)) (λ j, fV (below j)) n σ Π φ v).

Definition dummy_flevel : flevel := FLevel (λ _ _ _ _ _ _ _ _, False) (λ _ _ _ _ _, False).

Definition FLev (n : nat) : flevel := sfix dummy_flevel mk_flevel n.

Definition FuelE (N : fuel) (n : nat) : rty → fuel → nat → penv → cenv → nat → expr → Prop :=
  fE (FLev n) N.
Definition Vfuel (N : fuel) (n : nat) : rty → penv → cenv → expr → Prop := fV (FLev n) N.

(** A thread: result [RThread], reserve 0, frame ∞. *)
Abbreviation FuelT N n Π φ tk e := (FuelE N n RThread None 0 Π φ tk e).

(** Every held end starts at N, at a ticket count fixed for every index. *)
Definition fsem (N : fuel) (Π : penv) (e : expr) : Prop :=
  ∃ tk, ∀ n, FuelT N n Π (const N <$> Π) tk e.

(** ** Notations (Appendix A) *)

Notation "e ∈ F^ N '_' n ⟦ σ ▷ c ; r ⟧( Π , φ , tk )" := (FuelE N n σ c r Π φ tk e)
  (at level 70, N at level 0, n at level 0, σ at level 60, c at level 60,
   format "e  ∈  F^ N  '_'  n ⟦ σ  ▷  c  ;  r ⟧( Π ,  φ ,  tk )").
Notation "v ∈ FV^ N '_' n ⟦ σ ⟧( Π , φ )" := (Vfuel N n σ Π φ v)
  (at level 70, N at level 0, n at level 0, σ at level 60,
   format "v  ∈  FV^ N  '_'  n ⟦ σ ⟧( Π ,  φ )").

(** ** Unfolding *)

Section ext.
  Context (El1 El2 : nat → epred) (Vl1 Vl2 : nat → vpred).

  Lemma Fobl_ext_1 N n' σ d r Π φ tk α e' :
    (∀ j, j ≤ n' → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
    (∀ j, j ≤ n' → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Fobl N El1 Vl1 n' σ d r Π φ tk α e' → Fobl N El2 Vl2 n' σ d r Π φ tk α e'.
  Proof.
    intros HE HV.
    assert (HE' : ∀ N σ d r Π φ tk e, El1 n' N σ d r Π φ tk e → El2 n' N σ d r Π φ tk e)
      by (intros; apply HE; [lia|done]).
    destruct α as [|ℓ c|κ o c|v|[o w|o w|o|o i|o i|os]]; simpl;
      unfold f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link.
    - apply HE'.
    - intros H Hf. destruct (H Hf) as [S HS]. exists S. by apply HE'.
    - intros H Hf. destruct (H Hf) as [S HS]. exists S. by apply HE'.
    - intros (H1 & H2 & H3 & H4). split_and!; [done|done|by apply HE'|by apply HE'].
    - intros (Ha & S0 & m & T & b & S & H1 & H2 & H3 & H4 & H5 & H6).
      split; [done|]. exists S0, m, T, b, S. split_and!; try done; [apply HV; [lia|done]|by apply HE'].
    - intros (Ha & S0 & m & T & b & S & H1 & H2 & H3).
      split; [done|]. exists S0, m, T, b, S. split_and!; [done|done|].
      intros j Πi φi Hj Hd1 Hd2 Hv. apply HE; [done|]. apply H3; try done. by apply HV.
    - intros (Ha & S0 & H1 & H2 & H3). split; [done|]. exists S0. split_and!; [done|done|by apply HE'].
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|].
      exists S0, S1, S2. split_and!; [done|done|by apply HE'].
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|].
      exists S0, S1, S2. split_and!; [done|done|by apply HE'].
    - intros (H0 & H1 & H2 & H3). split_and!; [done|done|done|by apply HE'].
  Qed.

  Lemma Vty_ext_1 N n T a Π φ v :
    (∀ j, j < n → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
    (∀ j, j < n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Vty N El1 Vl1 n T a Π φ v → Vty N El2 Vl2 n T a Π φ v.
  Proof.
    intros HE HV. revert a Π φ v.
    induction T as [|ub lb c t h T1 IH1 a1 U IH2 a2|T1 IH1 a1 T2 IH2 a2|T1 IH1 a1 T2 IH2 a2
                   |m k C ub c t U IH aU|s x|lb m C T1 IH aT];
      intros a Π φ v; simpl; try done.
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done|done|].
      intros N' j φ' Πu φu u r tk HN Hj Hd' Hh HΠ Hφ Hu Ht.
      apply HE; [done|]. apply H; try done. by apply HV.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; auto.
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros N' j ss r tk HN Hj Hl Hs Ht. apply HE; [done|]. by apply H.
    - auto.
  Qed.

  Lemma Vres_ext_1 N n σ Π φ v :
    (∀ j, j < n → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
    (∀ j, j < n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Vres N El1 Vl1 n σ Π φ v → Vres N El2 Vl2 n σ Π φ v.
  Proof. intros HE HV. destruct σ; simpl; [by apply Vty_ext_1|done]. Qed.

  Lemma Fdef_ext_1 N n' σ d r Π φ tk e :
    (∀ j, j ≤ n' → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
    (∀ j, j ≤ n' → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
    Fdef N El1 Vl1 n' σ d r Π φ tk e → Fdef N El2 Vl2 n' σ d r Π φ tk e.
  Proof.
    intros HE HV H N' g Π' φ' HN H1 H2 H3 H4.
    destruct (H N' g Π' φ' HN H1 H2 H3 H4) as [Hv Hs]. split.
    - intros Hval. destruct (Hv Hval) as [Hr HV']. split; [done|].
      eapply Vres_ext_1; [| |exact HV']; intros j Hj; [apply HE|apply HV]; lia.
    - intros α e' Hst. eapply Fobl_ext_1; [exact HE|exact HV|by apply Hs].
  Qed.
End ext.

Lemma Fdef_ext El1 El2 Vl1 Vl2 N n' σ d r Π φ tk e :
  (∀ j, j ≤ n' → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
  (∀ j, j ≤ n' → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
  Fdef N El1 Vl1 n' σ d r Π φ tk e ↔ Fdef N El2 Vl2 n' σ d r Π φ tk e.
Proof.
  intros HE HV. split; apply Fdef_ext_1; try done; intros j Hj; intros; symmetry; auto.
Qed.

Lemma Vres_ext El1 El2 Vl1 Vl2 N n σ Π φ v :
  (∀ j, j < n → ∀ N σ d r Π φ tk e, El1 j N σ d r Π φ tk e ↔ El2 j N σ d r Π φ tk e) →
  (∀ j, j < n → ∀ N σ Π φ v, Vl1 j N σ Π φ v ↔ Vl2 j N σ Π φ v) →
  Vres N El1 Vl1 n σ Π φ v ↔ Vres N El2 Vl2 n σ Π φ v.
Proof.
  intros HE HV. split; apply Vres_ext_1; try done; intros j Hj; intros; symmetry; auto.
Qed.

Lemma FLev_below n j : j < n → sfix_below dummy_flevel mk_flevel n j = FLev j.
Proof. apply sfix_below_lt. Qed.

Lemma FuelE_0 N σ d r Π φ tk e : e ∈ F^N _ 0⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof. unfold FuelE, FLev. by rewrite sfix_unfold. Qed.

Lemma FuelE_S N n σ d r Π φ tk e :
  e ∈ F^N _ (S n)⟦σ ▷ d ; r⟧(Π, φ, tk) ↔ Fdef N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d r Π φ tk e.
Proof.
  unfold FuelE at 1, FLev. rewrite sfix_unfold. cbn [mk_flevel fE fV].
  apply Fdef_ext; intros j Hj; intros; unfold FuelE, Vfuel; by rewrite FLev_below by lia.
Qed.

Lemma Vfuel_eq N n σ Π φ v : v ∈ FV^N _ n⟦σ⟧(Π, φ) ↔ Vres N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ Π φ v.
Proof.
  unfold Vfuel at 1, FLev. rewrite sfix_unfold. cbn [mk_flevel fE fV].
  apply Vres_ext; intros j Hj; intros; unfold FuelE, Vfuel; by rewrite FLev_below by lia.
Qed.

Global Opaque FuelE Vfuel.
