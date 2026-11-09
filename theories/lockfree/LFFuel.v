(** * Fuel as a predicate on threads (lock-freedom plan §17.3, §17.8)

    [FuelE n W π φ e] is a step-indexed predicate on one thread e. It
    reads no type. π maps the ends the thread holds to their points and
    φ maps them to their counters. The budgets are read in the world,
    [w_bud W] for the refill and cap of an end at a point, and
    [w_pay W] for the floor of an end that arrives on a carrier at a
    point (§17.8). The index counts every step, administrative ones
    included.

    A channel step of the holder on another end burns one unit (F-Tick).
    Internal steps, new, spawn and links burn nothing. Acting on an end
    refills it to the budget of its next point. A send hands its payload
    on with the counter minus one, which must meet the floor of the
    carrier, and a spawn hands the ends of the closure to the child with
    the counter minus one. A link asks that the budget of the peer lie
    below the linker's counter. A thread acts only on ends whose partner
    has a finite budget (F-Wait), and no counter exceeds its budget
    (F-Cap). Receive is universal over the incoming ends.

    [fupd] computes the counters of the successor from the label. *)

From stdpp Require Import base gmap.
From LRGV Require Import lang.Semantics relation.Worlds.

(** ** Counters *)

(** A counter. [None] is ∞, the end carries no obligation. *)
Abbreviation fuel := (option nat).

(** The order on counters, with ∞ on top. *)
Definition fle (a b : fuel) : Prop :=
  match a, b with
  | _, None => True
  | None, Some _ => False
  | Some m, Some n => m ≤ n
  end.

(** One unit less. ∞ stays ∞. *)
Definition ftick (f : fuel) : fuel := (λ m, m - 1) <$> f.

Lemma fle_refl f : fle f f.
Proof. destruct f; simpl; lia. Qed.

Lemma fle_tick f g : fle f g → fle (ftick f) g.
Proof. destruct f, g; simpl; lia. Qed.

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

(** A link of o1 with o2 hands the obligation of o1 to the partner of
    o2, whose budget must lie below the counter of o1. *)
Definition flink1 (W : world) (π : gmap cend point) (φ : gmap cend fuel) (o1 o2 : cend)
    : Prop :=
  ∀ m, φ !! o1 = Some (Some m) →
    ∃ k2 m', π !! o2 = Some k2 ∧ w_bud W (pt_dual k2) = Some m' ∧ m' < m.

(** The link clause, for both ends of a link label (the set is
    unordered, so this covers both directions). A self-link has no
    clause. The relation rejects it. *)
Definition flink (W : world) (π : gmap cend point) (φ : gmap cend fuel) (cd : gset cend)
    : Prop :=
  ∀ o1 o2, cd = {[o1; o2]} → o1 ≠ o2 → flink1 W π φ o1 o2.

(** Incoming ends: points and counters on exactly the ends of w, under
    the cap and at or above the floor fl. *)
Definition fin_ok (W : world) (fl : nat) (w : expr)
    (πi : gmap cend point) (φi : gmap cend fuel) : Prop :=
  dom πi = fends w ∧ dom φi = fends w ∧ fcap W πi φi ∧
  (∀ o f, φi !! o = Some f → fle (Some fl) f) ∧
  ∀ o k, πi !! o = Some k → w_bud W (pt_dual k) ≠ None.

(** ** The predicates, level by level *)

Abbreviation fpred := (world → gmap cend point → gmap cend fuel → expr → Prop).

(** The obligation of a step e --α--> e' at index n' + 1, given the
    predicates E and V at the levels up to n'. *)
Definition Fobl (E V : nat → fpred) (n' : nat) (W : world)
    (π : gmap cend point) (φ : gmap cend fuel) (α : tlabel) (e' : expr) : Prop :=
  match α with
  | LBeta | LNew _ _ => E n' W (fupd W π φ α).1 (fupd W π φ α).2 e'
  | LSpawn w =>
      fhand 0 (fends w) φ ∧
      E n' W (fchild π φ w).1 (fchild π φ w).2 (App w EUnit) ∧
      E n' W (fupd W π φ α).1 (fupd W π φ α).2 e'
  | LSess σ =>
      (∀ o, sl_end σ = Some o → ftick_ok o φ) ∧
      match σ with
      | SSend o w =>
          (∀ k, π !! o = Some k → fhand (w_pay W k) (fends w) φ) ∧
          ftravel W π (fends w) ∧
          E n' W (fupd W π φ α).1 (fupd W π φ α).2 e'
      | SRecv o w =>
          (* the floor is keyed by the carrier's point at the sender,
             the dual of the receiver's point *)
          ∀ k j πi φi, π !! o = Some k → j ≤ n' →
            dom πi ## dom (fupd W π φ α).1 →
            fin_ok W (w_pay W (pt_dual k)) w πi φi →
            V j W πi φi w →
            E j W ((fupd W π φ α).1 ∪ πi) ((fupd W π φ α).2 ∪ φi) e'
      | SLink cd =>
          flink W π φ cd ∧ E n' W (fupd W π φ α).1 (fupd W π φ α).2 e'
      | _ => E n' W (fupd W π φ α).1 (fupd W π φ α).2 e'
      end
  end.

Definition Fdef (E V : nat → fpred) (n' : nat) (W : world)
    (π : gmap cend point) (φ : gmap cend fuel) (e : expr) : Prop :=
  fcap W π φ ∧ fwait W π e ∧
  ∀ α e', tstep e α e' → Fobl E V n' W π φ α e'.

(** Values. An end, a unit, a constant and a point carry nothing (the
    floor [b_val] of §17.3 is 0, and §17.8 drops it). A closure applied
    at a lower level to an argument in Vfuel satisfies FuelE, and so
    does a forced box. Pairs and injections componentwise. *)
Fixpoint Vfdef (E V : nat → fpred) (n : nat) (W : world)
    (π : gmap cend point) (φ : gmap cend fuel) (w : expr) : Prop :=
  match w with
  | EUnit | Konst _ | Chan _ _ | EPt _ => True
  | Lam eb =>
      ∀ j v πa φa, j < n → dom πa ## dom π → fin_ok W 0 v πa φa → V j W πa φa v →
        E j W (π ∪ πa) (φ ∪ φa) (App (Lam eb) v)
  | EBox eb => ∀ j, j < n → E j W π φ (App EForce (EBox eb))
  | Pair u v =>
      Vfdef E V n W (mres (fends u) π) (mres (fends u) φ) u ∧
      Vfdef E V n W (mres (fends v) π) (mres (fends v) φ) v
  | Inj1 u | Inj2 u => Vfdef E V n W π φ u
  | _ => False
  end.

Record flevel := FLevel { fE : fpred; fV : fpred }.

Definition mk_flevel (below : nat → flevel) (n : nat) : flevel :=
  {| fE := match n with
           | 0 => λ _ _ _ _, True
           | S n' => Fdef (λ j, fE (below j)) (λ j, fV (below j)) n'
           end;
     fV := Vfdef (λ j, fE (below j)) (λ j, fV (below j)) n |}.

Definition dummy_flevel : flevel := {| fE := λ _ _ _ _, False; fV := λ _ _ _ _, False |}.

(** [flevels n j] is level j for every j < n. *)
Fixpoint flevels (n : nat) : nat → flevel :=
  match n with
  | 0 => λ _, dummy_flevel
  | S n' => λ j, if decide (j < n') then flevels n' j else mk_flevel (flevels n') n'
  end.

Definition flevel_at (n : nat) : flevel := flevels (S n) n.

Definition FuelE (n : nat) : fpred := fE (flevel_at n).
Definition Vfuel (n : nat) : fpred := fV (flevel_at n).

(** Every held end starts full (§17.4). *)
Definition fsem (W : world) (π : gmap cend point) (t : expr) : Prop :=
  ∀ n, FuelE n W π (w_bud W <$> π) t.

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

Lemma Fobl_ext (E1 V1 E2 V2 : nat → fpred) n' W π φ α e' :
  (∀ j, j ≤ n' → ∀ W π φ e, E1 j W π φ e ↔ E2 j W π φ e) →
  (∀ j, j ≤ n' → ∀ W π φ e, V1 j W π φ e ↔ V2 j W π φ e) →
  Fobl E1 V1 n' W π φ α e' ↔ Fobl E2 V2 n' W π φ α e'.
Proof.
  intros HE HV.
  assert (HE' : ∀ W π φ e, E1 n' W π φ e ↔ E2 n' W π φ e) by (apply HE; lia).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl.
  - apply HE'.
  - split; intros [H1 H2]; split; try done; intros k j πi φi Hk Hj Hd Hin Hv;
      apply (HE j Hj); apply (H2 k); try done; by apply (HV j Hj).
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - by rewrite HE'.
  - apply HE'.
  - by rewrite !HE'.
Qed.

Lemma Fdef_ext (E1 V1 E2 V2 : nat → fpred) n' W π φ e :
  (∀ j, j ≤ n' → ∀ W π φ e, E1 j W π φ e ↔ E2 j W π φ e) →
  (∀ j, j ≤ n' → ∀ W π φ e, V1 j W π φ e ↔ V2 j W π φ e) →
  Fdef E1 V1 n' W π φ e ↔ Fdef E2 V2 n' W π φ e.
Proof.
  intros HE HV. unfold Fdef.
  split; intros (Hc & Hw & Hs); (split; [done|split; [done|]]);
    intros α e' Hst; specialize (Hs α e' Hst);
    [by rewrite <-(Fobl_ext E1 V1 E2 V2)|by rewrite (Fobl_ext E1 V1 E2 V2)].
Qed.

Lemma Vfdef_ext (E1 V1 E2 V2 : nat → fpred) n W π φ w :
  (∀ j, j < n → ∀ W π φ e, E1 j W π φ e ↔ E2 j W π φ e) →
  (∀ j, j < n → ∀ W π φ e, V1 j W π φ e ↔ V2 j W π φ e) →
  Vfdef E1 V1 n W π φ w ↔ Vfdef E2 V2 n W π φ w.
Proof.
  intros HE HV. induction w in π, φ |- *; simpl; try done.
  - split; intros H j v πa φa Hj Hd Hin Hv;
      [rewrite <-HE by done|rewrite HE by done];
      apply H; try done; [rewrite HV|rewrite <-HV]; done.
  - by rewrite IHw1, IHw2.
  - split; intros H j Hj; [rewrite <-HE by done|rewrite HE by done]; auto.
Qed.

Lemma FuelE_0 W π φ e : FuelE 0 W π φ e.
Proof. unfold FuelE. rewrite flevel_at_eq. done. Qed.

Lemma FuelE_S n W π φ e : FuelE (S n) W π φ e ↔ Fdef FuelE Vfuel n W π φ e.
Proof.
  unfold FuelE at 1. rewrite flevel_at_eq.
  change (Fdef (λ j, fE (flevels (S n) j)) (λ j, fV (flevels (S n) j)) n W π φ e
    ↔ Fdef FuelE Vfuel n W π φ e).
  apply Fdef_ext; intros j Hj W' π' φ' e'; unfold FuelE, Vfuel;
    by rewrite flevels_at by lia.
Qed.

Lemma Vfuel_eq n W π φ w : Vfuel n W π φ w ↔ Vfdef FuelE Vfuel n W π φ w.
Proof.
  unfold Vfuel at 1. rewrite flevel_at_eq.
  change (Vfdef (λ j, fE (flevels n j)) (λ j, fV (flevels n j)) n W π φ w
    ↔ Vfdef FuelE Vfuel n W π φ w).
  apply Vfdef_ext; intros j Hj W' π' φ' e'; unfold FuelE, Vfuel;
    by rewrite flevels_at by lia.
Qed.

(** ** Monotonicity in the index *)

Lemma FuelE_S_down n W π φ e : FuelE (S n) W π φ e → FuelE n W π φ e.
Proof.
  revert W π φ e. induction n as [|n IH]; intros W π φ e H; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H as (Hc & Hw & Hs).
  split; [done|split; [done|]]. intros α e' Hst. specialize (Hs α e' Hst).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in *.
  - by apply IH.
  - destruct Hs as [H1 H2]. split; [done|].
    intros k j πi φi Hk Hj. apply (H2 k j πi φi Hk). lia.
  - destruct Hs as (H1 & H2 & H3 & H4). auto.
  - destruct Hs as [H1 H2]. auto.
  - destruct Hs as (H1 & H2 & H3). auto.
  - destruct Hs as [H1 H2]. auto.
  - destruct Hs as [H1 H2]. auto.
  - by apply IH.
  - destruct Hs as (H1 & H2 & H3). auto.
Qed.

Lemma FuelE_down m n W π φ e : m ≤ n → FuelE n W π φ e → FuelE m W π φ e.
Proof. induction 1; eauto using FuelE_S_down. Qed.

Lemma Vfuel_down m n W π φ w : m ≤ n → Vfuel n W π φ w → Vfuel m W π φ w.
Proof.
  intros Hmn. rewrite !Vfuel_eq. induction w in π, φ |- *; simpl; try done.
  - intros H j v πa φa Hj. apply H. lia.
  - intros [H1 H2]. auto.
  - auto.
  - auto.
  - intros H j Hj. apply H. lia.
Qed.

(** ** The clauses of a thread at index n + 1 *)

Section clauses.
  Context (n : nat) (W : world) (π : gmap cend point) (φ : gmap cend fuel) (e : expr).
  Context (HF : FuelE (S n) W π φ e).

  (** F-Cap: counters stay at or below the budget of their point. *)
  Lemma fuel_cap : fcap W π φ.
  Proof. by apply FuelE_S in HF as (? & _ & _). Qed.

  (** F-Wait: the partner of an end the thread acts on has a finite
      budget, and the end is held. *)
  Lemma fuel_wait σ e' o :
    tstep e (LSess σ) e' → sl_end σ = Some o →
    ∃ k m, π !! o = Some k ∧ w_bud W (pt_dual k) = Some m.
  Proof.
    intros Hst Ho. apply FuelE_S in HF as (_ & Hw & _).
    destruct (Hw σ e' o Hst Ho) as (k & Hk & Hb).
    destruct (w_bud W (pt_dual k)) as [m|] eqn:E; [|done]. eauto.
  Qed.

  Lemma fuel_obl α e' : tstep e α e' → Fobl FuelE Vfuel n W π φ α e'.
  Proof. intros Hst. apply FuelE_S in HF as (_ & _ & Hs). by apply Hs. Qed.

  (** F-Tick. *)
  Lemma fuel_tick σ e' o : tstep e (LSess σ) e' → sl_end σ = Some o → ftick_ok o φ.
  Proof. intros Hst Ho. pose proof (fuel_obl _ _ Hst) as H. simpl in H. by apply H. Qed.

  (** The floor of a send, at the point of the carrier. *)
  Lemma fuel_send_floor o w e' k :
    tstep e (LSess (SSend o w)) e' → π !! o = Some k → fhand (w_pay W k) (fends w) φ.
  Proof. intros Hst Hk. pose proof (fuel_obl _ _ Hst) as (_ & H & _). by apply H. Qed.

  (** The payload of a send has finite partner budgets. *)
  Lemma fuel_send_travel o w e' : tstep e (LSess (SSend o w)) e' → ftravel W π (fends w).
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & _ & H & _). Qed.

  (** The link clause. *)
  Lemma fuel_link cd e' : tstep e (LSess (SLink cd)) e' → flink W π φ cd.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H & _). Qed.

  (** The ends a spawn hands to the child have a unit to spare. *)
  Lemma fuel_spawn_hand w e' : tstep e (LSpawn w) e' → fhand 0 (fends w) φ.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (H & _ & _). Qed.

  (** ** lffuel_step: the successor at the updated counters *)

  (** Every step but a receive. *)
  Lemma lffuel_step α e' :
    tstep e α e' → (∀ o w, α ≠ LSess (SRecv o w)) →
    FuelE n W (fupd W π φ α).1 (fupd W π φ α).2 e'.
  Proof.
    intros Hst Hr. pose proof (fuel_obl _ _ Hst) as H.
    destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in H |- *.
    - done.
    - by destruct (Hr o w).
    - by destruct H as (_ & _ & _ & H).
    - by destruct H as [_ H].
    - by destruct H as (_ & _ & H).
    - by destruct H as [_ H].
    - by destruct H as [_ H].
    - done.
    - by destruct H as (_ & _ & H).
  Qed.

  (** Receive: the receiver continues for every incoming value whose
      ends meet the floor of the carrier and the cap. *)
  Lemma lffuel_recv o w e' k j πi φi :
    tstep e (LSess (SRecv o w)) e' → π !! o = Some k → j ≤ n →
    dom πi ## dom (fupd W π φ (LSess (SRecv o w))).1 →
    fin_ok W (w_pay W (pt_dual k)) w πi φi → Vfuel j W πi φi w →
    FuelE j W ((fupd W π φ (LSess (SRecv o w))).1 ∪ πi)
      ((fupd W π φ (LSess (SRecv o w))).2 ∪ φi) e'.
  Proof.
    intros Hst Hk Hj Hd Hin Hv. pose proof (fuel_obl _ _ Hst) as [_ H]. eauto.
  Qed.

  (** Spawn: the child at the handed-on counters, the parent without them. *)
  Lemma lffuel_spawn w e' :
    tstep e (LSpawn w) e' →
    FuelE n W (fchild π φ w).1 (fchild π φ w).2 (App w EUnit) ∧
    FuelE n W (fupd W π φ (LSpawn w)).1 (fupd W π φ (LSpawn w)).2 e'.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H1 & H2). Qed.

  (** ** At counter 0 *)

  (** The holder's next channel step is on the end at 0. *)
  Lemma fuel_zero_act o σ e' o' :
    φ !! o = Some (Some 0) → tstep e (LSess σ) e' → sl_end σ = Some o' → o' = o.
  Proof.
    intros H0 Hst Ho'. destruct (decide (o = o')) as [|Hne]; [done|].
    pose proof (fuel_tick _ _ _ Hst Ho' o 0 Hne H0). lia.
  Qed.

  (** It does not send the end at 0. *)
  Lemma fuel_zero_nosend o o' w e' :
    φ !! o = Some (Some 0) → tstep e (LSess (SSend o' w)) e' → o ∉ fends w.
  Proof.
    intros H0 Hst Hin. destruct (fuel_wait _ _ o' Hst eq_refl) as (k & m & Hk & _).
    pose proof (fuel_send_floor _ _ _ _ Hst Hk o 0 Hin H0). lia.
  Qed.

  (** It does not spawn the end at 0 away. *)
  Lemma fuel_zero_nospawn o w e' :
    φ !! o = Some (Some 0) → tstep e (LSpawn w) e' → o ∉ fends w.
  Proof.
    intros H0 Hst Hin. pose proof (fuel_spawn_hand _ _ Hst o 0 Hin H0). lia.
  Qed.

  (** It does not link the end at 0 to another end. *)
  Lemma fuel_zero_nolink o o2 e' :
    φ !! o = Some (Some 0) → tstep e (LSess (SLink {[o; o2]})) e' → o2 = o.
  Proof.
    intros H0 Hst. destruct (decide (o2 = o)) as [|Hne]; [done|].
    destruct (fuel_link _ _ Hst o o2 eq_refl (not_eq_sym Hne) 0 H0)
      as (k2 & m' & _ & _ & Hlt). lia.
  Qed.
End clauses.

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

Lemma fcap_union (W : world) π1 φ1 π2 φ2 :
  fcap W π1 φ1 → fcap W π2 φ2 → dom π1 ## dom π2 → fcap W (π1 ∪ π2) (φ1 ∪ φ2).
Proof.
  intros H1 H2 Hd o f Hf. apply lookup_union_Some_raw in Hf as [Hf|[_ Hf]].
  - destruct (H1 o f Hf) as (k & Hk & Hle). exists k. split; [|done].
    by apply lookup_union_Some_l.
  - destruct (H2 o f Hf) as (k & Hk & Hle). exists k. split; [|done].
    rewrite lookup_union_r; [done|]. apply not_elem_of_dom. intros Hin.
    apply (Hd o Hin). apply elem_of_dom. eauto.
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

(** The ends handed on by a send at floor [w_pay W k], or by a spawn at
    floor 0, are admissible incoming ends for the receiver or the child.
    A receiver at the dual point pt_dual k reads the floor
    [w_pay W (pt_dual (pt_dual k))], which is [w_pay W k] by
    [pt_dual_dual]. *)
Lemma fhand_fin_ok (W : world) fl π φ w :
  fcap W π φ → dom φ = dom π → fends w ⊆ dom π → fhand fl (fends w) φ →
  ftravel W π (fends w) →
  fin_ok W fl w (fchild π φ w).1 (fchild π φ w).2.
Proof.
  intros Hc Hdom Hsub Hh Ht. unfold fchild; simpl. split_and!.
  - rewrite dom_mres. set_solver.
  - rewrite dom_fmap_L, dom_mres, Hdom. set_solver.
  - by apply fcap_tick, fcap_mres.
  - intros o f Hf. apply lookup_fmap_Some in Hf as (f0 & <- & Hf).
    apply lookup_mres_Some in Hf as [Hf Hx].
    destruct f0 as [m|]; simpl; [|done].
    pose proof (Hh o m Hx Hf). lia.
  - intros o k Hk. apply lookup_mres_Some in Hk as [Hk Hx]. by apply (Ht o k).
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

(** ** Full counters *)

Lemma fsem_cap (W : world) π : fcap W π (w_bud W <$> π).
Proof.
  intros o f Hf. apply lookup_fmap_Some in Hf as (k & <- & Hk).
  exists k. split; [done|apply fle_refl].
Qed.

Lemma fsem_FuelE (W : world) π t n : fsem W π t → FuelE n W π (w_bud W <$> π) t.
Proof. intros H. apply H. Qed.
