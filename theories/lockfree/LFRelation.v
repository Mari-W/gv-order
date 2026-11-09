(** * The lock-free relation with a placement oracle (lock-freedom plan §15)

    [LFPrel N ω n W Σ T p] is the live relation [LPrel n W Σ T p] with
    an invariant layer. The layer annotates every configuration that a
    run of p reaches with one environment per thread ([ac_env]) and one
    fuel counter per thread and channel ([ac_fuel]). The annotation of
    the start comes from the oracle ω ([or_init]), and every step
    updates it by [aupd], a function of the step. Every choice that the
    live relation makes existentially inside a level (the point and the
    session types at O-New, the split at O-Spawn and O-Send) is made by
    ω ([or_pick]) from the thread's environment and term, so the
    annotation of a reachable configuration does not depend on the step
    index. Every annotated configuration that a run reaches satisfies
    [LFconf n]: every thread is in the live term relation at index n
    under its environment ([LFErel]), the environments are linear and
    pair every entry with a dual one, and a counter at 0 forces the
    thread to act on that channel next.

    Fuel follows plan §3.1 and §7 in the conservative form: a counter
    ticks at every channel step of its holder on another channel, a
    channel step on it refills it to N, sending or spawning an entry
    passes its counter minus one, and a link passes the smaller counter
    of the linked entries minus one to the peers it connects. The
    counters never decide the environments.

    Rank is the well-foundedness of W (plan §10.2). It needs no number:
    the rank of a blocked thread is the point of the entry it offers. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Criterion lockfree.LocalProgress liveness.LiveAdequacy.

(** ** The oracle

    [or_pick Θ e] is read at a thread with environment Θ and term e.
    At a new it gives the point of the first end and the two session
    types, at a spawn or a send the entries handed to the spawned
    thread or sent as payload. It does not see the fresh name, so it
    is invariant under the choice of that name. [or_init q] gives the
    environments of the threads of a starting configuration q. *)
Record placement := Placement {
  pl_pt : point;
  pl_s : sty;
  pl_s' : sty;
  pl_give : tenv
}.

Record oracle := Oracle {
  or_init : config → nat → tenv;
  or_pick : tenv → expr → placement
}.

(** ** Annotated configurations *)
Record aconf := AConf {
  ac_q : config;
  ac_env : nat → tenv;
  ac_fuel : nat → chan → nat
}.

(** ** Operations on environments *)

(** The entries of o that o1 does not take. Two ends of one channel
    sit at different points, so the point says which end o1 takes. *)
Definition ends_minus (o o1 : ends) : option ends :=
  match o, o1 with
  | Both e1 e2, One e => if decide (e.2 = e1.2) then Some (One e2) else Some (One e1)
  | _, _ => None
  end.

Definition tenv_minus (Θ Θ1 : tenv) : tenv :=
  map_imap (λ c o, match Θ1 !! c with None => Some o | Some o1 => ends_minus o o1 end) Θ.

Definition ends_merge (o o1 : ends) : ends :=
  match o, o1 with One e, One e1 => Both e e1 | _, _ => o end.

Definition tenv_union (Θ Θ1 : tenv) : tenv :=
  union_with (λ o o1, Some (ends_merge o o1)) Θ Θ1.

(** A link removes r and renames it to o in every other thread. *)
Definition tenv_rename (r o : chan) (Θ : tenv) : tenv :=
  match Θ !! r with
  | None => Θ
  | Some x => tenv_union (delete r Θ) {[o := x]}
  end.

Definition step_entry (f : sty * point → sty * point) (c : chan) (Θ : tenv) : tenv :=
  match Θ !! c with Some (One e) => <[c := One (f e)]> Θ | _ => Θ end.

(** The entry after an action, as in O-Send, O-Recv, O-Select and
    O-Branch. *)
Definition snd_next (e : sty * point) : sty * point :=
  match unfoldS e.1 with SSeq (SSnd _ _) s => (s, pt_shift 1 e.2) | _ => e end.
Definition rcv_next (e : sty * point) : sty * point :=
  match unfoldS e.1 with SSeq (SRcv _ _) s => (s, pt_shift 1 e.2) | _ => e end.
Definition sel_next (b : bool) (e : sty * point) : sty * point :=
  match unfoldS e.1 with SPlus s1 s2 => (sbranch b s1 s2, sel_pt e.2 b) | _ => e end.
Definition bra_next (b : bool) (e : sty * point) : sty * point :=
  match unfoldS e.1 with SWith s1 s2 => (sbranch b s1 s2, bra_pt e.2 b) | _ => e end.

(** ** The update of an annotation along a step *)

Definition eupd (A : nat → tenv) (t : nat) (Θ : tenv) : nat → tenv :=
  λ u, if decide (u = t) then Θ else A u.
Definition fupd (Φ : nat → chan → nat) (t : nat) (f : chan → nat) : nat → chan → nat :=
  λ u, if decide (u = t) then f else Φ u.

(** A channel step on c: c refills, every other counter ticks. *)
Definition tick (N : nat) (c : chan) (φ : chan → nat) : chan → nat :=
  λ x, if decide (x = c) then N else pred (φ x).

Definition pick1 (L : gset nat) : option nat :=
  match elements L with [i] => Some i | _ => None end.
Definition pick2 (L : gset nat) : option (nat * nat) :=
  match elements L with [i; j] => Some (i, j) | _ => None end.

(** A message on c from s to t. The payload takes the entries ω gives. *)
Definition sync_msg (ω : oracle) (N : nat) (A : nat → tenv) (Φ : nat → chan → nat)
    (s t : nat) (c : chan) (es : expr) : (nat → tenv) * (nat → chan → nat) :=
  let give := pl_give (or_pick ω (A s) es) in
  let As := step_entry snd_next c (tenv_minus (A s) give) in
  let At := tenv_union (step_entry rcv_next c (A t)) give in
  let Ft := λ x, if decide (x = c) then N
                 else if decide (x ∈ dom give) then
                   (if decide (x ∈ dom (A t)) then min (pred (Φ t x)) (pred (Φ s x))
                    else pred (Φ s x))
                 else pred (Φ t x) in
  (eupd (eupd A s As) t At, fupd (fupd Φ s (tick N c (Φ s))) t Ft).

(** A close or a choice on c between s and t. *)
Definition sync2 (N : nat) (A : nat → tenv) (Φ : nat → chan → nat) (s t : nat) (c : chan)
    (fs ft : tenv → tenv) : (nat → tenv) * (nat → chan → nat) :=
  (eupd (eupd A s (fs (A s))) t (ft (A t)),
   fupd (fupd Φ s (tick N c (Φ s))) t (tick N c (Φ t))).

Definition link_fuel (A : nat → tenv) (Φ : nat → chan → nat) (i : nat) (r o : chan)
    : nat → chan → nat :=
  let m := pred (min (Φ i r) (Φ i o)) in
  λ u x, if decide (u ≠ i ∧ x = o ∧ (r ∈ dom (A u) ∨ o ∈ dom (A u))) then
           min (if decide (r ∈ dom (A u)) then
                  (if decide (o ∈ dom (A u)) then min (Φ u r) (Φ u o) else Φ u r)
                else Φ u o) m
         else Φ u x.

Definition upd1 (ω : oracle) (N : nat) (C : gset chan) (M : gmap nat expr) (A : nat → tenv)
    (Φ : nat → chan → nat) (i : nat) (q' : config) : (nat → tenv) * (nat → chan → nat) :=
  match M !! i with
  | Some e =>
    match act e with
    | Some ANew =>
        let c := default "" (head (elements (q'.1 ∖ C))) in
        let pl := or_pick ω (A i) e in
        (eupd A i (<[c := Both (pl_s pl, pl_pt pl) (pl_s' pl, pt_dual (pl_pt pl))]> (A i)),
         fupd Φ i (λ x, if decide (x = c) then N else Φ i x))
    | Some (ASpawn _) =>
        let j := default 0 (head (elements (dom q'.2 ∖ dom M))) in
        let give := pl_give (or_pick ω (A i) e) in
        (eupd (eupd A i (tenv_minus (A i) give)) j give, fupd Φ j (λ x, pred (Φ i x)))
    | Some (ALink c d) =>
        let rm := bool_decide (c ∈ C ∧ c ∉ q'.1) in
        let r := if rm then c else d in
        let o := if rm then d else c in
        (λ u, if decide (u = i) then delete r (delete o (A i)) else tenv_rename r o (A u),
         link_fuel A Φ i r o)
    | _ => (A, Φ)
    end
  | None => (A, Φ)
  end.

Definition upd2 (ω : oracle) (N : nat) (M : gmap nat expr) (A : nat → tenv)
    (Φ : nat → chan → nat) (i j : nat) : (nat → tenv) * (nat → chan → nat) :=
  match M !! i, M !! j with
  | Some ei, Some ej =>
    match act ei, act ej with
    | Some (ASend c _), Some (ARecv _) => sync_msg ω N A Φ i j c ei
    | Some (ARecv _), Some (ASend c _) => sync_msg ω N A Φ j i c ej
    | Some (AClos c), Some (AClos _) => sync2 N A Φ i j c (delete c) (delete c)
    | Some (ASel c b), Some (ABra _) =>
        sync2 N A Φ i j c (step_entry (sel_next b) c) (step_entry (bra_next b) c)
    | Some (ABra _), Some (ASel c b) =>
        sync2 N A Φ j i c (step_entry (sel_next b) c) (step_entry (bra_next b) c)
    | _, _ => (A, Φ)
    end
  | _, _ => (A, Φ)
  end.

Definition aupd (ω : oracle) (N : nat) (a : aconf) (L : gset nat) (q' : config) : aconf :=
  let AΦ :=
    match pick1 L with
    | Some i => upd1 ω N (ac_q a).1 (ac_q a).2 (ac_env a) (ac_fuel a) i q'
    | None =>
      match pick2 L with
      | Some (i, j) => upd2 ω N (ac_q a).2 (ac_env a) (ac_fuel a) i j
      | None => (ac_env a, ac_fuel a)
      end
    end in
  AConf q' AΦ.1 AΦ.2.

(** Annotated configurations reached by steps, and the start. *)
Definition astep (ω : oracle) (N : nat) (a a' : aconf) : Prop :=
  ∃ L q', istep (ac_q a) L q' ∧ a' = aupd ω N a L q'.

Definition areach (ω : oracle) (N : nat) : aconf → aconf → Prop := rtc (astep ω N).

Definition ainit (ω : oracle) (N : nat) (q : config) : aconf :=
  AConf q (or_init ω q) (λ _ _, N).

(** ** The invariant of one annotated configuration *)

(** The expression part: a thread with environment Θ and counters φ. *)
Definition LFErel (n : nat) (W : world) (Θ : tenv) (φ : chan → nat) (e : expr) : Prop :=
  (∃ U, LErel n W Θ U ∅ e) ∧
  dom Θ = fchans e ∧
  (irred e → Θ = ∅) ∧
  (∀ c, c ∈ dom Θ → φ c = 0 →
     ∃ a S, act e = Some a ∧ ¬ is_admin a ∧ asubjs a = Some S ∧ c ∈ S).

(** Every thread is related, the free channels are restricted or
    external, every internal entry has a partner entry at the dual
    point and type, and no channel has three entries. *)
Definition LFconf (n : nat) (W : world) (Σ : senv) (a : aconf) : Prop :=
  (∀ t e, (ac_q a).2 !! t = Some e → LFErel n W (ac_env a t) (ac_fuel a t) e) ∧
  (∀ t e, (ac_q a).2 !! t = Some e → fchans e ⊆ (ac_q a).1 ∪ dom Σ) ∧
  (∀ t e k ek, (ac_q a).2 !! t = Some e → tenv_entry (ac_env a t) k = Some ek → k.1 ∉ dom Σ →
     ∃ s es k' ek', (ac_q a).2 !! s = Some es ∧ tenv_entry (ac_env a s) k' = Some ek' ∧
       k'.1 = k.1 ∧ (s, k') ≠ (t, k) ∧ ek'.2 = pt_dual ek.2 ∧ sdual ek.1 ek'.1) ∧
  (∀ t1 t2 t3 e1 e2 e3 k1 k2 k3 x1 x2 x3,
     (ac_q a).2 !! t1 = Some e1 → (ac_q a).2 !! t2 = Some e2 → (ac_q a).2 !! t3 = Some e3 →
     tenv_entry (ac_env a t1) k1 = Some x1 → tenv_entry (ac_env a t2) k2 = Some x2 →
     tenv_entry (ac_env a t3) k3 = Some x3 → k1.1 = k2.1 → k2.1 = k3.1 →
     (t1, k1) = (t2, k2) ∨ (t1, k1) = (t3, k3) ∨ (t2, k2) = (t3, k3)).

(** ** The relation *)
Definition LFPrel (N : nat) (ω : oracle) (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    : Prop :=
  LPrel n W Σ T p ∧
  ∀ q a, erase q = p → areach ω N (ainit ω N q) a → LFconf n W Σ a.

(** ** Monotonicity in the index *)

Lemma LFErel_down n m W Θ φ e : m ≤ n → LFErel n W Θ φ e → LFErel m W Θ φ e.
Proof.
  intros Hmn ([U HU] & H1 & H2 & H3). split_and!; [|done..].
  exists U. by eapply LErel_down.
Qed.

Lemma LFconf_down n m W Σ a : m ≤ n → LFconf n W Σ a → LFconf m W Σ a.
Proof.
  intros Hmn (H1 & H2 & H3 & H4). split_and!; [|done..].
  intros t e He. eapply LFErel_down; [done|]. by apply H1.
Qed.

Theorem LFPrel_down N ω n m W Σ T p : m ≤ n → LFPrel N ω n W Σ T p → LFPrel N ω m W Σ T p.
Proof.
  intros Hmn [HP HL]. split; [by eapply LPrel_down|].
  intros q a Hq Ha. eapply LFconf_down; [done|]. by apply (HL q a).
Qed.

(** ** Monotonicity in the fuel

    More fuel asks less. The environments of an update do not read the
    counters, and every counter of an update is monotone in the
    counters and in N. *)

Definition fle (Φ Φ' : nat → chan → nat) : Prop := ∀ u x, Φ u x ≤ Φ' u x.

Lemma upd1_env ω N N' C M A Φ Φ' i q' : (upd1 ω N C M A Φ i q').1 = (upd1 ω N' C M A Φ' i q').1.
Proof. unfold upd1. destruct (M !! i) as [e|]; [|done]. by destruct (act e) as [[]|]. Qed.

Lemma upd2_env ω N N' M A Φ Φ' i j : (upd2 ω N M A Φ i j).1 = (upd2 ω N' M A Φ' i j).1.
Proof.
  unfold upd2. destruct (M !! i) as [ei|], (M !! j) as [ej|]; try done.
  by destruct (act ei) as [[]|], (act ej) as [[]|].
Qed.

Lemma tick_le N N' c φ φ' : N ≤ N' → (∀ x, φ x ≤ φ' x) → ∀ x, tick N c φ x ≤ tick N' c φ' x.
Proof. intros HN Hφ x. unfold tick. case_decide; [done|]. specialize (Hφ x). lia. Qed.

Lemma fupd_le Φ Φ' t f f' : fle Φ Φ' → (∀ x, f x ≤ f' x) → fle (fupd Φ t f) (fupd Φ' t f').
Proof. intros H Hf u x. unfold fupd. case_decide; auto. Qed.

Lemma link_fuel_le A Φ Φ' i r o : fle Φ Φ' → fle (link_fuel A Φ i r o) (link_fuel A Φ' i r o).
Proof.
  intros H u x. unfold link_fuel.
  pose proof (H u r). pose proof (H u o). pose proof (H i r). pose proof (H i o).
  pose proof (H u x). repeat case_decide; lia.
Qed.

Lemma upd1_fuel ω N N' C M A Φ Φ' i q' :
  N ≤ N' → fle Φ Φ' → fle (upd1 ω N C M A Φ i q').2 (upd1 ω N' C M A Φ' i q').2.
Proof.
  intros HN HΦ. unfold upd1. destruct (M !! i) as [e|]; [|done].
  destruct (act e) as [[]|]; simpl; try done.
  - apply fupd_le; [done|]. intros x. case_decide; [done|apply HΦ].
  - apply fupd_le; [done|]. intros x. specialize (HΦ i x). lia.
  - by apply link_fuel_le.
Qed.

Lemma upd2_fuel ω N N' M A Φ Φ' i j :
  N ≤ N' → fle Φ Φ' → fle (upd2 ω N M A Φ i j).2 (upd2 ω N' M A Φ' i j).2.
Proof.
  intros HN HΦ. unfold upd2. destruct (M !! i) as [ei|], (M !! j) as [ej|]; try done.
  assert (∀ s t c fs ft, fle (sync2 N A Φ s t c fs ft).2 (sync2 N' A Φ' s t c fs ft).2) as H2.
  { intros. simpl. apply fupd_le; [apply fupd_le; [done|]|]; apply tick_le; auto. }
  assert (∀ s t c es, fle (sync_msg ω N A Φ s t c es).2 (sync_msg ω N' A Φ' s t c es).2) as Hm.
  { intros s t c es. simpl. apply fupd_le; [apply fupd_le; [done|apply tick_le; auto]|].
    intros x. pose proof (HΦ s x). pose proof (HΦ t x). repeat case_decide; lia. }
  destruct (act ei) as [[]|], (act ej) as [[]|]; first [exact HΦ|apply H2|apply Hm].
Qed.

Lemma aupd_fuel_mono ω N N' a a' L q' :
  N ≤ N' → ac_q a = ac_q a' → ac_env a = ac_env a' → fle (ac_fuel a) (ac_fuel a') →
  ac_q (aupd ω N a L q') = ac_q (aupd ω N' a' L q') ∧
  ac_env (aupd ω N a L q') = ac_env (aupd ω N' a' L q') ∧
  fle (ac_fuel (aupd ω N a L q')) (ac_fuel (aupd ω N' a' L q')).
Proof.
  intros HN Hq HA HΦ. unfold aupd; simpl. rewrite Hq, HA.
  destruct (pick1 L) as [i|]; [split_and!; [done|apply upd1_env|by apply upd1_fuel]|].
  destruct (pick2 L) as [[i j]|]; [split_and!; [done|apply upd2_env|by apply upd2_fuel]|].
  done.
Qed.

Lemma areach_fuel_mono ω N N' a0 a0' a' :
  N ≤ N' → ac_q a0 = ac_q a0' → ac_env a0 = ac_env a0' → fle (ac_fuel a0) (ac_fuel a0') →
  areach ω N' a0' a' →
  ∃ a, areach ω N a0 a ∧ ac_q a = ac_q a' ∧ ac_env a = ac_env a' ∧ fle (ac_fuel a) (ac_fuel a').
Proof.
  intros HN Hq HA HΦ Hr. revert a0 Hq HA HΦ.
  induction Hr as [a0'|a0' a1' a' (L & q' & Hst & ->) _ IH]; intros a0 Hq HA HΦ.
  - exists a0. split_and!; [done|done|done|done].
  - destruct (aupd_fuel_mono ω N N' a0 a0' L q' HN Hq HA HΦ) as (Hq1 & HA1 & HΦ1).
    destruct (IH (aupd ω N a0 L q') Hq1 HA1 HΦ1) as (a & Ha & ?).
    exists a. split; [|done]. eapply rtc_l; [|exact Ha]. exists L, q'. split; [|done].
    by rewrite Hq.
Qed.

Lemma LFconf_fuel_mono n W Σ a a' :
  ac_q a = ac_q a' → ac_env a = ac_env a' → fle (ac_fuel a) (ac_fuel a') →
  LFconf n W Σ a → LFconf n W Σ a'.
Proof.
  destruct a as [q A Φ], a' as [q' A' Φ']; simpl. intros <- <- HΦ (H1 & H2 & H3 & H4).
  split_and!; [|done..]. intros t e He. destruct (H1 t e He) as (HU & Hd & Hi & Hf).
  split_and!; [done..|]. intros c Hc H0. apply Hf; [done|]. specialize (HΦ t c). simpl in *. lia.
Qed.

Theorem LFPrel_fuel N N' ω n W Σ T p : N ≤ N' → LFPrel N ω n W Σ T p → LFPrel N' ω n W Σ T p.
Proof.
  intros HN [HP HL]. split; [done|]. intros q a' Hq Ha'.
  destruct (areach_fuel_mono ω N N' (ainit ω N q) (ainit ω N' q) a' HN eq_refl eq_refl)
    as (a & Ha & Hqa & HAa & HΦa); [by intros ??|done|].
  eapply LFconf_fuel_mono; [done|done|done|]. by apply (HL q a).
Qed.
