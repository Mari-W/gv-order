(** * The lock-free judgment on thread soups (lock-freedom plan §16.3, §16.5, §17.3)

    A configuration is a soup of threads. [LFconf n W Σ T π q A U] says
    that every thread t of q is in the live term relation at index n
    under its environment [A t] and its type [U t], that the
    environments fit the terms (E-Fit) and hold pairwise disjoint ends,
    that every held end sits at the point π gives it, and that every end
    of an internal channel has a partner end, held by some thread, at
    the dual point and with a dual session type. The point map π lies
    outside the index: the environments and the session types are
    chosen again at every index, the points are not, because the
    program names the point of every [new] (sharp edges 173).

    [pupd] moves π along one step. It reads the step off the redexes of
    the participants, so it is a function of the run. [lfconf_step] is
    the preservation of the soup along a step at a fixed π: the soup at
    index n + 2 steps to the soup at index n at [pupd π]. Every
    environment of the successor is the one the clause of the stepping
    thread gives. A thread that does not take part keeps its
    environment, up to the renaming of a link ([LErel_fuse]).

    [LFsoup] adds the fuel conjunct of §17.3 (FuelE at the thread's ends,
    with counters φ outside the index), and [LFP] is the judgment of
    §17.8. The preservation of the fuel conjunct is open (see the
    progress log, stage L4a). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Criterion lockfree.LocalProgress.
From LRGV Require Import lockfree.LFFuel.
From LRGV Require Export liveness.LiveAdequacy liveness.LiveFuse liveness.LiveTermRules
  liveness.LiveConsts liveness.LiveInternalize liveness.LivePTerm.

Set Default Proof Using "Type".

(** ** The entry after an action, as in O-Send, O-Recv, O-Select and O-Branch *)

Definition snd_next (e : sty * point) : sty * point :=
  match unfoldS e.1 with SSeq (SSnd _ _) s => (s, pt_shift 1 e.2) | _ => e end.
Definition rcv_next (e : sty * point) : sty * point :=
  match unfoldS e.1 with SSeq (SRcv _ _) s => (s, pt_shift 1 e.2) | _ => e end.
Definition sel_next (b : bool) (e : sty * point) : sty * point :=
  match unfoldS e.1 with SPlus s1 s2 => (sbranch b s1 s2, sel_pt e.2 b) | _ => e end.
Definition bra_next (b : bool) (e : sty * point) : sty * point :=
  match unfoldS e.1 with SWith s1 s2 => (sbranch b s1 s2, bra_pt e.2 b) | _ => e end.

(** ** The entry of an end

    The end o = (c, b) of an environment is the entry of c whose point
    has polarity b. Under [tenv_bipol] the two entries of a channel are
    two ends. *)

Definition tenv_end (Θ : tenv) (o : cend) : option (sty * point) :=
  match Θ !! o.1 with
  | Some (One e) => if bool_decide (pt_pol e.2 = o.2) then Some e else None
  | Some (Both e1 e2) =>
      if bool_decide (pt_pol e1.2 = o.2) then Some e1
      else if bool_decide (pt_pol e2.2 = o.2) then Some e2 else None
  | None => None
  end.

Lemma tenv_end_pol Θ o x : tenv_end Θ o = Some x → pt_pol x.2 = o.2.
Proof.
  unfold tenv_end. destruct (Θ !! o.1) as [[e|e1 e2]|]; [| |done];
    repeat case_bool_decide; intros; simplify_eq; done.
Qed.

Lemma tenv_end_dom Θ o x : tenv_end Θ o = Some x → o.1 ∈ dom Θ.
Proof. unfold tenv_end. intros H. apply elem_of_dom. by destruct (Θ !! o.1). Qed.

Lemma tenv_end_none Θ o : o.1 ∉ dom Θ → tenv_end Θ o = None.
Proof. intros H. apply not_elem_of_dom in H. unfold tenv_end. by rewrite H. Qed.

Lemma tenv_ends_end Θ o : o ∈ tenv_ends Θ ↔ is_Some (tenv_end Θ o).
Proof.
  rewrite elem_of_tenv_ends. destruct o as [c b]. unfold tenv_end. simpl. split.
  - intros (c' & eo & Hc & Ho). destruct eo as [e|e1 e2]; simpl in Ho.
    + apply elem_of_singleton in Ho. injection Ho as <- ->. rewrite Hc.
      rewrite bool_decide_true by done. by exists e.
    + apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho;
        injection Ho as <- ->; rewrite Hc.
      * rewrite bool_decide_true by done. by exists e1.
      * destruct (bool_decide (pt_pol e1.2 = pt_pol e2.2)); [by exists e1|].
        rewrite bool_decide_true by done. by exists e2.
  - destruct (Θ !! c) as [[e|e1 e2]|] eqn:Hc; [| |by intros []].
    + case_bool_decide as Hb; [|by intros []]. intros _. subst b.
      exists c, (One e). split; [done|]. simpl. set_solver.
    + intros H. exists c, (Both e1 e2). split; [done|]. simpl.
      destruct (decide (pt_pol e1.2 = b)) as [<-|H1]; [set_solver|].
      destruct (decide (pt_pol e2.2 = b)) as [<-|H2]; [set_solver|].
      rewrite !bool_decide_false in H by done. by destruct H.
Qed.


Lemma tenv_end_entry Θ k ek :
  tenv_bipol Θ → tenv_entry Θ k = Some ek → tenv_end Θ (k.1, pt_pol ek.2) = Some ek.
Proof.
  intros Hb. destruct k as [c []]; unfold tenv_entry, tenv_end; simpl;
    destruct (Θ !! c) as [[e|e1 e2]|] eqn:Hc; intros H; simplify_eq.
  - rewrite (bool_decide_false (pt_pol e1.2 = pt_pol ek.2)) by (by apply (Hb c)).
    by rewrite bool_decide_true.
  - by rewrite bool_decide_true.
  - by rewrite bool_decide_true.
Qed.

Lemma tenv_end_entry_inv Θ o x :
  tenv_end Θ o = Some x → ∃ k, tenv_entry Θ k = Some x ∧ k.1 = o.1.
Proof.
  unfold tenv_end, tenv_entry. destruct (Θ !! o.1) as [[e|e1 e2]|] eqn:Hc; [| |done];
    repeat case_bool_decide; intros Heq; simplify_eq.
  - exists (o.1, false). simpl. by rewrite Hc.
  - exists (o.1, false). simpl. by rewrite Hc.
  - exists (o.1, true). simpl. by rewrite Hc.
Qed.

(** Two entries of one end are one entry. *)
Lemma tenv_entry_end_inj Θ k k' ek ek' :
  tenv_bipol Θ → tenv_entry Θ k = Some ek → tenv_entry Θ k' = Some ek' →
  k.1 = k'.1 → pt_pol ek.2 = pt_pol ek'.2 → k = k' ∧ ek = ek'.
Proof.
  intros Hb. destruct k as [c b], k' as [c' b']; simpl. intros H H' <- Hp.
  unfold tenv_entry in H, H'. simpl in *.
  destruct (Θ !! c) as [[e|e1 e2]|] eqn:Hc; [| |done].
  - destruct b, b'; simplify_eq; done.
  - pose proof (Hb c e1 e2 Hc). destruct b, b'; simplify_eq; done.
Qed.

Lemma tenv_end_empty o : tenv_end ∅ o = None.
Proof. unfold tenv_end. by rewrite lookup_empty. Qed.

Lemma tenv_end_insert_ne Θ c eo o : o.1 ≠ c → tenv_end (<[c := eo]> Θ) o = tenv_end Θ o.
Proof. intros H. unfold tenv_end. by rewrite lookup_insert_ne by done. Qed.

Lemma tenv_end_delete_ne Θ c o : o.1 ≠ c → tenv_end (delete c Θ) o = tenv_end Θ o.
Proof. intros H. unfold tenv_end. by rewrite lookup_delete_ne by done. Qed.

Lemma tenv_end_delete_eq Θ c o : o.1 = c → tenv_end (delete c Θ) o = None.
Proof. intros <-. unfold tenv_end. by rewrite lookup_delete_eq. Qed.

(** Θ = Θ1, c : e. *)
Lemma tenv_end_ext Θ1 c e Θ o :
  tenv_ext Θ1 c e Θ → tenv_bipol Θ →
  tenv_end Θ o = if decide (o = (c, pt_pol e.2)) then Some e else tenv_end Θ1 o.
Proof.
  intros Hext Hb. destruct o as [c' b]. destruct (decide (c' = c)) as [->|Hne].
  2:{ rewrite decide_False by congruence.
      destruct Hext as [[_ ->]|(e' & _ & [-> | ->])]; by apply tenv_end_insert_ne. }
  destruct Hext as [[Hn ->]|(e' & He' & [-> | ->])].
  - unfold tenv_end. simpl. rewrite lookup_insert_eq, Hn.
    destruct (decide ((c, b) = (c, pt_pol e.2))) as [Heq|Hneq].
    + injection Heq as Hbq. subst b. by rewrite bool_decide_true.
    + rewrite bool_decide_false; [done|]. intros Hq. apply Hneq. by rewrite Hq.
  - assert (pt_pol e.2 ≠ pt_pol e'.2) as Hp.
    { apply (Hb c). by rewrite lookup_insert_eq. }
    unfold tenv_end. simpl. rewrite lookup_insert_eq, He'.
    destruct (decide ((c, b) = (c, pt_pol e.2))) as [Heq|Hneq].
    + injection Heq as Hbq. subst b. by rewrite bool_decide_true.
    + rewrite bool_decide_false by (intros Hq; apply Hneq; by rewrite Hq). done.
  - assert (pt_pol e'.2 ≠ pt_pol e.2) as Hp.
    { apply (Hb c). by rewrite lookup_insert_eq. }
    unfold tenv_end. simpl. rewrite lookup_insert_eq, He'.
    destruct (decide ((c, b) = (c, pt_pol e.2))) as [Heq|Hneq].
    + injection Heq as Hbq. subst b. rewrite bool_decide_false by done. by rewrite bool_decide_true.
    + rewrite (bool_decide_false (pt_pol e.2 = b)) by (intros Hq; apply Hneq; by rewrite Hq).
      repeat case_bool_decide; done.
Qed.

Lemma tenv_end_ext_eq Θ1 c e Θ :
  tenv_ext Θ1 c e Θ → tenv_bipol Θ → tenv_end Θ (c, pt_pol e.2) = Some e.
Proof. intros H Hb. rewrite (tenv_end_ext _ _ _ _ _ H Hb). by rewrite decide_True. Qed.

Lemma tenv_end_ext_ne Θ1 c e Θ o :
  tenv_ext Θ1 c e Θ → tenv_bipol Θ → o ≠ (c, pt_pol e.2) → tenv_end Θ o = tenv_end Θ1 o.
Proof. intros H Hb Hne. rewrite (tenv_end_ext _ _ _ _ _ H Hb). by rewrite decide_False. Qed.

Lemma tenv_end_ext_none Θ1 c e Θ :
  tenv_ext Θ1 c e Θ → tenv_bipol Θ → tenv_end Θ1 (c, pt_pol e.2) = None.
Proof.
  intros Hext Hb. destruct Hext as [[Hn _]|(e' & He' & Hor)].
  - unfold tenv_end. simpl. by rewrite Hn.
  - assert (pt_pol e.2 ≠ pt_pol e'.2) as Hp.
    { destruct Hor as [->| ->].
      - apply (Hb c). by rewrite lookup_insert_eq.
      - apply not_eq_sym, (Hb c). by rewrite lookup_insert_eq. }
    unfold tenv_end. simpl. rewrite He'. by rewrite bool_decide_false by congruence.
Qed.

Lemma tenv_bipol_ext_l Θ1 c e Θ : tenv_ext Θ1 c e Θ → tenv_bipol Θ → tenv_bipol Θ1.
Proof.
  intros Hext Hb c' e1 e2 Hc'. destruct (decide (c' = c)) as [->|Hne].
  - destruct Hext as [[Hn _]|(e' & He' & _)]; congruence.
  - apply (Hb c'). destruct Hext as [[_ ->]|(e' & _ & [-> | ->])];
      by rewrite lookup_insert_ne.
Qed.

(** Θ = Θ1, Θ2. *)
Lemma tenv_end_comp Θ Θ1 Θ2 o :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ →
  tenv_end Θ o = match tenv_end Θ1 o with Some x => Some x | None => tenv_end Θ2 o end ∧
  (tenv_end Θ1 o = None ∨ tenv_end Θ2 o = None).
Proof.
  intros [Hj Hd] Hb. destruct o as [c b]. pose proof (Hj c) as Hjc.
  unfold tenv_end. simpl.
  inversion Hjc as [H1 H2 H3|eo H1 H2 H3|eo H1 H2 H3|f1 f2 H1 H2 H3|f1 f2 H1 H2 H3].
  - auto.
  - destruct eo; repeat case_bool_decide; auto.
  - destruct eo; repeat case_bool_decide; auto.
  - destruct (Hd c f1 f2 (eq_sym H1) (eq_sym H2)) as [Hp _].
    assert (pt_pol f1.2 ≠ pt_pol f2.2) as Hne.
    { rewrite Hp. simpl. by destruct (pt_pol f2.2). }
    repeat case_bool_decide; subst; try done; auto.
  - destruct (Hd c f1 f2 (eq_sym H1) (eq_sym H2)) as [Hp _].
    assert (pt_pol f1.2 ≠ pt_pol f2.2) as Hne.
    { rewrite Hp. simpl. by destruct (pt_pol f2.2). }
    repeat case_bool_decide; subst; try done; auto.
Qed.

Lemma tenv_end_comp_l Θ Θ1 Θ2 o x :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ → tenv_end Θ1 o = Some x → tenv_end Θ o = Some x.
Proof. intros Hc Hb H. destruct (tenv_end_comp Θ Θ1 Θ2 o Hc Hb) as [-> _]. by rewrite H. Qed.

Lemma tenv_end_comp_r Θ Θ1 Θ2 o x :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ → tenv_end Θ2 o = Some x → tenv_end Θ o = Some x.
Proof.
  intros Hc Hb H. destruct (tenv_end_comp Θ Θ1 Θ2 o Hc Hb) as [-> [H1|H1]].
  - by rewrite H1.
  - congruence.
Qed.

Lemma tenv_end_comp_inv Θ Θ1 Θ2 o x :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ → tenv_end Θ o = Some x →
  tenv_end Θ1 o = Some x ∨ tenv_end Θ2 o = Some x.
Proof.
  intros Hc Hb H. destruct (tenv_end_comp Θ Θ1 Θ2 o Hc Hb) as [He _]. rewrite He in H.
  destruct (tenv_end Θ1 o); [left|right]; congruence.
Qed.

(** new@x at a fresh c. *)
Lemma tenv_end_new Θ c s s' x o :
  tenv_end (<[c := Both (s, x) (s', pt_dual x)]> Θ) o =
  if decide (o = (c, pt_pol x)) then Some (s, x)
  else if decide (o = (c, negb (pt_pol x))) then Some (s', pt_dual x)
  else tenv_end Θ o.
Proof.
  destruct o as [c' b]. destruct (decide (c' = c)) as [->|Hne].
  - unfold tenv_end. simpl. rewrite lookup_insert_eq. simpl.
    destruct b, (pt_pol x) eqn:Hx; simpl; repeat case_bool_decide; repeat case_decide;
      simplify_eq; try done; try congruence.
  - rewrite !decide_False by congruence. by apply tenv_end_insert_ne.
Qed.

(** ** The partner end and the ends of a term *)

Lemma fchans_of_fends e o : o ∈ fends e → o.1 ∈ fchans e.
Proof. intros H. rewrite fchans_fends. apply elem_of_map. by exists o. Qed.

Lemma fends_of_fchans e c : c ∈ fchans e → ∃ b, (c, b) ∈ fends e.
Proof.
  rewrite fchans_fends. intros ([c' b] & -> & H)%elem_of_map. by exists b.
Qed.

Lemma cdual_fst o : (cdual o).1 = o.1.
Proof. done. Qed.

Lemma cdual_snd o : (cdual o).2 = negb o.2.
Proof. done. Qed.

Lemma cdual_inj o o' : cdual o = cdual o' → o = o'.
Proof. intros H. rewrite <-(cdual_cdual o), <-(cdual_cdual o'). by rewrite H. Qed.

(** ** The soup *)

Record LFconf (n : nat) (W : world) (Σ : senv) (T : ty) (π : gmap cend point)
    (q : config) (A : nat → tenv) (U : nat → ty) : Prop := LFConf {
  lf_prim : prim T;
  lf_rel t e : q.2 !! t = Some e → LErel n W (A t) (U t) ∅ e;
  lf_fit t e : q.2 !! t = Some e → tenv_fit (A t) e;
  lf_ty t e : q.2 !! t = Some e → U t = T ∨ U t = TUnit;
  lf_pt t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → π !! o = Some x.2;
  lf_disj t s e es : t ≠ s → q.2 !! t = Some e → q.2 !! s = Some es → fends e ## fends es;
  lf_pair t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → o.1 ∉ dom Σ →
    ∃ s es y, q.2 !! s = Some es ∧ tenv_end (A s) (cdual o) = Some y ∧
      y.2 = pt_dual x.2 ∧ sdual x.1 y.1;
  lf_closed t e : q.2 !! t = Some e → fchans e ⊆ q.1 ∪ dom Σ
}.

(** The fuel conjunct (§17.3): FuelE at the thread's ends, read in the
    counters φ, which lie outside the index as π does. *)
Definition lf_fuel (n : nat) (W : world) (π : gmap cend point) (φ : gmap cend fuel)
    (q : config) : Prop :=
  ∀ t e, q.2 !! t = Some e → FuelE n W (mres (fends e) π) (mres (fends e) φ) e.

Definition LFsoup (n : nat) (W : world) (Σ : senv) (T : ty) (π : gmap cend point)
    (φ : gmap cend fuel) (p : proc) : Prop :=
  ∃ q A U, erase q = p ∧ LFconf n W Σ T π q A U ∧ lf_fuel n W π φ q.

(** The lock-free judgment (§17.8). The budgets are read in W. *)
Definition LFP (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  (∀ n, LPrel n W Σ T p) ∧ ∃ π φ, ∀ n, LFsoup n W Σ T π φ p.

(** ** Monotonicity in the index *)

Lemma LFconf_down n m W Σ T π q A U : m ≤ n → LFconf n W Σ T π q A U → LFconf m W Σ T π q A U.
Proof.
  intros Hmn [? Hr ? ? ? ? ? ?]. split; try done.
  intros t e He. eapply LErel_down; [done|]. by apply Hr.
Qed.

Lemma lf_fuel_down n m W π φ q : m ≤ n → lf_fuel n W π φ q → lf_fuel m W π φ q.
Proof. intros Hmn H t e He. apply (FuelE_down m n); [done|]. exact (H t e He). Qed.

Theorem LFsoup_down n m W Σ T π φ p : m ≤ n → LFsoup n W Σ T π φ p → LFsoup m W Σ T π φ p.
Proof.
  intros Hmn (q & A & U & Hq & Hc & Hf). exists q, A, U. split_and!; [done| |].
  - by eapply LFconf_down.
  - by eapply lf_fuel_down.
Qed.

(** ** The points along a step

    [pev_of q L q'] reads the step off the redexes of the participants:
    the channel and point of a new, the channel of a message, a close or
    a link (the restricted one, which the link removes), and the end of
    the selector and the branch of a choice. [pupd] moves the points. A
    message shifts both ends of its channel. A choice moves the
    selecting end to (c, false) at [sel_pt] and the branching end to
    (c, true) at [bra_pt]. Close and link remove both ends of the
    channel: a link renames the peer of the removed end into the end of
    the other channel that the linker held, and that end sat at the
    peer's point already. β and spawn change nothing. *)

Inductive pev :=
  | PNone
  | PNew (c : chan) (x : point)
  | PMsg (c : chan)
  | PClose (c : chan)
  | PChoice (o : cend) (b : bool).

Definition pev_upd (π : gmap cend point) (ev : pev) : gmap cend point :=
  match ev with
  | PNone => π
  | PNew c x => <[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π)
  | PMsg c => alter (pt_shift 1) (c, true) (alter (pt_shift 1) (c, false) π)
  | PClose c => delete (c, true) (delete (c, false) π)
  | PChoice o b =>
      match π !! o with
      | Some k => <[(o.1, false) := sel_pt k b]> (<[(o.1, true) := bra_pt k b]> π)
      | None => π
      end
  end.

Definition pev1 (q : config) (q' : config) (e : expr) : pev :=
  match act e with
  | Some (ANew x) => PNew (default "" (head (elements (q'.1 ∖ q.1)))) x
  | Some (ALink _ _) => PClose (default "" (head (elements (q.1 ∖ q'.1))))
  | _ => PNone
  end.

Definition pev2 (ei ej : expr) : pev :=
  match act ei, act ej with
  | Some (ASend o _), _ | Some (ARecv o), _ => PMsg o.1
  | Some (AClos o), _ => PClose o.1
  | Some (ASel o b), _ => PChoice o b
  | Some (ABra _), Some (ASel o b) => PChoice o b
  | _, _ => PNone
  end.

Definition pev_of (q : config) (L : gset nat) (q' : config) : pev :=
  match elements L with
  | [i] => match q.2 !! i with Some e => pev1 q q' e | None => PNone end
  | [i; j] =>
      match q.2 !! i, q.2 !! j with Some ei, Some ej => pev2 ei ej | _, _ => PNone end
  | _ => PNone
  end.

Definition pupd (π : gmap cend point) (q : config) (L : gset nat) (q' : config) : gmap cend point :=
  pev_upd π (pev_of q L q').

(** ** The ends of an environment, through its operations *)

Lemma tenv_ends_ext Θ1 c e Θ :
  tenv_ext Θ1 c e Θ → tenv_bipol Θ →
  tenv_ends Θ = tenv_ends Θ1 ∪ {[(c, pt_pol e.2)]} ∧ (c, pt_pol e.2) ∉ tenv_ends Θ1.
Proof.
  intros Hext Hb. split.
  - apply set_eq. intros o. rewrite elem_of_union, elem_of_singleton, !tenv_ends_end.
    rewrite (tenv_end_ext _ _ _ _ o Hext Hb). case_decide; [naive_solver|].
    split; [by left|]. intros [?|?]; [done|congruence].
  - rewrite tenv_ends_end, (tenv_end_ext_none _ _ _ _ Hext Hb). by intros [].
Qed.

Lemma tenv_ends_comp Θ Θ1 Θ2 :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ →
  tenv_ends Θ = tenv_ends Θ1 ∪ tenv_ends Θ2 ∧ tenv_ends Θ1 ## tenv_ends Θ2.
Proof.
  intros Hc Hb. split.
  - apply set_eq. intros o. rewrite elem_of_union, !tenv_ends_end.
    destruct (tenv_end_comp Θ Θ1 Θ2 o Hc Hb) as [-> _].
    destruct (tenv_end Θ1 o); [naive_solver|]. split; [by right|]. intros [[]|]; done.
  - intros o. rewrite !tenv_ends_end. destruct (tenv_end_comp Θ Θ1 Θ2 o Hc Hb) as [_ [H|H]];
      rewrite H; by intros [].
Qed.

Lemma tenv_ends_new Θ c s s' x :
  tenv_ends (<[c := Both (s, x) (s', pt_dual x)]> Θ) =
  tenv_ends Θ ∪ {[(c, pt_pol x); (c, negb (pt_pol x))]}.
Proof.
  apply set_eq. intros o. rewrite elem_of_union, !tenv_ends_end, tenv_end_new.
  destruct (decide (o = (c, pt_pol x))) as [->|H1].
  { split; [intros _; right; set_solver|by eexists]. }
  destruct (decide (o = (c, negb (pt_pol x)))) as [->|H2].
  { split; [intros _; right; set_solver|by eexists]. }
  split; [by left|]. intros [H|H]; [done|set_solver].
Qed.

(** The two ends of a channel. *)
Definition cends (c : chan) : gset cend := {[(c, true); (c, false)]}.

Lemma elem_of_cends c o : o ∈ cends c ↔ o.1 = c.
Proof. destruct o as [c' []]; unfold cends; set_solver. Qed.

Lemma cends_cdual c o : o ∈ cends c ↔ cdual o ∈ cends c.
Proof. rewrite !elem_of_cends. done. Qed.

(** A channel has two ends: a thread holding one end and a thread
    holding the other differ in that end. *)
Lemma cend_two o1 o2 : o1.1 = o2.1 → o1 ≠ o2 → o2 = cdual o1.
Proof. destruct o1 as [c []], o2 as [c' []]; unfold cdual; simpl; intros <- H; congruence. Qed.

(** ** Composing two environments

    [tenv_merge Θ1 Θ2] is the union that joins two single ends of a
    channel into both ends. *)

Definition ends_merge2 (o1 o2 : ends) : ends :=
  match o1, o2 with One e1, One e2 => Both e1 e2 | _, _ => o1 end.

Definition tenv_merge (Θ1 Θ2 : tenv) : tenv :=
  union_with (λ o1 o2, Some (ends_merge2 o1 o2)) Θ1 Θ2.

Lemma tenv_comp_merge Θ1 Θ2 :
  (∀ c o1 o2, Θ1 !! c = Some o1 → Θ2 !! c = Some o2 →
     ∃ e1 e2, o1 = One e1 ∧ o2 = One e2 ∧ e1.2 = pt_dual e2.2 ∧ sdual e1.1 e2.1) →
  tenv_comp (@eq point) (tenv_merge Θ1 Θ2) Θ1 Θ2.
Proof.
  intros H. split.
  - intros c. unfold tenv_merge. rewrite lookup_union_with.
    destruct (Θ1 !! c) as [o1|] eqn:H1, (Θ2 !! c) as [o2|] eqn:H2; simpl; try constructor.
    destruct (H c o1 o2 H1 H2) as (e1 & e2 & -> & -> & _). simpl. constructor.
  - intros c e1 e2 H1 H2. destruct (H c _ _ H1 H2) as (f1 & f2 & [= <-] & [= <-] & ?). done.
Qed.

(** ** Renaming the removed channel of a link

    [tenv_mv c d Θ] moves the entries of c to d, as [chsubst c d] does
    with the term. *)

Definition ends_join2 (oc : ends) (od : option ends) : ends :=
  match oc, od with
  | One ec, Some (One ed) => Both ec ed
  | _, _ => oc
  end.

Definition tenv_mv (c d : chan) (Θ : tenv) : tenv :=
  match Θ !! c with
  | None => Θ
  | Some oc => <[d := ends_join2 oc (Θ !! d)]> (delete c Θ)
  end.

Lemma tenv_move_mv W c d Θ :
  c ≠ d →
  (∀ oc, Θ !! c = Some oc → ∀ od, Θ !! d = Some od →
     ∃ ec ed, oc = One ec ∧ od = One ed ∧ ec.2 = pt_dual ed.2 ∧ sdual ec.1 ed.1) →
  tenv_move W c d Θ (tenv_mv c d Θ).
Proof.
  intros Hcd H. unfold tenv_mv. destruct (Θ !! c) as [oc|] eqn:Hc.
  - split_and!.
    + rewrite lookup_insert_ne by done. by rewrite lookup_delete_eq.
    + intros k Hk1 Hk2. rewrite lookup_insert_ne by done. by rewrite lookup_delete_ne.
    + rewrite lookup_insert_eq. destruct (Θ !! d) as [od|] eqn:Hd.
      * destruct (H oc eq_refl od eq_refl) as (ec & ed & -> & -> & _). simpl.
        rewrite ?Hc. apply ends_join_both.
      * rewrite ?Hc. destruct oc; simpl; constructor.
    + intros e1 e2 He1 Hd. rewrite ?Hc in He1. injection He1 as ->.
      destruct (H _ eq_refl _ Hd) as (ec & ed & [= <-] & [= <-] & ?). done.
  - split_and!; [done|done| |].
    + rewrite ?Hc. destruct (Θ !! d); constructor.
    + intros e1 e2 He1. by rewrite Hc in He1.
Qed.

Lemma tenv_end_mv c d Θ o :
  c ≠ d → tenv_bipol (tenv_mv c d Θ) →
  (∀ oc od, Θ !! c = Some oc → Θ !! d = Some od → ∃ ec ed, oc = One ec ∧ od = One ed) →
  tenv_end (tenv_mv c d Θ) o =
    if decide (o.1 = c) then None
    else if decide (o.1 = d) then
      match tenv_end Θ (c, o.2) with Some x => Some x | None => tenv_end Θ o end
    else tenv_end Θ o.
Proof.
  intros Hcd Hb H. destruct o as [c' b]. simpl.
  unfold tenv_mv in *. destruct (Θ !! c) as [oc|] eqn:Hc.
  2:{ destruct (decide (c' = c)) as [->|Hne]; [by apply tenv_end_none, not_elem_of_dom|].
      destruct (decide (c' = d)) as [->|Hne']; [|done].
      by rewrite (tenv_end_none Θ (c, b)) by (by apply not_elem_of_dom). }
  destruct (decide (c' = c)) as [->|Hne].
  { unfold tenv_end. simpl. rewrite lookup_insert_ne by done. by rewrite lookup_delete_eq. }
  destruct (decide (c' = d)) as [->|Hne'].
  2:{ rewrite tenv_end_insert_ne by done. by rewrite tenv_end_delete_ne by done. }
  assert (Hbd := Hb d). rewrite lookup_insert_eq in Hbd.
  unfold tenv_end at 1. simpl. rewrite lookup_insert_eq.
  unfold tenv_end. simpl. rewrite Hc.
  destruct (Θ !! d) as [od|] eqn:Hd.
  - destruct (H oc od eq_refl eq_refl) as (ec & ed & -> & ->). simpl in *.
    specialize (Hbd ec ed eq_refl). repeat case_bool_decide; subst; done.
  - destruct oc as [ec|e1 e2]; simpl; repeat case_bool_decide; done.
Qed.

Lemma tenv_ends_mv c d Θ :
  c ≠ d → tenv_bipol (tenv_mv c d Θ) →
  (∀ oc od, Θ !! c = Some oc → Θ !! d = Some od → ∃ ec ed, oc = One ec ∧ od = One ed) →
  tenv_ends (tenv_mv c d Θ) = set_map (osub c d) (tenv_ends Θ).
Proof.
  intros Hcd Hb H. apply set_eq. intros o. rewrite elem_of_map, tenv_ends_end.
  rewrite (tenv_end_mv c d Θ o Hcd Hb H). destruct o as [c' b]; simpl.
  setoid_rewrite tenv_ends_end. unfold osub, csub. split.
  - case_decide as H1; [by intros []|]. case_decide as H2.
    + subst c'. destruct (tenv_end Θ (c, b)) as [x|] eqn:Hx.
      * intros _. exists (c, b). simpl. rewrite decide_True by done. split; [done|by eexists].
      * intros Hs. exists (d, b). simpl. rewrite decide_False by done. split; [done|done].
    + intros Hs. exists (c', b). simpl. rewrite decide_False by done. split; [done|done].
  - intros ([c'' b'] & Heq & Hs). simpl in Heq. injection Heq as Hc1 <-.
    destruct (decide (c'' = c)) as [->|Hne]; subst c'.
    + rewrite decide_False by done. rewrite decide_True by done. by destruct Hs as [? ->].
    + rewrite decide_False by done.
      destruct (decide (c'' = d)) as [->|Hne']; [|done].
      destruct (tenv_end Θ (c, _)); [by eexists|done].
Qed.

(** ** Facts of one soup *)

Section soup.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf n W ∅ T π q A U).

  Lemma lfc_bipol t e : q.2 !! t = Some e → tenv_bipol (A t).
  Proof. intros He. by destruct (lf_fit _ _ _ _ _ _ _ _ Hc t e He). Qed.

  Lemma lfc_ends t e : q.2 !! t = Some e → fends e = tenv_ends (A t).
  Proof. intros He. by destruct (lf_fit _ _ _ _ _ _ _ _ Hc t e He). Qed.

  Lemma lfc_held t e o : q.2 !! t = Some e → o ∈ fends e ↔ is_Some (tenv_end (A t) o).
  Proof. intros He. rewrite (lfc_ends t e He). apply tenv_ends_end. Qed.

  Lemma lfc_dom t e : q.2 !! t = Some e → dom (A t) = fchans e.
  Proof. intros He. by rewrite fchans_fends, (lfc_ends t e He), tenv_ends_dom. Qed.

  Lemma lfc_uniq t s e es o x y :
    q.2 !! t = Some e → q.2 !! s = Some es →
    tenv_end (A t) o = Some x → tenv_end (A s) o = Some y → t = s ∧ x = y.
  Proof.
    intros He Hes Hx Hy. destruct (decide (t = s)) as [<-|Hts].
    - rewrite He in Hes. injection Hes as <-. split; congruence.
    - exfalso. apply (lf_disj _ _ _ _ _ _ _ _ Hc t s e es Hts He Hes o).
      + apply (lfc_held t e o He). by eexists.
      + apply (lfc_held s es o Hes). by eexists.
  Qed.

  Lemma lfc_partner t e o x :
    q.2 !! t = Some e → tenv_end (A t) o = Some x →
    ∃ s es y, q.2 !! s = Some es ∧ tenv_end (A s) (cdual o) = Some y ∧
      y.2 = pt_dual x.2 ∧ sdual x.1 y.1.
  Proof. intros He Hx. apply (lf_pair _ _ _ _ _ _ _ _ Hc t e o x He Hx). by rewrite dom_empty_L. Qed.

  (** The partner of an end held by t and the end held by s are the same. *)
  Lemma lfc_partner_at t e o x s es y :
    q.2 !! t = Some e → tenv_end (A t) o = Some x →
    q.2 !! s = Some es → tenv_end (A s) (cdual o) = Some y →
    y.2 = pt_dual x.2 ∧ sdual x.1 y.1.
  Proof.
    intros He Hx Hes Hy. destruct (lfc_partner t e o x He Hx) as (s' & es' & y' & Hes' & Hy' & ?).
    destruct (lfc_uniq s s' es es' (cdual o) y y' Hes Hes' Hy Hy') as [-> ->]. done.
  Qed.

  Lemma lfc_closed_end t e o : q.2 !! t = Some e → o ∈ fends e → o.1 ∈ q.1.
  Proof.
    intros He Ho. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc t e He) as H.
    rewrite dom_empty_L, union_empty_r_L in H. apply H. by apply fchans_of_fends.
  Qed.
End soup.

(** The entries of a soup, with their holders forgotten. *)
Definition ent (q : config) (A : nat → tenv) (o : cend) (x : sty * point) : Prop :=
  ∃ t e, q.2 !! t = Some e ∧ tenv_end (A t) o = Some x.

(** ** The frame of a step

    A step changes the entries of a set Ch of ends, closed under the
    partner. Outside Ch the entries of the successor are those of the
    configuration, possibly with other holders, and π stays. Inside Ch
    the successor's entries have to be checked by hand. *)
Lemma LFconf_frame (n m : nat) (W : world) (T : ty) (π π' : gmap cend point) (q q' : config)
    (A A' : nat → tenv) (U U1 : nat → ty) (Ch : gset cend) :
  LFconf n W ∅ T π q A U →
  (∀ t e, q'.2 !! t = Some e → LErel m W (A' t) (U1 t) ∅ e) →
  (∀ t e, q'.2 !! t = Some e → tenv_fit (A' t) e) →
  (∀ t e, q'.2 !! t = Some e → U1 t = T ∨ U1 t = TUnit) →
  (∀ t s e es, t ≠ s → q'.2 !! t = Some e → q'.2 !! s = Some es → fends e ## fends es) →
  (∀ t e, q'.2 !! t = Some e → fchans e ⊆ q'.1) →
  (∀ o, o ∈ Ch ↔ cdual o ∈ Ch) →
  (∀ o x, o ∉ Ch → ent q' A' o x ↔ ent q A o x) →
  (∀ o, o ∉ Ch → π' !! o = π !! o) →
  (∀ o x, o ∈ Ch → ent q' A' o x →
     π' !! o = Some x.2 ∧ ∃ y, ent q' A' (cdual o) y ∧ y.2 = pt_dual x.2 ∧ sdual x.1 y.1) →
  LFconf m W ∅ T π' q' A' U1.
Proof.
  intros Hc Hrel Hfit Hty Hdisj Hcl HCh Hent Hπ HChk. split; try done.
  - apply (lf_prim _ _ _ _ _ _ _ _ Hc).
  - intros t e o x He Hx. destruct (decide (o ∈ Ch)) as [Ho|Ho].
    + by destruct (HChk o x Ho (ex_intro _ t (ex_intro _ e (conj He Hx)))) as [? _].
    + rewrite Hπ by done. destruct (proj1 (Hent o x Ho) (ex_intro _ t (ex_intro _ e (conj He Hx))))
        as (t0 & e0 & He0 & Hx0).
      apply (lf_pt _ _ _ _ _ _ _ _ Hc t0 e0 o x He0 Hx0).
  - intros t e o x He Hx _. destruct (decide (o ∈ Ch)) as [Ho|Ho].
    + destruct (HChk o x Ho (ex_intro _ t (ex_intro _ e (conj He Hx)))) as (_ & y & (s & es & Hes & Hy) & Hd1 & Hd2).
      exists s, es, y. by split_and!.
    + destruct (proj1 (Hent o x Ho) (ex_intro _ t (ex_intro _ e (conj He Hx))))
        as (t0 & e0 & He0 & Hx0).
      destruct (lfc_partner _ _ _ _ _ _ _ Hc t0 e0 o x He0 Hx0) as (s & es & y & Hes & Hy & Hd1 & Hd2).
      assert (cdual o ∉ Ch) as Hdo by (by rewrite <-HCh).
      destruct (proj2 (Hent (cdual o) y Hdo) (ex_intro _ s (ex_intro _ es (conj Hes Hy))))
        as (s' & es' & Hes' & Hy'). exists s', es', y. by split_and!.
  - intros t e He. pose proof (Hcl t e He). set_solver.
Qed.
