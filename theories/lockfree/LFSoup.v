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

(** ** Updates of the environments *)

Definition eupd {X : Type} (A : nat → X) (t : nat) (x : X) : nat → X :=
  λ u, if decide (u = t) then x else A u.

Lemma eupd_eq {X : Type} (A : nat → X) t x : eupd A t x t = x.
Proof. unfold eupd. by rewrite decide_True. Qed.

Lemma eupd_ne {X : Type} (A : nat → X) t x u : u ≠ t → eupd A t x u = A u.
Proof. intros H. unfold eupd. by rewrite decide_False. Qed.

Lemma fchans_eq_fends e e' : fends e' = fends e → fchans e' = fchans e.
Proof. intros H. by rewrite !fchans_fends, H. Qed.

Lemma pev_of_single q q' i : pev_of q {[i]} q' = match q.2 !! i with Some e => pev1 q q' e | None => PNone end.
Proof. unfold pev_of. by rewrite elements_singleton. Qed.

Lemma pev_of_pair q q' i j ei ej :
  i ≠ j → q.2 !! i = Some ei → q.2 !! j = Some ej →
  pev_of q {[i; j]} q' = pev2 ei ej ∨ pev_of q {[i; j]} q' = pev2 ej ei.
Proof.
  intros Hij Hi Hj. unfold pev_of.
  assert (elements ({[i; j]} : gset nat) = [i; j] ∨ elements ({[i; j]} : gset nat) = [j; i]) as [H|H].
  { apply Permutation_length_2_inv. symmetry.
    rewrite elements_union_singleton by set_solver. by rewrite elements_singleton. }
  - rewrite H, Hi, Hj. by left.
  - rewrite H, Hi, Hj. by right.
Qed.

(** ** Entries and ends around the participants of a step *)

Definition others (M : gmap nat expr) (A : nat → tenv) (I : gset nat) (o : cend)
    (x : sty * point) : Prop :=
  ∃ t f, (t ∉ I) ∧ M !! t = Some f ∧ tenv_end (A t) o = Some x.

Lemma ent_split C M A (I : gset nat) o x :
  (∀ i, i ∈ I → is_Some (M !! i)) →
  ent (C, M) A o x ↔ (∃ i, i ∈ I ∧ tenv_end (A i) o = Some x) ∨ others M A I o x.
Proof.
  intros HI. split.
  - intros (t & f & Hf & Hx). destruct (decide (t ∈ I)) as [Ht|Ht]; [left; by exists t|].
    right. by exists t, f.
  - intros [(i & Hi & Hx)|(t & f & _ & Hf & Hx)].
    + destruct (HI i Hi) as [f Hf]. by exists i, f.
    + by exists t, f.
Qed.

Lemma others_ext M M' A A' (I : gset nat) o x :
  (∀ t, t ∉ I → M' !! t = M !! t) → (∀ t, t ∉ I → A' t = A t) →
  others M' A' I o x ↔ others M A I o x.
Proof.
  intros HM HA. split; intros (t & f & Ht & Hf & Hx); exists t, f; split_and!; try done.
  - by rewrite <-HM. - by rewrite <-HA. - by rewrite HM. - by rewrite HA.
Qed.

Lemma disj_frame (M M' : gmap nat expr) (I : gset nat) :
  (∀ t s e es, t ≠ s → M !! t = Some e → M !! s = Some es → fends e ## fends es) →
  (∀ t, t ∉ I → M' !! t = M !! t) →
  (∀ p e' t e, p ∈ I → t ∉ I → M' !! p = Some e' → M !! t = Some e → fends e' ## fends e) →
  (∀ p p' e e', p ∈ I → p' ∈ I → p ≠ p' → M' !! p = Some e → M' !! p' = Some e' →
     fends e ## fends e') →
  ∀ t s e es, t ≠ s → M' !! t = Some e → M' !! s = Some es → fends e ## fends es.
Proof.
  intros Hd HM Hpt Hpp t s e es Hts He Hes.
  destruct (decide (t ∈ I)) as [Ht|Ht], (decide (s ∈ I)) as [Hs|Hs].
  - by apply (Hpp t s).
  - rewrite HM in Hes by done. by apply (Hpt t e s es).
  - rewrite HM in He by done. symmetry. by apply (Hpt s es t e).
  - rewrite HM in He, Hes by done. by apply (Hd t s).
Qed.

(** ** One step of a soup *)

Section step.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (C : gset chan) (M : gmap nat expr) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S (S n)) W ∅ T π (C, M) A U).

  Lemma st_rel t e : M !! t = Some e → LErel (S (S n)) W (A t) (U t) ∅ e.
  Proof. apply (lf_rel _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_step t e : M !! t = Some e → LEstep (LErel (S (S n))) (S n) W (A t) (U t) ∅ e.
  Proof. intros He. apply LErel_S_iff. by apply st_rel. Qed.

  Lemma st_down t e : M !! t = Some e → LErel n W (A t) (U t) ∅ e.
  Proof. intros He. eapply LErel_down; [|by apply st_rel]. lia. Qed.

  Lemma st_fit t e : M !! t = Some e → tenv_fit (A t) e.
  Proof. apply (lf_fit _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_ends t e : M !! t = Some e → fends e = tenv_ends (A t).
  Proof. apply (lfc_ends _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_bipol t e : M !! t = Some e → tenv_bipol (A t).
  Proof. apply (lfc_bipol _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_closed t e : M !! t = Some e → fchans e ⊆ C.
  Proof.
    intros He. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc t e He) as H. simpl in H. set_solver.
  Qed.

  Lemma st_disj t s e es : t ≠ s → M !! t = Some e → M !! s = Some es → fends e ## fends es.
  Proof. apply (lf_disj _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_ty t e : M !! t = Some e → U t = T ∨ U t = TUnit.
  Proof. apply (lf_ty _ _ _ _ _ _ _ _ Hc). Qed.

  (** The clauses at W itself. *)
  Lemma st_beta t e e' : M !! t = Some e → tstep e LBeta e' → LErel (S (S n)) W (A t) (U t) ∅ e'.
  Proof.
    intros He Hst. destruct (proj2 (st_step t e He) W (wext_r_refl W)) as (_ & _ & Hb & _). auto.
  Qed.

  Lemma st_new t e c x e' :
    M !! t = Some e → tstep e (LNew c x) e' → c ∉ dom (A t) →
    ∃ s s', sdual s s' ∧ LErel (S (S n)) W (<[c := Both (s, x) (s', pt_dual x)]> (A t)) (U t) ∅ e'.
  Proof.
    intros He Hst Hc'. destruct (proj2 (st_step t e He) W (wext_r_refl W)) as (_ & _ & _ & Hn & _).
    by destruct (Hn c x e' Hst Hc') as (_ & ?).
  Qed.

  Lemma st_spawn t e w e' :
    M !! t = Some e → tstep e (LSpawn w) e' →
    ∃ Θ1 Θ2, tenv_comp (@eq point) (A t) Θ1 Θ2 ∧
      LErel (S (S n)) W Θ1 TUnit ∅ (App w EUnit) ∧ LErel (S (S n)) W Θ2 (U t) ∅ e'.
  Proof.
    intros He Hst. destruct (proj2 (st_step t e He) W (wext_r_refl W)) as (_ & _ & _ & _ & Hsp & _).
    destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & Hcomp & Hv & HE).
    exists Θ1, Θ2. split_and!; [done| |done].
    apply Vspawn_LVrel in Hv.
    apply (LErel_app _ W Θ1 Θ1 ∅ ub lb TUnit TUnit ∅ w EUnit HW); [apply tenv_comp_empty_r|done| |].
    - by apply LVrel_unit_iff.
    - destruct ub; simpl; set_solver.
  Qed.

  Lemma st_sess t e σ e' :
    M !! t = Some e → tstep e (LSess σ) e' → LEobl LVrel LErel (S (S n)) W (A t) (U t) ∅ σ e'.
  Proof. intros He Hst. apply (LErel_S_step _ _ _ _ _ _ _ _ (st_rel t e He) Hst). Qed.

  Lemma st_link t e cd e' :
    M !! t = Some e → tstep e (LSess (SLink cd)) e' →
    LElink (λ W Θ F e, LErel (S (S n)) W Θ (U t) F e) W (A t) ∅ cd e'.
  Proof. intros He Hst. apply (LErel_S_link _ _ _ _ _ _ _ _ (st_rel t e He) Hst). Qed.

  (** ** β *)
  Lemma step_beta i e e' :
    M !! i = Some e → tstep e LBeta e' →
    LFconf n W ∅ T (pupd π (C, M) {[i]} (C, <[i := e']> M)) (C, <[i := e']> M) A U.
  Proof.
    intros He Hst.
    assert (pupd π (C, M) {[i]} (C, <[i := e']> M) = π) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. by apply offers_beta in Ho as ->. }
    pose proof (st_beta i e e' He Hst) as HE'.
    pose proof (LErel_S_fit _ _ _ _ _ _ HE') as Hfit'.
    assert (fends e' = fends e) as Hends by (by rewrite (st_ends i e He), (proj1 Hfit')).
    assert (∀ t f, <[i := e']> M !! t = Some f → ∃ f0, M !! t = Some f0 ∧ fends f = fends f0 ∧
              (t = i → f = e') ∧ (t ≠ i → f = f0)) as Hlk.
    { intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      - rewrite lookup_insert_eq in Hf. injection Hf as <-. exists e. done.
      - rewrite lookup_insert_ne in Hf by done. exists f. done. }
    apply (LFconf_frame (S (S n)) n W T π π (C, M) (C, <[i := e']> M) A A U U ∅ Hc); simpl.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. eapply LErel_down; [|exact HE']. lia.
      + rewrite lookup_insert_ne in Hf by done. by apply st_down.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. by injection Hf as <-.
      + rewrite lookup_insert_ne in Hf by done. by apply st_fit.
    - intros t f Hf. destruct (Hlk t f Hf) as (f0 & Hf0 & _). by apply (st_ty t f0).
    - intros t s f fs Hts Hf Hfs. destruct (Hlk t f Hf) as (f0 & Hf0 & -> & _).
      destruct (Hlk s fs Hfs) as (fs0 & Hfs0 & -> & _). by apply (st_disj t s f0 fs0).
    - intros t f Hf. destruct (Hlk t f Hf) as (f0 & Hf0 & Hfe & _).
      rewrite (fchans_eq_fends f0 f Hfe). by apply (st_closed t).
    - set_solver.
    - intros o x _. split.
      + intros (t & f & Hf & Hx). destruct (Hlk t f Hf) as (f0 & Hf0 & _). by exists t, f0.
      + intros (t & f0 & Hf0 & Hx). exists t. destruct (decide (t = i)) as [->|Hti].
        * exists e'. simpl. by rewrite lookup_insert_eq.
        * exists f0. simpl. by rewrite lookup_insert_ne.
    - done.
    - set_solver.
  Qed.

  Lemma st_nomention t e c : M !! t = Some e → c ∉ fchans e → ∀ b, tenv_end (A t) (c, b) = None.
  Proof.
    intros He Hc' b. apply tenv_end_none. simpl. by rewrite (lfc_dom _ _ _ _ _ _ _ Hc t e He).
  Qed.

  Lemma st_fresh_mention c t e : c ∉ echans (soup M) → M !! t = Some e → c ∉ fchans e.
  Proof.
    intros Hc' He Hce. apply Hc'. apply elem_of_echans. exists e. split; [|done].
    apply elem_of_soup. by exists t.
  Qed.

  (** ** new *)
  Lemma step_new i e c x e' :
    M !! i = Some e → tstep e (LNew c x) e' → c ∉ C → c ∉ echans (soup M) →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M))
      (C ∪ {[c]}, <[i := e']> M) A' U.
  Proof.
    intros He Hst HcC Hcs.
    assert (∀ t f, M !! t = Some f → c ∉ fchans f) as Hnm by (intros t f Hf; by eapply st_fresh_mention).
    assert (c ∉ dom (A i)) as Hci by (rewrite (lfc_dom _ _ _ _ _ _ _ Hc i e He); by apply (Hnm i)).
    destruct (st_new i e c x e' He Hst Hci) as (s & s' & Hss & HE').
    set (Θn := <[c := Both (s, x) (s', pt_dual x)]> (A i)).
    assert (pupd π (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M) =
            <[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π)) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. apply offers_new in Ho as ->.
      simpl. assert ((C ∪ {[c]}) ∖ C = {[c]}) as -> by set_solver. by rewrite elements_singleton. }
    pose proof (LErel_S_fit _ _ _ _ _ _ HE') as Hfit'.
    assert (fends e' = fends e ∪ cends c) as Hends.
    { rewrite (st_ends i e He), <-(proj1 Hfit'). unfold Θn.
      rewrite tenv_ends_new. unfold cends. destruct (pt_pol x); set_solver. }
    exists (eupd A i Θn).
    apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∪ {[c]}, <[i := e']> M) A _ U U (cends c) Hc);
      simpl.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite eupd_eq.
        eapply LErel_down; [|exact HE']. lia.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply (st_down).
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. by rewrite eupd_eq.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply (st_fit).
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + by apply (st_ty i e).
      + rewrite lookup_insert_ne in Hf by done. by apply (st_ty t f).
    - apply (disj_frame M _ {[i]} (st_disj)).
      + intros t Ht. rewrite lookup_insert_ne; set_solver.
      + intros p f t g Hp Ht Hf Hg. apply elem_of_singleton in Hp as ->.
        rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite Hends.
        assert (t ≠ i) by set_solver.
        pose proof (st_disj i t e g ltac:(done) He Hg).
        intros o Ho1 Ho2. apply elem_of_union in Ho1 as [Ho1|Ho1]; [set_solver|].
        apply elem_of_cends in Ho1. apply (Hnm t g Hg). rewrite <-Ho1. by apply fchans_of_fends.
      + intros p p' f f' Hp Hp' Hpp. set_solver.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-.
        rewrite fchans_fends, Hends, set_map_union_L, <-fchans_fends.
        pose proof (st_closed i e He).
        intros d Hd. apply elem_of_union in Hd as [Hd|Hd]; [set_solver|].
        apply elem_of_map in Hd as (o & -> & Ho%elem_of_cends). set_solver.
      + rewrite lookup_insert_ne in Hf by done. pose proof (st_closed t f Hf).
        set_solver.
    - intros o. apply cends_cdual.
    - intros o x0 Ho.
      assert (HI : ∀ i', i' ∈ ({[i]} : gset nat) → is_Some (M !! i'))
        by (intros i' ->%elem_of_singleton; by eexists).
      assert (HI' : ∀ i', i' ∈ ({[i]} : gset nat) → is_Some (<[i:=e']> M !! i'))
        by (intros i' ->%elem_of_singleton; rewrite lookup_insert_eq; by eexists).
      rewrite (ent_split _ (<[i:=e']> M) (eupd A i Θn) {[i]} o x0 HI'), (ent_split C M A {[i]} o x0 HI).
      rewrite (others_ext (<[i:=e']> M) M (eupd A i Θn) A);
        [|intros t Ht; rewrite lookup_insert_ne; set_solver|intros t Ht; rewrite eupd_ne; set_solver].
      assert (tenv_end Θn o = tenv_end (A i) o) as Hθ.
      { unfold Θn. rewrite tenv_end_new. rewrite !decide_False; [done| |];
          intros ->; apply Ho, elem_of_cends; done. }
      split; intros [(i' & Hi' & Hx)|Ho']; [|by right| |by right];
        apply elem_of_singleton in Hi' as ->; left; exists i; (split; [by apply elem_of_singleton|]).
      + by rewrite eupd_eq, Hθ in Hx.
      + by rewrite eupd_eq, Hθ.
    - intros o Ho. assert (o ≠ (c, pt_pol x)) by (intros ->; apply Ho, elem_of_cends; done).
      assert (o ≠ (c, negb (pt_pol x))) by (intros ->; apply Ho, elem_of_cends; done).
      by rewrite !lookup_insert_ne by done.
    - intros o x0 Ho%elem_of_cends (t & f & Hf & Hx).
      assert (t = i) as ->.
      { destruct (decide (t = i)) as [->|Hti]; [done|]. simpl in Hf.
        rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne in Hx by done.
        destruct o as [c' b]. simpl in Ho. subst c'.
        by rewrite (st_nomention t f c Hf (Hnm t f Hf)) in Hx. }
      rewrite eupd_eq in Hx. unfold Θn in Hx. rewrite tenv_end_new in Hx.
      assert (Hent_i : ∀ o' y, tenv_end Θn o' = Some y → ent (C ∪ {[c]}, <[i:=e']> M) (eupd A i Θn) o' y).
      { intros o' y Hy. exists i, e'. simpl. rewrite lookup_insert_eq, eupd_eq. done. }
      destruct (decide (o = (c, pt_pol x))) as [->|H1].
      + injection Hx as <-. simpl. split; [by rewrite lookup_insert_eq|].
        exists (s', pt_dual x). split_and!; [|done|done]. apply Hent_i. unfold Θn.
        rewrite tenv_end_new. unfold cdual. simpl.
        rewrite decide_False by (intros [=]; by destruct (pt_pol x)). by rewrite decide_True.
      + destruct (decide (o = (c, negb (pt_pol x)))) as [->|H2].
        2:{ exfalso. destruct o as [c' b]. simpl in Ho. subst c'.
            destruct b, (pt_pol x); simpl in *; congruence. }
        injection Hx as <-. simpl. split.
        { rewrite lookup_insert_ne by (intros [=]; by destruct (pt_pol x)). by rewrite lookup_insert_eq. }
        exists (s, x). split_and!; [|by rewrite pt_dual_dual|by apply sdual_sym].
        apply Hent_i. unfold Θn. rewrite tenv_end_new. unfold cdual. simpl.
        rewrite negb_involutive. by rewrite decide_True.
  Qed.
  (** ** spawn *)
  Lemma step_spawn i j e w e' :
    M !! i = Some e → tstep e (LSpawn w) e' → M !! j = None →
    ∃ A' U', LFconf n W ∅ T (pupd π (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M)))
      (C, <[j := App w EUnit]> (<[i := e']> M)) A' U'.
  Proof.
    intros He Hst Hj.
    assert (i ≠ j) as Hij by (intros ->; congruence).
    destruct (st_spawn i e w e' He Hst) as (Θ1 & Θ2 & Hcomp & HE1 & HE2).
    assert (pupd π (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M)) = π) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. by apply offers_spawn in Ho as ->. }
    pose proof (LErel_S_fit _ _ _ _ _ _ HE1) as Hfit1.
    pose proof (LErel_S_fit _ _ _ _ _ _ HE2) as Hfit2.
    pose proof (st_bipol i e He) as Hb.
    destruct (tenv_ends_comp _ _ _ Hcomp Hb) as [Hu Hd].
    rewrite (proj1 Hfit1), (proj1 Hfit2) in Hu, Hd. rewrite <-(st_ends i e He) in Hu.
    set (M' := <[j := App w EUnit]> (<[i := e']> M)).
    assert (HM' : ∀ t, M' !! t = if decide (t = j) then Some (App w EUnit)
                                 else if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M'. destruct (decide (t = j)) as [->|Htj]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done.
      destruct (decide (t = i)) as [->|Hti]; [by rewrite lookup_insert_eq|]. by rewrite lookup_insert_ne. }
    set (A' := eupd (eupd A i Θ2) j Θ1).
    assert (HA' : ∀ t, A' t = if decide (t = j) then Θ1 else if decide (t = i) then Θ2 else A t).
    { intros t. unfold A', eupd. repeat case_decide; congruence. }
    assert (Hsub : ∀ t f, M' !! t = Some f → (t = j ∨ t = i) → fends f ⊆ fends e).
    { intros t f Hf Ht. rewrite HM' in Hf. rewrite Hu.
      destruct (decide (t = j)); [injection Hf as <-; set_solver|].
      destruct (decide (t = i)); [injection Hf as <-; set_solver|]. naive_solver. }
    exists A', (eupd U j TUnit).
    apply (LFconf_frame (S (S n)) n W T π π (C, M) (C, M') A A' U _ ∅ Hc); simpl.
    - intros t f Hf. rewrite HM' in Hf. rewrite HA'. unfold eupd.
      destruct (decide (t = j)) as [->|Htj].
      + injection Hf as <-. eapply LErel_down; [|exact HE1]. lia.
      + destruct (decide (t = i)) as [->|Hti].
        * injection Hf as <-. eapply LErel_down; [|exact HE2]. lia.
        * by apply st_down.
    - intros t f Hf. rewrite HM' in Hf. rewrite HA'.
      destruct (decide (t = j)) as [->|Htj]; [by injection Hf as <-|].
      destruct (decide (t = i)) as [->|Hti]; [by injection Hf as <-|]. by apply st_fit.
    - intros t f Hf. rewrite HM' in Hf. unfold eupd.
      destruct (decide (t = j)) as [->|Htj]; [by right|].
      destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|]. by apply (st_ty t f).
    - apply (disj_frame M M' {[i; j]} st_disj).
      + intros t Ht. rewrite HM'. rewrite !decide_False by set_solver. done.
      + intros p f t g Hp Ht Hf Hg.
        assert (t ≠ i) by set_solver.
        pose proof (st_disj i t e g ltac:(done) He Hg).
        pose proof (Hsub p f Hf ltac:(set_solver)). set_solver.
      + intros p p' f f' Hp Hp' Hpp Hf Hf'. rewrite HM' in Hf, Hf'.
        apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->;
          apply elem_of_union in Hp' as [Hp'|Hp']; apply elem_of_singleton in Hp' as ->; try done.
        * rewrite decide_False in Hf by done. rewrite decide_True in Hf by done.
          rewrite decide_True in Hf' by done. injection Hf as <-. injection Hf' as <-. by symmetry.
        * rewrite decide_True in Hf by done.
          rewrite decide_False in Hf' by done. rewrite decide_True in Hf' by done.
          injection Hf as <-. injection Hf' as <-. done.
    - intros t f Hf. pose proof (Hf) as Hf0. rewrite HM' in Hf0.
      destruct (decide (t = j ∨ t = i)) as [Ht|Ht].
      + pose proof (Hsub t f Hf Ht) as Hs. pose proof (st_closed i e He).
        rewrite fchans_fends. rewrite fchans_fends in *.
        intros c Hc'. apply elem_of_map in Hc' as (o & -> & Ho). apply H.
        apply elem_of_map. exists o. split; [done|]. by apply Hs.
      + rewrite !decide_False in Hf0 by naive_solver. by apply (st_closed t).
    - set_solver.
    - intros o x _. split.
      + intros (t & f & Hf & Hx). rewrite HA' in Hx. rewrite HM' in Hf.
        destruct (decide (t = j)) as [->|Htj].
        { exists i, e. split; [done|]. by apply (tenv_end_comp_l _ _ _ _ _ Hcomp Hb). }
        destruct (decide (t = i)) as [->|Hti].
        { exists i, e. split; [done|]. by apply (tenv_end_comp_r _ _ _ _ _ Hcomp Hb). }
        by exists t, f.
      + intros (t & f & Hf & Hx). destruct (decide (t = i)) as [->|Hti].
        * simpl in Hf. rewrite He in Hf. injection Hf as <-.
          destruct (tenv_end_comp_inv _ _ _ _ _ Hcomp Hb Hx) as [H1|H2].
          -- exists j, (App w EUnit). rewrite HM', HA', !decide_True by done. done.
          -- exists i, e'. rewrite HM', HA', decide_False, decide_True by done.
             rewrite decide_False, decide_True by done. done.
        * assert (t ≠ j) by (intros ->; simpl in Hf; congruence).
          exists t, f. rewrite HM', HA', !decide_False by done. done.
    - done.
    - set_solver.
  Qed.

  (** ** Two participants on one channel *)

  (** Nobody else mentions a channel whose two ends i and j hold. *)
  Lemma st_cowner i j e f c b t g :
    M !! i = Some e → M !! j = Some f → (c, b) ∈ fends e → (c, negb b) ∈ fends f →
    t ≠ i → t ≠ j → M !! t = Some g → c ∉ fchans g.
  Proof.
    intros He Hf Hi Hj Hti Htj Hg Hcg. apply fends_of_fchans in Hcg as [b' Hb'].
    destruct b, b'; simpl in *.
    - by apply (st_disj t i g e Hti Hg He (c, true)).
    - by apply (st_disj t j g f Htj Hg Hf (c, false)).
    - by apply (st_disj t j g f Htj Hg Hf (c, true)).
    - by apply (st_disj t i g e Hti Hg He (c, false)).
  Qed.

  Lemma hd_end Θ o u k Θ1 :
    tenv_hd_end Θ o u k Θ1 → tenv_bipol Θ →
    ∃ s, unfoldS s = u ∧ tenv_ext Θ1 o.1 (s, k) Θ ∧ tenv_end Θ o = Some (s, k) ∧
      tenv_end Θ1 o = None ∧ (∀ o', o' ≠ o → tenv_end Θ o' = tenv_end Θ1 o').
  Proof.
    intros [(s & Hext & Hu) Hp] Hb. exists s. destruct o as [c b]. simpl in *. subst b.
    split_and!; [done|done|by apply (tenv_end_ext_eq _ _ _ _ Hext Hb)
      |by apply (tenv_end_ext_none _ _ _ _ Hext Hb)|].
    intros o' Ho'. by apply (tenv_end_ext_ne _ _ _ _ _ Hext Hb).
  Qed.

  Lemma two_frame (i j : nat) (e f e' f' : expr) (Θi Θj : tenv) (c : chan) (π' : gmap cend point) (C' : gset chan) :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    LErel n W Θi (U i) ∅ e' → LErel n W Θj (U j) ∅ f' → tenv_fit Θi e' → tenv_fit Θj f' →
    fends e' ∪ fends f' ⊆ fends e ∪ fends f → fends e' ## fends f' →
    (C' = C ∨ (C' = (C ∖ {[c]}) ∧ (c ∉ fchans e') ∧ (c ∉ fchans f'))) →
    (∀ t g, t ≠ i → t ≠ j → M !! t = Some g → c ∉ fchans g) →
    (∀ o x, o.1 ≠ c → ((tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) ↔
                       (tenv_end (A i) o = Some x ∨ tenv_end (A j) o = Some x))) →
    (∀ o, o.1 ≠ c → π' !! o = π !! o) →
    (∀ o x, o.1 = c → (tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) →
       π' !! o = Some x.2 ∧ ∃ y, (tenv_end Θi (cdual o) = Some y ∨ tenv_end Θj (cdual o) = Some y) ∧
         y.2 = pt_dual x.2 ∧ sdual x.1 y.1) →
    LFconf n W ∅ T π' (C', <[j := f']> (<[i := e']> M)) (eupd (eupd A i Θi) j Θj) U.
  Proof.
    intros Hij He Hf HEi HEj Hfi Hfj Hsub Hdij HC' Hoth Hent Hπ HChk.
    set (M' := <[j := f']> (<[i := e']> M)).
    assert (HM' : ∀ t, M' !! t = if decide (t = j) then Some f'
                                 else if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M'. destruct (decide (t = j)) as [->|Htj]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done.
      destruct (decide (t = i)) as [->|Hti]; [by rewrite lookup_insert_eq|]. by rewrite lookup_insert_ne. }
    set (A' := eupd (eupd A i Θi) j Θj).
    assert (HA' : ∀ t, A' t = if decide (t = j) then Θj else if decide (t = i) then Θi else A t).
    { intros t. unfold A', eupd. repeat case_decide; congruence. }
    assert (Hsub' : ∀ t g, M' !! t = Some g → (t = j ∨ t = i) → fends g ⊆ fends e ∪ fends f).
    { intros t g Hg Ht. rewrite HM' in Hg.
      destruct (decide (t = j)); [injection Hg as <-; set_solver|].
      destruct (decide (t = i)); [injection Hg as <-; set_solver|]. naive_solver. }
    apply (LFconf_frame (S (S n)) n W T π π' (C, M) (C', M') A A' U U (cends c) Hc); simpl.
    - intros t g Hg. rewrite HM' in Hg. rewrite HA'.
      destruct (decide (t = j)) as [->|Htj]; [by injection Hg as <-|].
      destruct (decide (t = i)) as [->|Hti]; [by injection Hg as <-|]. by apply st_down.
    - intros t g Hg. rewrite HM' in Hg. rewrite HA'.
      destruct (decide (t = j)) as [->|Htj]; [by injection Hg as <-|].
      destruct (decide (t = i)) as [->|Hti]; [by injection Hg as <-|]. by apply st_fit.
    - intros t g Hg. rewrite HM' in Hg.
      destruct (decide (t = j)) as [->|Htj]; [by apply (st_ty j f)|].
      destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|]. by apply (st_ty t g).
    - apply (disj_frame M M' {[i; j]} st_disj).
      + intros t Ht. rewrite HM'. rewrite !decide_False by set_solver. done.
      + intros p g t h Hp Ht Hg Hh.
        assert (t ≠ i ∧ t ≠ j) as [Hti Htj] by set_solver.
        pose proof (st_disj i t e h ltac:(done) He Hh).
        pose proof (st_disj j t f h ltac:(done) Hf Hh).
        pose proof (Hsub' p g Hg ltac:(set_solver)). set_solver.
      + intros p p' g g' Hp Hp' Hpp Hg Hg'. rewrite HM' in Hg, Hg'.
        apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->;
          apply elem_of_union in Hp' as [Hp'|Hp']; apply elem_of_singleton in Hp' as ->; try done.
        * rewrite decide_False in Hg by done. rewrite decide_True in Hg by done.
          rewrite decide_True in Hg' by done. injection Hg as <-. injection Hg' as <-. done.
        * rewrite decide_True in Hg by done.
          rewrite decide_False in Hg' by done. rewrite decide_True in Hg' by done.
          injection Hg as <-. injection Hg' as <-. by symmetry.
    - intros t g Hg. pose proof (Hg) as Hg0. rewrite HM' in Hg0.
      pose proof (st_closed i e He). pose proof (st_closed j f Hf).
      destruct (decide (t = j ∨ t = i)) as [Ht|Ht].
      + pose proof (Hsub' t g Hg Ht) as Hs.
        assert (fchans g ⊆ C) as HgC.
        { intros d Hd'. rewrite fchans_fends in Hd'. apply elem_of_map in Hd' as (o & -> & Ho).
          apply Hs, elem_of_union in Ho as [Ho|Ho].
          - apply (st_closed i e He). by apply fchans_of_fends.
          - apply (st_closed j f Hf). by apply fchans_of_fends. }
        destruct HC' as [->|(-> & Hce & Hcf)]; [done|].
        assert (c ∉ fchans g).
        { revert Hg0. case_decide; [intros [= <-]; done|]. case_decide; [intros [= <-]; done|].
          naive_solver. }
        set_solver.
      + rewrite !decide_False in Hg0 by naive_solver. pose proof (st_closed t g Hg0).
        destruct HC' as [->|(-> & _ & _)]; [done|].
        pose proof (Hoth t g ltac:(naive_solver) ltac:(naive_solver) Hg0). set_solver.
    - intros o. apply cends_cdual.
    - intros o x Ho. rewrite elem_of_cends in Ho. split.
      + intros (t & g & Hg & Hx). rewrite HA' in Hx. rewrite HM' in Hg.
        destruct (decide (t = j)) as [->|Htj].
        { destruct (proj1 (Hent o x Ho) (or_intror Hx)) as [H|H]; [by exists i, e|by exists j, f]. }
        destruct (decide (t = i)) as [->|Hti].
        { destruct (proj1 (Hent o x Ho) (or_introl Hx)) as [H|H]; [by exists i, e|by exists j, f]. }
        by exists t, g.
      + intros (t & g & Hg & Hx). simpl in Hg.
        destruct (decide (t = i ∨ t = j)) as [Ht|Ht].
        * assert (tenv_end (A i) o = Some x ∨ tenv_end (A j) o = Some x) as Hor.
          { destruct Ht as [->| ->]; auto. }
          destruct (proj2 (Hent o x Ho) Hor) as [H|H].
          -- exists i, e'. rewrite HM', HA', decide_False, decide_True by done.
             rewrite decide_False, decide_True by done. done.
          -- exists j, f'. rewrite HM', HA', !decide_True by done. done.
        * exists t, g. rewrite HM', HA', !decide_False by naive_solver. done.
    - intros o Ho. apply Hπ. intros Ho'. apply Ho. by apply elem_of_cends.
    - intros o x Ho%elem_of_cends (t & g & Hg & Hx). rewrite HM' in Hg. rewrite HA' in Hx.
      assert (tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) as Hor.
      { destruct (decide (t = j)) as [->|Htj]; [by right|].
        destruct (decide (t = i)) as [->|Hti]; [by left|].
        exfalso. pose proof (Hoth t g Hti Htj Hg) as Hn. destruct o as [c' b']. simpl in Ho. subst c'.
        rewrite (st_nomention t g c Hg Hn) in Hx. done. }
      destruct (HChk o x Ho Hor) as (Hp & y & Hy & Hd1 & Hd2). split; [done|].
      exists y. split; [|done]. destruct Hy as [Hy|Hy].
      + exists i, e'. rewrite HM', HA', decide_False, decide_True by done.
        rewrite decide_False, decide_True by done. done.
      + exists j, f'. rewrite HM', HA', !decide_True by done. done.
  Qed.

  Lemma st_held t e o x : M !! t = Some e → tenv_end (A t) o = Some x → o ∈ fends e.
  Proof. intros He Hx. apply (lfc_held _ _ _ _ _ _ _ Hc t e o He). by eexists. Qed.

  (** The rest of an environment after the action on o, and the ends
      of the continuation. *)
  Lemma st_rest t e o u k Θ1 :
    M !! t = Some e → tenv_hd_end (A t) o u k Θ1 →
    ∃ s, unfoldS s = u ∧ tenv_ext Θ1 o.1 (s, k) (A t) ∧ tenv_end (A t) o = Some (s, k) ∧
      o ∈ fends e ∧ tenv_ends Θ1 = fends e ∖ {[o]} ∧
      (∀ o', o' ≠ o → tenv_end (A t) o' = tenv_end Θ1 o').
  Proof.
    intros He Hhd. destruct (hd_end _ _ _ _ _ Hhd (st_bipol t e He)) as (s & Hu & Hext & Ho & Hn & Hr).
    exists s. split_and!; try done.
    - by apply (st_held t e o (s, k)).
    - destruct Hhd as [_ Hp]. destruct o as [c b]. simpl in *. subst b.
      destruct (tenv_ends_ext _ _ _ _ Hext (st_bipol t e He)) as [H1 H2].
      rewrite (st_ends t e He), H1. set_solver.
  Qed.

  Lemma fchans_not e c : (∀ b, (c, b) ∉ fends e) → c ∉ fchans e.
  Proof. intros H Hc'. apply fends_of_fchans in Hc' as [b Hb]. by apply (H b). Qed.

  (** ** close *)
  Lemma step_close i j c b e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SClos (c, b))) e' → tstep f (LSess (SClos (c, negb b))) f' → c ∈ C →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M)))
      (C ∖ {[c]}, <[j := f']> (<[i := e']> M)) A' U.
  Proof.
    intros Hij He Hf Hse Hsf HcC.
    pose proof (st_sess i e _ e' He Hse) as (Θ1 & k & Hhd & HE). simpl in HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θ1j & kj & Hhdj & HEj). simpl in HEj.
    destruct (st_rest i e _ _ _ _ He Hhd) as (s & _ & _ & Hxi & Hoi & Hends & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (sj & _ & _ & Hxj & Hoj & Hendsj & Hrj).
    pose proof (LErel_S_fit _ _ _ _ _ _ HE) as Hfit. pose proof (LErel_S_fit _ _ _ _ _ _ HEj) as Hfitj.
    rewrite (proj1 Hfit) in Hends. rewrite (proj1 Hfitj) in Hendsj.
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    assert (∀ b', (c, b') ∉ fends e') as Hne.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = b)) as [->|Hb]; [set_solver|].
      assert (b' = negb b) as -> by (by destruct b, b').
      apply (Hdisj (c, negb b)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ fends f') as Hnej.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb b)) as [->|Hb]; [set_solver|].
      assert (b' = b) as -> by (by destruct b, b').
      apply (Hdisj (c, b)); [done|set_solver]. }
    exists (eupd (eupd A i Θ1) j Θ1j).
    eapply (two_frame i j e f e' f' Θ1 Θ1j c); try done.
    - eapply LErel_down; [|exact HE]. lia.
    - eapply LErel_down; [|exact HEj]. lia.
    - rewrite Hends, Hendsj. set_solver.
    - rewrite Hends, Hendsj. set_solver.
    - right. split_and!; [done|by apply fchans_not|by apply fchans_not].
    - intros t g Hti Htj Hg. by apply (st_cowner i j e f c b t g).
    - intros o x Ho. rewrite (Hri o), (Hrj o); [done| |]; intros ->; by apply Ho.
    - intros o Ho. unfold pupd.
      destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_clos in Hoa as ->.
      destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_clos in Hoa' as ->.
      destruct (pev_of_pair (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold pev2; rewrite ?Ha, ?Ha'; simpl; rewrite !lookup_delete_ne; try done;
        intros Heq; apply Ho; by rewrite <-Heq.
    - intros o x Ho [Hx|Hx]; exfalso.
      + assert (o ∈ tenv_ends Θ1) as Hin by (apply tenv_ends_end; by eexists).
        rewrite (proj1 Hfit) in Hin. destruct o as [c' b']. simpl in Ho. subst c'. by apply (Hne b').
      + assert (o ∈ tenv_ends Θ1j) as Hin by (apply tenv_ends_end; by eexists).
        rewrite (proj1 Hfitj) in Hin. destruct o as [c' b']. simpl in Ho. subst c'. by apply (Hnej b').
  Qed.

End step.
