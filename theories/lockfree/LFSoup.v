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

  (** ** choice *)
  Lemma step_choice i j c β b e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SSel (c, β) b)) e' → tstep f (LSess (SBra (c, negb β) b)) f' →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
      (C, <[j := f']> (<[i := e']> M)) A' U.
  Proof.
    intros Hij He Hf Hse Hsf.
    pose proof (st_sess i e _ e' He Hse) as (Θr & s1 & s2 & k & Θ' & Hhd & Hext & HE). simpl in HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θr' & r1 & r2 & k' & Θ'' & Hhdj & Hextj & HEj).
    simpl in HEj.
    destruct (st_rest i e _ _ _ _ He Hhd) as (s0 & Hu & _ & Hxi & Hoi & Hends & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (r0 & Hur & _ & Hxj & Hoj & Hendsj & Hrj).
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e (c, β) _ j f _ He Hxi Hf Hxj) as [Hk' Hsd].
    simpl in Hk'. subst k'.
    destruct (sdual_plus_with _ _ _ _ _ _ Hsd Hu Hur) as [Hd1 Hd2].
    pose proof (sdual_sbranch b _ _ _ _ Hd1 Hd2) as Hdb.
    pose proof (LErel_S_fit _ _ _ _ _ _ HE) as Hfit. pose proof (LErel_S_fit _ _ _ _ _ _ HEj) as Hfitj.
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    assert (∀ b', (c, b') ∉ tenv_ends Θr) as Hnr.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = β)) as [->|Hb]; [set_solver|].
      assert (b' = negb β) as -> by (by destruct β, b').
      apply (Hdisj (c, negb β)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ tenv_ends Θr') as Hnr'.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb β)) as [->|Hb]; [set_solver|].
      assert (b' = β) as -> by (by destruct β, b').
      apply (Hdisj (c, β)); [done|set_solver]. }
    assert (∀ b', tenv_end Θr (c, b') = None) as Hnr0.
    { intros b'. destruct (tenv_end Θr (c, b')) eqn:H; [|done]. exfalso. apply (Hnr b').
      apply tenv_ends_end. by eexists. }
    assert (∀ b', tenv_end Θr' (c, b') = None) as Hnr0'.
    { intros b'. destruct (tenv_end Θr' (c, b')) eqn:H; [|done]. exfalso. apply (Hnr' b').
      apply tenv_ends_end. by eexists. }
    assert (pt_pol (sel_pt k b) = false) as Hps by done.
    assert (pt_pol (bra_pt (pt_dual k) b) = true) as Hpb by done.
    destruct (tenv_ends_ext _ _ _ _ Hext (proj2 Hfit)) as [He1 _].
    destruct (tenv_ends_ext _ _ _ _ Hextj (proj2 Hfitj)) as [He2 _].
    rewrite (proj1 Hfit) in He1. cbn [snd] in He1. rewrite ?Hps in He1.
    rewrite (proj1 Hfitj) in He2. cbn [snd] in He2. rewrite ?Hpb in He2.
    assert (HΘ' : ∀ o, tenv_end Θ' o = if decide (o = (c, false)) then Some (sbranch b s1 s2, sel_pt k b)
                                       else tenv_end Θr o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext (proj2 Hfit)). cbn [snd]. by rewrite ?Hps. }
    assert (HΘ'' : ∀ o, tenv_end Θ'' o = if decide (o = (c, true))
                                         then Some (sbranch b r1 r2, bra_pt (pt_dual k) b)
                                         else tenv_end Θr' o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hextj (proj2 Hfitj)). cbn [snd]. by rewrite ?Hpb. }
    assert (π !! (c, β) = Some k) as Hπk by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi).
    assert (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)) =
            <[(c, false) := sel_pt k b]> (<[(c, true) := bra_pt k b]> π)) as Hpu.
    { unfold pupd.
      destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_sel in Hoa as ->.
      destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_bra in Hoa' as ->.
      destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold pev2; rewrite ?Ha, ?Ha'; simpl; by rewrite Hπk. }
    exists (eupd (eupd A i Θ') j Θ'').
    rewrite Hpu.
    eapply (two_frame i j e f e' f' Θ' Θ'' c); try done.
    - eapply LErel_down; [|exact HE]. lia.
    - eapply LErel_down; [|exact HEj]. lia.
    - rewrite He1, He2, Hends, Hendsj. cbn [fst]. intros o Ho. destruct β; set_solver.
    - rewrite He1, He2. cbn [fst]. intros o Ho1 Ho2.
      apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_union in Ho2 as [Ho2|Ho2].
      + rewrite Hends in Ho1. rewrite Hendsj in Ho2. apply (Hdisj o); set_solver.
      + apply elem_of_singleton in Ho2 as ->. by apply (Hnr true).
      + apply elem_of_singleton in Ho1 as ->. by apply (Hnr' false).
      + apply elem_of_singleton in Ho1, Ho2. congruence.
    - by left.
    - intros t g Hti Htj Hg. by apply (st_cowner i j e f c β t g).
    - intros o x Ho. rewrite HΘ', HΘ'', !decide_False by (intros ->; by apply Ho).
      rewrite (Hri o), (Hrj o); [done| |]; intros ->; by apply Ho.
    - intros o Ho. rewrite !lookup_insert_ne; [done| |]; intros <-; by apply Ho.
    - intros o x Ho Hx. rewrite HΘ', HΘ'' in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
      rewrite Hnr0, Hnr0' in Hx. destruct b'.
      + destruct Hx as [Hx|Hx]; [rewrite decide_False in Hx by done; done|].
        rewrite decide_True in Hx by done. injection Hx as <-. simpl. split.
        { rewrite lookup_insert_ne by done. rewrite lookup_insert_eq. done. }
        exists (sbranch b s1 s2, sel_pt k b). split_and!.
        * left. rewrite HΘ'. unfold cdual. simpl. by rewrite decide_True.
        * done.
        * by apply sdual_sym.
      + destruct Hx as [Hx|Hx]; [|rewrite decide_False in Hx by done; done].
        rewrite decide_True in Hx by done. injection Hx as <-. simpl. split.
        { by rewrite lookup_insert_eq. }
        exists (sbranch b r1 r2, bra_pt (pt_dual k) b). split_and!.
        * right. rewrite HΘ''. unfold cdual. simpl. by rewrite decide_True.
        * unfold sel_pt, bra_pt. by rewrite pt_dual_dual.
        * done.
  Qed.

  Lemma tenv_end_comp_iff Θ Θ1 Θ2 o x :
    tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ →
    tenv_end Θ o = Some x ↔ tenv_end Θ1 o = Some x ∨ tenv_end Θ2 o = Some x.
  Proof.
    intros Hcp Hb. split; [by apply tenv_end_comp_inv|].
    intros [H|H]; [by eapply tenv_end_comp_l|by eapply tenv_end_comp_r].
  Qed.

  Lemma tenv_end_lookup Θ d o x :
    tenv_bipol Θ → Θ !! d = Some o → (o = One x ∨ (∃ y, o = Both x y) ∨ (∃ y, o = Both y x)) →
    tenv_end Θ (d, pt_pol x.2) = Some x.
  Proof.
    intros Hb Hd Ho. pose proof (Hb d) as Hbd. unfold tenv_end. simpl. rewrite Hd.
    destruct Ho as [->|[(y & ->)|(y & ->)]].
    - by rewrite bool_decide_true.
    - by rewrite bool_decide_true.
    - specialize (Hbd y x Hd). rewrite bool_decide_false by done. by rewrite bool_decide_true.
  Qed.

  (** The rest of a receiver and the payload of a sender compose. *)
  Lemma merge_cond Θa Θb ta tb ea eb :
    M !! ta = Some ea → M !! tb = Some eb → ta ≠ tb → tenv_bipol Θa → tenv_bipol Θb →
    (∀ o x, tenv_end Θa o = Some x → tenv_end (A ta) o = Some x) →
    (∀ o x, tenv_end Θb o = Some x → tenv_end (A tb) o = Some x) →
    ∀ d oa ob, Θa !! d = Some oa → Θb !! d = Some ob →
      ∃ e1 e2, oa = One e1 ∧ ob = One e2 ∧ e1.2 = pt_dual e2.2 ∧ sdual e1.1 e2.1.
  Proof.
    intros Ha Hb Hab Hba Hbb HA HB d oa ob Hoa Hob.
    assert (∀ x y, (oa = One x ∨ (∃ z, oa = Both x z) ∨ (∃ z, oa = Both z x)) →
                   (ob = One y ∨ (∃ z, ob = Both y z) ∨ (∃ z, ob = Both z y)) →
                   pt_pol x.2 ≠ pt_pol y.2) as Hne.
    { intros x y Hx Hy Hp. pose proof (HA _ _ (tenv_end_lookup _ _ _ _ Hba Hoa Hx)) as H1.
      pose proof (HB _ _ (tenv_end_lookup _ _ _ _ Hbb Hob Hy)) as H2. rewrite Hp in H1.
      by destruct (lfc_uniq _ _ _ _ _ _ _ Hc ta tb ea eb _ _ _ Ha Hb H1 H2). }
    destruct oa as [x|x1 x2], ob as [y|y1 y2].
    - exists x, y. split_and!; [done|done| |].
      + assert (pt_pol x.2 ≠ pt_pol y.2) as Hp by (apply Hne; by left).
        pose proof (HA _ _ (tenv_end_lookup _ _ _ _ Hba Hoa (or_introl eq_refl))) as H1.
        pose proof (HB _ _ (tenv_end_lookup _ _ _ _ Hbb Hob (or_introl eq_refl))) as H2.
        assert ((d, pt_pol y.2) = cdual (d, pt_pol x.2)) as Hdc.
        { unfold cdual. simpl. f_equal. by destruct (pt_pol x.2), (pt_pol y.2). }
        rewrite Hdc in H2. destruct (lfc_partner_at _ _ _ _ _ _ _ Hc ta ea _ x tb eb y Ha H1 Hb H2).
        by apply eq_dual_sym.
      + assert (pt_pol x.2 ≠ pt_pol y.2) as Hp by (apply Hne; by left).
        pose proof (HA _ _ (tenv_end_lookup _ _ _ _ Hba Hoa (or_introl eq_refl))) as H1.
        pose proof (HB _ _ (tenv_end_lookup _ _ _ _ Hbb Hob (or_introl eq_refl))) as H2.
        assert ((d, pt_pol y.2) = cdual (d, pt_pol x.2)) as Hdc.
        { unfold cdual. simpl. f_equal. by destruct (pt_pol x.2), (pt_pol y.2). }
        rewrite Hdc in H2. by destruct (lfc_partner_at _ _ _ _ _ _ _ Hc ta ea _ x tb eb y Ha H1 Hb H2).
    - exfalso. pose proof (Hbb d y1 y2 Hob).
      pose proof (Hne x y1 (or_introl eq_refl) (or_intror (or_introl (ex_intro _ y2 eq_refl)))).
      pose proof (Hne x y2 (or_introl eq_refl) (or_intror (or_intror (ex_intro _ y1 eq_refl)))).
      destruct (pt_pol x.2), (pt_pol y1.2), (pt_pol y2.2); congruence.
    - exfalso. pose proof (Hba d x1 x2 Hoa).
      pose proof (Hne x1 y (or_intror (or_introl (ex_intro _ x2 eq_refl))) (or_introl eq_refl)).
      pose proof (Hne x2 y (or_intror (or_intror (ex_intro _ x1 eq_refl))) (or_introl eq_refl)).
      destruct (pt_pol x1.2), (pt_pol x2.2), (pt_pol y.2); congruence.
    - exfalso. pose proof (Hba d x1 x2 Hoa).
      pose proof (Hne x1 y1 (or_intror (or_introl (ex_intro _ x2 eq_refl)))
        (or_intror (or_introl (ex_intro _ y2 eq_refl)))).
      pose proof (Hne x2 y1 (or_intror (or_intror (ex_intro _ x1 eq_refl)))
        (or_intror (or_introl (ex_intro _ y2 eq_refl)))).
      destruct (pt_pol x1.2), (pt_pol x2.2), (pt_pol y1.2); congruence.
  Qed.

  Lemma no_chan_none Θ c : (∀ b, (c, b) ∉ tenv_ends Θ) → Θ !! c = None ∧ ∀ b, tenv_end Θ (c, b) = None.
  Proof.
    intros H. split.
    - apply not_elem_of_dom. rewrite <-tenv_ends_dom. intros ([c' b] & Hc' & Hin)%elem_of_map.
      simpl in Hc'. subst c'. by apply (H b).
    - intros b. destruct (tenv_end Θ (c, b)) eqn:E; [|done]. exfalso. apply (H b).
      apply tenv_ends_end. by eexists.
  Qed.

  (** ** message *)
  Lemma step_msg i j c b v e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SSend (c, b) v)) e' → tstep f (LSess (SRecv (c, negb b) v)) f' →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
      (C, <[j := f']> (<[i := e']> M)) A' U.
  Proof.
    intros Hij He Hf Hse Hsf.
    pose proof (st_sess i e _ e' He Hse) as (Θr & Θ1 & Θ2 & m & Uu & s & k & Θ' & Hhd & Hcomp & HV & Hext & HE).
    simpl in HV, HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θ1r & mr & Ur & sr & kr & Hhdj & Hrecv).
    destruct (st_rest i e _ _ _ _ He Hhd) as (s0 & Hu & Hexti & Hxi & Hoi & Hends & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (r0 & Hur & Hextj & Hxj & Hoj & Hendsj & Hrj).
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e (c, b) _ j f _ He Hxi Hf Hxj) as [Hk' Hsd].
    simpl in Hk'. subst kr.
    destruct (sdual_snd_rcv _ _ _ _ _ _ _ _ Hsd Hu Hur) as (<- & Hteq & Hss).
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    pose proof (tenv_bipol_ext_l _ _ _ _ Hexti (st_bipol i e He)) as Hbr.
    pose proof (tenv_bipol_ext_l _ _ _ _ Hextj (st_bipol j f Hf)) as Hbr'.
    destruct (tenv_ends_comp _ _ _ Hcomp Hbr) as [Hu12 Hd12].
    assert (∀ b', (c, b') ∉ tenv_ends Θr) as Hnr.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = b)) as [->|Hb]; [set_solver|].
      assert (b' = negb b) as -> by (by destruct b, b').
      apply (Hdisj (c, negb b)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ tenv_ends Θ1r) as Hnr'.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb b)) as [->|Hb]; [set_solver|].
      assert (b' = b) as -> by (by destruct b, b').
      apply (Hdisj (c, b)); [done|set_solver]. }
    destruct (no_chan_none Θ1 c) as [_ Hn1]; [intros b'; rewrite Hu12 in Hnr; set_solver|].
    destruct (no_chan_none Θ2 c) as [Hc2 Hn2]; [intros b'; rewrite Hu12 in Hnr; set_solver|].
    destruct (no_chan_none Θ1r c) as [Hc1r Hn1r]; [done|].
    set (Θ1c := <[c := One (sr, pt_shift 1 (pt_dual k))]> Θ1r).
    assert (tenv_ext Θ1r c (sr, pt_shift 1 (pt_dual k)) Θ1c) as Hext1c by (left; by split).
    assert (Hcomp'' : tenv_comp (@eq point) (tenv_merge Θ1c Θ2) Θ1c Θ2).
    { apply tenv_comp_merge. intros d oa ob Hoa Hob.
      destruct (decide (d = c)) as [->|Hdc]; [by rewrite Hc2 in Hob|].
      unfold Θ1c in Hoa. rewrite lookup_insert_ne in Hoa by done.
      refine (merge_cond Θ1r Θ2 j i f e Hf He (not_eq_sym Hij) Hbr' (tenv_bipol_comp_r _ _ _ _ Hcomp Hbr)
        _ _ d oa ob Hoa Hob).
      - intros o x Hx. rewrite Hrj; [done|]. intros ->. by rewrite Hn1r in Hx.
      - intros o x Hx. rewrite Hri; [|intros ->; by rewrite Hn2 in Hx].
        by apply (tenv_end_comp_r _ _ _ _ _ Hcomp Hbr). }
    assert (LVrel (S n) W Θ2 (payload_at m Ur (pt_dual k)) v) as HVr.
    { rewrite payload_at_dual. eapply LVrel_teq; [apply HW| |exact HV]. by apply teq_ty_inst. }
    pose proof (Hrecv W (S n) Θ2 Θ1c (tenv_merge Θ1c Θ2) (wext_refl W HW) (le_n _) Hext1c Hcomp'' HVr)
      as HEj.
    set (Θ'' := tenv_merge Θ1c Θ2). fold Θ'' in HEj, Hcomp''.
    pose proof (LErel_S_fit _ _ _ _ _ _ HE) as Hfit. pose proof (LErel_S_fit _ _ _ _ _ _ HEj) as Hfitj.
    pose proof (tenv_bipol_comp_l _ _ _ _ Hcomp'' (proj2 Hfitj)) as Hb1c.
    assert (pt_pol (pt_shift 1 k) = b) as Hpk.
    { destruct Hhd as [_ Hp]. simpl in Hp. by rewrite <-Hp. }
    assert (pt_pol (pt_shift 1 (pt_dual k)) = negb b) as Hpk'.
    { destruct Hhd as [_ Hp]. simpl in Hp. by rewrite <-Hp. }
    assert (HΘ' : ∀ o, tenv_end Θ' o = if decide (o = (c, b)) then Some (s, pt_shift 1 k)
                                       else tenv_end Θ1 o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext (proj2 Hfit)). cbn [snd]. by rewrite Hpk. }
    assert (HΘ1c : ∀ o, tenv_end Θ1c o = if decide (o = (c, negb b))
                                         then Some (sr, pt_shift 1 (pt_dual k)) else tenv_end Θ1r o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext1c Hb1c). cbn [snd]. by rewrite Hpk'. }
    assert (HΘ'' : ∀ o x, tenv_end Θ'' o = Some x ↔ tenv_end Θ1c o = Some x ∨ tenv_end Θ2 o = Some x)
      by (intros o x; apply (tenv_end_comp_iff _ _ _ _ _ Hcomp'' (proj2 Hfitj))).
    destruct (tenv_ends_ext _ _ _ _ Hext (proj2 Hfit)) as [He1 _].
    rewrite (proj1 Hfit) in He1. cbn [snd] in He1. rewrite Hpk in He1.
    destruct (tenv_ends_comp _ _ _ Hcomp'' (proj2 Hfitj)) as [He2 _].
    destruct (tenv_ends_ext _ _ _ _ Hext1c Hb1c) as [He3 _]. cbn [snd] in He3. rewrite Hpk' in He3.
    rewrite (proj1 Hfitj), He3 in He2.
    assert (π !! (c, b) = Some k) as Hπk by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi).
    assert (π !! (c, negb b) = Some (pt_dual k)) as Hπk'
      by apply (lf_pt _ _ _ _ _ _ _ _ Hc j f _ _ Hf Hxj).
    assert (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)) =
            alter (pt_shift 1) (c, true) (alter (pt_shift 1) (c, false) π)) as Hpu.
    { unfold pupd.
      destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_send in Hoa as ->.
      destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_recv in Hoa' as ->.
      destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold pev2; rewrite ?Ha, ?Ha'; done. }
    assert (Hπ' : ∀ o, o.1 = c → (alter (pt_shift 1) (c, true) (alter (pt_shift 1) (c, false) π)) !! o =
                                 pt_shift 1 <$> π !! o).
    { intros [c' []] Ho; simpl in Ho; subst c'.
      - by rewrite lookup_alter_eq, lookup_alter_ne.
      - by rewrite lookup_alter_ne, lookup_alter_eq. }
    exists (eupd (eupd A i Θ') j Θ'').
    rewrite Hpu.
    eapply (two_frame i j e f e' f' Θ' Θ'' c); try done.
    - eapply LErel_down; [|exact HE]. lia.
    - eapply LErel_down; [|exact HEj]. lia.
    - rewrite He1, He2. rewrite Hu12 in Hends.
      intros o Ho. apply elem_of_union. apply elem_of_union in Ho as [Ho|Ho].
      + apply elem_of_union in Ho as [Ho|Ho]; [left; set_solver|apply elem_of_singleton in Ho as ->; by left].
      + apply elem_of_union in Ho as [Ho|Ho]; [|left; set_solver].
        apply elem_of_union in Ho as [Ho|Ho]; [right; set_solver|apply elem_of_singleton in Ho as ->; by right].
    - rewrite He1, He2. rewrite Hu12 in Hends, Hnr.
      intros o Ho1 Ho2. apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_union in Ho2 as [Ho2|Ho2].
      + apply elem_of_union in Ho2 as [Ho2|Ho2].
        * apply (Hdisj o); set_solver.
        * apply elem_of_singleton in Ho2 as ->. apply (Hnr (negb b)). set_solver.
      + by apply (Hd12 o).
      + apply elem_of_singleton in Ho1 as ->. apply elem_of_union in Ho2 as [Ho2|Ho2].
        * by apply (Hnr' b).
        * apply elem_of_singleton in Ho2. simpl in Ho2. injection Ho2 as Hb. by destruct b.
      + apply elem_of_singleton in Ho1 as ->. apply (Hnr b). set_solver.
    - by left.
    - intros t g Hti Htj Hg. by apply (st_cowner i j e f c b t g).
    - intros o x Ho. rewrite HΘ', HΘ'', HΘ1c, !decide_False by (intros ->; by apply Ho).
      rewrite (Hri o), (Hrj o) by (intros ->; by apply Ho).
      rewrite (tenv_end_comp_iff _ _ _ _ _ Hcomp Hbr). naive_solver.
    - intros o Ho. destruct o as [c' []]; simpl in Ho; rewrite ?lookup_alter_ne; try done;
        intros [=]; by apply Ho.
    - intros o x Ho Hx. rewrite HΘ', HΘ'', HΘ1c in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
      rewrite Hn1, Hn1r, Hn2 in Hx. rewrite Hπ' by done.
      destruct (decide ((c, b') = (c, b))) as [Heq|Hneq].
      + injection Heq as ->. destruct Hx as [Hx|[Hx|Hx]]; [|by rewrite decide_False in Hx by (destruct b; done)|done].
        injection Hx as <-. simpl. rewrite Hπk. split; [done|].
        exists (sr, pt_shift 1 (pt_dual k)). split_and!; [|done|done].
        right. apply HΘ''. left. rewrite HΘ1c. unfold cdual. simpl. by rewrite decide_True.
      + destruct Hx as [Hx|[Hx|Hx]]; [done| |done].
        destruct (decide ((c, b') = (c, negb b))) as [Heq'|]; [|done].
        injection Heq' as ->. injection Hx as <-. simpl. rewrite Hπk'. split; [done|].
        exists (s, pt_shift 1 k). split_and!; [|by rewrite pt_dual_shift, pt_dual_dual|by apply sdual_sym].
        left. rewrite HΘ'. unfold cdual. simpl. rewrite negb_involutive. by rewrite decide_True.
  Qed.

  (** ** link *)
  Lemma st_link_data i e c bc d bd e' :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' →
    ∃ Θ1 xc xd, (c, bc) ≠ (d, bd) ∧ tenv_end (A i) (c, bc) = Some xc ∧
      tenv_end (A i) (d, bd) = Some xd ∧ xc.2 = pt_dual xd.2 ∧ sdual xc.1 xd.1 ∧
      tenv_end Θ1 (c, bc) = None ∧ tenv_end Θ1 (d, bd) = None ∧
      (∀ o, o ≠ (c, bc) → o ≠ (d, bd) → tenv_end (A i) o = tenv_end Θ1 o) ∧
      tenv_ends Θ1 = fends e ∖ {[(c, bc); (d, bd)]} ∧
      LErel (S (S n)) W Θ1 (U i) ∅ e'.
  Proof.
    intros He Hst.
    destruct (st_link i e _ e' He Hst) as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & Hcd & H1 & H2 & Hsd & Hk & HE).
    simpl in HE.
    pose proof (st_bipol i e He) as Hb. pose proof (tenv_bipol_ext_l _ _ _ _ H2 Hb) as Hbm.
    assert ((c1, pt_pol kc) ≠ (d1, pt_pol kd)) as H12.
    { intros [= _ Hp]. rewrite Hk, pt_pol_dual in Hp. by destruct (pt_pol kd). }
    assert (tenv_end (A i) (c1, pt_pol kc) = Some (sc, kc)) as Hx1
      by apply (tenv_end_ext_eq _ _ _ _ H2 Hb).
    assert (tenv_end (A i) (d1, pt_pol kd) = Some (sd, kd)) as Hx2.
    { rewrite (tenv_end_ext_ne _ _ _ _ _ H2 Hb) by (intros H; by apply H12).
      apply (tenv_end_ext_eq _ _ _ _ H1 Hbm). }
    assert (tenv_end Θ1 (c1, pt_pol kc) = None) as Hn1.
    { rewrite <-(tenv_end_ext_ne _ _ _ _ _ H1 Hbm) by done. apply (tenv_end_ext_none _ _ _ _ H2 Hb). }
    assert (tenv_end Θ1 (d1, pt_pol kd) = None) as Hn2 by apply (tenv_end_ext_none _ _ _ _ H1 Hbm).
    assert (∀ o, o ≠ (c1, pt_pol kc) → o ≠ (d1, pt_pol kd) → tenv_end (A i) o = tenv_end Θ1 o) as Hr.
    { intros o Ho1 Ho2. rewrite (tenv_end_ext_ne _ _ _ _ _ H2 Hb) by done.
      by rewrite (tenv_end_ext_ne _ _ _ _ _ H1 Hbm) by done. }
    destruct (tenv_ends_ext _ _ _ _ H2 Hb) as [Hu2 Hm2].
    destruct (tenv_ends_ext _ _ _ _ H1 Hbm) as [Hu1 Hm1]. cbn [snd] in *.
    assert (tenv_ends Θ1 = fends e ∖ {[(c1, pt_pol kc); (d1, pt_pol kd)]}) as Hends.
    { rewrite (st_ends i e He), Hu2, Hu1. rewrite Hu1 in Hm2.
      apply set_eq. intros o. split; [|set_solver].
      intros Ho. apply elem_of_difference. split; [set_solver|].
      intros Hin. apply elem_of_union in Hin as [Hin|Hin]; apply elem_of_singleton in Hin as ->.
      - apply Hm2. set_solver.
      - by apply Hm1. }
    destruct (upair_eq_inv _ _ _ _ (eq_sym Hcd) H12) as [[Hc1 Hd1]|[Hc1 Hd1]].
    - exists Θ1, (sc, kc), (sd, kd). rewrite <-Hc1, <-Hd1.
      split_and!; try done. simpl. by apply sdual_sym.
    - exists Θ1, (sd, kd), (sc, kc). rewrite <-Hc1, <-Hd1.
      split_and!; try done.
      all: try (simpl; by apply eq_dual_sym).
      all: try (rewrite Hends; set_solver).
      all: intros o Ho1 Ho2; by apply Hr.
  Qed.

  Lemma sdual_link a b y1 y2 : sdual a b → sdual a y1 → sdual b y2 → sdual y1 y2.
  Proof.
    intros Hab Ha Hb. apply sdual_seq_dual.
    apply sdual_seq_dual in Hab, Ha, Hb.
    apply seq_dual in Ha. rewrite dual_involutive in Ha. apply seq_sym in Ha.
    apply seq_dual in Hab. rewrite dual_involutive in Hab.
    eapply seq_trans; [exact Ha|]. eapply seq_trans; [exact Hab|exact Hb].
  Qed.

  (** A self-link holds both ends of c and closes it. *)
  Lemma step_link_self i e c bc bd e' :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (c, bd)]})) e' → c ∈ C →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c c <$> <[i := e']> M))
      (C ∖ {[c]}, chsubst c c <$> <[i := e']> M) A' U.
  Proof.
    intros He Hst HcC.
    destruct (st_link_data i e c bc c bd e' He Hst)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & _ & _ & _ & _ & Hr & Hends & HE).
    assert (bd = negb bc) as -> by (destruct bc, bd; simpl; try done; by contradiction Hne).
    assert (Hfm : chsubst c c <$> <[i := e']> M = <[i := e']> M).
    { apply map_eq. intros t. rewrite lookup_fmap. destruct (<[i:=e']> M !! t); simpl; [|done].
      by rewrite chsubst_refl. }
    rewrite Hfm.
    assert (pupd π (C, M) {[i]} (C ∖ {[c]}, <[i := e']> M) = delete (c, true) (delete (c, false) π)) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. apply offers_link in Ho as (o1 & o2 & -> & _).
      simpl. assert (C ∖ (C ∖ {[c]}) = {[c]}) as ->.
      { apply set_eq. intros x. destruct (decide (x = c)) as [->|]; set_solver. }
      by rewrite elements_singleton. }
    pose proof (LErel_S_fit _ _ _ _ _ _ HE) as Hfit.
    assert (∀ b', (c, b') ∉ fends e') as Hnc.
    { intros b' Hb'. rewrite <-(proj1 Hfit), Hends in Hb'. destruct b', bc; set_solver. }
    assert (Hoth : ∀ t g, t ≠ i → M !! t = Some g → c ∉ fchans g).
    { intros t g Hti Hg Hcg. apply fends_of_fchans in Hcg as [b' Hb'].
      apply (st_disj t i g e Hti Hg He (c, b')); [done|].
      destruct b', bc; [apply (st_held i e _ _ He Hxc)|apply (st_held i e _ _ He Hxd)
        |apply (st_held i e _ _ He Hxd)|apply (st_held i e _ _ He Hxc)]. }
    exists (eupd A i Θ1).
    apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∖ {[c]}, <[i := e']> M) A _ U U (cends c) Hc);
      simpl.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite eupd_eq.
        eapply LErel_down; [|exact HE]. lia.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply st_down.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. by rewrite eupd_eq.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply st_fit.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|].
      rewrite lookup_insert_ne in Hf by done. by apply (st_ty t f).
    - apply (disj_frame M _ {[i]} st_disj).
      + intros t Ht. rewrite lookup_insert_ne; set_solver.
      + intros p f t g Hp Ht Hf Hg. apply elem_of_singleton in Hp as ->.
        rewrite lookup_insert_eq in Hf. injection Hf as <-.
        rewrite <-(proj1 Hfit), Hends. pose proof (st_disj i t e g ltac:(set_solver) He Hg). set_solver.
      + intros p p' f f' Hp Hp' Hpp. set_solver.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. pose proof (st_closed i e He).
        assert (fchans e' ⊆ fchans e).
        { rewrite !fchans_fends, <-(proj1 Hfit), Hends. intros x (o & -> & Ho)%elem_of_map.
          apply elem_of_map. exists o. set_solver. }
        pose proof (fchans_not e' c Hnc). set_solver.
      + rewrite lookup_insert_ne in Hf by done. pose proof (st_closed t f Hf). pose proof (Hoth t f Hti Hf).
        set_solver.
    - intros o. apply cends_cdual.
    - intros o x0 Ho.
      assert (HI : ∀ i', i' ∈ ({[i]} : gset nat) → is_Some (M !! i'))
        by (intros i' ->%elem_of_singleton; by eexists).
      assert (HI' : ∀ i', i' ∈ ({[i]} : gset nat) → is_Some (<[i:=e']> M !! i'))
        by (intros i' ->%elem_of_singleton; rewrite lookup_insert_eq; by eexists).
      rewrite (ent_split _ (<[i:=e']> M) (eupd A i Θ1) {[i]} o x0 HI'), (ent_split C M A {[i]} o x0 HI).
      rewrite (others_ext (<[i:=e']> M) M (eupd A i Θ1) A);
        [|intros t Ht; rewrite lookup_insert_ne; set_solver|intros t Ht; rewrite eupd_ne; set_solver].
      assert (tenv_end Θ1 o = tenv_end (A i) o) as Hθ.
      { symmetry. apply Hr; intros ->; apply Ho, elem_of_cends; done. }
      split; intros [(i' & Hi' & Hx)|Ho']; [|by right| |by right];
        apply elem_of_singleton in Hi' as ->; left; exists i; (split; [by apply elem_of_singleton|]).
      + by rewrite eupd_eq, Hθ in Hx.
      + by rewrite eupd_eq, Hθ.
    - intros [c' b'] Ho. rewrite !lookup_delete_ne; [done| |]; intros [= <- _]; apply Ho;
        apply elem_of_cends; done.
    - intros o x0 Ho%elem_of_cends (t & f & Hf & Hx). exfalso.
      destruct (decide (t = i)) as [->|Hti].
      + rewrite eupd_eq in Hx. simpl in Hf. rewrite lookup_insert_eq in Hf. injection Hf as <-.
        assert (o ∈ tenv_ends Θ1) as Hin by (apply tenv_ends_end; by eexists).
        rewrite (proj1 Hfit) in Hin. destruct o as [c' b']. simpl in Ho. subst c'. by apply (Hnc b').
      + rewrite eupd_ne in Hx by done. simpl in Hf. rewrite lookup_insert_ne in Hf by done.
        destruct o as [c' b']. simpl in Ho. subst c'.
        by rewrite (st_nomention t f c Hf (Hoth t f Hti Hf)) in Hx.
  Qed.

  Ltac neq_tac := let H := fresh in intros H; injection H; intros; subst; try congruence;
    repeat match goal with b : bool |- _ => destruct b end; simpl in *; congruence.

  Lemma osub_eq_cases c d o1 o2 :
    c ≠ d → osub c d o1 = osub c d o2 → o1 ≠ o2 →
    (o1 = (c, o1.2) ∧ o2 = (d, o1.2)) ∨ (o1 = (d, o1.2) ∧ o2 = (c, o1.2)).
  Proof.
    destruct o1 as [c1 b1], o2 as [c2 b2]. unfold osub, csub. simpl. intros Hcd H Hne.
    injection H as H <-. repeat case_decide; subst; try congruence; auto.
  Qed.

  (** A link of two distinct channels: the peer of the removed end is
      renamed into the end of d the linker held. *)
  Lemma step_link_ne i e c bc d bd e' :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' → c ∈ C → c ≠ d →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M))
      (C ∖ {[c]}, chsubst c d <$> <[i := e']> M) A' U.
  Proof.
    intros He Hst HcC Hcd.
    destruct (st_link_data i e c bc d bd e' He Hst)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & Hsx & Hn1 & Hn2 & Hr & Hends & HE).
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd.
    simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    set (M'' := <[i := e']> M). set (A'' := eupd A i Θ1).
    assert (HM'' : ∀ t, M'' !! t = if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M''. destruct (decide (t = i)) as [->|]; [by rewrite lookup_insert_eq|].
      by rewrite lookup_insert_ne. }
    pose proof (LErel_S_fit _ _ _ _ _ _ HE) as Hfit.
    assert (Hthr : ∀ t g, M'' !! t = Some g →
              ∃ g0, M !! t = Some g0 ∧ LErel (S (S n)) W (A'' t) (U t) ∅ g ∧ tenv_fit (A'' t) g ∧
                fends g ⊆ fends g0 ∧ (U t = T ∨ U t = TUnit)).
    { intros t g Hg. rewrite HM'' in Hg. unfold A''. destruct (decide (t = i)) as [->|Hti].
      - injection Hg as <-. exists e. rewrite eupd_eq. split_and!; try done.
        + rewrite <-(proj1 Hfit), Hends. set_solver.
        + by apply (st_ty i e).
      - exists g. rewrite eupd_ne by done. split_and!; try done.
        + by apply st_rel. + by apply st_fit. + by apply (st_ty t g). }
    assert (Heq'' : ∀ t g o, M !! t = Some g → o ≠ (c, bc) → o ≠ (d, bd) →
              tenv_end (A'' t) o = tenv_end (A t) o).
    { intros t g o Hg Ho1 Ho2. unfold A''. destruct (decide (t = i)) as [->|Hti].
      - rewrite eupd_eq. symmetry. by apply Hr.
      - by rewrite eupd_ne. }
    assert (Hfree : ∀ t, tenv_end (A'' t) (c, bc) = None ∧ tenv_end (A'' t) (d, bd) = None ∨
                          M !! t = None).
    { intros t. destruct (M !! t) as [g|] eqn:Hg; [left|by right]. unfold A''.
      destruct (decide (t = i)) as [->|Hti]; [rewrite eupd_eq; done|]. rewrite eupd_ne by done.
      split.
      - destruct (tenv_end (A t) (c, bc)) eqn:Hy; [|done]. exfalso.
        by destruct (lfc_uniq _ _ _ _ _ _ _ Hc t i g e _ _ _ Hg He Hy Hxc).
      - destruct (tenv_end (A t) (d, bd)) eqn:Hy; [|done]. exfalso.
        by destruct (lfc_uniq _ _ _ _ _ _ _ Hc t i g e _ _ _ Hg He Hy Hxd). }
    assert (Hfree' : ∀ t g, M'' !! t = Some g →
              tenv_end (A'' t) (c, bc) = None ∧ tenv_end (A'' t) (d, bd) = None).
    { intros t g Hg. destruct (Hthr t g Hg) as (g0 & Hg0 & _). destruct (Hfree t) as [?|?]; congruence. }
    (* the single remaining end of c, and of d *)
    assert (Hone : ∀ t g ch b0, M'' !! t = Some g → tenv_end (A'' t) (ch, b0) = None →
              ∀ o, A'' t !! ch = Some o → ∃ y, o = One y ∧ tenv_end (A'' t) (ch, negb b0) = Some y).
    { intros t g ch b0 Hg Hn o Ho. destruct (Hthr t g Hg) as (g0 & _ & _ & [_ Hb] & _).
      destruct o as [y|y1 y2].
      - exists y. split; [done|]. pose proof (tenv_end_lookup _ _ _ y Hb Ho (or_introl eq_refl)) as Hy.
        destruct (decide (pt_pol y.2 = b0)) as [Hp|Hp]; [by rewrite Hp, Hn in Hy|].
        assert (pt_pol y.2 = negb b0) as <- by (by destruct (pt_pol y.2), b0). done.
      - exfalso. pose proof (Hb ch y1 y2 Ho).
        pose proof (tenv_end_lookup _ _ _ y1 Hb Ho (or_intror (or_introl (ex_intro _ y2 eq_refl)))) as H1.
        pose proof (tenv_end_lookup _ _ _ y2 Hb Ho (or_intror (or_intror (ex_intro _ y1 eq_refl)))) as H2.
        destruct (decide (pt_pol y1.2 = b0)) as [<-|Hp1]; [by rewrite Hn in H1|].
        destruct (decide (pt_pol y2.2 = b0)) as [<-|Hp2]; [by rewrite Hn in H2|].
        destruct (pt_pol y1.2), (pt_pol y2.2), b0; congruence. }
    assert (Hcond : ∀ t g, M'' !! t = Some g → ∀ oc od, A'' t !! c = Some oc → A'' t !! d = Some od →
              ∃ ec ed, oc = One ec ∧ od = One ed ∧ ec.2 = pt_dual ed.2 ∧ sdual ec.1 ed.1).
    { intros t g Hg oc od Hoc Hod. destruct (Hfree' t g Hg) as [Hfc Hfd].
      destruct (Hone t g c bc Hg Hfc oc Hoc) as (yc & -> & Hyc).
      destruct (Hone t g d bd Hg Hfd od Hod) as (yd & -> & Hyd).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _).
      rewrite (Heq'' t g0) in Hyc by (done || neq_tac).
      rewrite (Heq'' t g0) in Hyd by (done || neq_tac).
      assert ((c, negb bc) = cdual (c, bc)) as Hdc by done. rewrite Hdc in Hyc.
      assert ((d, negb bd) = cdual (d, bd)) as Hdd by done. rewrite Hdd in Hyd.
      destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e _ _ t g0 _ He Hxc Hg0 Hyc) as [Hyc2 Hyc1].
      destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e _ _ t g0 _ He Hxd Hg0 Hyd) as [Hyd2 Hyd1].
      exists yc, yd. split_and!; [done|done| |].
      - rewrite Hyc2, Hyd2, Hdx. by rewrite !pt_dual_dual.
      - by apply (sdual_link xc.1 xd.1). }
    assert (HEf : ∀ t g, M'' !! t = Some g →
              LErel (S (S n)) W (tenv_mv c d (A'' t)) (U t) ∅ (chsubst c d g)).
    { intros t g Hg. destruct (Hthr t g Hg) as (g0 & _ & HEg & _).
      apply (LErel_fuse _ W (A'' t)); [done|done| |done].
      apply tenv_move_mv; [done|]. intros oc Hoc od Hod. by apply (Hcond t g Hg). }
    assert (Hfitf : ∀ t g, M'' !! t = Some g → tenv_fit (tenv_mv c d (A'' t)) (chsubst c d g)).
    { intros t g Hg. apply (LErel_S_fit _ _ _ _ _ _ (HEf t g Hg)). }
    assert (Hmv : ∀ t g o, M'' !! t = Some g →
              tenv_end (tenv_mv c d (A'' t)) o =
                if decide (o.1 = c) then None
                else if decide (o.1 = d) then
                  match tenv_end (A'' t) (c, o.2) with Some x => Some x | None => tenv_end (A'' t) o end
                else tenv_end (A'' t) o).
    { intros t g o Hg. apply (tenv_end_mv c d (A'' t) o Hcd (proj2 (Hfitf t g Hg))).
      intros oc od Hoc Hod. destruct (Hcond t g Hg oc od Hoc Hod) as (ec & ed & -> & -> & _). eauto. }
    assert (HM' : ∀ t g', (chsubst c d <$> M'') !! t = Some g' → ∃ g, M'' !! t = Some g ∧ g' = chsubst c d g).
    { intros t g' Hg'. rewrite lookup_fmap in Hg'. destruct (M'' !! t) as [g|]; [|done].
      injection Hg' as <-. by exists g. }
    assert (HM'b : ∀ t g, M'' !! t = Some g → (chsubst c d <$> M'') !! t = Some (chsubst c d g)).
    { intros t g Hg. by rewrite lookup_fmap, Hg. }
    assert (HMM'' : ∀ t g, M !! t = Some g → ∃ g'', M'' !! t = Some g'').
    { intros t g Hg. rewrite HM''. case_decide; eauto. }
    assert (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> M'') = delete (c, true) (delete (c, false) π))
      as Hpu.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. apply offers_link in Ho as (o1 & o2 & -> & _).
      simpl. assert (C ∖ (C ∖ {[c]}) = {[c]}) as ->.
      { apply set_eq. intros x. destruct (decide (x = c)) as [->|]; set_solver. }
      by rewrite elements_singleton. }
    fold M''. rewrite Hpu.
    assert (d ∈ C) as HdC.
    { apply (st_closed i e He). apply fchans_of_fends with (o := (d, bd)). by apply (st_held i e _ xd). }
    exists (λ t, tenv_mv c d (A'' t)).
    apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∖ {[c]}, chsubst c d <$> M'') A _ U U
      (cends c ∪ cends d) Hc); simpl.
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->).
      eapply LErel_down; [|exact (HEf t g Hg)]. lia.
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->). by apply Hfitf.
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->). by destruct (Hthr t g Hg) as (? & _ & _ & _ & _ & ?).
    - intros t s g' h' Hts Hg' Hh'. destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (HM' s h' Hh') as (h & Hh & ->).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _ & [Hfg _] & Hsg & _).
      destruct (Hthr s h Hh) as (h0 & Hh0 & _ & [Hfh _] & Hsh & _).
      pose proof (st_disj t s g0 h0 Hts Hg0 Hh0) as Hd0.
      rewrite !fends_chsubst. intros o Ho1 Ho2.
      apply elem_of_map in Ho1 as (o1 & -> & Ho1). apply elem_of_map in Ho2 as (o2 & Ho12 & Ho2).
      destruct (decide (o1 = o2)) as [<-|Hne12]; [by apply (Hd0 o1); [apply Hsg|apply Hsh]|].
      assert (∀ u k b0, M'' !! u = Some k → (c, b0) ∈ fends k → b0 = negb bc) as Hcend.
      { intros u k b0 Hk Hin. destruct (Hthr u k Hk) as (_ & _ & _ & [Hfk _] & _).
        rewrite <-Hfk, tenv_ends_end in Hin. destruct (decide (b0 = bc)) as [->|Hb].
        - by rewrite (proj1 (Hfree' u k Hk)) in Hin; destruct Hin.
        - by destruct b0, bc. }
      assert (∀ u k, M'' !! u = Some k → (d, bd) ∉ fends k) as Hdend.
      { intros u k Hk Hin. destruct (Hthr u k Hk) as (_ & _ & _ & [Hfk _] & _).
        rewrite <-Hfk, tenv_ends_end in Hin. rewrite (proj2 (Hfree' u k Hk)) in Hin. by destruct Hin. }
      destruct (osub_eq_cases c d o1 o2 Hcd Ho12 Hne12) as [[E1 E2]|[E1 E2]].
      + rewrite E1 in Ho1. rewrite E2 in Ho2. pose proof (Hcend t g _ Hg Ho1) as Hb.
        rewrite Hb, <-Hbd in Ho2. by apply (Hdend s h Hh).
      + rewrite E1 in Ho1. rewrite E2 in Ho2. pose proof (Hcend s h _ Hh Ho2) as Hb.
        rewrite Hb, <-Hbd in Ho1. by apply (Hdend t g Hg).
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _ & _ & Hsg & _). pose proof (st_closed t g0 Hg0).
      pose proof (fchans_chsubst c d g).
      assert (fchans g ⊆ fchans g0).
      { rewrite !fchans_fends. intros x (o & -> & Ho)%elem_of_map. apply elem_of_map. exists o. set_solver. }
      set_solver.
    - intros o. rewrite !elem_of_union, <-!cends_cdual. done.
    - intros o x Ho. assert (o.1 ≠ c ∧ o.1 ≠ d) as [Hoc Hod].
      { split; intros Heq; apply Ho; apply elem_of_union; [left|right]; by apply elem_of_cends. }
      assert (o ≠ (c, bc) ∧ o ≠ (d, bd)) as [Ho1 Ho2] by (split; intros ->; done).
      split.
      + intros (t & g' & Hg' & Hx). destruct (HM' t g' Hg') as (g & Hg & ->).
        rewrite (Hmv t g o Hg), !decide_False in Hx by done.
        destruct (Hthr t g Hg) as (g0 & Hg0 & _). rewrite (Heq'' t g0) in Hx by done.
        by exists t, g0.
      + intros (t & g0 & Hg0 & Hx). destruct (HMM'' t g0 Hg0) as [g Hg].
        exists t, (chsubst c d g). split; [by apply HM'b|].
        rewrite (Hmv t g o Hg), !decide_False by done. by rewrite (Heq'' t g0).
    - intros o Ho. rewrite !lookup_delete_ne; [done| |]; intros <-; apply Ho; apply elem_of_union; left;
        by apply elem_of_cends.
    - intros o x Ho (t & g' & Hg' & Hx). destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _).
      rewrite (Hmv t g o Hg) in Hx. destruct o as [c' β]. simpl in Hx.
      destruct (decide (c' = c)) as [->|Hc']; [done|].
      destruct (decide (c' = d)) as [->|Hd'].
      2:{ exfalso. apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_cends in Ho; simpl in Ho; congruence. }
      rewrite !lookup_delete_ne by (intros [=]; congruence).
      (* the partners of the linker's two ends *)
      destruct (lfc_partner _ _ _ _ _ _ _ Hc i e _ _ He Hxc) as (s & gs & ys & Hgs & Hys & Hys2 & Hys1).
      destruct (lfc_partner _ _ _ _ _ _ _ Hc i e _ _ He Hxd) as (u & gu & yu & Hgu & Hyu & Hyu2 & Hyu1).
      destruct (HMM'' s gs Hgs) as [gs'' Hgs'']. destruct (HMM'' u gu Hgu) as [gu'' Hgu''].
      assert (cdual (c, bc) ≠ (c, bc) ∧ cdual (c, bc) ≠ (d, bd)) as [Hq1 Hq2]
        by (split; [apply cdual_ne|intros [=]; congruence]).
      assert (cdual (d, bd) ≠ (c, bc) ∧ cdual (d, bd) ≠ (d, bd)) as [Hq3 Hq4]
        by (split; [intros [=]; congruence|apply cdual_ne]).
      assert (Hys' : tenv_end (tenv_mv c d (A'' s)) (d, bd) = Some ys).
      { rewrite (Hmv s gs'' _ Hgs''). simpl. rewrite decide_False, decide_True by done.
        rewrite (Heq'' s gs); [|done|rewrite Hbd; intros [= H]; destruct bc; simpl in H; congruence
          |intros [= H]; congruence]. rewrite Hbd. unfold cdual in Hys. simpl in Hys.
        by rewrite Hys. }
      assert (Hyu' : tenv_end (tenv_mv c d (A'' u)) (d, negb bd) = Some yu).
      { rewrite (Hmv u gu'' _ Hgu''). simpl. rewrite decide_False, decide_True by done.
        assert (negb bd = bc) as -> by (rewrite Hbd; by destruct bc).
        rewrite (proj1 (Hfree' u gu'' Hgu'')).
        assert (bc = negb bd) as Hbc by (rewrite Hbd; by destruct bc). rewrite Hbc.
        rewrite (Heq'' u gu) by (done || neq_tac). done. }
      destruct (decide (β = bd)) as [->|Hβ].
      + (* the renamed peer of the removed end *)
        assert (tenv_end (A'' t) (c, bd) = Some x) as Hxt.
        { destruct (tenv_end (A'' t) (c, bd)) eqn:E; [done|]. by rewrite (proj2 (Hfree' t g Hg)) in Hx. }
        rewrite Hbd in Hxt. rewrite (Heq'' t g0) in Hxt by (done || neq_tac).
        destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e _ _ t g0 _ He Hxc Hg0 Hxt) as [Hx2 Hx1].
        assert (x.2 = xd.2) as Hx2' by (rewrite Hx2, Hdx; by rewrite pt_dual_dual).
        split; [rewrite Hx2'; by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxd)|].
        exists yu. split_and!.
        * exists u, (chsubst c d gu''). split; [by apply HM'b|]. done.
        * by rewrite Hyu2, Hx2'.
        * by apply (sdual_link xc.1 xd.1).
      + (* the peer of the linker's end of d keeps its entry *)
        assert (β = negb bd) as -> by (by destruct β, bd).
        assert (tenv_end (A'' t) (c, negb bd) = None) as Hnt.
        { assert (negb bd = bc) as -> by (rewrite Hbd; by destruct bc). apply (proj1 (Hfree' t g Hg)). }
        rewrite Hnt in Hx. rewrite (Heq'' t g0) in Hx by (done || neq_tac).
        destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e _ _ t g0 _ He Hxd Hg0 Hx) as [Hx2 Hx1].
        split; [by apply (lf_pt _ _ _ _ _ _ _ _ Hc t g0 _ _ Hg0 Hx)|].
        exists ys. split_and!.
        * exists s, (chsubst c d gs''). split; [by apply HM'b|]. unfold cdual. simpl.
          by rewrite negb_involutive.
        * rewrite Hys2, Hx2, Hdx. done.
        * apply (sdual_link xd.1 xc.1); [by apply sdual_sym|done|done].
  Qed.

End step.

(** ** Preservation of the soup along a step *)

Theorem lfconf_step n W T π q A U L q' :
  strict W → LFconf (S (S n)) W ∅ T π q A U → istep q L q' →
  ∃ A' U', LFconf n W ∅ T (pupd π q L q') q' A' U'.
Proof.
  intros HW Hc Hst. destruct q as [C M].
  inversion Hst as [C0 M0 i e e' Hi Hs|C0 M0 i e c x e' Hi Hs HC Hcs|C0 M0 i j e v e' Hi Hs Hj
    |C0 M0 i j c b v e e' f f' Hij Hi Hj He Hf|C0 M0 i j c b e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j c β b e e' f f' Hij Hi Hj He Hf|C0 M0 i e c bc d bd e' Hi Hs HC]; subst.
  - exists A, U. by apply (step_beta n W HW T π C M A U Hc i e e').
  - destruct (step_new n W HW T π C M A U Hc i e c x e' Hi Hs HC Hcs) as [A' ?]. by exists A', U.
  - by apply (step_spawn n W HW T π C M A U Hc i j e v e').
  - destruct (step_msg n W HW T π C M A U Hc i j c b v e e' f f') as [A' ?]; try done. by exists A', U.
  - destruct (step_close n W HW T π C M A U Hc i j c b e e' f f') as [A' ?]; try done. by exists A', U.
  - destruct (step_choice n W HW T π C M A U Hc i j c β b e e' f f') as [A' ?]; try done.
    by exists A', U.
  - destruct (decide (c = d)) as [<-|Hcd].
    + destruct (step_link_self n W HW T π C M A U Hc i e c bc bd e') as [A' ?]; try done.
      by exists A', U.
    + destruct (step_link_ne n W HW T π C M A U Hc i e c bc d bd e') as [A' ?]; try done.
      by exists A', U.
Qed.

(** ** One placement for every index (§16.5)

    Along a run, π_k is computed from π by [pupd] at every step. It does
    not depend on the index, and every position of the run carries the
    soup at every index, at π_k. *)

Fixpoint prun (π : gmap cend point) (r : nat → config) (l : nat → gset nat) (k : nat)
    : gmap cend point :=
  match k with 0 => π | S k' => pupd (prun π r l k') (r k') (l k') (r (S k')) end.

Lemma pupd_stuck π q : pupd π q ∅ q = π.
Proof. unfold pupd, pev_of. by rewrite elements_empty. Qed.

Theorem lfconf_run W T π r l :
  strict W → maximal r l →
  (∀ n, ∃ A U, LFconf n W ∅ T π (r 0) A U) →
  ∀ k n, ∃ A U, LFconf n W ∅ T (prun π r l k) (r k) A U.
Proof.
  intros HW Hmax H0 k. induction k as [|k IH]; [done|]. intros n. simpl.
  destruct (IH (S (S n))) as (A & U & Hc).
  destruct (Hmax k) as [Hst|(_ & Heq & Hl)].
  - by apply (lfconf_step n W T _ (r k) A U (l k)).
  - rewrite Heq, Hl, pupd_stuck. exists A, U. eapply LFconf_down; [|exact Hc]. lia.
Qed.

(** ** Local progress of one soup *)

Definition skind (σ : slabel) : hkind :=
  match σ with
  | SSend _ _ => KdSnd | SRecv _ _ => KdRcv | SClos _ => KdEnd
  | SSel _ _ => KdPlus | SBra _ _ => KdWith | SLink _ => KdStuck
  end.

(** A selected entry is the entry of the label's end, of the label's kind. *)
Lemma selects_info Θ σ k ek o :
  selects Θ σ k → tenv_entry Θ k = Some ek → sl_end σ = Some o →
  k.1 = o.1 ∧ pt_pol ek.2 = o.2 ∧ kind (hd ek.1) = skind σ.
Proof.
  intros Hsel Hk Ho. destruct σ; simpl in Hsel, Ho; try discriminate; injection Ho as <-.
  - destruct Hsel as (H1 & x & m & T & s & Hx & Hp & Hu). rewrite Hk in Hx. injection Hx as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hsel as (H1 & x & m & T & s & Hx & Hp & Hu). rewrite Hk in Hx. injection Hx as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hsel as (H1 & x & Hx & Hp & Hu & _). rewrite Hk in Hx. injection Hx as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hsel as (H1 & x & s1 & s2 & Hx & Hp & Hu). rewrite Hk in Hx. injection Hx as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hsel as (H1 & x & s1 & s2 & Hx & Hp & Hu). rewrite Hk in Hx. injection Hx as <-.
    by rewrite (hd_of _ _ Hu).
Qed.

Lemma sl_end_some σ : (∀ cd, σ ≠ SLink cd) → ∃ o, sl_end σ = Some o.
Proof. destruct σ; simpl; try (intros; by eexists). intros H. by destruct (H cd). Qed.

(** The ends a redex acts on are ends of the term. *)
Lemma act_aends_fends e a S : act e = Some a → aends a = Some S → S ⊆ fends e.
Proof.
  induction e as [| | |c b|x|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
    |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; simpl; intros Ha HS; try discriminate.
  - destruct (is_val e1); [destruct (is_val e2)|].
    + repeat (case_match; simplify_eq/=); set_solver.
    + specialize (IH2 Ha HS). set_solver.
    + specialize (IH1 Ha HS). set_solver.
  - destruct (is_val e1).
    + specialize (IH2 Ha HS). set_solver.
    + specialize (IH1 Ha HS). set_solver.
  - destruct (is_val e1); [repeat (case_match; simplify_eq/=); done|].
    specialize (IH1 Ha HS). set_solver.
  - destruct (is_val e1); [repeat (case_match; simplify_eq/=); done|].
    specialize (IH1 Ha HS). set_solver.
  - by apply IH.
  - by apply IH.
  - destruct (is_val e); [repeat (case_match; simplify_eq/=); done|].
    specialize (IH Ha HS). set_solver.
Qed.

Section progress.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S n) W ∅ T π q A U).

  Lemma lp_closed t e : q.2 !! t = Some e → fchans e ⊆ q.1.
  Proof. intros He. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc t e He) as H. set_solver. Qed.

  Lemma lp_link t e : q.2 !! t = Some e → link_t e → enabled q t.
  Proof.
    intros He (cd & e' & Hst). destruct (act_step _ _ _ Hst) as (a & Ha & Ho).
    destruct a; simpl in Ho; try done.
    apply (admin_enabled q t e _ He Ha I). intros c' d' [= <- <-]. left.
    apply (lp_closed t e He). apply fchans_of_fends.
    apply (act_aends_fends e (ALink c d) {[c; d]} Ha eq_refl). set_solver.
  Qed.
End progress.
