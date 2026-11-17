(** * The lock-free judgment on thread soups (lock-freedom plan §16.3, §16.5, §17.3, §18)

    A configuration is a soup of threads. [LFconf n W Σ T π q A U] says
    that every thread t of q is in the live term relation at index n
    under its environment [A t] and its type [U t], that the
    environments are polarized and hold pairwise disjoint ends, that
    every held end sits at the point π gives it, and that every end of an
    internal channel has a partner end, held by some thread, at the dual
    point and with a dual session type. The soup reads environments only,
    never the term of a thread (decision of 2026-11-16).

    [LFsoupAt] adds the fuel conjunct of §17.3. Each thread carries its own
    points [P t] and counters [F t] on exactly the ends of its
    environment, and its ticket count [K t] (plan §18.3). FuelE holds at
    them. [LFsoup] takes for π the union of the maps [P t] ([ppts]).
    [LFP] fixes the threads, P, F and K outside the index, so a thread
    holds the same ends at every index, and the points lie outside the
    index because the program names the point of every [new] (sharp
    edges 173).

    [pupd] computes π, [fstep] P and F, and [kstep] K along one step.
    They read the step off the redexes of the participants, so they are
    functions of the run. [lfsoup_step] preserves the soup from index
    n + 2 to index n. A thread that does not take part keeps its
    environment, its counters and its tickets, up to the renaming of a
    link ([LErel_fuse]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Criterion lockfree.LocalProgress.
From LRGV Require Import lockfree.LFFuel.
From LRGV Require Export liveness.LiveAdequacy liveness.LiveFuse liveness.LiveTermRules
  liveness.LiveConsts liveness.LiveInternalize liveness.LivePTerm.

Set Default Proof Using "Type".

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


(** The points of the ends of an environment. *)
Definition tenv_points (Θ : tenv) : gmap cend point :=
  map_imap (λ o (_ : unit), snd <$> tenv_end Θ o) (gset_to_gmap () (tenv_ends Θ)).

Lemma lookup_tenv_points Θ o : tenv_points Θ !! o = snd <$> tenv_end Θ o.
Proof.
  unfold tenv_points. rewrite map_lookup_imap.
  destruct (decide (o ∈ tenv_ends Θ)) as [Ho|Ho].
  - rewrite (proj2 (lookup_gset_to_gmap_Some _ _ _ _) (conj Ho eq_refl)). done.
  - rewrite (proj2 (lookup_gset_to_gmap_None _ _ _) Ho). simpl.
    destruct (tenv_end Θ o) eqn:E; [|done]. exfalso. apply Ho, tenv_ends_end. by eexists.
Qed.

Lemma dom_tenv_points Θ : dom (tenv_points Θ) = tenv_ends Θ.
Proof.
  apply set_eq. intros o. by rewrite elem_of_dom, lookup_tenv_points, fmap_is_Some, tenv_ends_end.
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

Lemma tenv_end_insert_ne Θ c eo o : o.1 ≠ c → tenv_end (<[c := eo]> Θ) o = tenv_end Θ o.
Proof. intros H. unfold tenv_end. by rewrite lookup_insert_ne by done. Qed.

Lemma tenv_end_delete_ne Θ c o : o.1 ≠ c → tenv_end (delete c Θ) o = tenv_end Θ o.
Proof. intros H. unfold tenv_end. by rewrite lookup_delete_ne by done. Qed.

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

(** ** The soup *)

(** The soup reads environments only (decision of 2026-11-16). A thread
    holds the ends of its environment, the environments of two threads
    hold disjoint ends, every channel of an environment is a channel of
    the configuration or of Σ, and every end of an internal channel has
    a partner end, held by some thread, at the dual point and with a
    dual session type. An end of an external channel, one of Σ, is held
    at the entry of Σ, and every entry of Σ is held by some thread
    (decision 2026-11-16, under delegation). Every point a thread holds
    an end at is known to W ([lf_known]): a new channel sits at a known
    point (O-New), and a received end at a field of a known carrier.
    Nothing reads the term of a thread except the live relation
    [lf_rel]. *)
Record LFconf (n : nat) (W : world) (Σ : senv) (T : ty) (π : gmap cend point)
    (q : config) (A : nat → tenv) (U : nat → ty) : Prop := LFConf {
  lf_prim : prim T;
  lf_rel t e : q.2 !! t = Some e → LErel n W (A t) (U t) ∅ e;
  lf_bipol t e : q.2 !! t = Some e → tenv_bipol (A t);
  lf_ty t e : q.2 !! t = Some e → U t = T ∨ U t = TUnit;
  lf_pt t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → π !! o = Some x.2;
  lf_disj t s e es : t ≠ s → q.2 !! t = Some e → q.2 !! s = Some es →
    tenv_ends (A t) ## tenv_ends (A s);
  lf_pair t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → o.1 ∉ dom Σ →
    ∃ s es y, q.2 !! s = Some es ∧ tenv_end (A s) (cdual o) = Some y ∧
      y.2 = pt_dual x.2 ∧ sdual x.1 y.1;
  lf_closed t e : q.2 !! t = Some e → dom (A t) ⊆ q.1 ∪ dom Σ;
  lf_sig t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → o.1 ∈ dom Σ →
    Σ !! o.1 = Some x;
  lf_own c x : Σ !! c = Some x →
    ∃ t e, q.2 !! t = Some e ∧ tenv_end (A t) (c, pt_pol x.2) = Some x;
  lf_known t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → pt_known W x.2
}.

(** The fuel conjunct (§17.3). Each thread t carries its own points
    [P t], counters [F t] and tickets [K t], outside the index, and FuelE
    holds at them. The points and counters are kept on exactly the ends
    of the thread's environment, so the ends a thread holds are the same
    at every index. *)
Definition lf_fuelc (n : nat) (W : world) (π : gmap cend point) (P : nat → gmap cend point)
    (F : nat → gmap cend fuel) (K : nat → nat) (A : nat → tenv) (q : config) : Prop :=
  ∀ t e, q.2 !! t = Some e →
    FuelT n W (P t) (F t) (K t) e ∧ dom (P t) = tenv_ends (A t) ∧ dom (F t) = tenv_ends (A t) ∧
    ∀ o, o ∈ tenv_ends (A t) → P t !! o = π !! o.

Definition LFsoupAt (n : nat) (W : world) (Σ : senv) (T : ty) (π : gmap cend point)
    (P : nat → gmap cend point) (F : nat → gmap cend fuel) (K : nat → nat) (q : config) : Prop :=
  ∃ A U, LFconf n W Σ T π q A U ∧ lf_fuelc n W π P F K A q.

(** The points of the held ends, the union of the per-thread point maps. *)
Definition ppts (P : nat → gmap cend point) (q : config) : gmap cend point :=
  foldr (λ t acc, P t ∪ acc) ∅ (elements (dom q.2)).

(** The soup with the points read off the per-thread maps P. *)
Definition LFsoup (n : nat) (W : world) (Σ : senv) (T : ty)
    (P : nat → gmap cend point) (F : nat → gmap cend fuel) (K : nat → nat) (q : config) : Prop :=
  LFsoupAt n W Σ T (ppts P q) P F K q.

(** The lock-free judgment (§17.8). The budgets are read in W. The
    threads, their points, counters and tickets are fixed outside the
    index, the environments and the session types are chosen at each
    index. The points of the held ends are the union of the per-thread
    maps P. *)
Definition LFP (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  (∀ n, LPrel n W Σ T p) ∧ ∃ q P F K, erase q = p ∧ ∀ n, LFsoup n W Σ T P F K q.

Lemma ppts_lookup P q t e o v :
  q.2 !! t = Some e → P t !! o = Some v →
  (∀ s es, q.2 !! s = Some es → s ≠ t → P s !! o = None) → ppts P q !! o = Some v.
Proof.
  intros He Hv Hu. unfold ppts.
  assert (t ∈ elements (dom q.2)) as Ht by (apply elem_of_elements, elem_of_dom; eauto).
  assert (∀ s, s ∈ elements (dom q.2) → s ≠ t → P s !! o = None) as Hu'.
  { intros s' Hs' Hne. apply elem_of_elements, elem_of_dom in Hs' as [es Hes]. by apply (Hu s' es). }
  clear He Hu. revert Ht Hu'. generalize (elements (dom q.2)) as l.
  induction l as [|s' l IH]; intros Ht Hu'; [by apply not_elem_of_nil in Ht|].
  simpl. destruct (decide (s' = t)) as [->|Hne].
  - by apply lookup_union_Some_l.
  - rewrite lookup_union_r by (apply Hu'; [left|done]). apply IH.
    + by apply elem_of_cons in Ht as [?|?].
    + intros s'' Hs'' Hne'. apply Hu'; [by right|done].
Qed.

(** On the held ends, the union of the point maps is the point map of
    the soup. *)
Lemma lf_ppts n W Σ T π q A U P F K t e o :
  LFconf n W Σ T π q A U → lf_fuelc n W π P F K A q →
  q.2 !! t = Some e → o ∈ tenv_ends (A t) → ppts P q !! o = π !! o.
Proof.
  intros Hc HF He Ho. destruct (HF t e He) as (_ & HdP & _ & Hpt).
  assert (is_Some (P t !! o)) as [v Hv] by (apply elem_of_dom; by rewrite HdP).
  rewrite <-Hpt, Hv by done. apply (ppts_lookup P q t e); [done|done|].
  intros s es Hes Hst. apply not_elem_of_dom. destruct (HF s es Hes) as (_ & HdPs & _). rewrite HdPs.
  intros Hos. by apply (lf_disj _ _ _ _ _ _ _ _ Hc s t es e Hst Hes He o).
Qed.

(** A soup at any point map π is a soup at the union of its point maps. *)
Lemma LFsoupAt_ppts n W Σ T π P F K q : LFsoupAt n W Σ T π P F K q → LFsoup n W Σ T P F K q.
Proof.
  intros (A & U & Hc & HF).
  pose proof (λ t e o, lf_ppts n W Σ T π q A U P F K t e o Hc HF) as Hpp.
  exists A, U. destruct Hc as [Hp Hr Hb Hty Hpt Hd Hpair Hcl Hsig Hown].
  split; [split|]; try done.
  - intros t e o x He Hx. rewrite (Hpp t e o He) by (apply tenv_ends_end; by eexists). by apply (Hpt t e).
  - intros t e He. destruct (HF t e He) as (H1 & H2 & H3 & H4). split_and!; try done.
    intros o Ho. rewrite (Hpp t e o He Ho). by apply H4.
Qed.

(** ** Monotonicity in the index *)

Lemma LFconf_down n m W Σ T π q A U : m ≤ n → LFconf n W Σ T π q A U → LFconf m W Σ T π q A U.
Proof.
  intros Hmn [? Hr ? ? ? ? ? ? ? ? ?]. split; try done.
  intros t e He. eapply LErel_down; [done|]. by apply Hr.
Qed.

Lemma lf_fuelc_down n m W π P F K A q : m ≤ n → lf_fuelc n W π P F K A q → lf_fuelc m W π P F K A q.
Proof.
  intros Hmn H t e He. destruct (H t e He) as (H1 & H2). split; [|done]. by apply (FuelE_down m n).
Qed.

Lemma LFsoupAt_down n m W Σ T π P F K q :
  m ≤ n → LFsoupAt n W Σ T π P F K q → LFsoupAt m W Σ T π P F K q.
Proof.
  intros Hmn (A & U & Hc & Hf). exists A, U. split.
  - by eapply LFconf_down.
  - by eapply lf_fuelc_down.
Qed.

Theorem LFsoup_down n m W Σ T P F K q : m ≤ n → LFsoup n W Σ T P F K q → LFsoup m W Σ T P F K q.
Proof. apply LFsoupAt_down. Qed.

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

(** ** Channels and ends of an environment *)

Lemma dom_tenv_ends Θ c : c ∈ dom Θ ↔ ∃ b, (c, b) ∈ tenv_ends Θ.
Proof.
  rewrite <-tenv_ends_dom, elem_of_map. split.
  - intros ([c' b] & -> & H). by exists b.
  - intros [b H]. by exists (c, b).
Qed.

Lemma dom_sub_ends Θ1 Θ : tenv_ends Θ1 ⊆ tenv_ends Θ → dom Θ1 ⊆ dom Θ.
Proof. intros H c. rewrite !dom_tenv_ends. intros [b Hb]. exists b. by apply H. Qed.

Lemma dom_sub_ends2 Θ1 Θ Θ' : tenv_ends Θ1 ⊆ tenv_ends Θ ∪ tenv_ends Θ' → dom Θ1 ⊆ dom Θ ∪ dom Θ'.
Proof.
  intros H c. rewrite elem_of_union, !dom_tenv_ends. intros [b Hb].
  apply H, elem_of_union in Hb as [?|?]; [left|right]; by exists b.
Qed.

Lemma tenv_end_ends Θ o x : tenv_end Θ o = Some x → o ∈ tenv_ends Θ.
Proof. intros H. apply tenv_ends_end. by eexists. Qed.

Lemma tenv_end_none_ends Θ o : o ∉ tenv_ends Θ → tenv_end Θ o = None.
Proof. rewrite tenv_ends_end. destruct (tenv_end Θ o); [|done]. intros H. by destruct H. Qed.

Lemma tenv_bipol_ext_none Θ1 c e Θ :
  tenv_ext Θ1 c e Θ → Θ1 !! c = None → tenv_bipol Θ1 → tenv_bipol Θ.
Proof.
  intros [[_ ->]|(e' & He' & _)] Hn Hb; [|congruence].
  intros c' e1 e2 H. destruct (decide (c' = c)) as [->|Hne].
  - by rewrite lookup_insert_eq in H.
  - rewrite lookup_insert_ne in H by done. by apply (Hb c').
Qed.

Lemma no_chan_none Θ c : (∀ b, (c, b) ∉ tenv_ends Θ) → Θ !! c = None ∧ ∀ b, tenv_end Θ (c, b) = None.
Proof.
  intros H. split.
  - apply not_elem_of_dom. rewrite dom_tenv_ends. intros [b Hb]. by apply (H b).
  - intros b. apply tenv_end_none_ends, H.
Qed.

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
  Proof. apply (lf_bipol _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma lfc_uniq t s e es o x y :
    q.2 !! t = Some e → q.2 !! s = Some es →
    tenv_end (A t) o = Some x → tenv_end (A s) o = Some y → t = s ∧ x = y.
  Proof.
    intros He Hes Hx Hy. destruct (decide (t = s)) as [<-|Hts].
    - rewrite He in Hes. injection Hes as <-. split; congruence.
    - exfalso. apply (lf_disj _ _ _ _ _ _ _ _ Hc t s e es Hts He Hes o);
        by eapply tenv_end_ends.
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

  Lemma lfc_closed t e : q.2 !! t = Some e → dom (A t) ⊆ q.1.
  Proof.
    intros He. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc t e He) as H.
    rewrite dom_empty_L, union_empty_r_L in H. done.
  Qed.

  Lemma lfc_closed_end t e o x : q.2 !! t = Some e → tenv_end (A t) o = Some x → o.1 ∈ q.1.
  Proof. intros He Hx. apply (lfc_closed t e He). by eapply tenv_end_dom. Qed.
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
  (∀ t e, q'.2 !! t = Some e → tenv_bipol (A' t)) →
  (∀ t e, q'.2 !! t = Some e → U1 t = T ∨ U1 t = TUnit) →
  (∀ t s e es, t ≠ s → q'.2 !! t = Some e → q'.2 !! s = Some es →
     tenv_ends (A' t) ## tenv_ends (A' s)) →
  (∀ t e, q'.2 !! t = Some e → dom (A' t) ⊆ q'.1) →
  (∀ o, o ∈ Ch ↔ cdual o ∈ Ch) →
  (∀ o x, o ∉ Ch → ent q' A' o x ↔ ent q A o x) →
  (∀ o, o ∉ Ch → π' !! o = π !! o) →
  (∀ o x, o ∈ Ch → ent q' A' o x →
     π' !! o = Some x.2 ∧ ∃ y, ent q' A' (cdual o) y ∧ y.2 = pt_dual x.2 ∧ sdual x.1 y.1) →
  (∀ o x, o ∈ Ch → ent q' A' o x → pt_known W x.2) →
  LFconf m W ∅ T π' q' A' U1.
Proof.
  intros Hc Hrel Hbip Hty Hdisj Hcl HCh Hent Hπ HChk HKn. split; try done.
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
  - intros t e o x He Hx. destruct (decide (o ∈ Ch)) as [Ho|Ho].
    + exact (HKn o x Ho (ex_intro _ t (ex_intro _ e (conj He Hx)))).
    + destruct (proj1 (Hent o x Ho) (ex_intro _ t (ex_intro _ e (conj He Hx))))
        as (t0 & e0 & He0 & Hx0).
      apply (lf_known _ _ _ _ _ _ _ _ Hc t0 e0 o x He0 Hx0).
Qed.

(** ** Updates of the environments *)

Definition eupd {X : Type} (A : nat → X) (t : nat) (x : X) : nat → X :=
  λ u, if decide (u = t) then x else A u.

Lemma eupd_eq {X : Type} (A : nat → X) t x : eupd A t x t = x.
Proof. unfold eupd. by rewrite decide_True. Qed.

Lemma eupd_ne {X : Type} (A : nat → X) t x u : u ≠ t → eupd A t x u = A u.
Proof. intros H. unfold eupd. by rewrite decide_False. Qed.

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

Lemma disj_frame (M M' : gmap nat expr) (X X' : nat → gset cend) (I : gset nat) :
  (∀ t s e es, t ≠ s → M !! t = Some e → M !! s = Some es → X t ## X s) →
  (∀ t, t ∉ I → M' !! t = M !! t) → (∀ t, t ∉ I → X' t = X t) →
  (∀ p e' t e, p ∈ I → t ∉ I → M' !! p = Some e' → M !! t = Some e → X' p ## X t) →
  (∀ p p' e e', p ∈ I → p' ∈ I → p ≠ p' → M' !! p = Some e → M' !! p' = Some e' → X' p ## X' p') →
  ∀ t s e es, t ≠ s → M' !! t = Some e → M' !! s = Some es → X' t ## X' s.
Proof.
  intros Hd HM HX Hpt Hpp t s e es Hts He Hes.
  destruct (decide (t ∈ I)) as [Ht|Ht], (decide (s ∈ I)) as [Hs|Hs].
  - by apply (Hpp t s e es).
  - rewrite HM in Hes by done. rewrite (HX s Hs). by apply (Hpt t e s es).
  - rewrite HM in He by done. rewrite (HX t Ht). symmetry. by apply (Hpt s es t e).
  - rewrite HM in He, Hes by done. rewrite (HX t Ht), (HX s Hs). by apply (Hd t s e es).
Qed.

(** ** Counters along a step

    The fuel of a thread is read in its own points and counters,
    [P t] and [F t], which a run computes step by step, outside the
    index, as π is. [fstep] is the update: the participants move by
    [fupd], a spawned thread gets [fchild], a receiver adds the sender's
    payload at its counters minus one, and a link renames the peer of the
    removed end in every map ([kren]). No step writes the counters of a
    thread that does not take part in it (plan §18.3). *)

Definition kren {Y : Type} (g : chan → chan) (m : gmap cend Y) : gmap cend Y :=
  list_to_map ((λ ov : cend * Y, ((g ov.1.1, ov.1.2), ov.2)) <$> map_to_list m).

Definition fmsg (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel)
    (s t : nat) (o o' : cend) (w : expr) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  let rs := fupd W (P s) (F s) (LSess (SSend o w)) in
  let rr := fupd W (P t) (F t) (LSess (SRecv o' w)) in
  (eupd (eupd P s rs.1) t (rr.1 ∪ mres (fends w) (P s)),
   eupd (eupd F s rs.2) t (rr.2 ∪ (ftick <$> mres (fends w) (F s)))).

Definition f2 (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel)
    (s t : nat) (σs σt : slabel) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  let rs := fupd W (P s) (F s) (LSess σs) in
  let rt := fupd W (P t) (F t) (LSess σt) in
  (eupd (eupd P s rs.1) t rt.1, eupd (eupd F s rs.2) t rt.2).

Definition fpair (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel)
    (i j : nat) (ei ej : expr) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  match act ei, act ej with
  | Some (ASend o w), Some (ARecv o') => fmsg W P F i j o o' w
  | Some (ARecv o'), Some (ASend o w) => fmsg W P F j i o o' w
  | Some (AClos o), Some (AClos o') => f2 W P F i j (SClos o) (SClos o')
  | Some (ASel o b), Some (ABra o') => f2 W P F i j (SSel o b) (SBra o' b)
  | Some (ABra o'), Some (ASel o b) => f2 W P F j i (SSel o b) (SBra o' b)
  | _, _ => (P, F)
  end.

Definition fsingle (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel)
    (q q' : config) (i : nat) (e : expr) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  match act e with
  | Some (ANew x) =>
      let r := fupd W (P i) (F i) (LNew (default "" (head (elements (q'.1 ∖ q.1)))) x) in
      (eupd P i r.1, eupd F i r.2)
  | Some (ASpawn w) =>
      let j := default 0 (head (elements (dom q'.2 ∖ dom q.2))) in
      let r := fupd W (P i) (F i) (LSpawn w) in
      let ch := fchild (P i) (F i) w in
      (eupd (eupd P i r.1) j ch.1, eupd (eupd F i r.2) j ch.2)
  | Some (ALink o1 o2) =>
      let c := default "" (head (elements (q.1 ∖ q'.1))) in
      let d := if decide (o1.1 = c) then o2.1 else o1.1 in
      let r := fupd W (P i) (F i) (LSess (SLink {[o1; o2]})) in
      (λ t, kren (csub c d) (eupd P i r.1 t), λ t, kren (csub c d) (eupd F i r.2 t))
  | _ => (P, F)
  end.

Definition fstep (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel)
    (q : config) (L : gset nat) (q' : config) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  match elements L with
  | [i] => match q.2 !! i with Some e => fsingle W P F q q' i e | None => (P, F) end
  | [i; j] => match q.2 !! i, q.2 !! j with Some ei, Some ej => fpair W P F i j ei ej | _, _ => (P, F) end
  | _ => (P, F)
  end.

(** The tickets along a step (plan §18.3). A link spends one ticket of
    the linker, a spawn gives ⌈K i/2⌉ to the child and keeps ⌊K i/2⌋, and
    every other step keeps every count. *)
Definition ksingle (K : nat → nat) (q q' : config) (i : nat) (e : expr) : nat → nat :=
  match act e with
  | Some (ASpawn _) =>
      let j := default 0 (head (elements (dom q'.2 ∖ dom q.2))) in
      eupd (eupd K i (Nat.div2 (K i))) j (Nat.div2 (S (K i)))
  | Some (ALink _ _) => eupd K i (K i - 1)
  | _ => K
  end.

Definition kstep (K : nat → nat) (q : config) (L : gset nat) (q' : config) : nat → nat :=
  match elements L with
  | [i] => match q.2 !! i with Some e => ksingle K q q' i e | None => K end
  | _ => K
  end.

(** [kinj] lives in LFFuel.v. *)
Lemma renk_kren {Y : Type} (g : chan → chan) (m : gmap cend Y) : kinj g m → renk g m (kren g m).
Proof.
  intros Hi. unfold kren. split.
  - intros o v Ho. apply elem_of_list_to_map_1'.
    + intros y ([o2 v2] & Heq & Hov)%list_elem_of_fmap. apply elem_of_map_to_list in Hov.
      simpl in Heq. assert (o2 = o) as ->.
      { apply (Hi o2 o v2 v Hov Ho). inversion Heq. by f_equal. }
      rewrite Ho in Hov. injection Hov as ->. by inversion Heq.
    + apply list_elem_of_fmap. exists (o, v). split; [done|]. by apply elem_of_map_to_list.
  - intros o' v Ho'. apply elem_of_list_to_map_2 in Ho'.
    apply list_elem_of_fmap in Ho' as ([o v'] & Heq & Hov). apply elem_of_map_to_list in Hov.
    simpl in Heq. injection Heq as -> ->. by exists o.
Qed.

Lemma kren_lookup {Y : Type} (g : chan → chan) (m : gmap cend Y) o v :
  kinj g m → m !! o = Some v → kren g m !! (g o.1, o.2) = Some v.
Proof. intros Hi Ho. by apply (renk_kren g m Hi). Qed.

Lemma kren_lookup_inv {Y : Type} (g : chan → chan) (m : gmap cend Y) o' v :
  kinj g m → kren g m !! o' = Some v → ∃ o, o' = (g o.1, o.2) ∧ m !! o = Some v.
Proof. intros Hi Ho. by apply (renk_kren g m Hi). Qed.

Lemma kren_dom {Y : Type} (g : chan → chan) (m : gmap cend Y) :
  kinj g m → dom (kren g m) = set_map (λ o : cend, (g o.1, o.2)) (dom m).
Proof.
  intros Hi. apply set_eq. intros o'. rewrite elem_of_map. split.
  - intros [v Hv]%elem_of_dom. destruct (kren_lookup_inv g m o' v Hi Hv) as (o & -> & Ho).
    exists o. split; [done|]. by apply elem_of_dom_2 in Ho.
  - intros (o & -> & [v Hv]%elem_of_dom). apply elem_of_dom. exists v. by apply kren_lookup.
Qed.

Lemma lookup_mres {Y : Type} (X : gset cend) (m : gmap cend Y) o :
  mres X m !! o = if decide (o ∈ X) then m !! o else None.
Proof.
  destruct (mres X m !! o) as [v|] eqn:E.
  - apply lookup_mres_Some in E as [E H]. by rewrite decide_True.
  - case_decide; [|done]. destruct (m !! o) as [v|] eqn:E'; [|done].
    exfalso. assert (mres X m !! o = Some v) by (by apply lookup_mres_Some). congruence.
Qed.

Lemma lookup_mrem {Y : Type} (X : gset cend) (m : gmap cend Y) o :
  mrem X m !! o = if decide (o ∈ X) then None else m !! o.
Proof.
  destruct (mrem X m !! o) as [v|] eqn:E.
  - apply lookup_mrem_Some in E as [E H]. by rewrite decide_False.
  - case_decide; [done|]. destruct (m !! o) as [v|] eqn:E'; [|done].
    exfalso. assert (mrem X m !! o = Some v) by (by apply lookup_mrem_Some). congruence.
Qed.

Lemma lf_fuelc_ext n W π P1 F1 P2 F2 K A q :
  (∀ t, P1 t = P2 t) → (∀ t, F1 t = F2 t) → lf_fuelc n W π P1 F1 K A q → lf_fuelc n W π P2 F2 K A q.
Proof. intros HP HF H t e He. rewrite <-HP, <-HF. by apply H. Qed.

Lemma fstep_single W P F q q' i :
  fstep W P F q {[i]} q' = match q.2 !! i with Some e => fsingle W P F q q' i e | None => (P, F) end.
Proof. unfold fstep. by rewrite elements_singleton. Qed.

Lemma fstep_pair W P F q q' i j ei ej :
  i ≠ j → q.2 !! i = Some ei → q.2 !! j = Some ej →
  fstep W P F q {[i; j]} q' = fpair W P F i j ei ej ∨ fstep W P F q {[i; j]} q' = fpair W P F j i ej ei.
Proof.
  intros Hij Hi Hj. unfold fstep.
  assert (elements ({[i; j]} : gset nat) = [i; j] ∨ elements ({[i; j]} : gset nat) = [j; i]) as [H|H].
  { apply Permutation_length_2_inv. symmetry.
    rewrite elements_union_singleton by set_solver. by rewrite elements_singleton. }
  - rewrite H, Hi, Hj. by left.
  - rewrite H, Hi, Hj. by right.
Qed.

(** The tickets along one step, read off its label. *)
Lemma kstep_one K q q' i e α e' :
  q.2 !! i = Some e → tstep e α e' →
  kstep K q {[i]} q' =
    match α with
    | LSpawn _ =>
        eupd (eupd K i (Nat.div2 (K i))) (default 0 (head (elements (dom q'.2 ∖ dom q.2))))
          (Nat.div2 (S (K i)))
    | LSess (SLink _) => eupd K i (K i - 1)
    | _ => K
    end.
Proof.
  intros He Hst. unfold kstep. rewrite elements_singleton, He. unfold ksingle.
  destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha.
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w], a; simpl in Ho; try done.
Qed.

Lemma kstep_pair K q q' i j : i ≠ j → kstep K q {[i; j]} q' = K.
Proof.
  intros Hij. unfold kstep.
  assert (elements ({[i; j]} : gset nat) = [i; j] ∨ elements ({[i; j]} : gset nat) = [j; i]) as [H|H].
  { apply Permutation_length_2_inv. symmetry.
    rewrite elements_union_singleton by set_solver. by rewrite elements_singleton. }
  all: by rewrite H.
Qed.

Lemma fupd_act W σ π φ o k :
  sl_end σ = Some o → mrem (sl_out σ) π !! o = Some k →
  fupd W π φ (LSess σ) =
    match sl_next σ k with
    | None => (delete o (mrem (sl_out σ) π), ftick <$> delete o (mrem (sl_out σ) φ))
    | Some (o', k') => (<[o' := k']> (delete o (mrem (sl_out σ) π)),
                        <[o' := w_bud W k']> (ftick <$> delete o (mrem (sl_out σ) φ)))
    end.
Proof. intros Ho Hk. unfold fupd, LFFuel.fact. by rewrite Ho, Hk. Qed.

Lemma f2_swap W P F i j σi σj :
  i ≠ j → (∀ t, (f2 W P F i j σi σj).1 t = (f2 W P F j i σj σi).1 t) ∧
          (∀ t, (f2 W P F i j σi σj).2 t = (f2 W P F j i σj σi).2 t).
Proof. intros Hij. unfold f2, eupd. simpl. split; intros t; repeat case_decide; congruence. Qed.

(** ** One step of a soup

    The soup at index n + 2 steps to the soup at index n. Every
    environment of the successor is the one the clause of the stepping
    thread gives, and the points and counters of every thread move by
    [fstep]. A thread that does not take part keeps its environment, up
    to the renaming of a link. *)

Section step.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (C : gset chan) (M : gmap nat expr) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S (S n)) W ∅ T π (C, M) A U).
  Context (P : nat → gmap cend point) (F : nat → gmap cend fuel) (K : nat → nat).
  Context (HF : lf_fuelc (S (S n)) W π P F K A (C, M)).

  Lemma st_rel t e : M !! t = Some e → LErel (S (S n)) W (A t) (U t) ∅ e.
  Proof. apply (lf_rel _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_step t e : M !! t = Some e → LEstep (LErel (S (S n))) (S n) W (A t) (U t) ∅ e.
  Proof. intros He. apply LErel_S_iff. by apply st_rel. Qed.

  Lemma st_down t e : M !! t = Some e → LErel n W (A t) (U t) ∅ e.
  Proof. intros He. eapply LErel_down; [|by apply st_rel]. lia. Qed.

  Lemma st_bipol t e : M !! t = Some e → tenv_bipol (A t).
  Proof. apply (lfc_bipol _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_closed t e : M !! t = Some e → dom (A t) ⊆ C.
  Proof. apply (lfc_closed _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_disj t s e es : t ≠ s → M !! t = Some e → M !! s = Some es →
    tenv_ends (A t) ## tenv_ends (A s).
  Proof. apply (lf_disj _ _ _ _ _ _ _ _ Hc). Qed.

  Lemma st_ty t e : M !! t = Some e → U t = T ∨ U t = TUnit.
  Proof. apply (lf_ty _ _ _ _ _ _ _ _ Hc). Qed.

  (** The clauses at W itself. *)
  Lemma st_beta t e e' : M !! t = Some e → tstep e LBeta e' → LErel (S (S n)) W (A t) (U t) ∅ e'.
  Proof.
    intros He Hst. destruct (st_step t e He W (wext_r_refl W)) as (_ & _ & Hb & _). auto.
  Qed.

  Lemma st_new t e c x e' :
    M !! t = Some e → tstep e (LNew c x) e' → c ∉ dom (A t) →
    pt_known W x ∧
    ∃ s s', sdual s s' ∧ LErel (S (S n)) W (<[c := Both (s, x) (s', pt_dual x)]> (A t)) (U t) ∅ e'.
  Proof.
    intros He Hst Hc'. destruct (st_step t e He W (wext_r_refl W)) as (_ & _ & _ & Hn & _).
    by apply (Hn c x e' Hst Hc').
  Qed.

  (** A spawned closure holds exactly its ends (V at the arrow). *)
  Lemma st_spawn t e w e' :
    M !! t = Some e → tstep e (LSpawn w) e' →
    ∃ Θ1 Θ2, tenv_comp (@eq point) (A t) Θ1 Θ2 ∧ tenv_ends Θ1 = fends w ∧
      LErel (S (S n)) W Θ1 TUnit ∅ (App w EUnit) ∧ LErel (S (S n)) W Θ2 (U t) ∅ e'.
  Proof.
    intros He Hst. destruct (st_step t e He W (wext_r_refl W)) as (_ & _ & _ & _ & Hsp & _).
    destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & Hcomp & Hv & HE).
    apply Vspawn_LVrel in Hv.
    exists Θ1, Θ2. split_and!; [done|by destruct (LVrel_fit _ _ _ _ _ Hv)| |done].
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

  Lemma ff t e : M !! t = Some e →
    FuelT (S (S n)) W (P t) (F t) (K t) e ∧ dom (P t) = tenv_ends (A t) ∧ dom (F t) = tenv_ends (A t) ∧
    ∀ o, o ∈ tenv_ends (A t) → P t !! o = π !! o.
  Proof. apply HF. Qed.

  Lemma ff_pt t e o x : M !! t = Some e → tenv_end (A t) o = Some x → P t !! o = Some x.2.
  Proof.
    intros He Hx. destruct (ff t e He) as (_ & _ & _ & H4). rewrite H4.
    - apply (lf_pt _ _ _ _ _ _ _ _ Hc t e o x He Hx).
    - by eapply tenv_end_ends.
  Qed.

  (** The fuel of the successor, from the fuel of the threads that step. *)
  Lemma ffr (q' : config) (π' : gmap cend point) (A' : nat → tenv) P' F' K' (I : gset nat) :
    (∀ t, t ∉ I → q'.2 !! t = M !! t ∧ A' t = A t ∧ P' t = P t ∧ F' t = F t ∧ K' t = K t) →
    (∀ t e o, t ∉ I → M !! t = Some e → o ∈ tenv_ends (A t) → π' !! o = π !! o) →
    (∀ p e', p ∈ I → q'.2 !! p = Some e' →
       FuelT n W (P' p) (F' p) (K' p) e' ∧ dom (P' p) = tenv_ends (A' p) ∧
       dom (F' p) = tenv_ends (A' p) ∧ ∀ o, o ∈ tenv_ends (A' p) → P' p !! o = π' !! o) →
    lf_fuelc n W π' P' F' K' A' q'.
  Proof.
    intros Hout Hπ Hin t e He. destruct (decide (t ∈ I)) as [Ht|Ht]; [by apply Hin|].
    destruct (Hout t Ht) as (Hq & -> & -> & -> & ->). rewrite Hq in He.
    destruct (ff t e He) as (H1 & H2 & H3 & H4). split_and!; [|done|done|].
    - apply (FuelE_down n (S (S n))); [lia|done].
    - intros o Ho. rewrite H4 by done. symmetry. by apply (Hπ t e).
  Qed.

  (** ** β *)
  Lemma step_beta i e e' :
    M !! i = Some e → tstep e LBeta e' →
    LFconf n W ∅ T (pupd π (C, M) {[i]} (C, <[i := e']> M)) (C, <[i := e']> M) A U ∧
    lf_fuelc n W (pupd π (C, M) {[i]} (C, <[i := e']> M))
      (fstep W P F (C, M) {[i]} (C, <[i := e']> M)).1
      (fstep W P F (C, M) {[i]} (C, <[i := e']> M)).2 K A (C, <[i := e']> M).
  Proof.
    intros He Hst. destruct (act_step _ _ _ Hst) as (a & Ha & Ho). apply offers_beta in Ho as ->.
    assert (pupd π (C, M) {[i]} (C, <[i := e']> M) = π) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1. by rewrite Ha. }
    assert (fstep W P F (C, M) {[i]} (C, <[i := e']> M) = (P, F)) as ->.
    { rewrite fstep_single. simpl. rewrite He. unfold fsingle. by rewrite Ha. }
    pose proof (st_beta i e e' He Hst) as HE'.
    assert (Hlk : ∀ t f, <[i := e']> M !! t = Some f → ∃ f0, M !! t = Some f0).
    { intros t f Hf. destruct (decide (t = i)) as [->|Hti]; [by exists e|].
      rewrite lookup_insert_ne in Hf by done. by exists f. }
    split.
    - apply (LFconf_frame (S (S n)) n W T π π (C, M) (C, <[i := e']> M) A A U U ∅ Hc); simpl.
      + intros t f Hf. destruct (decide (t = i)) as [->|Hti].
        * rewrite lookup_insert_eq in Hf. injection Hf as <-. eapply LErel_down; [|exact HE']. lia.
        * rewrite lookup_insert_ne in Hf by done. by apply st_down.
      + intros t f Hf. destruct (Hlk t f Hf) as [f0 Hf0]. by apply (st_bipol t f0).
      + intros t f Hf. destruct (Hlk t f Hf) as [f0 Hf0]. by apply (st_ty t f0).
      + intros t s f fs Hts Hf Hfs. destruct (Hlk t f Hf) as [f0 Hf0].
        destruct (Hlk s fs Hfs) as [fs0 Hfs0]. by apply (st_disj t s f0 fs0).
      + intros t f Hf. destruct (Hlk t f Hf) as [f0 Hf0]. by apply (st_closed t f0).
      + set_solver.
      + intros o x _. split.
        * intros (t & f & Hf & Hx). destruct (Hlk t f Hf) as [f0 Hf0]. by exists t, f0.
        * intros (t & f0 & Hf0 & Hx). exists t. destruct (decide (t = i)) as [->|Hti].
          -- exists e'. simpl. by rewrite lookup_insert_eq.
          -- exists f0. simpl. by rewrite lookup_insert_ne.
      + done.
      + set_solver.
      + set_solver.
    - apply (ffr _ π A P F K {[i]}).
      + intros t Ht. simpl. split_and!; [|done|done|done|done]. rewrite lookup_insert_ne; [done|set_solver].
      + done.
      + intros p f Hp Hf. apply elem_of_singleton in Hp as ->. simpl in Hf.
        rewrite lookup_insert_eq in Hf. injection Hf as <-.
        destruct (ff i e He) as (H1 & H2 & H3 & H4). split_and!; [|done|done|done].
        pose proof (lffuel_step (S n) W (P i) (F i) (K i) e H1 LBeta e' Hst ltac:(done) ltac:(done) ltac:(by intros ? ? [?|?])) as H. simpl in H.
        apply (FuelE_down n (S n)); [lia|done].
  Qed.

  (** ** new *)
  Lemma step_new i e c x e' :
    M !! i = Some e → tstep e (LNew c x) e' → c ∉ C →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M))
        (C ∪ {[c]}, <[i := e']> M) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M))
        (fstep W P F (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M)).1
        (fstep W P F (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M)).2 K A' (C ∪ {[c]}, <[i := e']> M).
  Proof.
    intros He Hst HcC.
    assert (Hnd : ∀ t f, M !! t = Some f → c ∉ dom (A t)).
    { intros t f Hf Hd. apply HcC, (st_closed t f Hf), Hd. }
    assert (Hnm : ∀ t f b, M !! t = Some f → (c, b) ∉ tenv_ends (A t)).
    { intros t f b Hf Hin. apply (Hnd t f Hf). apply dom_tenv_ends. by exists b. }
    destruct (st_new i e c x e' He Hst (Hnd i e He)) as (Hxk & s & s' & Hss & HE').
    set (Θn := <[c := Both (s, x) (s', pt_dual x)]> (A i)).
    assert (Hends : tenv_ends Θn = tenv_ends (A i) ∪ cends c).
    { unfold Θn. rewrite tenv_ends_new. unfold cends. destruct (pt_pol x); set_solver. }
    destruct (act_step _ _ _ Hst) as (a & Ha & Ho). apply offers_new in Ho as ->.
    assert ((C ∪ {[c]}) ∖ C = {[c]}) as HCc by set_solver.
    assert (pupd π (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M) =
            <[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> π)) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1. rewrite Ha.
      simpl. by rewrite HCc, elements_singleton. }
    rewrite fstep_single. simpl. rewrite He. unfold fsingle. rewrite Ha. simpl.
    rewrite HCc, elements_singleton. simpl.
    exists (eupd A i Θn). split.
    - apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∪ {[c]}, <[i := e']> M) A _ U U (cends c) Hc);
        simpl.
      + intros t f Hf. destruct (decide (t = i)) as [->|Hti].
        * rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite eupd_eq.
          eapply LErel_down; [|exact HE']. lia.
        * rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply (st_down).
      + intros t f Hf. destruct (decide (t = i)) as [->|Hti].
        * rewrite eupd_eq. apply tenv_bipol_insert_new, (st_bipol i e He).
        * rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply (st_bipol t f).
      + intros t f Hf. destruct (decide (t = i)) as [->|Hti].
        * by apply (st_ty i e).
        * rewrite lookup_insert_ne in Hf by done. by apply (st_ty t f).
      + apply (disj_frame M _ (λ t, tenv_ends (A t)) (λ t, tenv_ends (eupd A i Θn t)) {[i]} st_disj).
        * intros t Ht. rewrite lookup_insert_ne; set_solver.
        * intros t Ht. simpl. rewrite eupd_ne; set_solver.
        * intros p f t g Hp Ht Hf Hg. apply elem_of_singleton in Hp as ->. simpl.
          rewrite eupd_eq, Hends. assert (t ≠ i) by set_solver.
          pose proof (st_disj i t e g ltac:(done) He Hg).
          intros o Ho1 Ho2. apply elem_of_union in Ho1 as [Ho1|Ho1]; [set_solver|].
          apply elem_of_cends in Ho1. destruct o as [c' b']. simpl in Ho1. subst c'.
          by apply (Hnm t g b').
        * intros p p' f f' Hp Hp' Hpp. set_solver.
      + intros t f Hf. destruct (decide (t = i)) as [->|Hti].
        * rewrite eupd_eq. unfold Θn. rewrite dom_insert_L. pose proof (st_closed i e He). set_solver.
        * rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done.
          pose proof (st_closed t f Hf). set_solver.
      + intros o. apply cends_cdual.
      + intros o x0 Ho.
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
        * by rewrite eupd_eq, Hθ in Hx.
        * by rewrite eupd_eq, Hθ.
      + intros o Ho. assert (o ≠ (c, pt_pol x)) by (intros ->; apply Ho, elem_of_cends; done).
        assert (o ≠ (c, negb (pt_pol x))) by (intros ->; apply Ho, elem_of_cends; done).
        by rewrite !lookup_insert_ne by done.
      + intros o x0 Ho%elem_of_cends (t & f & Hf & Hx).
        assert (t = i) as ->.
        { destruct (decide (t = i)) as [->|Hti]; [done|]. simpl in Hf.
          rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne in Hx by done.
          destruct o as [c' b]. simpl in Ho. subst c'.
          by rewrite (tenv_end_none_ends _ _ (Hnm t f b Hf)) in Hx. }
        rewrite eupd_eq in Hx. unfold Θn in Hx. rewrite tenv_end_new in Hx.
        assert (Hent_i : ∀ o' y, tenv_end Θn o' = Some y → ent (C ∪ {[c]}, <[i:=e']> M) (eupd A i Θn) o' y).
        { intros o' y Hy. exists i, e'. simpl. rewrite lookup_insert_eq, eupd_eq. done. }
        destruct (decide (o = (c, pt_pol x))) as [->|H1].
        * injection Hx as <-. simpl. split; [by rewrite lookup_insert_eq|].
          exists (s', pt_dual x). split_and!; [|done|done]. apply Hent_i. unfold Θn.
          rewrite tenv_end_new. unfold cdual. simpl.
          rewrite decide_False by (intros [=]; by destruct (pt_pol x)). by rewrite decide_True.
        * destruct (decide (o = (c, negb (pt_pol x)))) as [->|H2].
          2:{ exfalso. destruct o as [c' b]. simpl in Ho. subst c'.
              destruct b, (pt_pol x); simpl in *; congruence. }
          injection Hx as <-. simpl. split.
          { rewrite lookup_insert_ne by (intros [=]; by destruct (pt_pol x)). by rewrite lookup_insert_eq. }
          exists (s, x). split_and!; [|by rewrite pt_dual_dual|by apply sdual_sym].
          apply Hent_i. unfold Θn. rewrite tenv_end_new. unfold cdual. simpl.
          rewrite negb_involutive. by rewrite decide_True.
      + intros o x0 Ho%elem_of_cends (t & f & Hf & Hx).
        assert (t = i) as ->.
        { destruct (decide (t = i)) as [->|Hti]; [done|]. simpl in Hf.
          rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne in Hx by done.
          destruct o as [c' b]. simpl in Ho. subst c'.
          by rewrite (tenv_end_none_ends _ _ (Hnm t f b Hf)) in Hx. }
        rewrite eupd_eq in Hx. unfold Θn in Hx. rewrite tenv_end_new in Hx.
        destruct (decide (o = (c, pt_pol x))); [injection Hx as <-; exact Hxk|].
        destruct (decide (o = (c, negb (pt_pol x)))); [injection Hx as <-; exact Hxk|].
        destruct o as [c' b]. simpl in Ho. subst c'. destruct b, (pt_pol x); simpl in *; congruence.
    - apply (ffr _ _ _ _ _ K {[i]}).
      + intros t Ht. simpl. rewrite lookup_insert_ne by set_solver. rewrite !eupd_ne by set_solver. done.
      + intros t f o Ht Hf Hof. assert (o.1 ≠ c) as Hoc.
        { intros Heq. destruct o as [c' b']. simpl in Heq. subst c'. by apply (Hnm t f b'). }
        rewrite !lookup_insert_ne; [done| |]; intros <-; done.
      + intros p f Hp Hf. apply elem_of_singleton in Hp as ->. simpl in Hf.
        rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite !eupd_eq.
        destruct (ff i e He) as (H1 & H2 & H3 & H4).
        (* the soup creates only fresh channels (plan §19.8, hole 2) *)
        assert (Hfr : ∀ c0 x0, LNew c x = LNew c0 x0 →
                  ((c0, true) ∉ dom (P i)) ∧ ((c0, false) ∉ dom (P i))).
        { intros c0 x0 [= <- <-]. rewrite H2. split; apply (Hnm i e _ He). }
        pose proof (lffuel_step (S n) W (P i) (F i) (K i) e H1 _ e' Hst ltac:(done) Hfr ltac:(by intros ? ? [?|?])) as H. simpl in H.
        split_and!.
        * apply (FuelE_down n (S n)); [lia|done].
        * rewrite Hends, !dom_insert_L, H2. unfold cends. destruct (pt_pol x); set_solver.
        * rewrite Hends, !dom_insert_L, H3. unfold cends. destruct (pt_pol x); set_solver.
        * intros o Ho. destruct (decide (o = (c, pt_pol x))) as [->|H5]; [by rewrite !lookup_insert_eq|].
          rewrite (lookup_insert_ne _ (c, pt_pol x)) by done. rewrite (lookup_insert_ne _ (c, pt_pol x)) by done.
          destruct (decide (o = (c, negb (pt_pol x)))) as [->|H6]; [by rewrite !lookup_insert_eq|].
          rewrite !lookup_insert_ne by done. apply H4.
          rewrite Hends in Ho. apply elem_of_union in Ho as [Ho|Ho]; [done|].
          exfalso. apply elem_of_cends in Ho. destruct o as [c' b']. simpl in Ho. subst c'.
          destruct b', (pt_pol x); simpl in *; congruence.
  Qed.

  (** ** spawn *)
  Lemma step_spawn i j e w e' :
    M !! i = Some e → tstep e (LSpawn w) e' → M !! j = None →
    ∃ A' U', LFconf n W ∅ T (pupd π (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M)))
        (C, <[j := App w EUnit]> (<[i := e']> M)) A' U' ∧
      lf_fuelc n W (pupd π (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M)))
        (fstep W P F (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M))).1
        (fstep W P F (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M))).2
        (eupd (eupd K i (Nat.div2 (K i))) j (Nat.div2 (S (K i)))) A'
        (C, <[j := App w EUnit]> (<[i := e']> M)).
  Proof.
    intros He Hst Hj.
    assert (i ≠ j) as Hij by (intros ->; congruence).
    destruct (st_spawn i e w e' He Hst) as (Θ1 & Θ2 & Hcomp & Hw1 & HE1 & HE2).
    destruct (act_step _ _ _ Hst) as (a & Ha & Ho). apply offers_spawn in Ho as ->.
    assert (pupd π (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := e']> M)) = π) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1. by rewrite Ha. }
    rewrite fstep_single. simpl. rewrite He. unfold fsingle. rewrite Ha. simpl.
    assert (dom (<[j:=App w EUnit]> (<[i:=e']> M)) ∖ dom M = {[j]}) as ->.
    { rewrite !dom_insert_L. apply elem_of_dom_2 in He. apply not_elem_of_dom in Hj. set_solver. }
    rewrite elements_singleton. simpl.
    pose proof (st_bipol i e He) as Hb.
    destruct (tenv_ends_comp _ _ _ Hcomp Hb) as [Hu Hd].
    set (M' := <[j := App w EUnit]> (<[i := e']> M)).
    assert (HM' : ∀ t, M' !! t = if decide (t = j) then Some (App w EUnit)
                                 else if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M'. destruct (decide (t = j)) as [->|Htj]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done.
      destruct (decide (t = i)) as [->|Hti]; [by rewrite lookup_insert_eq|]. by rewrite lookup_insert_ne. }
    set (A' := eupd (eupd A i Θ2) j Θ1).
    assert (HA' : ∀ t, A' t = if decide (t = j) then Θ1 else if decide (t = i) then Θ2 else A t).
    { intros t. unfold A', eupd. repeat case_decide; congruence. }
    assert (Hsub : ∀ t, (t = j ∨ t = i) → tenv_ends (A' t) ⊆ tenv_ends (A i)).
    { intros t Ht. rewrite HA', Hu.
      destruct (decide (t = j)); [set_solver|]. destruct (decide (t = i)); [set_solver|]. naive_solver. }
    exists A', (eupd U j TUnit). split.
    - apply (LFconf_frame (S (S n)) n W T π π (C, M) (C, M') A A' U _ ∅ Hc); simpl.
      + intros t f Hf. rewrite HM' in Hf. rewrite HA'. unfold eupd.
        destruct (decide (t = j)) as [->|Htj].
        * injection Hf as <-. eapply LErel_down; [|exact HE1]. lia.
        * destruct (decide (t = i)) as [->|Hti].
          -- injection Hf as <-. eapply LErel_down; [|exact HE2]. lia.
          -- by apply st_down.
      + intros t f Hf. rewrite HM' in Hf. rewrite HA'.
        destruct (decide (t = j)) as [->|Htj]; [apply (tenv_bipol_comp_l _ _ _ _ Hcomp Hb)|].
        destruct (decide (t = i)) as [->|Hti]; [apply (tenv_bipol_comp_r _ _ _ _ Hcomp Hb)|].
        by apply (st_bipol t f).
      + intros t f Hf. rewrite HM' in Hf. unfold eupd.
        destruct (decide (t = j)) as [->|Htj]; [by right|].
        destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|]. by apply (st_ty t f).
      + apply (disj_frame M M' (λ t, tenv_ends (A t)) (λ t, tenv_ends (A' t)) {[i; j]} st_disj).
        * intros t Ht. rewrite HM'. rewrite !decide_False by set_solver. done.
        * intros t Ht. simpl. rewrite HA', !decide_False by set_solver. done.
        * intros p f t g Hp Ht Hf Hg. simpl. assert (t ≠ i) by set_solver.
          pose proof (st_disj i t e g ltac:(done) He Hg).
          pose proof (Hsub p ltac:(set_solver)). set_solver.
        * intros p p' f f' Hp Hp' Hpp _ _. simpl. rewrite !HA'.
          apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->;
            apply elem_of_union in Hp' as [Hp'|Hp']; apply elem_of_singleton in Hp' as ->; try done.
          -- repeat case_decide; try congruence; first [done|by symmetry].
          -- repeat case_decide; try congruence; first [done|by symmetry].
      + intros t f Hf. pose proof (st_closed i e He).
        destruct (decide (t = j ∨ t = i)) as [Ht|Ht].
        * pose proof (dom_sub_ends _ _ (Hsub t Ht)). set_solver.
        * rewrite HM', !decide_False in Hf by naive_solver.
          rewrite HA', !decide_False by naive_solver. by apply (st_closed t f).
      + set_solver.
      + intros o x _. split.
        * intros (t & f & Hf & Hx). rewrite HA' in Hx. rewrite HM' in Hf.
          destruct (decide (t = j)) as [->|Htj].
          { exists i, e. split; [done|]. by apply (tenv_end_comp_l _ _ _ _ _ Hcomp Hb). }
          destruct (decide (t = i)) as [->|Hti].
          { exists i, e. split; [done|]. by apply (tenv_end_comp_r _ _ _ _ _ Hcomp Hb). }
          by exists t, f.
        * intros (t & f & Hf & Hx). destruct (decide (t = i)) as [->|Hti].
          -- simpl in Hf. rewrite He in Hf. injection Hf as <-.
             destruct (tenv_end_comp_inv _ _ _ _ _ Hcomp Hb Hx) as [H1|H2].
             ++ exists j, (App w EUnit). rewrite HM', HA', !decide_True by done. done.
             ++ exists i, e'. rewrite HM', HA', decide_False, decide_True by done.
                rewrite decide_False, decide_True by done. done.
          -- assert (t ≠ j) by (intros ->; simpl in Hf; congruence).
             exists t, f. rewrite HM', HA', !decide_False by done. done.
      + done.
      + set_solver.
      + set_solver.
    - apply (ffr _ _ _ _ _ (eupd (eupd K i (Nat.div2 (K i))) j (Nat.div2 (S (K i)))) {[i; j]}).
      + intros t Ht. rewrite HM', HA', !decide_False by set_solver. rewrite !eupd_ne by set_solver. done.
      + done.
      + intros p f Hp Hf. simpl in Hf. destruct (ff i e He) as (H1 & H2 & H3 & H4).
        destruct (lffuel_spawn (S n) W (P i) (F i) (K i) e H1 w e' Hst) as [Hch Hpar].
        apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->.
        * rewrite HM', decide_False, decide_True in Hf by done. injection Hf as <-.
          rewrite HA', decide_False, decide_True by done.
          unfold eupd. destruct (decide (i = j)); [done|]. destruct (decide (i = i)); [|done].
          simpl in Hpar. split_and!.
          -- apply (FuelE_down n (S n)); [lia|done].
          -- rewrite dom_mrem, H2, Hu, <-Hw1. set_solver.
          -- rewrite dom_mrem, H3, Hu, <-Hw1. set_solver.
          -- intros o Ho. rewrite lookup_mrem, decide_False by (rewrite <-Hw1; set_solver).
             apply H4. set_solver.
        * rewrite HM', decide_True in Hf by done. injection Hf as <-. rewrite HA', decide_True by done.
          rewrite !eupd_eq. simpl in Hch. split_and!.
          -- apply (FuelE_down n (S n)); [lia|done].
          -- rewrite dom_mres, H2, Hu, <-Hw1. set_solver.
          -- rewrite dom_fmap_L, dom_mres, H3, Hu, <-Hw1. set_solver.
          -- intros o Ho. rewrite lookup_mres, decide_True by (by rewrite <-Hw1).
             apply H4. set_solver.
  Qed.
  (** ** Two participants on one channel *)

  (** Nobody else holds a channel whose two ends i and j hold. *)
  Lemma st_cowner i j e f c b t g :
    M !! i = Some e → M !! j = Some f → (c, b) ∈ tenv_ends (A i) → (c, negb b) ∈ tenv_ends (A j) →
    t ≠ i → t ≠ j → M !! t = Some g → c ∉ dom (A t).
  Proof.
    intros He Hf Hi Hj Hti Htj Hg Hcg. apply dom_tenv_ends in Hcg as [b' Hb'].
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

  Lemma two_frame (i j : nat) (e f e' f' : expr) (Θi Θj : tenv) (c : chan) (π' : gmap cend point)
      (C' : gset chan) :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    LErel n W Θi (U i) ∅ e' → LErel n W Θj (U j) ∅ f' → tenv_bipol Θi → tenv_bipol Θj →
    tenv_ends Θi ∪ tenv_ends Θj ⊆ tenv_ends (A i) ∪ tenv_ends (A j) → tenv_ends Θi ## tenv_ends Θj →
    (C' = C ∨ (C' = (C ∖ {[c]}) ∧ (c ∉ dom Θi) ∧ (c ∉ dom Θj))) →
    (∀ t g, t ≠ i → t ≠ j → M !! t = Some g → c ∉ dom (A t)) →
    (∀ o x, o.1 ≠ c → ((tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) ↔
                       (tenv_end (A i) o = Some x ∨ tenv_end (A j) o = Some x))) →
    (∀ o, o.1 ≠ c → π' !! o = π !! o) →
    (∀ o x, o.1 = c → (tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) →
       π' !! o = Some x.2 ∧ ∃ y, (tenv_end Θi (cdual o) = Some y ∨ tenv_end Θj (cdual o) = Some y) ∧
         y.2 = pt_dual x.2 ∧ sdual x.1 y.1) →
    (∀ o x, o.1 = c → (tenv_end Θi o = Some x ∨ tenv_end Θj o = Some x) → pt_known W x.2) →
    LFconf n W ∅ T π' (C', <[j := f']> (<[i := e']> M)) (eupd (eupd A i Θi) j Θj) U.
  Proof.
    intros Hij He Hf HEi HEj Hbi Hbj Hsub Hdij HC' Hoth Hent Hπ HChk HKn.
    set (M' := <[j := f']> (<[i := e']> M)).
    assert (HM' : ∀ t, M' !! t = if decide (t = j) then Some f'
                                 else if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M'. destruct (decide (t = j)) as [->|Htj]; [by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne by done.
      destruct (decide (t = i)) as [->|Hti]; [by rewrite lookup_insert_eq|]. by rewrite lookup_insert_ne. }
    set (A' := eupd (eupd A i Θi) j Θj).
    assert (HA' : ∀ t, A' t = if decide (t = j) then Θj else if decide (t = i) then Θi else A t).
    { intros t. unfold A', eupd. repeat case_decide; congruence. }
    assert (Hsub' : ∀ t, (t = j ∨ t = i) → tenv_ends (A' t) ⊆ tenv_ends (A i) ∪ tenv_ends (A j)).
    { intros t Ht. rewrite HA'.
      destruct (decide (t = j)); [set_solver|]. destruct (decide (t = i)); [set_solver|]. naive_solver. }
    apply (LFconf_frame (S (S n)) n W T π π' (C, M) (C', M') A A' U U (cends c) Hc); simpl.
    - intros t g Hg. rewrite HM' in Hg. rewrite HA'.
      destruct (decide (t = j)) as [->|Htj]; [by injection Hg as <-|].
      destruct (decide (t = i)) as [->|Hti]; [by injection Hg as <-|]. by apply st_down.
    - intros t g Hg. rewrite HM' in Hg. rewrite HA'.
      destruct (decide (t = j)) as [->|Htj]; [done|].
      destruct (decide (t = i)) as [->|Hti]; [done|]. by apply (st_bipol t g).
    - intros t g Hg. rewrite HM' in Hg.
      destruct (decide (t = j)) as [->|Htj]; [by apply (st_ty j f)|].
      destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|]. by apply (st_ty t g).
    - apply (disj_frame M M' (λ t, tenv_ends (A t)) (λ t, tenv_ends (A' t)) {[i; j]} st_disj).
      + intros t Ht. rewrite HM'. rewrite !decide_False by set_solver. done.
      + intros t Ht. simpl. rewrite HA', !decide_False by set_solver. done.
      + intros p g t h Hp Ht Hg Hh. simpl.
        assert (t ≠ i ∧ t ≠ j) as [Hti Htj] by set_solver.
        pose proof (st_disj i t e h ltac:(done) He Hh) as Di.
        pose proof (st_disj j t f h ltac:(done) Hf Hh) as Dj.
        pose proof (Hsub' p ltac:(set_solver)) as Dp. clear - Di Dj Dp. set_solver.
      + intros p p' g g' Hp Hp' Hpp _ _. simpl. rewrite !HA'.
        apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->;
          apply elem_of_union in Hp' as [Hp'|Hp']; apply elem_of_singleton in Hp' as ->; try done.
        * repeat case_decide; try congruence; first [done|by symmetry].
        * repeat case_decide; try congruence; first [done|by symmetry].
    - intros t g Hg. pose proof (Hg) as Hg0. rewrite HM' in Hg0.
      pose proof (st_closed i e He). pose proof (st_closed j f Hf).
      destruct (decide (t = j ∨ t = i)) as [Ht|Ht].
      + pose proof (dom_sub_ends2 _ _ _ (Hsub' t Ht)) as Hd.
        destruct HC' as [->|(-> & Hci & Hcj)]; [set_solver|].
        assert (c ∉ dom (A' t)).
        { rewrite HA'. destruct (decide (t = j)); [done|]. destruct (decide (t = i)); [done|]. naive_solver. }
        set_solver.
      + rewrite !decide_False in Hg0 by naive_solver. rewrite HA', !decide_False by naive_solver.
        pose proof (st_closed t g Hg0).
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
        rewrite (tenv_end_none (A t) (c, b') Hn) in Hx. done. }
      destruct (HChk o x Ho Hor) as (Hp & y & Hy & Hd1 & Hd2). split; [done|].
      exists y. split; [|done]. destruct Hy as [Hy|Hy].
      + exists i, e'. rewrite HM', HA', decide_False, decide_True by done.
        rewrite decide_False, decide_True by done. done.
      + exists j, f'. rewrite HM', HA', !decide_True by done. done.
    - intros o x Ho%elem_of_cends (t & g & Hg & Hx). rewrite HM' in Hg. rewrite HA' in Hx.
      apply (HKn o x Ho).
      destruct (decide (t = j)) as [->|Htj]; [by right|].
      destruct (decide (t = i)) as [->|Hti]; [by left|].
      exfalso. pose proof (Hoth t g Hti Htj Hg) as Hn. destruct o as [c' b']. simpl in Ho. subst c'.
      rewrite (tenv_end_none (A t) (c, b') Hn) in Hx. done.
  Qed.

  (** The rest of an environment after the action on o. *)
  Lemma st_rest t e o u k Θ1 :
    M !! t = Some e → tenv_hd_end (A t) o u k Θ1 →
    ∃ s, unfoldS s = u ∧ tenv_ext Θ1 o.1 (s, k) (A t) ∧ tenv_end (A t) o = Some (s, k) ∧
      o ∈ tenv_ends (A t) ∧ tenv_ends Θ1 = tenv_ends (A t) ∖ {[o]} ∧ tenv_bipol Θ1 ∧
      (∀ o', o' ≠ o → tenv_end (A t) o' = tenv_end Θ1 o').
  Proof.
    intros He Hhd. destruct (hd_end _ _ _ _ _ Hhd (st_bipol t e He)) as (s & Hu & Hext & Ho & Hn & Hr).
    exists s. split_and!; try done.
    - by eapply tenv_end_ends.
    - destruct Hhd as [_ Hp]. destruct o as [c b]. simpl in *. subst b.
      destruct (tenv_ends_ext _ _ _ _ Hext (st_bipol t e He)) as [H1 H2].
      rewrite H1. set_solver.
    - by apply (tenv_bipol_ext_l _ _ _ _ Hext (st_bipol t e He)).
  Qed.

  (** A participant on one end, for close, select and branch. *)
  Lemma fuel_one t e σ e' o k X Θ' :
    M !! t = Some e → tstep e (LSess σ) e' → (∀ o0 w, σ ≠ SRecv o0 w) → sl_out σ = ∅ →
    sl_end σ = Some o → tenv_end (A t) o = Some (X, k) →
    tenv_ends Θ' = (match sl_next σ k with None => ∅ | Some (o', _) => {[o']} end) ∪
                   (tenv_ends (A t) ∖ {[o]}) →
    (∀ o0 b0, σ = SSel o0 b0 ∨ σ = SBra o0 b0 → fsolo (P t) o0) →
    FuelT n W (fupd W (P t) (F t) (LSess σ)).1 (fupd W (P t) (F t) (LSess σ)).2 (K t) e' ∧
    dom (fupd W (P t) (F t) (LSess σ)).1 = tenv_ends Θ' ∧
    dom (fupd W (P t) (F t) (LSess σ)).2 = tenv_ends Θ' ∧
    (∀ o', o' ∈ tenv_ends Θ' → (fupd W (P t) (F t) (LSess σ)).1 !! o' =
       if decide (Some o' = (fst <$> sl_next σ k)) then snd <$> sl_next σ k else P t !! o').
  Proof.
    intros He Hst Hnr Hout Ho Hx Hends Hso. destruct (ff t e He) as (H1 & H2 & H3 & H4).
    assert (Hso' : ∀ o0 b0, LSess σ = LSess (SSel o0 b0) ∨ LSess σ = LSess (SBra o0 b0) → fsolo (P t) o0).
    { intros o0 b0 [[= Hs]|[= Hs]]; apply (Hso o0 b0); auto. }
    assert (mrem (sl_out σ) (P t) !! o = Some k) as Hk.
    { rewrite Hout, lookup_mrem, decide_False by set_solver. apply (ff_pt t e o (X, k) He Hx). }
    assert (Hnr' : ∀ o0 w, LSess σ ≠ LSess (SRecv o0 w)) by (intros o0 w [= Heq]; by apply (Hnr o0 w)).
    pose proof (lffuel_step (S n) W (P t) (F t) (K t) e H1 _ e' Hst Hnr' ltac:(done) Hso') as HE.
    rewrite dupd_None in HE. rewrite (tkupd_act _ _ _ Ho) in HE.
    rewrite (fupd_act W σ (P t) (F t) o k Ho Hk) in HE |- *. rewrite ?Hout in HE. rewrite ?Hout.
    assert (o ∈ tenv_ends (A t)) as Hoe by (by eapply tenv_end_ends).
    destruct (sl_next σ k) as [[o' k']|] eqn:Hn; simpl in *.
    - split_and!.
      + apply (FuelE_down n (S n)); [lia|]. exact HE.
      + rewrite dom_insert_L, dom_delete_L, dom_mrem, H2, Hends. set_solver.
      + rewrite dom_insert_L, dom_fmap_L, dom_delete_L, dom_mrem, H3, Hends. set_solver.
      + intros o2 Ho2. destruct (decide (o2 = o')) as [->|Hne].
        * rewrite lookup_insert_eq. by rewrite decide_True.
        * rewrite lookup_insert_ne by done. rewrite decide_False by congruence.
          rewrite Hends in Ho2.
          rewrite lookup_delete_ne by set_solver. rewrite lookup_mrem, decide_False by set_solver. done.
    - split_and!.
      + apply (FuelE_down n (S n)); [lia|]. exact HE.
      + rewrite dom_delete_L, dom_mrem, H2, Hends. set_solver.
      + rewrite dom_fmap_L, dom_delete_L, dom_mrem, H3, Hends. set_solver.
      + intros o2 Ho2. rewrite Hends in Ho2. rewrite lookup_delete_ne by set_solver.
        rewrite lookup_mrem, decide_False by set_solver. done.
  Qed.

  Lemma fuel_f2 (i j : nat) (e f e' f' : expr) (σi σj : slabel) (q' : config) (π' : gmap cend point)
      (Θi Θj : tenv) :
    i ≠ j → M !! i = Some e → M !! j = Some f → q'.2 = <[j := f']> (<[i := e']> M) →
    (let r := fupd W (P i) (F i) (LSess σi) in
     FuelT n W r.1 r.2 (K i) e' ∧ dom r.1 = tenv_ends Θi ∧ dom r.2 = tenv_ends Θi ∧
     ∀ o, o ∈ tenv_ends Θi → r.1 !! o = π' !! o) →
    (let r := fupd W (P j) (F j) (LSess σj) in
     FuelT n W r.1 r.2 (K j) f' ∧ dom r.1 = tenv_ends Θj ∧ dom r.2 = tenv_ends Θj ∧
     ∀ o, o ∈ tenv_ends Θj → r.1 !! o = π' !! o) →
    (∀ t g o, t ≠ i → t ≠ j → M !! t = Some g → o ∈ tenv_ends (A t) → π' !! o = π !! o) →
    lf_fuelc n W π' (f2 W P F i j σi σj).1 (f2 W P F i j σi σj).2 K (eupd (eupd A i Θi) j Θj) q'.
  Proof.
    intros Hij He Hf Hq Hi Hj Hπ. apply (ffr _ _ _ _ _ K {[i; j]}).
    - intros t Ht. rewrite Hq. unfold f2, eupd. simpl.
      rewrite !lookup_insert_ne by set_solver. rewrite !decide_False by set_solver. done.
    - intros t g o Ht Hg Ho. apply (Hπ t g o); [set_solver|set_solver|done|done].
    - intros p g Hp Hg. rewrite Hq in Hg. unfold f2, eupd. simpl.
      apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->.
      + rewrite lookup_insert_ne in Hg by done. rewrite lookup_insert_eq in Hg. injection Hg as <-.
        destruct (decide (i = j)); [done|]. rewrite !decide_True by done. apply Hi.
      + rewrite lookup_insert_eq in Hg. injection Hg as <-. rewrite !decide_True by done. apply Hj.
  Qed.

  (** ** close *)
  Lemma step_close i j c b e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SClos (c, b))) e' → tstep f (LSess (SClos (c, negb b))) f' → c ∈ C →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M)))
        (C ∖ {[c]}, <[j := f']> (<[i := e']> M)) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M)))
        (fstep W P F (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M))).1
        (fstep W P F (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M))).2 K A'
        (C ∖ {[c]}, <[j := f']> (<[i := e']> M)).
  Proof.
    intros Hij He Hf Hse Hsf HcC.
    pose proof (st_sess i e _ e' He Hse) as (Θ1 & k & Hhd & HE). simpl in HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θ1j & kj & Hhdj & HEj). simpl in HEj.
    destruct (st_rest i e _ _ _ _ He Hhd) as (s & _ & _ & Hxi & Hoi & Hends & Hb1 & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (sj & _ & _ & Hxj & Hoj & Hendsj & Hb1j & Hrj).
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    assert (∀ b', (c, b') ∉ tenv_ends Θ1) as Hne.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = b)) as [->|Hb]; [set_solver|].
      assert (b' = negb b) as -> by (by destruct b, b').
      apply (Hdisj (c, negb b)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ tenv_ends Θ1j) as Hnej.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb b)) as [->|Hb]; [set_solver|].
      assert (b' = b) as -> by (by destruct b, b').
      apply (Hdisj (c, b)); [done|set_solver]. }
    destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_clos in Hoa as ->.
    destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_clos in Hoa' as ->.
    assert (pupd π (C, M) {[i; j]} (C ∖ {[c]}, <[j:=f']> (<[i:=e']> M)) = delete (c, true) (delete (c, false) π))
      as ->.
    { unfold pupd. destruct (pev_of_pair (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf)
        as [-> | ->]; unfold pev2; by rewrite ?Ha, ?Ha'. }
    assert (Hπ : ∀ o, o.1 ≠ c → delete (c, true) (delete (c, false) π) !! o = π !! o).
    { intros o Ho. rewrite !lookup_delete_ne; [done| |]; intros <-; done. }
    assert (Hoc : ∀ (X : gset cend) (o : cend), (∀ b', (c, b') ∉ X) → o ∈ X → o.1 ≠ c).
    { intros X [c' b'] HX Ho Heq. simpl in Heq. subst c'. by apply (HX b'). }
    exists (eupd (eupd A i Θ1) j Θ1j). split.
    - eapply (two_frame i j e f e' f' Θ1 Θ1j c); try done.
      + eapply LErel_down; [|exact HE]. lia.
      + eapply LErel_down; [|exact HEj]. lia.
      + rewrite Hends, Hendsj. set_solver.
      + rewrite Hends, Hendsj. set_solver.
      + right. split_and!; [done| |]; intros Hd; apply dom_tenv_ends in Hd as [b' Hb'];
          [by apply (Hne b')|by apply (Hnej b')].
      + intros t g Hti Htj Hg. by apply (st_cowner i j e f c b t g).
      + intros o x Ho. rewrite (Hri o), (Hrj o); [done| |]; intros ->; by apply Ho.
      + intros o x Ho [Hx|Hx]; exfalso; apply tenv_end_ends in Hx;
          [by apply (Hoc _ o Hne Hx)|by apply (Hoc _ o Hnej Hx)].
      + intros o x Ho [Hx|Hx]; exfalso; apply tenv_end_ends in Hx;
          [by apply (Hoc _ o Hne Hx)|by apply (Hoc _ o Hnej Hx)].
    - assert (Hmain : lf_fuelc n W (delete (c, true) (delete (c, false) π))
        (f2 W P F i j (SClos (c, b)) (SClos (c, negb b))).1 (f2 W P F i j (SClos (c, b)) (SClos (c, negb b))).2
        K (eupd (eupd A i Θ1) j Θ1j) (C ∖ {[c]}, <[j:=f']> (<[i:=e']> M))).
      { apply (fuel_f2 i j e f e' f'); try done.
        - destruct (fuel_one i e _ e' _ k s Θ1 He Hse ltac:(done) eq_refl eq_refl Hxi) as (H1 & H2 & H3 & H4).
          { simpl. rewrite Hends. set_solver. }
          { by intros ? ? [?|?]. }
          split_and!; try done. intros o Ho. rewrite H4 by done. simpl.
          rewrite Hπ by (by apply (Hoc _ o Hne)). apply (ff i e He). rewrite Hends in Ho. set_solver.
        - destruct (fuel_one j f _ f' _ kj sj Θ1j Hf Hsf ltac:(done) eq_refl eq_refl Hxj) as (H1 & H2 & H3 & H4).
          { simpl. rewrite Hendsj. set_solver. }
          { by intros ? ? [?|?]. }
          split_and!; try done. intros o Ho. rewrite H4 by done. simpl.
          rewrite Hπ by (by apply (Hoc _ o Hnej)). apply (ff j f Hf). rewrite Hendsj in Ho. set_solver.
        - intros t g o Hti Htj Hg Ho. apply Hπ. intros Heq.
          apply (st_cowner i j e f c b t g He Hf Hoi Hoj Hti Htj Hg).
          apply dom_tenv_ends. exists o.2. rewrite <-Heq. by destruct o. }
      destruct (fstep_pair W P F (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold fpair; rewrite ?Ha, ?Ha'; [done|].
      destruct (f2_swap W P F i j (SClos (c, b)) (SClos (c, negb b)) Hij) as [S1 S2].
      by apply (lf_fuelc_ext _ _ _ _ _ _ _ _ _ _ S1 S2).
  Qed.

  (** ** choice *)
  Lemma step_choice i j c β b e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SSel (c, β) b)) e' → tstep f (LSess (SBra (c, negb β) b)) f' →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
        (C, <[j := f']> (<[i := e']> M)) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
        (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))).1
        (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))).2 K A'
        (C, <[j := f']> (<[i := e']> M)).
  Proof.
    intros Hij He Hf Hse Hsf.
    pose proof (st_sess i e _ e' He Hse) as (Θr & s1 & s2 & k & Θ' & Hhd & Hext & HE). simpl in HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θr' & r1 & r2 & k' & Θ'' & Hhdj & Hextj & HEj).
    simpl in HEj.
    destruct (st_rest i e _ _ _ _ He Hhd) as (s0 & Hu & _ & Hxi & Hoi & Hends & Hbr & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (r0 & Hur & _ & Hxj & Hoj & Hendsj & Hbr' & Hrj).
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e (c, β) _ j f _ He Hxi Hf Hxj) as [Hk' Hsd].
    simpl in Hk'. subst k'.
    destruct (sdual_plus_with _ _ _ _ _ _ Hsd Hu Hur) as [Hd1 Hd2].
    pose proof (sdual_sbranch b _ _ _ _ Hd1 Hd2) as Hdb.
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    assert (∀ b', (c, b') ∉ tenv_ends Θr) as Hnr.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = β)) as [->|Hb]; [set_solver|].
      assert (b' = negb β) as -> by (by destruct β, b').
      apply (Hdisj (c, negb β)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ tenv_ends Θr') as Hnr'.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb β)) as [->|Hb]; [set_solver|].
      assert (b' = β) as -> by (by destruct β, b').
      apply (Hdisj (c, β)); [done|set_solver]. }
    destruct (no_chan_none Θr c Hnr) as [Hcr Hnr0].
    destruct (no_chan_none Θr' c Hnr') as [Hcr' Hnr0'].
    pose proof (tenv_bipol_ext_none _ _ _ _ Hext Hcr Hbr) as Hb'.
    pose proof (tenv_bipol_ext_none _ _ _ _ Hextj Hcr' Hbr') as Hb''.
    assert (pt_pol (sel_pt k b) = false) as Hps by done.
    assert (pt_pol (bra_pt (pt_dual k) b) = true) as Hpb by done.
    destruct (tenv_ends_ext _ _ _ _ Hext Hb') as [He1 _].
    destruct (tenv_ends_ext _ _ _ _ Hextj Hb'') as [He2 _].
    cbn [snd] in He1, He2. rewrite ?Hps in He1. rewrite ?Hpb in He2.
    assert (HΘ' : ∀ o, tenv_end Θ' o = if decide (o = (c, false)) then Some (sbranch b s1 s2, sel_pt k b)
                                       else tenv_end Θr o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext Hb'). cbn [snd]. by rewrite ?Hps. }
    assert (HΘ'' : ∀ o, tenv_end Θ'' o = if decide (o = (c, true))
                                         then Some (sbranch b r1 r2, bra_pt (pt_dual k) b)
                                         else tenv_end Θr' o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hextj Hb''). cbn [snd]. by rewrite ?Hpb. }
    assert (π !! (c, β) = Some k) as Hπk by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi).
    destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_sel in Hoa as ->.
    destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_bra in Hoa' as ->.
    assert (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)) =
            <[(c, false) := sel_pt k b]> (<[(c, true) := bra_pt k b]> π)) as ->.
    { unfold pupd. destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold pev2; rewrite ?Ha, ?Ha'; simpl; by rewrite Hπk. }
    assert (Hπo : ∀ o, o.1 ≠ c → (<[(c, false) := sel_pt k b]> (<[(c, true) := bra_pt k b]> π)) !! o = π !! o).
    { intros o Ho. rewrite !lookup_insert_ne; [done| |]; intros <-; done. }
    assert (Hoc : ∀ (X : gset cend) (o : cend), (∀ b', (c, b') ∉ X) → o ∈ X → o.1 ≠ c).
    { intros X [c' b'] HX Ho Heq. simpl in Heq. subst c'. by apply (HX b'). }
    exists (eupd (eupd A i Θ') j Θ''). split.
    - eapply (two_frame i j e f e' f' Θ' Θ'' c); try done.
      + eapply LErel_down; [|exact HE]. lia.
      + eapply LErel_down; [|exact HEj]. lia.
      + rewrite He1, He2, Hends, Hendsj. cbn [fst]. intros o Ho. destruct β; set_solver.
      + rewrite He1, He2. cbn [fst]. intros o Ho1 Ho2.
        apply elem_of_union in Ho1 as [Ho1|Ho1]; apply elem_of_union in Ho2 as [Ho2|Ho2].
        * rewrite Hends in Ho1. rewrite Hendsj in Ho2. apply (Hdisj o); set_solver.
        * apply elem_of_singleton in Ho2 as ->. by apply (Hnr true).
        * apply elem_of_singleton in Ho1 as ->. by apply (Hnr' false).
        * apply elem_of_singleton in Ho1, Ho2. congruence.
      + by left.
      + intros t g Hti Htj Hg. by apply (st_cowner i j e f c β t g).
      + intros o x Ho. rewrite HΘ', HΘ'', !decide_False by (intros ->; by apply Ho).
        rewrite (Hri o), (Hrj o); [done| |]; intros ->; by apply Ho.
      + intros o x Ho Hx. rewrite HΘ', HΘ'' in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
        rewrite Hnr0, Hnr0' in Hx. destruct b'.
        * destruct Hx as [Hx|Hx]; [rewrite decide_False in Hx by done; done|].
          rewrite decide_True in Hx by done. injection Hx as <-. simpl. split.
          { rewrite lookup_insert_ne by done. rewrite lookup_insert_eq. done. }
          exists (sbranch b s1 s2, sel_pt k b). split_and!.
          -- left. rewrite HΘ'. unfold cdual. simpl. by rewrite decide_True.
          -- done.
          -- by apply sdual_sym.
        * destruct Hx as [Hx|Hx]; [|rewrite decide_False in Hx by done; done].
          rewrite decide_True in Hx by done. injection Hx as <-. simpl. split.
          { by rewrite lookup_insert_eq. }
          exists (sbranch b r1 r2, bra_pt (pt_dual k) b). split_and!.
          -- right. rewrite HΘ''. unfold cdual. simpl. by rewrite decide_True.
          -- unfold sel_pt, bra_pt. by rewrite pt_dual_dual.
          -- done.
      + intros o x Ho Hx. pose proof (lf_known _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi) as Hk.
        rewrite HΘ', HΘ'' in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
        rewrite Hnr0, Hnr0' in Hx.
        destruct b'; destruct Hx as [Hx|Hx];
          first [rewrite decide_False in Hx by done; done
                |rewrite decide_True in Hx by done; injection Hx as <-; exact Hk].
    - assert (Hmain : lf_fuelc n W (<[(c, false) := sel_pt k b]> (<[(c, true) := bra_pt k b]> π))
        (f2 W P F i j (SSel (c, β) b) (SBra (c, negb β) b)).1
        (f2 W P F i j (SSel (c, β) b) (SBra (c, negb β) b)).2 K (eupd (eupd A i Θ') j Θ'')
        (C, <[j:=f']> (<[i:=e']> M))).
      { apply (fuel_f2 i j e f e' f'); try done.
        - destruct (fuel_one i e _ e' _ k s0 Θ' He Hse ltac:(done) eq_refl eq_refl Hxi) as (H1 & H2 & H3 & H4).
          { simpl. rewrite He1, Hends, ?Hps. set_solver. }
          { intros o0 b0 [[= <- _]|?]; [|done]. intros b' Hbs. simpl in Hbs |- *.
            destruct (ff i e He) as (_ & Hd & _). rewrite Hd in Hbs.
            destruct (decide (b' = β)) as [->|Hb]; [done|]. exfalso. apply (Hnr b').
            rewrite Hends. set_solver. }
          split_and!; try done. intros o Ho. rewrite H4 by done. simpl.
          destruct (decide (o = (c, false))) as [->|Hno].
          + rewrite decide_True by done. by rewrite lookup_insert_eq.
          + rewrite decide_False by congruence. rewrite He1 in Ho.
            assert (o ∈ tenv_ends Θr) as Ho' by set_solver.
            rewrite Hπo by (by apply (Hoc _ o Hnr)). apply (ff i e He). rewrite Hends in Ho'. set_solver.
        - destruct (fuel_one j f _ f' _ (pt_dual k) r0 Θ'' Hf Hsf ltac:(done) eq_refl eq_refl Hxj) as (H1 & H2 & H3 & H4).
          { simpl. rewrite He2, Hendsj, ?Hpb. set_solver. }
          { intros o0 b0 [?|[= <- _]]; [done|]. intros b' Hbs. simpl in Hbs |- *.
            destruct (ff j f Hf) as (_ & Hd & _). rewrite Hd in Hbs.
            destruct (decide (b' = negb β)) as [->|Hb]; [done|]. exfalso. apply (Hnr' b').
            rewrite Hendsj. set_solver. }
          split_and!; try done. intros o Ho. rewrite H4 by done. simpl.
          destruct (decide (o = (c, true))) as [->|Hno].
          + rewrite decide_True by done. rewrite lookup_insert_ne by done. by rewrite lookup_insert_eq.
          + rewrite decide_False by congruence. rewrite He2 in Ho.
            assert (o ∈ tenv_ends Θr') as Ho' by set_solver.
            rewrite Hπo by (by apply (Hoc _ o Hnr')). apply (ff j f Hf). rewrite Hendsj in Ho'. set_solver.
        - intros t g o Hti Htj Hg Ho. apply Hπo. intros Heq.
          apply (st_cowner i j e f c β t g He Hf Hoi Hoj Hti Htj Hg).
          apply dom_tenv_ends. exists o.2. rewrite <-Heq. by destruct o. }
      destruct (fstep_pair W P F (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold fpair; rewrite ?Ha, ?Ha'; done.
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

  (** ** message *)
  Lemma step_msg i j c b v e e' f f' :
    i ≠ j → M !! i = Some e → M !! j = Some f →
    tstep e (LSess (SSend (c, b) v)) e' → tstep f (LSess (SRecv (c, negb b) v)) f' →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
        (C, <[j := f']> (<[i := e']> M)) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)))
        (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))).1
        (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))).2 K A'
        (C, <[j := f']> (<[i := e']> M)).
  Proof.
    intros Hij He Hf Hse Hsf.
    pose proof (st_sess i e _ e' He Hse) as (Θr & Θ1 & Θ2 & m & Uu & s & k & Θ' & Hhd & Hcomp & HV & Hext & HE).
    simpl in HV, HE.
    pose proof (st_sess j f _ f' Hf Hsf) as (Θ1r & mr & Ur & sr & kr & Hhdj & Hrecv).
    destruct (st_rest i e _ _ _ _ He Hhd) as (s0 & Hu & Hexti & Hxi & Hoi & Hends & Hbr & Hri).
    destruct (st_rest j f _ _ _ _ Hf Hhdj) as (r0 & Hur & Hextj & Hxj & Hoj & Hendsj & Hbr' & Hrj).
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e (c, b) _ j f _ He Hxi Hf Hxj) as [Hk' Hsd].
    simpl in Hk'. subst kr.
    destruct (sdual_snd_rcv _ _ _ _ _ _ _ _ Hsd Hu Hur) as (<- & Hteq & Hss).
    pose proof (st_disj i j e f Hij He Hf) as Hdisj.
    destruct (tenv_ends_comp _ _ _ Hcomp Hbr) as [Hu12 Hd12].
    assert (∀ b', (c, b') ∉ tenv_ends Θr) as Hnr.
    { intros b' Hb'. rewrite Hends in Hb'. destruct (decide (b' = b)) as [->|Hb]; [set_solver|].
      assert (b' = negb b) as -> by (by destruct b, b').
      apply (Hdisj (c, negb b)); [set_solver|done]. }
    assert (∀ b', (c, b') ∉ tenv_ends Θ1r) as Hnr'.
    { intros b' Hb'. rewrite Hendsj in Hb'. destruct (decide (b' = negb b)) as [->|Hb]; [set_solver|].
      assert (b' = b) as -> by (by destruct b, b').
      apply (Hdisj (c, b)); [done|set_solver]. }
    destruct (no_chan_none Θ1 c) as [Hc1 Hn1]; [intros b'; rewrite Hu12 in Hnr; set_solver|].
    destruct (no_chan_none Θ2 c) as [Hc2 Hn2]; [intros b'; rewrite Hu12 in Hnr; set_solver|].
    destruct (no_chan_none Θ1r c) as [Hc1r Hn1r]; [done|].
    set (Θ1c := <[c := One (sr, pt_shift 1 (pt_dual k))]> Θ1r).
    assert (tenv_ext Θ1r c (sr, pt_shift 1 (pt_dual k)) Θ1c) as Hext1c by (left; by split).
    pose proof (tenv_bipol_comp_l _ _ _ _ Hcomp Hbr) as Hb1.
    pose proof (tenv_bipol_comp_r _ _ _ _ Hcomp Hbr) as Hb2.
    assert (Hcomp'' : tenv_comp (@eq point) (tenv_merge Θ1c Θ2) Θ1c Θ2).
    { apply tenv_comp_merge. intros d oa ob Hoa Hob.
      destruct (decide (d = c)) as [->|Hdc]; [by rewrite Hc2 in Hob|].
      unfold Θ1c in Hoa. rewrite lookup_insert_ne in Hoa by done.
      refine (merge_cond Θ1r Θ2 j i f e Hf He (not_eq_sym Hij) Hbr' Hb2 _ _ d oa ob Hoa Hob).
      - intros o x Hx. rewrite Hrj; [done|]. intros ->. by rewrite Hn1r in Hx.
      - intros o x Hx. rewrite Hri; [|intros ->; by rewrite Hn2 in Hx].
        by apply (tenv_end_comp_r _ _ _ _ _ Hcomp Hbr). }
    assert (LVrel (S n) W Θ2 (payload_at m Ur (pt_dual k)) v) as HVr.
    { rewrite payload_at_dual. eapply LVrel_teq; [apply HW| |exact HV]. by apply teq_ty_inst. }
    pose proof (Hrecv W (S n) Θ2 Θ1c (tenv_merge Θ1c Θ2) (wext_refl W HW) (le_n _) Hext1c Hcomp'' HVr)
      as HEj.
    set (Θ'' := tenv_merge Θ1c Θ2). fold Θ'' in HEj, Hcomp''.
    pose proof (tenv_bipol_ext_none _ _ _ _ Hext Hc1 Hb1) as Hb'.
    pose proof (tenv_bipol_ext_none _ _ _ _ Hext1c Hc1r Hbr') as Hb1c.
    pose proof (tenv_bipol_comp _ _ _ Hcomp'' Hb1c Hb2) as Hb''.
    assert (pt_pol (pt_shift 1 k) = b) as Hpk.
    { destruct Hhd as [_ Hp]. simpl in Hp. by rewrite <-Hp. }
    assert (pt_pol (pt_shift 1 (pt_dual k)) = negb b) as Hpk'.
    { destruct Hhd as [_ Hp]. simpl in Hp. by rewrite <-Hp. }
    assert (HΘ' : ∀ o, tenv_end Θ' o = if decide (o = (c, b)) then Some (s, pt_shift 1 k)
                                       else tenv_end Θ1 o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext Hb'). cbn [snd]. by rewrite Hpk. }
    assert (HΘ1c : ∀ o, tenv_end Θ1c o = if decide (o = (c, negb b))
                                         then Some (sr, pt_shift 1 (pt_dual k)) else tenv_end Θ1r o).
    { intros o. rewrite (tenv_end_ext _ _ _ _ o Hext1c Hb1c). cbn [snd]. by rewrite Hpk'. }
    assert (HΘ'' : ∀ o x, tenv_end Θ'' o = Some x ↔ tenv_end Θ1c o = Some x ∨ tenv_end Θ2 o = Some x)
      by (intros o x; apply (tenv_end_comp_iff _ _ _ _ _ Hcomp'' Hb'')).
    destruct (tenv_ends_ext _ _ _ _ Hext Hb') as [He1 _]. cbn [snd] in He1. rewrite Hpk in He1.
    destruct (tenv_ends_comp _ _ _ Hcomp'' Hb'') as [He2 _].
    destruct (tenv_ends_ext _ _ _ _ Hext1c Hb1c) as [He3 _]. cbn [snd] in He3. rewrite Hpk' in He3.
    rewrite He3 in He2.
    assert (π !! (c, b) = Some k) as Hπk by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi).
    assert (π !! (c, negb b) = Some (pt_dual k)) as Hπk'
      by apply (lf_pt _ _ _ _ _ _ _ _ Hc j f _ _ Hf Hxj).
    destruct (act_step _ _ _ Hse) as (a & Ha & Hoa). apply offers_send in Hoa as ->.
    destruct (act_step _ _ _ Hsf) as (a' & Ha' & Hoa'). apply offers_recv in Hoa' as ->.
    set (π' := alter (pt_shift 1) (c, true) (alter (pt_shift 1) (c, false) π)).
    assert (pupd π (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M)) = π') as ->.
    { unfold pupd. destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold pev2; rewrite ?Ha, ?Ha'; done. }
    assert (Hπc : ∀ o, o.1 = c → π' !! o = pt_shift 1 <$> π !! o).
    { intros [c' []] Ho; simpl in Ho; subst c'; unfold π'.
      - by rewrite lookup_alter_eq, lookup_alter_ne.
      - by rewrite lookup_alter_ne, lookup_alter_eq. }
    assert (Hπo : ∀ o, o.1 ≠ c → π' !! o = π !! o).
    { intros [c' b'] Ho. unfold π'. simpl in Ho. rewrite !lookup_alter_ne; [done| |]; intros [=]; congruence. }
    assert (tenv_ends Θ2 = fends v) as HΘ2 by (by destruct (LVrel_fit _ _ _ _ _ HV)).
    rewrite Hu12 in Hends, Hnr.
    assert ((c, b) ∉ tenv_ends Θ2) as Hcb2 by (pose proof (Hnr b); set_solver).
    assert ((c, negb b) ∉ tenv_ends Θ1 ∪ tenv_ends Θ2) as Hcnb by apply Hnr.
    assert ((c, b) ≠ (c, negb b)) as Hbnb by (destruct b; done).
    exists (eupd (eupd A i Θ') j Θ''). split.
    - eapply (two_frame i j e f e' f' Θ' Θ'' c); try done.
      + eapply LErel_down; [|exact HE]. lia.
      + eapply LErel_down; [|exact HEj]. lia.
      + rewrite He1, He2. clear -Hends Hendsj Hoi Hoj. set_solver.
      + rewrite He1, He2. pose proof (Hnr' b) as Hnr'b.
        clear -Hends Hendsj Hdisj Hd12 Hcb2 Hcnb Hbnb Hnr'b. set_solver.
      + by left.
      + intros t g Hti Htj Hg. by apply (st_cowner i j e f c b t g).
      + intros o x Ho. rewrite HΘ', HΘ'', HΘ1c, !decide_False by (intros ->; by apply Ho).
        rewrite (Hri o), (Hrj o) by (intros ->; by apply Ho).
        rewrite (tenv_end_comp_iff _ _ _ _ _ Hcomp Hbr). naive_solver.
      + intros o x Ho Hx. rewrite HΘ', HΘ'', HΘ1c in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
        rewrite Hn1, Hn1r, Hn2 in Hx. rewrite Hπc by done.
        destruct (decide ((c, b') = (c, b))) as [Heq|Hneq].
        * injection Heq as ->. destruct Hx as [Hx|[Hx|Hx]]; [|by rewrite decide_False in Hx by (destruct b; done)|done].
          injection Hx as <-. simpl. rewrite Hπk. split; [done|].
          exists (sr, pt_shift 1 (pt_dual k)). split_and!; [|done|done].
          right. apply HΘ''. left. rewrite HΘ1c. unfold cdual. simpl. by rewrite decide_True.
        * destruct Hx as [Hx|[Hx|Hx]]; [done| |done].
          destruct (decide ((c, b') = (c, negb b))) as [Heq'|]; [|done].
          injection Heq' as ->. injection Hx as <-. simpl. rewrite Hπk'. split; [done|].
          exists (s, pt_shift 1 k). split_and!; [|by rewrite pt_dual_shift, pt_dual_dual|by apply sdual_sym].
          left. rewrite HΘ'. unfold cdual. simpl. rewrite negb_involutive. by rewrite decide_True.
      + intros o x Ho Hx. pose proof (lf_known _ _ _ _ _ _ _ _ Hc i e _ _ He Hxi) as Hk.
        rewrite HΘ', HΘ'', HΘ1c in Hx. destruct o as [c' b']. simpl in Ho. subst c'.
        rewrite Hn1, Hn1r, Hn2 in Hx.
        destruct Hx as [Hx|[Hx|Hx]]; [| |done]; case_decide; try done;
          injection Hx as <-; exact Hk.
    - assert (Hcend : ∀ g t o, M !! t = Some g → o ∈ tenv_ends (A t) → o.1 = c →
                (t = i ∧ o = (c, b)) ∨ (t = j ∧ o = (c, negb b))).
      { intros g t [c' b'] Hg Ho Heq. simpl in Heq. subst c'.
        destruct (decide (b' = b)) as [->|Hb].
        - left. destruct (decide (t = i)) as [->|Hti]; [done|].
          exfalso. by apply (st_disj t i g e Hti Hg He (c, b)).
        - assert (b' = negb b) as -> by (by destruct b, b'). right.
          destruct (decide (t = j)) as [->|Htj]; [done|].
          exfalso. by apply (st_disj t j g f Htj Hg Hf (c, negb b)). }
      assert (Hve : fends v ⊆ tenv_ends (A i)) by (rewrite <-HΘ2; clear -Hends; set_solver).
      assert ((c, b) ∉ fends v) as Hcbv by (by rewrite <-HΘ2).
      destruct (ff i e He) as (H1i & H2i & H3i & H4i). destruct (ff j f Hf) as (H1j & H2j & H3j & H4j).
      pose proof (ff_pt i e _ _ He Hxi) as Pk. pose proof (ff_pt j f _ _ Hf Hxj) as Pk'. simpl in Pk, Pk'.
      assert (Hee : tenv_ends Θ' = ((tenv_ends (A i) ∖ fends v) ∖ {[(c, b)]}) ∪ {[(c, b)]}).
      { rewrite He1, <-HΘ2. clear -Hends Hd12 Hoi Hcb2. apply set_eq. intros o.
        destruct (decide (o = (c, b))) as [->|Hob]; set_solver. }
      assert (Hff : tenv_ends Θ'' = tenv_ends (A j) ∪ fends v).
      { rewrite He2, <-HΘ2, Hendsj. clear -Hoj. apply set_eq. intros o.
        destruct (decide (o = (c, negb b))) as [->|]; set_solver. }
      set (πi := mres (fends v) (P i)). set (φi := ftick <$> mres (fends v) (F i)).
      assert (Hmain : lf_fuelc n W π' (fmsg W P F i j (c, b) (c, negb b) v).1
                        (fmsg W P F i j (c, b) (c, negb b) v).2 K (eupd (eupd A i Θ') j Θ'')
                        (C, <[j:=f']> (<[i:=e']> M))).
      { apply (ffr _ _ _ _ _ K {[i; j]}).
        - intros t Ht. unfold fmsg, eupd. simpl. rewrite !lookup_insert_ne by (clear -Ht; set_solver).
          rewrite !decide_False by (clear -Ht; set_solver). done.
        - intros t g o Ht Hg Ho. apply Hπo. intros Heq.
          destruct (Hcend g t o Hg Ho Heq) as [[-> _]|[-> _]]; clear -Ht; set_solver.
        - intros p g Hp Hg. simpl in Hg. unfold fmsg, eupd. cbn [fst snd].
          apply elem_of_union in Hp as [Hp|Hp]; apply elem_of_singleton in Hp as ->.
          + rewrite lookup_insert_ne in Hg by done. rewrite lookup_insert_eq in Hg. injection Hg as <-.
            destruct (decide (i = j)); [done|]. rewrite !decide_True by done.
            assert (mrem (sl_out (SSend (c, b) v)) (P i) !! (c, b) = Some k) as Hk.
            { simpl. by rewrite lookup_mrem, decide_False. }
            pose proof (lffuel_step (S n) W (P i) (F i) (K i) e H1i _ e' Hse ltac:(done) ltac:(done) ltac:(by intros ? ? [?|?])) as HEf.
            rewrite (fupd_act W (SSend (c, b) v) (P i) (F i) (c, b) k eq_refl Hk) in HEf |- *. simpl in HEf |- *.
            split_and!.
            * apply (FuelE_down n (S n)); [lia|done].
            * rewrite dom_insert_L, dom_delete_L, dom_mrem, H2i, Hee. clear. set_solver.
            * rewrite dom_insert_L, dom_fmap_L, dom_delete_L, dom_mrem, H3i, Hee. clear. set_solver.
            * intros o Ho. destruct (decide (o = (c, b))) as [->|Hob].
              -- rewrite lookup_insert_eq, Hπc, Hπk by done. done.
              -- rewrite lookup_insert_ne, lookup_delete_ne by done. rewrite Hee in Ho.
                 rewrite lookup_mrem, decide_False by (clear -Ho Hob; set_solver).
                 rewrite H4i by (clear -Ho Hob; set_solver).
                 rewrite Hπo; [done|]. intros Heq.
                 destruct (Hcend e i o He ltac:(clear -Ho Hob; set_solver) Heq) as [[_ ->]|[Hji _]];
                   congruence.
          + rewrite lookup_insert_eq in Hg. injection Hg as <-. rewrite !decide_True by done.
            assert (dom πi = fends v) as Hdπi by (unfold πi; rewrite dom_mres, H2i; clear -Hve; set_solver).
            assert (mrem (sl_out (SRecv (c, negb b) v)) (P j) !! (c, negb b) = Some (pt_dual k)) as Hk.
            { simpl. by rewrite lookup_mrem, decide_False by (clear; set_solver). }
            assert (dom (fupd W (P j) (F j) (LSess (SRecv (c, negb b) v))).1 = tenv_ends (A j)) as Hdr.
            { rewrite (fupd_act W (SRecv (c, negb b) v) (P j) (F j) (c, negb b) (pt_dual k) eq_refl Hk). simpl.
              rewrite dom_insert_L, dom_delete_L, dom_mrem, H2j. clear -Hoj. apply set_eq; intros o.
              destruct (decide (o = (c, negb b))) as [->|]; set_solver. }
            assert (dom (fupd W (P j) (F j) (LSess (SRecv (c, negb b) v))).2 = tenv_ends (A j)) as Hdr2.
            { rewrite (fupd_act W (SRecv (c, negb b) v) (P j) (F j) (c, negb b) (pt_dual k) eq_refl Hk). simpl.
              rewrite dom_insert_L, dom_fmap_L, dom_delete_L, dom_mrem, H3j. clear -Hoj. apply set_eq; intros o.
              destruct (decide (o = (c, negb b))) as [->|]; set_solver. }
            pose proof (lffuel_recv (S n) W (P j) (F j) (K j) f H1j _ v f' (pt_dual k) n πi φi Hsf Pk' ltac:(lia))
              as HEr.
            split_and!.
            * apply HEr.
              -- rewrite Hdπi, Hdr. clear -Hve Hdisj. set_solver.
              -- split_and!.
                 ++ done.
                 ++ unfold φi. rewrite dom_fmap_L, dom_mres, H3i. clear -Hve. set_solver.
                 ++ apply fcap_tick, fcap_mres, (fuel_cap (S n) W _ _ _ e H1i).
                 ++ intros o k0 Hk0. unfold πi in Hk0. rewrite lookup_mres in Hk0. case_decide; [|done].
                    by apply (fuel_send_travel (S n) W _ _ _ e H1i _ _ _ Hse o k0).
                 ++ intros o k0 Hk0. unfold πi in Hk0. rewrite lookup_mres in Hk0.
                    case_decide as Hov; [|done].
                    assert (o ∈ tenv_ends (A i)) as Hoi' by (clear -Hov Hve; set_solver).
                    destruct (proj1 (tenv_ends_end _ _) Hoi') as [x Hx].
                    rewrite (ff_pt i e o x He Hx) in Hk0. injection Hk0 as <-.
                    apply (lf_known _ _ _ _ _ _ _ _ Hc i e o x He Hx).
              -- (* the payload cost type at the receiver's dual point is the sender's *)
                 rewrite pt_dual_dual.
                 eapply Vfuel_down; [|exact (fuel_send_val (S n) W _ _ _ e H1i _ _ _ _ Hse Pk)]. lia.
            * rewrite dom_union_L, Hdr. unfold πi. rewrite dom_mres, H2i, Hff. clear -Hve. set_solver.
            * unfold φi. rewrite dom_union_L, Hdr2, dom_fmap_L, dom_mres, H3i, Hff. clear -Hve. set_solver.
            * intros o Ho. rewrite Hff in Ho.
              destruct (decide (o ∈ tenv_ends (A j))) as [Hof|Hof].
              -- rewrite lookup_union_l'.
                 2:{ apply elem_of_dom. by rewrite Hdr. }
                 rewrite (fupd_act W (SRecv (c, negb b) v) (P j) (F j) (c, negb b) (pt_dual k) eq_refl Hk). simpl.
                 destruct (decide (o = (c, negb b))) as [->|Hob].
                 ++ rewrite lookup_insert_eq, Hπc, Hπk' by done. done.
                 ++ rewrite lookup_insert_ne, lookup_delete_ne by done.
                    rewrite lookup_mrem, decide_False by (clear; set_solver). rewrite H4j by done.
                    rewrite Hπo; [done|]. intros Heq.
                    destruct (Hcend f j o Hf Hof Heq) as [[Hji _]|[_ ->]]; congruence.
              -- assert (o ∈ fends v) as Hov by (clear -Ho Hof; set_solver).
                 rewrite lookup_union_r.
                 2:{ apply not_elem_of_dom. by rewrite Hdr. }
                 unfold πi. rewrite lookup_mres, decide_True by done.
                 rewrite H4i by (clear -Hov Hve; set_solver).
                 rewrite Hπo; [done|]. intros Heq.
                 destruct (Hcend e i o He ltac:(clear -Hov Hve; set_solver) Heq) as [[_ ->]|[Hji _]];
                   congruence. }
      destruct (fstep_pair W P F (C, M) (C, <[j:=f']> (<[i:=e']> M)) i j e f Hij He Hf) as [-> | ->];
        unfold fpair; rewrite ?Ha, ?Ha'; done.
  Qed.
  (** ** link *)
  Lemma st_link_data i e c bc d bd e' :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' →
    ∃ Θ1 xc xd, (c, bc) ≠ (d, bd) ∧ tenv_end (A i) (c, bc) = Some xc ∧
      tenv_end (A i) (d, bd) = Some xd ∧ xc.2 = pt_dual xd.2 ∧ sdual xc.1 xd.1 ∧
      tenv_end Θ1 (c, bc) = None ∧ tenv_end Θ1 (d, bd) = None ∧
      (∀ o, o ≠ (c, bc) → o ≠ (d, bd) → tenv_end (A i) o = tenv_end Θ1 o) ∧
      tenv_ends Θ1 = tenv_ends (A i) ∖ {[(c, bc); (d, bd)]} ∧ tenv_bipol Θ1 ∧
      LErel (S (S n)) W Θ1 (U i) ∅ e'.
  Proof.
    intros He Hst.
    destruct (st_link i e _ e' He Hst) as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & Hcd & H1 & H2 & Hsd & Hk & HE).
    simpl in HE.
    pose proof (st_bipol i e He) as Hb. pose proof (tenv_bipol_ext_l _ _ _ _ H2 Hb) as Hbm.
    pose proof (tenv_bipol_ext_l _ _ _ _ H1 Hbm) as Hb1.
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
    assert (tenv_ends Θ1 = tenv_ends (A i) ∖ {[(c1, pt_pol kc); (d1, pt_pol kd)]}) as Hends.
    { rewrite Hu2, Hu1. rewrite Hu1 in Hm2.
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

  (** The counters along a link: every map is renamed, the linker loses
      both ends and spends a ticket. No other counter changes (plan
      §18.3). A' is the environment of the successor, whose ends are the
      renamed ends of the environments after the linker's step. *)
  Lemma fuel_link i e c bc d bd e' Θ1 xc xd (A' : nat → tenv) :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' → c ∈ C →
    (c, bc) ≠ (d, bd) → tenv_end (A i) (c, bc) = Some xc → tenv_end (A i) (d, bd) = Some xd →
    xc.2 = pt_dual xd.2 → tenv_ends Θ1 = tenv_ends (A i) ∖ {[(c, bc); (d, bd)]} →
    (∀ t g, (chsubst c d <$> <[i := e']> M) !! t = Some g →
       tenv_ends (A' t) = set_map (osub c d) (tenv_ends (eupd A i Θ1 t))) →
    lf_fuelc n W (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M))
      (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M)).1
      (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M)).2
      (eupd K i (K i - 1)) A' (C ∖ {[c]}, chsubst c d <$> <[i := e']> M).
  Proof.
    intros He Hst HcC Hne Hxc Hxd Hdx Hends HA'.
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd. simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    pose proof (tenv_end_ends _ _ _ Hxc) as Hci. pose proof (tenv_end_ends _ _ _ Hxd) as Hdi.
    destruct (act_step _ _ _ Hst) as (a & Ha & Hoa). apply offers_link in Hoa as (o1 & o2 & -> & Hcd).
    assert (C ∖ (C ∖ {[c]}) = {[c]}) as HCc.
    { apply set_eq. intros x. destruct (decide (x = c)) as [->|Hx]; [clear -HcC|clear -HcC Hx]; set_solver. }
    assert ((if decide (o1.1 = c) then o2.1 else o1.1) = d) as Hd'.
    { destruct (upair_eq_inv _ _ _ _ Hcd Hne) as [[<- <-]|[<- <-]]; simpl.
      - by rewrite decide_True.
      - destruct (decide (d = c)) as [->|]; done. }
    rewrite fstep_single. unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold fsingle, pev1.
    rewrite Ha. simpl. rewrite HCc, elements_singleton. simpl. rewrite Hd'.
    rewrite <-Hcd.
    set (M'' := <[i := e']> M). set (A'' := eupd A i Θ1).
    set (BP := eupd P i (mrem {[(c, bc); (d, bd)]} (P i))).
    set (BF0 := eupd F i (mrem {[(c, bc); (d, bd)]} (F i))).
    set (BK := eupd K i (K i - 1)).
    assert (Hbase : ∀ t g, M'' !! t = Some g →
              FuelT (S n) W (BP t) (BF0 t) (BK t) g ∧ dom (BP t) = tenv_ends (A'' t) ∧
              dom (BF0 t) = tenv_ends (A'' t) ∧
              (∀ o, o ∈ tenv_ends (A'' t) → BP t !! o = π !! o) ∧
              ((c, bc) ∉ tenv_ends (A'' t)) ∧ ((d, bd) ∉ tenv_ends (A'' t))).
    { intros t g Hg. unfold M'' in Hg. unfold BP, BF0, BK, A'', eupd. destruct (decide (t = i)) as [->|Hti].
      - rewrite lookup_insert_eq in Hg. injection Hg as <-. destruct (ff i e He) as (H1 & H2 & H3 & H4).
        pose proof (lffuel_step (S n) W (P i) (F i) (K i) e H1 _ e' Hst ltac:(done) ltac:(done) ltac:(by intros ? ? [?|?])) as H. simpl in H.
        unfold LFFuel.fact in H. simpl in H.
        split_and!; [done|by rewrite dom_mrem, H2, Hends|by rewrite dom_mrem, H3, Hends
          | |rewrite Hends; clear; set_solver|rewrite Hends; clear; set_solver].
        intros o Ho. rewrite Hends in Ho. rewrite lookup_mrem, decide_False by (clear -Ho; set_solver).
        apply H4. clear -Ho. set_solver.
      - rewrite lookup_insert_ne in Hg by done. destruct (ff t g Hg) as (H1 & H2 & H3 & H4).
        pose proof (st_disj t i g e Hti Hg He) as Hd0.
        split_and!; try done; [apply (FuelE_down (S n) (S (S n))); [lia|done]|clear -Hd0 Hci; set_solver
          |clear -Hd0 Hdi; set_solver]. }
    assert (Hcend : ∀ t g β, M'' !! t = Some g → (c, β) ∈ tenv_ends (A'' t) → c ≠ d → β = bd).
    { intros t g β Hg Hin Hcd'. destruct (Hbase t g Hg) as (_ & _ & _ & _ & Hn & _).
      destruct (decide (β = bc)) as [->|Hb]; [done|]. rewrite Hbd. by destruct β, bc. }
    assert (Hkinj : ∀ t g, M'' !! t = Some g → kinj (csub c d) (BP t) ∧ kinj (csub c d) (BF0 t)).
    { intros t g Hg. destruct (Hbase t g Hg) as (_ & H2 & H3 & _ & Hn1' & Hn2').
      assert (∀ o, o ∈ tenv_ends (A'' t) → ∀ o2, o2 ∈ tenv_ends (A'' t) →
                (csub c d o.1, o.2) = (csub c d o2.1, o2.2) → o = o2) as Hi.
      { intros [c1 b1] Ho [c2 b2] Ho2 Heq.
        pose proof (f_equal fst Heq) as Hc12. pose proof (f_equal snd Heq) as Hb12.
        unfold csub in Hc12. simpl in Hc12, Hb12. subst b2.
        destruct (decide (c1 = c)) as [->|Hq1], (decide (c2 = c)) as [->|Hq2]; try (by subst).
        - subst c2. exfalso. assert (c ≠ d) as Hcd' by congruence.
          pose proof (Hcend t g _ Hg Ho Hcd'). subst. by apply Hn2'.
        - subst c1. exfalso. assert (c ≠ d) as Hcd' by congruence.
          pose proof (Hcend t g _ Hg Ho2 Hcd'). subst. by apply Hn2'. }
      split; intros o1' o2' v1 v2 Hv1 Hv2 Heq; apply Hi; try done.
      - rewrite <-H2. by apply elem_of_dom_2 in Hv1.
      - rewrite <-H2. by apply elem_of_dom_2 in Hv2.
      - rewrite <-H3. by apply elem_of_dom_2 in Hv1.
      - rewrite <-H3. by apply elem_of_dom_2 in Hv2. }
    assert (Hpc' : π !! (c, negb bc) = π !! (d, bd)).
    { destruct (lfc_partner _ _ _ _ _ _ _ Hc i e _ _ He Hxc) as (s & gs & ys & Hgs & Hys & Hys2 & _).
      change (c, negb bc) with (cdual (c, bc)).
      rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s gs _ _ Hgs Hys), (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxd).
      by rewrite Hys2, Hdx, pt_dual_dual. }
    intros t g' Hg'. pose proof (HA' t g' Hg') as HAt. fold A'' in HAt.
    simpl in Hg'. rewrite lookup_fmap in Hg'.
    destruct (M'' !! t) as [g|] eqn:Hg; [|done]. simpl in Hg'. injection Hg' as <-.
    destruct (Hbase t g Hg) as (H1 & H2 & H3 & H4 & Hn1' & Hn2').
    destruct (Hkinj t g Hg) as [Hk1 Hk2].
    rewrite chsubst_emap. split_and!.
    - apply (FuelE_down n (S n)); [lia|].
      apply (FuelE_rename _ _ _ _ (BP t) (BF0 t) _ _ g); [done| | |done].
      + by apply renk_kren.
      + by apply renk_kren.
    - rewrite kren_dom, H2 by done. rewrite HAt. unfold osub. done.
    - rewrite kren_dom, H3 by done. rewrite HAt. unfold osub. done.
    - intros o' Ho'. rewrite HAt in Ho'.
      apply elem_of_map in Ho' as (o0 & -> & Ho0).
      assert (is_Some (BP t !! o0)) as [v Hv] by (apply elem_of_dom; by rewrite H2).
      unfold osub. rewrite (kren_lookup _ _ o0 v Hk1 Hv). rewrite <-Hv, H4 by done.
      destruct o0 as [c0 b0]. unfold csub. simpl. destruct (decide (c0 = c)) as [->|Hc0].
      + destruct (decide (c = d)) as [<-|Hcd'].
        * exfalso. destruct (decide (b0 = bc)) as [->|Hb]; [done|].
          assert (b0 = bd) as -> by (rewrite Hbd; by destruct b0, bc). done.
        * pose proof (Hcend t g b0 Hg Ho0 Hcd') as ->. rewrite lookup_delete_ne by (intros [=]; congruence).
          rewrite lookup_delete_ne by (intros [=]; congruence). rewrite Hbd. by rewrite Hpc', Hbd.
      + rewrite !lookup_delete_ne; [done| |]; intros [=]; congruence.
  Qed.

  Lemma osub_refl c o : osub c c o = o.
  Proof. destruct o as [c0 b0]. unfold osub, csub. simpl. by destruct (decide (c0 = c)) as [->|]. Qed.

  (** A self-link holds both ends of c and closes it. *)
  Lemma step_link_self i e c bc bd e' :
    M !! i = Some e → tstep e (LSess (SLink {[(c, bc); (c, bd)]})) e' → c ∈ C →
    ∃ A', LFconf n W ∅ T (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c c <$> <[i := e']> M))
        (C ∖ {[c]}, chsubst c c <$> <[i := e']> M) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c c <$> <[i := e']> M))
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c c <$> <[i := e']> M)).1
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c c <$> <[i := e']> M)).2 (eupd K i (K i - 1)) A'
        (C ∖ {[c]}, chsubst c c <$> <[i := e']> M).
  Proof.
    intros He Hst HcC.
    destruct (st_link_data i e c bc c bd e' He Hst)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & _ & _ & _ & Hr & Hends & Hb1 & HE).
    exists (eupd A i Θ1). split.
    2:{ apply (fuel_link i e c bc c bd e' Θ1 xc xd); try done.
        intros t g _. apply set_eq. intros o. rewrite elem_of_map. split.
        - intros Ho. exists o. by rewrite osub_refl.
        - intros (o0 & -> & Ho0). by rewrite osub_refl. }
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
    assert (∀ b', (c, b') ∉ tenv_ends Θ1) as Hnc.
    { intros b' Hb'. rewrite Hends in Hb'. destruct b', bc; set_solver. }
    assert (Hoth : ∀ t g, t ≠ i → M !! t = Some g → c ∉ dom (A t)).
    { intros t g Hti Hg Hcg. apply dom_tenv_ends in Hcg as [b' Hb'].
      apply (st_disj t i g e Hti Hg He (c, b')); [done|].
      destruct b', bc; [apply (tenv_end_ends _ _ _ Hxc)|apply (tenv_end_ends _ _ _ Hxd)
        |apply (tenv_end_ends _ _ _ Hxd)|apply (tenv_end_ends _ _ _ Hxc)]. }
    apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∖ {[c]}, <[i := e']> M) A _ U U (cends c) Hc);
      simpl.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite lookup_insert_eq in Hf. injection Hf as <-. rewrite eupd_eq.
        eapply LErel_down; [|exact HE]. lia.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply st_down.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + by rewrite eupd_eq.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done. by apply (st_bipol t f).
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti]; [by apply (st_ty i e)|].
      rewrite lookup_insert_ne in Hf by done. by apply (st_ty t f).
    - apply (disj_frame M _ (λ t, tenv_ends (A t)) (λ t, tenv_ends (eupd A i Θ1 t)) {[i]} st_disj).
      + intros t Ht. rewrite lookup_insert_ne; set_solver.
      + intros t Ht. simpl. rewrite eupd_ne; set_solver.
      + intros p f t g Hp Ht Hf Hg. apply elem_of_singleton in Hp as ->. simpl.
        rewrite eupd_eq, Hends. pose proof (st_disj i t e g ltac:(set_solver) He Hg). set_solver.
      + intros p p' f f' Hp Hp' Hpp. set_solver.
    - intros t f Hf. destruct (decide (t = i)) as [->|Hti].
      + rewrite eupd_eq. pose proof (st_closed i e He).
        assert (dom Θ1 ⊆ dom (A i)) by (apply dom_sub_ends; rewrite Hends; set_solver).
        assert (c ∉ dom Θ1) by (rewrite dom_tenv_ends; intros [b' Hb']; by apply (Hnc b')).
        set_solver.
      + rewrite lookup_insert_ne in Hf by done. rewrite eupd_ne by done.
        pose proof (st_closed t f Hf). pose proof (Hoth t f Hti Hf). set_solver.
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
      destruct o as [c' b']. simpl in Ho. subst c'.
      destruct (decide (t = i)) as [->|Hti].
      + rewrite eupd_eq in Hx. apply (Hnc b'). by eapply tenv_end_ends.
      + rewrite eupd_ne in Hx by done. simpl in Hf. rewrite lookup_insert_ne in Hf by done.
        by rewrite (tenv_end_none (A t) (c, b') (Hoth t f Hti Hf)) in Hx.
    - intros o x0 Ho%elem_of_cends (t & f & Hf & Hx). exfalso.
      destruct o as [c' b']. simpl in Ho. subst c'.
      destruct (decide (t = i)) as [->|Hti].
      + rewrite eupd_eq in Hx. apply (Hnc b'). by eapply tenv_end_ends.
      + rewrite eupd_ne in Hx by done. simpl in Hf. rewrite lookup_insert_ne in Hf by done.
        by rewrite (tenv_end_none (A t) (c, b') (Hoth t f Hti Hf)) in Hx.
  Qed.
  Ltac neq_tac := let H := fresh in intros H; inversion H;
    first [congruence|(repeat match goal with b : bool |- _ => destruct b end); simpl in *; congruence].

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
        (C ∖ {[c]}, chsubst c d <$> <[i := e']> M) A' U ∧
      lf_fuelc n W (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M))
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M)).1
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := e']> M)).2 (eupd K i (K i - 1)) A'
        (C ∖ {[c]}, chsubst c d <$> <[i := e']> M).
  Proof.
    intros He Hst HcC Hcd.
    destruct (st_link_data i e c bc d bd e' He Hst)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & Hsx & Hn1 & Hn2 & Hr & Hends & Hb1 & HE).
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd.
    simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    set (M'' := <[i := e']> M). set (A'' := eupd A i Θ1).
    assert (HM'' : ∀ t, M'' !! t = if decide (t = i) then Some e' else M !! t).
    { intros t. unfold M''. destruct (decide (t = i)) as [->|]; [by rewrite lookup_insert_eq|].
      by rewrite lookup_insert_ne. }
    assert (Hthr : ∀ t g, M'' !! t = Some g →
              ∃ g0, M !! t = Some g0 ∧ LErel (S (S n)) W (A'' t) (U t) ∅ g ∧ tenv_bipol (A'' t) ∧
                tenv_ends (A'' t) ⊆ tenv_ends (A t) ∧ (U t = T ∨ U t = TUnit)).
    { intros t g Hg. rewrite HM'' in Hg. unfold A''. destruct (decide (t = i)) as [->|Hti].
      - injection Hg as <-. exists e. rewrite eupd_eq. split_and!; try done.
        + rewrite Hends. set_solver.
        + by apply (st_ty i e).
      - exists g. rewrite eupd_ne by done. split_and!; try done.
        + by apply st_rel. + by apply (st_bipol t g). + by apply (st_ty t g). }
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
    { intros t g ch b0 Hg Hn o Ho. destruct (Hthr t g Hg) as (g0 & _ & _ & Hb & _).
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
    assert (Hmove : ∀ t g, M'' !! t = Some g → tenv_move W c d (A'' t) (tenv_mv c d (A'' t))).
    { intros t g Hg. apply tenv_move_mv; [done|]. intros oc Hoc od Hod. by apply (Hcond t g Hg). }
    assert (HEf : ∀ t g, M'' !! t = Some g →
              LErel (S (S n)) W (tenv_mv c d (A'' t)) (U t) ∅ (chsubst c d g)).
    { intros t g Hg. destruct (Hthr t g Hg) as (g0 & _ & HEg & _).
      apply (LErel_fuse _ W (A'' t)); [done|done| |done]. by apply (Hmove t g). }
    assert (Hbipf : ∀ t g, M'' !! t = Some g → tenv_bipol (tenv_mv c d (A'' t))).
    { intros t g Hg. destruct (Hthr t g Hg) as (g0 & _ & _ & Hb & _).
      apply (tenv_bipol_move W c d (A'' t)); [done| |done]. by apply (Hmove t g). }
    assert (Hcond' : ∀ t g, M'' !! t = Some g → ∀ oc od, A'' t !! c = Some oc → A'' t !! d = Some od →
              ∃ ec ed, oc = One ec ∧ od = One ed).
    { intros t g Hg oc od Hoc Hod. destruct (Hcond t g Hg oc od Hoc Hod) as (ec & ed & -> & -> & _). eauto. }
    assert (Hmv : ∀ t g o, M'' !! t = Some g →
              tenv_end (tenv_mv c d (A'' t)) o =
                if decide (o.1 = c) then None
                else if decide (o.1 = d) then
                  match tenv_end (A'' t) (c, o.2) with Some x => Some x | None => tenv_end (A'' t) o end
                else tenv_end (A'' t) o).
    { intros t g o Hg. apply (tenv_end_mv c d (A'' t) o Hcd (Hbipf t g Hg) (Hcond' t g Hg)). }
    assert (Hendsmv : ∀ t g, M'' !! t = Some g →
              tenv_ends (tenv_mv c d (A'' t)) = set_map (osub c d) (tenv_ends (A'' t))).
    { intros t g Hg. apply (tenv_ends_mv c d (A'' t) Hcd (Hbipf t g Hg) (Hcond' t g Hg)). }
    assert (HM' : ∀ t g', (chsubst c d <$> M'') !! t = Some g' → ∃ g, M'' !! t = Some g ∧ g' = chsubst c d g).
    { intros t g' Hg'. rewrite lookup_fmap in Hg'. destruct (M'' !! t) as [g|]; [|done].
      injection Hg' as <-. by exists g. }
    assert (HM'b : ∀ t g, M'' !! t = Some g → (chsubst c d <$> M'') !! t = Some (chsubst c d g)).
    { intros t g Hg. by rewrite lookup_fmap, Hg. }
    assert (HMM'' : ∀ t g, M !! t = Some g → ∃ g'', M'' !! t = Some g'').
    { intros t g Hg. rewrite HM''. case_decide; eauto. }
    assert (d ∈ C) as HdC by apply (lfc_closed_end _ _ _ _ _ _ _ Hc i e _ _ He Hxd).
    exists (λ t, tenv_mv c d (A'' t)). split.
    2:{ apply (fuel_link i e c bc d bd e' Θ1 xc xd); try done.
        intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->). by apply (Hendsmv t g). }
    assert (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> M'') = delete (c, true) (delete (c, false) π))
      as Hpu.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite He. unfold pev1.
      destruct (act_step _ _ _ Hst) as (a & Ha & Ho). rewrite Ha. apply offers_link in Ho as (o1 & o2 & -> & _).
      simpl. assert (C ∖ (C ∖ {[c]}) = {[c]}) as ->.
      { apply set_eq. intros x. destruct (decide (x = c)) as [->|]; set_solver. }
      by rewrite elements_singleton. }
    fold M''. rewrite Hpu.
    apply (LFconf_frame (S (S n)) n W T π _ (C, M) (C ∖ {[c]}, chsubst c d <$> M'') A _ U U
      (cends c ∪ cends d) Hc); simpl.
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->).
      eapply LErel_down; [|exact (HEf t g Hg)]. lia.
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->). by apply (Hbipf t g).
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->). by destruct (Hthr t g Hg) as (? & _ & _ & _ & _ & ?).
    - intros t s g' h' Hts Hg' Hh'. destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (HM' s h' Hh') as (h & Hh & ->).
      rewrite (Hendsmv t g Hg), (Hendsmv s h Hh).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _ & _ & Hsg & _).
      destruct (Hthr s h Hh) as (h0 & Hh0 & _ & _ & Hsh & _).
      pose proof (st_disj t s g0 h0 Hts Hg0 Hh0) as Hd0.
      intros o Ho1 Ho2.
      apply elem_of_map in Ho1 as (o1 & -> & Ho1). apply elem_of_map in Ho2 as (o2 & Ho12 & Ho2).
      destruct (decide (o1 = o2)) as [<-|Hne12]; [by apply (Hd0 o1); [apply Hsg|apply Hsh]|].
      assert (∀ u k b0, M'' !! u = Some k → (c, b0) ∈ tenv_ends (A'' u) → b0 = negb bc) as Hcend.
      { intros u k b0 Hk Hin. destruct (decide (b0 = bc)) as [->|Hb].
        - exfalso. rewrite tenv_ends_end, (proj1 (Hfree' u k Hk)) in Hin. by destruct Hin.
        - by destruct b0, bc. }
      assert (∀ u k, M'' !! u = Some k → (d, bd) ∉ tenv_ends (A'' u)) as Hdend.
      { intros u k Hk Hin. rewrite tenv_ends_end, (proj2 (Hfree' u k Hk)) in Hin. by destruct Hin. }
      destruct (osub_eq_cases c d o1 o2 Hcd Ho12 Hne12) as [[E1 E2]|[E1 E2]].
      + rewrite E1 in Ho1. rewrite E2 in Ho2. pose proof (Hcend t g _ Hg Ho1) as Hb.
        rewrite Hb, <-Hbd in Ho2. by apply (Hdend s h Hh).
      + rewrite E1 in Ho1. rewrite E2 in Ho2. pose proof (Hcend s h _ Hh Ho2) as Hb.
        rewrite Hb, <-Hbd in Ho1. by apply (Hdend t g Hg).
    - intros t g' Hg'. destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _ & _ & Hsg & _). pose proof (st_closed t g0 Hg0) as Hcl.
      rewrite <-tenv_ends_dom, (Hendsmv t g Hg). intros x (o & -> & Ho)%elem_of_map.
      apply elem_of_map in Ho as (o0 & -> & Ho0). destruct o0 as [c0 b0].
      unfold osub, csub. simpl. destruct (decide (c0 = c)) as [->|Hc0]; [set_solver|].
      assert (c0 ∈ dom (A t)) by (apply dom_tenv_ends; exists b0; by apply Hsg).
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
      destruct (lfc_partner _ _ _ _ _ _ _ Hc i e _ _ He Hxc) as (s & gs & ys & Hgs & Hys & Hys2 & Hys1).
      destruct (lfc_partner _ _ _ _ _ _ _ Hc i e _ _ He Hxd) as (u & gu & yu & Hgu & Hyu & Hyu2 & Hyu1).
      destruct (HMM'' s gs Hgs) as [gs'' Hgs'']. destruct (HMM'' u gu Hgu) as [gu'' Hgu''].
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
        rewrite (Heq'' u gu); [done|done|intros [= ? ?]; congruence|intros [= Hb]; by destruct bd]. }
      destruct (decide (β = bd)) as [->|Hβ].
      + assert (tenv_end (A'' t) (c, bd) = Some x) as Hxt.
        { destruct (tenv_end (A'' t) (c, bd)) eqn:E; [done|]. by rewrite (proj2 (Hfree' t g Hg)) in Hx. }
        rewrite Hbd in Hxt. rewrite (Heq'' t g0) in Hxt by (done || neq_tac).
        destruct (lfc_partner_at _ _ _ _ _ _ _ Hc i e _ _ t g0 _ He Hxc Hg0 Hxt) as [Hx2 Hx1].
        assert (x.2 = xd.2) as Hx2' by (rewrite Hx2, Hdx; by rewrite pt_dual_dual).
        split; [rewrite Hx2'; by apply (lf_pt _ _ _ _ _ _ _ _ Hc i e _ _ He Hxd)|].
        exists yu. split_and!.
        * exists u, (chsubst c d gu''). split; [by apply HM'b|]. done.
        * by rewrite Hyu2, Hx2'.
        * by apply (sdual_link xc.1 xd.1).
      + assert (β = negb bd) as -> by (by destruct β, bd).
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
    - intros o x Ho (t & g' & Hg' & Hx). destruct (HM' t g' Hg') as (g & Hg & ->).
      destruct (Hthr t g Hg) as (g0 & Hg0 & _).
      rewrite (Hmv t g o Hg) in Hx. destruct o as [c' β]. simpl in Hx.
      destruct (decide (c' = c)) as [->|Hc']; [done|].
      destruct (decide (c' = d)) as [->|Hd'].
      2:{ exfalso. apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_cends in Ho; simpl in Ho; congruence. }
      destruct (decide (β = bd)) as [->|Hβ].
      + assert (tenv_end (A'' t) (c, bd) = Some x) as Hxt.
        { destruct (tenv_end (A'' t) (c, bd)) eqn:E; [done|]. by rewrite (proj2 (Hfree' t g Hg)) in Hx. }
        rewrite Hbd in Hxt. rewrite (Heq'' t g0) in Hxt by (done || neq_tac).
        exact (lf_known _ _ _ _ _ _ _ _ Hc t g0 _ _ Hg0 Hxt).
      + assert (β = negb bd) as -> by (by destruct β, bd).
        assert (tenv_end (A'' t) (c, negb bd) = None) as Hnt.
        { assert (negb bd = bc) as -> by (rewrite Hbd; by destruct bc). apply (proj1 (Hfree' t g Hg)). }
        rewrite Hnt in Hx. rewrite (Heq'' t g0) in Hx by (done || neq_tac).
        exact (lf_known _ _ _ _ _ _ _ _ Hc t g0 _ _ Hg0 Hx).
  Qed.
End step.

(** ** Preservation of the soup along a step *)

Theorem lfsoup_conf_step n W T π P F K q A U L q' :
  strict W → LFconf (S (S n)) W ∅ T π q A U → lf_fuelc (S (S n)) W π P F K A q → istep q L q' →
  ∃ A' U', LFconf n W ∅ T (pupd π q L q') q' A' U' ∧
    lf_fuelc n W (pupd π q L q') (fstep W P F q L q').1 (fstep W P F q L q').2 (kstep K q L q') A' q'.
Proof.
  intros HW Hc HF Hst. destruct q as [C M].
  inversion Hst as [C0 M0 i e e' Hi Hs|C0 M0 i e c x e' Hi Hs HC Hcs|C0 M0 i j e v e' Hi Hs Hj
    |C0 M0 i j c b v e e' f f' Hij Hi Hj He Hf|C0 M0 i j c b e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j c β b e e' f f' Hij Hi Hj He Hf|C0 M0 i e c bc d bd e' Hi Hs HC]; subst;
    match goal with |- context [kstep K ?q ?L ?q'] =>
      first [ pose proof (kstep_one K q q' i _ _ _ Hi Hs) as Hk; simpl in Hk
            | pose proof (kstep_pair K q q' i j Hij) as Hk ] end;
    setoid_rewrite Hk; clear Hk.
  - exists A, U. by apply (step_beta n W HW T π C M A U Hc P F K HF i e e').
  - destruct (step_new n W HW T π C M A U Hc P F K HF i e c x e' Hi Hs HC) as [A' ?]. by exists A', U.
  - assert (dom (<[j:=App v EUnit]> (<[i:=e']> M)) ∖ dom M = {[j]}) as Hdj.
    { rewrite !dom_insert_L. apply elem_of_dom_2 in Hi. apply not_elem_of_dom in Hj. set_solver. }
    setoid_rewrite Hdj. setoid_rewrite elements_singleton. simpl. by apply (step_spawn n W HW T π C M A U Hc P F K HF i j e v e').
  - destruct (step_msg n W HW T π C M A U Hc P F K HF i j c b v e e' f f') as [A' ?]; try done.
    by exists A', U.
  - destruct (step_close n W HW T π C M A U Hc P F K HF i j c b e e' f f') as [A' ?]; try done.
    by exists A', U.
  - destruct (step_choice n W HW T π C M A U Hc P F K HF i j c β b e e' f f') as [A' ?]; try done.
    by exists A', U.
  - destruct (decide (c = d)) as [<-|Hcd].
    + destruct (step_link_self n W HW T π C M A U Hc P F K HF i e c bc bd e') as [A' ?]; try done.
      by exists A', U.
    + destruct (step_link_ne n W HW T π C M A U Hc P F K HF i e c bc d bd e') as [A' ?]; try done.
      by exists A', U.
Qed.

(** The soup steps: the key lemma of §16.5 with the fuel conjunct of §17.3. *)
Theorem lfsoup_step n W T P F K q L q' :
  strict W → LFsoup (S (S n)) W ∅ T P F K q → istep q L q' →
  LFsoup n W ∅ T (fstep W P F q L q').1 (fstep W P F q L q').2 (kstep K q L q') q'.
Proof.
  intros HW (A & U & Hc & HF) Hst. apply (LFsoupAt_ppts n W ∅ T (pupd (ppts P q) q L q')).
  by apply (lfsoup_conf_step n W T (ppts P q) P F K q A U L q').
Qed.

(** ** One placement for every index (§16.5)

    Along a run, the points, counters and tickets of every thread are
    computed by [fstep] and [kstep] at every step. They do not depend on
    the index, and every position of the run carries the soup at every
    index. *)

Fixpoint frun (W : world) (P : nat → gmap cend point) (F : nat → gmap cend fuel) (r : nat → config)
    (l : nat → gset nat) (k : nat) : (nat → gmap cend point) * (nat → gmap cend fuel) :=
  match k with
  | 0 => (P, F)
  | S k' => fstep W (frun W P F r l k').1 (frun W P F r l k').2 (r k') (l k') (r (S k'))
  end.

Fixpoint krun (K : nat → nat) (r : nat → config) (l : nat → gset nat) (k : nat) : nat → nat :=
  match k with
  | 0 => K
  | S k' => kstep (krun K r l k') (r k') (l k') (r (S k'))
  end.

Lemma fstep_stuck W P F q : fstep W P F q ∅ q = (P, F).
Proof. unfold fstep. by rewrite elements_empty. Qed.

Lemma kstep_stuck K q : kstep K q ∅ q = K.
Proof. unfold kstep. by rewrite elements_empty. Qed.

Theorem lfsoup_run W T P F K r l :
  strict W → maximal r l → (∀ n, LFsoup n W ∅ T P F K (r 0)) →
  ∀ k n, LFsoup n W ∅ T (frun W P F r l k).1 (frun W P F r l k).2 (krun K r l k) (r k).
Proof.
  intros HW Hmax H0 k. induction k as [|k IH]; [done|]. intros n. simpl.
  destruct (Hmax k) as [Hst|(_ & Heq & Hl)].
  - by apply (lfsoup_step n W T _ _ _ (r k) (l k)); [|apply IH|].
  - rewrite Heq, Hl, fstep_stuck, kstep_stuck. eapply LFsoup_down; [|apply (IH (S n))]. lia.
Qed.

(** Along any sequence of steps. *)
Lemma lfsoup_isteps W T P F K q0 q1 :
  strict W → isteps q0 q1 → (∀ n, LFsoup n W ∅ T P F K q0) →
  ∃ P' F' K', ∀ n, LFsoup n W ∅ T P' F' K' q1.
Proof.
  intros HW Hs. revert P F K. induction Hs as [q|q q2 q3 [L Hst] _ IH]; intros P F K H0.
  { by exists P, F, K. }
  apply (IH (fstep W P F q L q2).1 (fstep W P F q L q2).2 (kstep K q L q2)). intros n.
  by apply (lfsoup_step n W T P F K q L q2).
Qed.

(** ** Local progress of one soup

    The dependency of a pending thread is the holder of the partner end
    in the soup, the thread whose own ends (dom of its points) contain it.
    A term may name an end in code it never runs, so the soup does not
    speak about [waits], which reads names. *)

Definition hwaits (P : nat → gmap cend point) (q : config) (t s : nat) : Prop :=
  s ≠ t ∧ ∃ e a S o, q.2 !! t = Some e ∧ act e = Some a ∧ aends a = Some S ∧ o ∈ S ∧
    is_Some (q.2 !! s) ∧ cdual o ∈ dom (P s).

Lemma tenv_ext_dom Θ1 c e Θ : tenv_ext Θ1 c e Θ → dom Θ = {[c]} ∪ dom Θ1.
Proof. intros [[_ ->]|(e' & _ & [-> | ->])]; by rewrite dom_insert_L. Qed.

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

Section progress.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S n) W ∅ T π q A U).

  (** A link acts on two ends of the actor's environment, one of them
      restricted. *)
  Lemma lp_link t e : q.2 !! t = Some e → link_t e → enabled q t.
  Proof.
    intros He (cd & e' & Hst). destruct (act_step _ _ _ Hst) as (a & Ha & Ho).
    apply offers_link in Ho as (c & d & -> & Hcd).
    apply (admin_enabled q t e _ He Ha I). intros c' d' [= <- <-]. left.
    destruct (LErel_S_link _ _ _ _ _ _ _ _ (lf_rel _ _ _ _ _ _ _ _ Hc t e He) Hst)
      as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & Hcd' & H1 & H2 & _).
    apply (lfc_closed _ _ _ _ _ _ _ Hc t e He).
    rewrite (tenv_ext_dom _ _ _ _ H2), (tenv_ext_dom _ _ _ _ H1).
    assert (c ∈ ({[(c1, pt_pol kc); (d1, pt_pol kd)]} : gset cend)) as Hin
      by (rewrite <-Hcd', Hcd; set_solver).
    apply elem_of_union in Hin as [->%elem_of_singleton| ->%elem_of_singleton]; simpl; set_solver.
  Qed.
  Lemma offers_same_end a σ σ' :
    offers a (LSess σ) → offers a (LSess σ') → (∀ cd, σ ≠ SLink cd) → sl_end σ = sl_end σ'.
  Proof.
    intros H1 H2 Hnl. destruct a, σ, σ'; simpl in *; try done; destruct_and?; subst; try done.
  Qed.

  Lemma lp_meet t e s es k ek k' ek' :
    q.2 !! t = Some e → q.2 !! s = Some es →
    offered_t (A t) e k → offered_t (A s) es k' →
    tenv_entry (A t) k = Some ek → tenv_entry (A s) k' = Some ek' →
    k'.1 = k.1 → (s, k') ≠ (t, k) → ek'.2 = pt_dual ek.2 →
    enabled q t ∨ (enabled q s ∧ link_t es).
  Proof.
    intros He Hes (σ & e1 & Hst & Hsel) (σ' & es1 & Hst' & Hsel') Hk Hk' H1 Hne Hd.
    destruct (slabel_link_dec σ) as [[cd ->]|Hnl]; [left; apply (lp_link t e He); by exists cd, e1|].
    destruct (slabel_link_dec σ') as [[cd ->]|Hnl'].
    { right. split; [apply (lp_link s es Hes)|]; by exists cd, es1. }
    destruct (sl_end_some σ Hnl) as [o Ho]. destruct (sl_end_some σ' Hnl') as [o' Ho'].
    destruct (selects_info _ _ _ _ _ Hsel Hk Ho) as (Ho1 & Ho2 & Hkd).
    destruct (selects_info _ _ _ _ _ Hsel' Hk' Ho') as (Ho1' & Ho2' & Hkd').
    assert (o' = cdual o) as Ho'o.
    { destruct o as [c β], o' as [c' β']. unfold cdual. simpl in *. f_equal; [congruence|].
      by rewrite <-Ho2', <-Ho2, Hd, pt_pol_dual. }
    destruct (decide (s = t)) as [->|Hst_].
    { exfalso. rewrite He in Hes. injection Hes as <-.
      destruct (act_step _ _ _ Hst) as (a & Ha & Hoa). destruct (act_step _ _ _ Hst') as (a' & Ha' & Hoa').
      rewrite Ha in Ha'. injection Ha' as <-. pose proof (offers_same_end a σ σ' Hoa Hoa' Hnl) as Hse.
      rewrite Ho, Ho', Ho'o in Hse. injection Hse as Hse. by apply (cdual_ne o). }
    pose proof (lfc_bipol _ _ _ _ _ _ _ Hc t e He) as Hbt. pose proof (lfc_bipol _ _ _ _ _ _ _ Hc s es Hes) as Hbs.
    pose proof (tenv_end_entry _ _ _ Hbt Hk) as Het. pose proof (tenv_end_entry _ _ _ Hbs Hk') as Hes'.
    assert ((k'.1, pt_pol ek'.2) = cdual (k.1, pt_pol ek.2)) as Hcd.
    { unfold cdual. simpl. by rewrite H1, Hd, pt_pol_dual. }
    rewrite Hcd in Hes'.
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc t e _ _ s es _ He Het Hes Hes') as [_ Hsd].
    pose proof (sdual_kind _ _ Hsd) as Hkk. rewrite Hkd, Hkd' in Hkk.
    assert (o.1 ∈ q.1) as Hoq.
    { rewrite <-Ho1. apply (lfc_closed_end _ _ _ _ _ _ _ Hc t e _ ek He Het). }
    destruct q as [C Mq]. simpl in *. left.
    destruct o as [c β]. subst o'. unfold cdual in *; simpl in *.
    destruct σ as [o0 w|o0 w|o0|cd|o0 bb|o0 bb]; destruct σ' as [o1 w'|o1 w'|o1|cd'|o1 bb'|o1 bb'];
      simpl in Hkk, Ho, Ho'; try discriminate; try (by destruct (Hnl cd)); try (by destruct (Hnl' cd'));
      injection Ho as ->; injection Ho' as ->.
    - (* t receives, s sends *)
      destruct (recv_retarget e _ w e1 w' Hst (tstep_send_val _ _ _ _ Hst')) as [e2 He2].
      eexists _, _. split; [eapply (IMsg C Mq s t c (negb β) w'); [done|done|done|exact Hst'|]|set_solver].
      by rewrite negb_involutive.
    - (* t sends, s receives *)
      destruct (recv_retarget es _ w' es1 w Hst' (tstep_send_val _ _ _ _ Hst)) as [es2 Hes2].
      eexists _, _. split; [eapply (IMsg C Mq t s c β w); [done|done|done|exact Hst|exact Hes2]|set_solver].
    - (* close *)
      eexists _, _. split; [eapply (IClose C Mq t s c β); [done|done|done|exact Hst|exact Hst'|]|set_solver].
      exact Hoq.
    - (* t selects, s branches *)
      destruct (bra_retarget es _ bb' es1 bb Hst') as [es2 Hes2].
      eexists _, _. split; [eapply (IChoice C Mq t s c β bb); [done|done|done|exact Hst|exact Hes2]|set_solver].
    - (* t branches, s selects *)
      destruct (bra_retarget e _ bb e1 bb' Hst) as [e2 He2].
      eexists _, _. split; [eapply (IChoice C Mq s t c (negb β) bb'); [done|done|done|exact Hst'|]|set_solver].
      by rewrite negb_involutive.
  Qed.

  Theorem lfc_local_progress (P : nat → gmap cend point) :
    (∀ t e, q.2 !! t = Some e → dom (P t) = tenv_ends (A t)) →
    ∀ t, pend q t → ∃ s, rtc (hwaits P q) t s ∧ enabled q s.
  Proof.
    intros HP. apply (local_progress_gen q W A (λ _, ∅) HW (hwaits P q)).
    - intros t e He Hnirr. apply (LErel_S_ready n W (A t) (U t) ∅ e); [|done].
      apply (lf_rel _ _ _ _ _ _ _ _ Hc t e He).
    - intros t e k ek He Hk Hirr.
      pose proof (LErel_S_stop n W (A t) (U t) ∅ e (lf_rel _ _ _ _ _ _ _ _ Hc t e He) Hirr) as HV.
      assert (A t = ∅) as HA.
      { destruct (lf_ty _ _ _ _ _ _ _ _ Hc t e He) as [HU|HU]; rewrite HU in HV.
        - eapply LVrel_prim_empty; [apply (lf_prim _ _ _ _ _ _ _ _ Hc)|exact HV].
        - by apply LVrel_unit_iff in HV as [-> _]. }
      rewrite HA in Hk. unfold tenv_entry in Hk. rewrite lookup_empty in Hk. by destruct k.2.
    - intros t e k ek s es k' ek' He Ho Hk Hes Hk' Hk1 Hd Hst.
      destruct (offered_aends _ _ _ _ Ho Hk) as (a & S & Ha & HS & HkS).
      split; [done|]. exists e, a, S, (k.1, pt_pol ek.2). split_and!; [done|done|done|done|by eexists|].
      rewrite (HP s es Hes).
      pose proof (tenv_end_entry _ _ _ (lfc_bipol _ _ _ _ _ _ _ Hc s es Hes) Hk') as Hx.
      apply tenv_end_ends in Hx. rewrite Hk1, Hd, pt_pol_dual in Hx. exact Hx.
    - intros t e k ek He Hk.
      pose proof (tenv_end_entry _ _ _ (lfc_bipol _ _ _ _ _ _ _ Hc t e He) Hk) as Hx.
      destruct (lfc_partner _ _ _ _ _ _ _ Hc t e _ _ He Hx) as (s & es & y & Hes & Hy & Hy2 & _).
      destruct (tenv_end_entry_inv _ _ _ Hy) as (k' & Hk' & Hk1).
      exists s, es, k', y. split_and!; [done|done|done| |done].
      intros [= -> ->]. rewrite Hk in Hk'. injection Hk' as ->.
      assert (pt_pol y.2 = negb (pt_pol y.2)) as Hp by (rewrite Hy2 at 1; apply pt_pol_dual).
      by destruct (pt_pol y.2).
    - intros t e s es k ek k' ek' He Hes Ho Ho' Hk Hk' H1 Hne Hd.
      destruct (lp_meet t e s es k ek k' ek') as [?|[? _]]; auto.
    - by apply lp_link.
  Qed.
End progress.

(** ** Relabelling the threads *)

Lemma relabel_map (M1 M2 : gmap nat expr) :
  soup M1 = soup M2 →
  ∃ f : nat → nat, (∀ t e, M2 !! t = Some e → M1 !! f t = Some e) ∧
    (∀ t t' e e', M2 !! t = Some e → M2 !! t' = Some e' → f t = f t' → t = t') ∧
    (∀ s e, M1 !! s = Some e → ∃ t, f t = s ∧ M2 !! t = Some e).
Proof.
  revert M1. induction M2 as [|i e M2 Hi IH] using map_ind; intros M1 HM.
  - rewrite soup_empty in HM. exists id. split_and!; [by intros ??; rewrite lookup_empty..|].
    intros s e Hs. exfalso. assert (e ∈ soup M1) as Hin by (apply elem_of_soup; by exists s).
    rewrite HM in Hin. multiset_solver.
  - rewrite soup_insert in HM by done.
    destruct (soup_extract M1 (soup M2) e HM) as (j & Hj & HMj).
    destruct (IH (delete j M1) HMj) as (f & H1 & H2 & H3).
    exists (λ t, if decide (t = i) then j else f t). split_and!.
    + intros t e' Ht. destruct (decide (t = i)) as [->|Hti].
      * rewrite lookup_insert_eq in Ht. by injection Ht as <-.
      * rewrite lookup_insert_ne in Ht by done. pose proof (H1 t e' Ht) as H. by apply lookup_delete_Some in H as [_ ?].
    + intros t t' e1 e2 Ht Ht' Hf.
      destruct (decide (t = i)) as [->|Hti], (decide (t' = i)) as [->|Ht'i]; try done.
      * exfalso. rewrite lookup_insert_ne in Ht' by done. pose proof (H1 t' e2 Ht') as H.
        rewrite <-Hf, lookup_delete_eq in H. done.
      * exfalso. rewrite lookup_insert_ne in Ht by done. pose proof (H1 t e1 Ht) as H.
        rewrite Hf, lookup_delete_eq in H. done.
      * rewrite lookup_insert_ne in Ht, Ht' by done. by apply (H2 t t' e1 e2).
    + intros s e' Hs. destruct (decide (s = j)) as [->|Hsj].
      * exists i. rewrite decide_True by done. rewrite lookup_insert_eq. split; [done|]. congruence.
      * destruct (H3 s e') as (t & <- & Ht); [by rewrite lookup_delete_ne|].
        exists t. assert (t ≠ i) by (intros ->; congruence).
        rewrite decide_False by done. rewrite lookup_insert_ne by done. done.
Qed.

Lemma LFsoupAt_relabel n W Σ T π P F K C M1 M2 (f : nat → nat) :
  (∀ t e, M2 !! t = Some e → M1 !! f t = Some e) →
  (∀ t t' e e', M2 !! t = Some e → M2 !! t' = Some e' → f t = f t' → t = t') →
  (∀ s e, M1 !! s = Some e → ∃ t, f t = s ∧ M2 !! t = Some e) →
  LFsoupAt n W Σ T π P F K (C, M1) → LFsoupAt n W Σ T π (P ∘ f) (F ∘ f) (K ∘ f) (C, M2).
Proof.
  intros H1 H2 H3 (A & U & Hc & HF). exists (A ∘ f), (U ∘ f).
  destruct Hc as [Hp Hr Hb Hty Hpt Hd Hpair Hcl Hsig Hown Hkn]. split; [split|]; simpl in *.
  - done.
  - intros t e He. exact (Hr (f t) e (H1 t e He)).
  - intros t e He. exact (Hb (f t) e (H1 t e He)).
  - intros t e He. exact (Hty (f t) e (H1 t e He)).
  - intros t e o x He Hx. apply (Hpt (f t) e o x); [by apply H1|done].
  - intros t s e es Hts He Hes. apply (Hd (f t) (f s) e es); [|by apply H1|by apply H1].
    intros Heq. apply Hts. by apply (H2 t s e es).
  - intros t e o x He Hx Ho. destruct (Hpair (f t) e o x (H1 t e He) Hx Ho) as (s & es & y & Hes & Hy & ?).
    destruct (H3 s es Hes) as (t' & <- & Ht'). by exists t', es, y.
  - intros t e He. exact (Hcl (f t) e (H1 t e He)).
  - intros t e o x He. exact (Hsig (f t) e o x (H1 t e He)).
  - intros c x Hx. destruct (Hown c x Hx) as (s & es & Hes & Hy).
    destruct (H3 s es Hes) as (t' & <- & Ht'). by exists t', es.
  - intros t e o x He. exact (Hkn (f t) e o x (H1 t e He)).
  - intros t e He. exact (HF (f t) e (H1 t e He)).
Qed.

(** The soup of a judgment, at any lifting of the process. *)
Lemma LFP_soup W Σ T p q :
  LFP W Σ T p → erase q = p → ∃ P F K, ∀ n, LFsoup n W Σ T P F K q.
Proof.
  intros [_ (q0 & P & F & K & Hq0 & HS)] Hq. destruct q as [C M], q0 as [C0 M0].
  unfold erase in Hq, Hq0. simpl in *. rewrite <-Hq in Hq0. injection Hq0 as -> HM.
  destruct (relabel_map M0 M HM) as (f & H1 & H2 & H3).
  exists (P ∘ f), (F ∘ f), (K ∘ f). intros n. apply (LFsoupAt_ppts n W Σ T (ppts P (C, M0))).
  apply (LFsoupAt_relabel n W Σ T _ P F K C M0 M f); [done|done|done|apply HS].
Qed.
