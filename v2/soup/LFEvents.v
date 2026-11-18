(** * The ends an event touches (stage S8)

    In a soup, the ends a step acts on and the ends it hands on are held
    by its actors ([s_ev_ends]). So the entry of an end held by a thread
    outside a step other than a link is kept ([own_next_keep]), and the
    entry of an end of an actor that the step does not act on only ticks
    or moves with one unit less ([own_next_tick]). *)

From stdpp Require Import relations.
From GV Require Export soup.LFLocal.

Definition owns (K : own) (o : cend) (t : nat) : Prop := ∃ h, K !! o = Some h ∧ h.(h_th) = t.

Definition ev_ends (K : own) (ev : event) : Prop :=
  match ev with
  | EvMsg i j o M => owns K o i ∧ owns K (edual o) j ∧ (∀ m, m ∈ M → owns K m i ∧ m ≠ o)
  | EvClose i j o | EvChoice i j o _ => owns K o i ∧ owns K (edual o) j
  | EvSpawn i j M => ∀ m, m ∈ M → owns K m i
  | EvLink u o1 o2 => owns K o1 u ∧ owns K o2 u ∧ o1 ≠ o2
  | EvNew _ _ c | EvNewAt _ _ _ c => (EPos c ∉ dom K) ∧ (ENeg c ∉ dom K)
  | _ => True
  end.

Lemma owns_unique K o t s : owns K o t → owns K o s → t = s.
Proof. intros (h & H1 & <-) (h' & H2 & <-). congruence. Qed.

Lemma owns_of {Y : Type} (K : own) t (m : gmap cend Y) o v : kres K t m !! o = Some v → owns K o t.
Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

Lemma s_ev_ends N n W T C Mq K tk A Π U ev q' :
  soup_inv N (S n) W ∅ T (LFState (C, Mq) K tk) A Π U → types.Worlds.strict W →
  istep (C, Mq) ev q' → ev_tau ev → ev_ends K ev.
Proof.
  intros Hs HW Hst Hτ.
  pose proof (l_obl _ _ _ _ _ _ _ _ Hs HW) as Hobl. cbn [s_q s_K] in Hobl.
  inversion Hst as [C0 M0 i e e' Hi Hs'|C0 M0 i e ℓ c e' Hi Hs' HC Hc|C0 M0 i e κ o c e' Hi Hs' HC Hc
    |C0 M0 i j e Mv v e' Hi Hs' Hj
    |C0 M0 i j o Mv v e e' f f' Hij Hi Hj He Hf|C0 M0 i j o e e' f f' Hij Hi Hj He Hf HC
    |C0 M0 i j o b e e' f f' Hij Hi Hj He Hf|C0 M0 i e o1 o2 e' Hi Hs' HC
    |C0 M0 i e σ e' Hi Hs' HC]; subst; simpl; try done.
  - split; intros Hd; apply HC; exact (s_closed _ _ _ _ _ _ _ _ Hs _ Hd).
  - split; intros Hd; apply HC; exact (s_closed _ _ _ _ _ _ _ _ Hs _ Hd).
  - pose proof (Hobl i e _ e' Hi Hs') as H. cbn [Eobl] in H.
    destruct H as (ΘM & Θr & Hd & HΘ & HM & _).
    intros m Hm. destruct (split_mres _ _ _ _ Hd HΘ HM) as [-> _].
    rewrite <-HM, dom_mres in Hm. apply elem_of_intersection in Hm as [Hm _].
    apply elem_of_dom in Hm as [v' Hv']. exact (owns_of _ _ _ _ _ Hv').
  - pose proof (Hobl i e _ e' Hi He) as H1. pose proof (Hobl j f _ f' Hj Hf) as H2. cbn [Eobl] in H1, H2.
    destruct H1 as (S0 & x & m & U0 & b0 & S & ΘM & Θr & Ho & _ & Hd & HΘ & HM & _).
    destruct H2 as (S0' & x' & m' & U0' & b0' & S' & Ho' & _).
    split_and!; [exact (owns_of _ _ _ _ _ Ho)|exact (owns_of _ _ _ _ _ Ho')|].
    intros m1 Hm. destruct (split_mres _ _ _ _ Hd HΘ HM) as [-> _].
    rewrite <-HM, dom_mres in Hm. apply elem_of_intersection in Hm as [Hm _].
    apply elem_of_dom in Hm as [v' Hv']. apply lookup_delete_Some in Hv' as [Hne Hv'].
    split; [exact (owns_of _ _ _ _ _ Hv')|done].
  - pose proof (Hobl i e _ e' Hi He) as H1. pose proof (Hobl j f _ f' Hj Hf) as H2. cbn [Eobl] in H1, H2.
    destruct H1 as (S0 & x & Ho & _). destruct H2 as (S0' & x' & Ho' & _).
    split; [exact (owns_of _ _ _ _ _ Ho)|exact (owns_of _ _ _ _ _ Ho')].
  - pose proof (Hobl i e _ e' Hi He) as H1. pose proof (Hobl j f _ f' Hj Hf) as H2. cbn [Eobl] in H1, H2.
    destruct H1 as (S0 & x & S1 & S2 & Ho & _). destruct H2 as (S0' & x' & S1' & S2' & Ho' & _).
    split; [exact (owns_of _ _ _ _ _ Ho)|exact (owns_of _ _ _ _ _ Ho')].
  - destruct (link_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e o1 o2 e' Hi Hs') as (H12 & H1 & H2 & _). done.
Qed.

(** ** Entries after an event *)

Lemma owns_ne K o h t o' p : K !! o = Some h → h.(h_th) = t → owns K o' p → p ≠ t → o ≠ o'.
Proof. intros Ho Eh (h' & Ho' & Ep) Hpt ->. rewrite Ho in Ho'. by simplify_eq. Qed.

Ltac ne_tac Ho Eh :=
  first [ eapply (owns_ne _ _ _ _ _ _ Ho Eh); [eassumption|set_solver] ].


Lemma own_next_keep N ev K t o h :
  ev_ends K ev → (∀ u o1 o2, ev ≠ EvLink u o1 o2) → t ∉ ev_parts ev →
  K !! o = Some h → h.(h_th) = t → own_next N ev K !! o = Some h.
Proof.
  intros Hen Hnl Ht Ho Eh. destruct ev as [i|i ℓ c|i κ o' c|i j M|i j o' M|i j o'|i j o' b|u o1 o2|i σ];
    simpl in Hen, Ht |- *; try done.
  - destruct Hen as [H1 H2]. unfold knew. pose proof (elem_of_dom_2 _ _ _ Ho) as Hd.
    rewrite !lookup_insert_ne; [done|intros <-; done|intros <-; done].
  - destruct Hen as [H1 H2]. unfold knew. pose proof (elem_of_dom_2 _ _ _ Ho) as Hd.
    rewrite !lookup_insert_ne; [done|intros <-; done|intros <-; done].
  - rewrite lookup_khand, Ho. simpl. case_decide as Hm; [|done].
    destruct (Hen o Hm) as (h' & Ho' & <-). rewrite Ho in Ho'. simplify_eq. set_solver.
  - destruct Hen as (H1 & H2 & H3).
    assert (o ≠ o') by ne_tac Ho Eh. assert (o ≠ edual o') by ne_tac Ho Eh.
    assert (o ∉ M) as HoM.
    { intros Hm. destruct (H3 o Hm) as [Hm' _]. by apply (owns_ne _ _ _ _ _ _ Ho Eh Hm'); [set_solver|]. }
    rewrite lookup_ksync, !decide_False by done. rewrite Ho. simpl.
    rewrite !decide_False; [done|subst t; set_solver|done].
  - destruct Hen as (H1 & H2).
    assert (o ≠ o') by ne_tac Ho Eh. assert (o ≠ edual o') by ne_tac Ho Eh.
    unfold ktick. rewrite lookup_kmod, !lookup_delete_ne by done. rewrite Ho. simpl.
    rewrite decide_False; [done|subst t; set_solver].
  - destruct Hen as (H1 & H2).
    assert (o ≠ o') by ne_tac Ho Eh. assert (o ≠ edual o') by ne_tac Ho Eh.
    rewrite lookup_ksync, !decide_False by done. rewrite Ho. simpl.
    rewrite !decide_False; [done|subst t; set_solver|set_solver].
  - by destruct (Hnl u o1 o2).
Qed.
