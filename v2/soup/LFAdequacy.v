(** * Adequacy of the lock-free judgment (stage S8, proposal §2.13, A.3)

      lf_adequacy        : lfworld W → ∅ ⊪_W p : T → lock_free p
      lf_thread_progress : lfworld W → ∅ ⊪_W p : T →
                           every weakly fair maximal run makes every thread progress

    The proof instantiates [lf_run_criterion] along one weakly fair maximal
    run r, with the soup at every position and every index at the state
    the run computes ([lf_run_state]).

    - The dependency [wt k t s]: t is pending on an end o and s owns the
      partner of o in the ownership K_k. Ownership is fixed outside the
      index, so the holder is unique.
    - Local progress: the holder of the partner is enabled, or acts on
      the partner (then the two redexes fit and t is enabled), or waits on
      an end below the end of t (readiness). By well-founded induction on
      the point, ordered by ≺_W.
    - The rank of t is the point of its end in K_k. A thread that does not
      step keeps it, a link renames the end and keeps the point.
    - The measure of t is the pair of the tickets left and the counter of
      the partner end in K_k, ordered lexicographically. A link spends a
      ticket. Every other step of the holder on another end ticks the
      counter, which F-Tick keeps at 1 or more because the partner is not
      idle (F-Wait of t and [idle_dual]), and a hand-over passes it on
      with one unit less. Every other step keeps it.
    - No τ-divergence comes from the soup ([soup_no_tau_divergence]), and
      restricted links from the live relation of each thread. *)

From stdpp Require Import relations.
From GV Require Export soup.LFEvents soup.LFRunFacts.

Lemma compat_enabled' q t s e es a1 a2 :
  t ≠ s → q.2 !! t = Some e → q.2 !! s = Some es → act e = Some a1 → act es = Some a2 → compat a1 a2 →
  (∀ o, a1 = AClose o → ech o ∈ q.1) → tenabled q t.
Proof. destruct q as [C M]. apply compat_enabled. Qed.

(** ** The measure *)


Section run.
  #[local] Set Default Proof Using "All".
  Context (N : nat) (W : world) (HW : lfworld W) (T : ty) (a0 : lfstate).
  Context (Hs0 : ∀ n, a0 ∈ S^{N,W} _ n⟦∅ ⊢ T⟧).
  Context (r : nat → config) (l : nat → option event).
  Context (Hr0 : s_q a0 = r 0) (Hmax : maximal r l).

  Local Abbreviation ak k := (lf_run_state N a0 r l k).

  Lemma HWs : types.Worlds.strict W.
  Proof. exact (proj1 HW). Qed.

  Lemma ak_q k : s_q (ak k) = r k.
  Proof. by apply lf_run_state_q. Qed.

  Lemma ak_inv k n : ∃ A Π U, soup_inv N n W ∅ T (ak k) A Π U.
  Proof. exact (lfsoup_run N W T a0 r l Hmax Hr0 Hs0 k n). Qed.

  Definition wt (k t s : nat) : Prop :=
    pend (r k) t ∧ ∃ o, rend (r k) t = Some o ∧ owns (s_K (ak k)) (edual o) s.

  Definition fu (k t : nat) : nat * nat :=
    (ksum (s_tk (ak k)) (r k),
     match rend (r k) t with Some o => kval (s_K (ak k)) (edual o) | None => 0 end).

  Definition we (k t : nat) : point :=
    match rend (r k) t with Some o => kpt (s_K (ak k)) o | None => pvar 0 end.

  (** A pending thread is a link or acts on one end. *)
  Lemma pend_cases q t : pend q t →
    ∃ e a1, q.2 !! t = Some e ∧ act e = Some a1 ∧
      ((∃ o1 o2, a1 = ALink o1 o2) ∨ ∃ o, aend a1 = Some o ∧ rend q t = Some o).
  Proof.
    intros (e & a1 & He & Ha & Hs). exists e, a1. split_and!; [done|done|].
    destruct a1; simpl in Hs; try (by destruct Hs); eauto.
    all: right; eexists; split; [done|]; unfold rend; by rewrite He; simpl; rewrite Ha.
  Qed.

  Lemma npend_end q t : npend q t → ∃ e a1 o, q.2 !! t = Some e ∧ act e = Some a1 ∧ aend a1 = Some o ∧ rend q t = Some o.
  Proof.
    intros [Hp Hna]. destruct (pend_cases q t Hp) as (e & a1 & He & Ha & [(o1 & o2 & ->)|(o & Ho & Hr)]).
    - exfalso. apply Hna. by exists e, (ALink o1 o2).
    - eauto 10.
  Qed.

  (** ** Restricted links and no τ-divergence *)

  Lemma lf_links_restricted : links_restricted (erase (r 0)).
  Proof.
    intros q E e o1 o2 Hq HE Ha. rewrite <-Hr0 in Hq. destruct (pred_star_lift _ _ Hq) as (q' & Hq' & <-).
    destruct (lfsoup_isteps N W T a0 q' Hs0 Hq') as (a' & <- & Hs').
    destruct (Hs' 1) as (A & Π & U & Hs). simpl in HE.
    assert (e ∈ soup (s_q a').2) as Hin by (rewrite HE; multiset_solver).
    apply elem_of_soup in Hin as [t Ht]. exact (s_link _ _ _ _ _ _ _ _ Hs HWs t e o1 o2 Ht Ha).
  Qed.

  Lemma lf_no_tau : no_tau_divergence (erase (r 0)).
  Proof. rewrite <-Hr0. exact (soup_no_tau_divergence N W T a0 Hs0). Qed.

  (** ** Local progress *)

  Lemma lp_end k : ∀ x t e a1 o, (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    kpt (s_K (ak k)) o = x → ∃ s, rtc (wt k) t s ∧ tenabled (r k) s.
  Proof.
    destruct (ak_inv k 1) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    intros x. induction x as [x IH] using (well_founded_ind (proj2 HW)).
    intros t e a1 o He Ha Ho Hx. rewrite <-Hq in He.
    destruct (s_partner _ _ _ _ _ _ _ _ Hs HWs t e a1 o He Ha Ho) as (s & es & h' & Kh' & Eh' & Hes & Hst).
    assert (Hwt : wt k t s).
    { split; [rewrite <-Hq; exists e, a1; split_and!; [done|done|by apply aend_sess in Ho as [? _]]|].
      exists o. split; [rewrite <-Hq; unfold rend; by rewrite He; simpl; rewrite Ha|by exists h']. }
    destruct (s_holder_act _ _ _ _ _ _ _ _ Hs HWs s es (edual o) h' Kh' Eh' Hes) as [a2 Ha2].
    destruct (action_cases a2) as [Had|(o2 & Ho2)].
    - exists s. split; [by apply rtc_once|]. rewrite <-Hq.
      apply (admin_enabled _ s es a2 Hes Ha2 Had). intros o1 o3 ->.
      exact (s_link _ _ _ _ _ _ _ _ Hs HWs s es o1 o3 Hes Ha2).
    - destruct (decide (o2 = edual o)) as [->|Hne].
      + exists t. split; [done|]. rewrite <-Hq.
        apply (compat_enabled' _ t s e es a1 a2); try done.
        * exact (s_compat _ _ _ _ _ _ _ _ Hs HWs t e a1 o s es a2 He Ha Ho Hes Ha2 Ho2).
        * intros o' ->. simpl in Ho. injection Ho as ->.
          destruct (s_held_end _ _ _ _ _ _ _ _ Hs HWs t e _ o He Ha eq_refl) as (S0 & x0 & Hx0 & _).
          destruct (owns_of _ _ _ _ _ Hx0) as (h & Kh & _).
          exact (s_closed _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)).
      + pose proof (s_rank _ _ _ _ _ _ _ _ Hs HWs t e a1 o s es a2 o2 He Ha Ho (ex_intro _ h' (conj Kh' Eh'))
          Hes Ha2 Ho2 Hne) as Hlt.
        rewrite Hq in Hes. destruct (IH (kpt (s_K (ak k)) o2) ltac:(by rewrite <-Hx) s es a2 o2 Hes Ha2 Ho2 eq_refl)
          as (s' & Hch & Hen).
        exists s'. split; [by eapply rtc_l|done].
  Qed.

  Lemma lf_local_progress k t : pend (r k) t → ∃ s, rtc (wt k) t s ∧ tenabled (r k) s.
  Proof.
    intros Hp. destruct (pend_cases _ _ Hp) as (e & a1 & He & Ha & [(o1 & o2 & ->)|(o & Ho & _)]).
    - exists t. split; [done|]. destruct (ak_inv k 1) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
      apply (admin_enabled _ t e _ He Ha I). intros p1 p2 [= <- <-]. rewrite <-Hq in He |- *.
      exact (s_link _ _ _ _ _ _ _ _ Hs HWs t e o1 o2 He Ha).
    - exact (lp_end k _ t e a1 o He Ha Ho eq_refl).
  Qed.

  (** ** The dependency *)

  Lemma wt_pend k t s : wt k t s → pend (r k) t.
  Proof. by intros [? _]. Qed.

  Lemma wt_holder k t s : wt k t s → ∃ es, (r k).2 !! s = Some es.
  Proof.
    intros (_ & o & _ & h & Kh & <-). destruct (ak_inv k 0) as (A & Π & U & Hs).
    rewrite <-(ak_q k). exact (sp_owner _ _ _ _ _ _ _ _ Hs _ _ Kh).
  Qed.

  Lemma wt_uniq k t s s' : npend (r k) t → wt k t s → wt k t s' → s = s'.
  Proof.
    intros _ (_ & o & Ho & H1) (_ & o' & Ho' & H2). rewrite Ho in Ho'. injection Ho' as <-.
    exact (owns_unique _ _ _ _ H1 H2).
  Qed.

  (** ** The rank *)

  Lemma lf_rank k t s : npend (r k) t → wt k t s → npend (r k) s →
    tenabled (r k) t ∨ W ⊢ we k s ≺ we k t.
  Proof.
    intros Hpt (_ & o & Ho & Hown) Hps.
    destruct (npend_end _ _ Hpt) as (e & a1 & o' & He & Ha & Ho1 & Hr). rewrite Ho in Hr. injection Hr as <-.
    destruct (npend_end _ _ Hps) as (es & a2 & o2 & Hes & Ha2 & Ho2 & Hr2).
    destruct (ak_inv k 1) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    unfold we. rewrite Ho, Hr2.
    rewrite <-Hq in He, Hes.
    destruct (decide (o2 = edual o)) as [->|Hne].
    - left. rewrite <-Hq.
      assert (t ≠ s) as Hts.
      { intros <-. rewrite He in Hes. injection Hes as <-. rewrite Ha in Ha2. injection Ha2 as <-.
        rewrite Ho1 in Ho2. injection Ho2 as Hx. by apply (edual_ne o). }
      apply (compat_enabled' _ t s e es a1 a2); try done.
      + exact (s_compat _ _ _ _ _ _ _ _ Hs HWs t e a1 o s es a2 He Ha Ho1 Hes Ha2 Ho2).
      + intros o' ->. simpl in Ho1. injection Ho1 as ->.
        destruct (s_held_end _ _ _ _ _ _ _ _ Hs HWs t e _ o He Ha eq_refl) as (S0 & x0 & Hx0 & _).
        destruct (owns_of _ _ _ _ _ Hx0) as (h & Kh & _).
        exact (s_closed _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)).
    - right. exact (s_rank _ _ _ _ _ _ _ _ Hs HWs t e a1 o s es a2 o2 He Ha Ho1 Hown Hes Ha2 Ho2 Hne).
  Qed.

  (** ** One step of the run *)

  Lemma ak_next k ev : l k = Some ev →
    s_K (ak (S k)) = own_next N ev (s_K (ak k)) ∧ s_tk (ak (S k)) = tk_next ev (s_tk (ak k)).
  Proof. intros Hl. simpl. unfold lf_upd. by rewrite Hl. Qed.

  Lemma ak_stutter k : l k = None → s_K (ak (S k)) = s_K (ak k) ∧ s_tk (ak (S k)) = s_tk (ak k).
  Proof. intros Hl. simpl. unfold lf_upd. by rewrite Hl. Qed.

  Lemma ak_ev_ends k ev : itstep (r k) ev (r (S k)) → ev_ends (s_K (ak k)) ev.
  Proof.
    intros [Hst Hτ]. destruct (ak_inv k 1) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    remember (ak k) as a eqn:Ea. clear Ea. destruct a as [[C Mq] K tk]. simpl in Hq |- *. rewrite <-Hq in Hst.
    exact (s_ev_ends _ _ _ _ _ _ _ _ _ _ _ _ _ Hs HWs Hst Hτ).
  Qed.

  Lemma rend_emap q t g e a1 o : q.2 !! t = Some (emap g e) → act e = Some a1 → aend a1 = Some o →
    rend q t = Some (g o).
  Proof. intros He Ha Ho. unfold rend. rewrite He. simpl. rewrite act_emap, Ha. simpl. by apply aend_amap. Qed.

  Lemma held_at k t e a1 o : (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    owns (s_K (ak k)) o t.
  Proof.
    intros He Ha Ho. destruct (ak_inv k 1) as (A & Π & U & Hs). rewrite <-(ak_q k) in He.
    destruct (s_held_end _ _ _ _ _ _ _ _ Hs HWs t e a1 o He Ha Ho) as (S0 & x & Hx & _).
    exact (owns_of _ _ _ _ _ Hx).
  Qed.

  Lemma closed_at k o t : owns (s_K (ak k)) o t → ech o ∈ (r k).1.
  Proof.
    intros (h & Kh & _). destruct (ak_inv k 0) as (A & Π & U & Hs). rewrite <-(ak_q k).
    destruct (sp_closed _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)) as [?|Hd]; [done|].
    by rewrite dom_empty_L in Hd.
  Qed.

  (** ** The rank is stable *)

  Lemma lf_stab k t : npend (r k) t → t ∉ lparts (l k) → we (S k) t = we k t.
  Proof.
    intros Hp Ht. destruct (npend_end _ _ Hp) as (e & a1 & o & He & Ha & Ho & Hr).
    unfold we. rewrite Hr.
    destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)].
    - rewrite Hl in Ht. simpl in Ht. destruct (ak_next k ev Hl) as [HK _].
      pose proof (ak_ev_ends k ev Hst) as Hen. destruct (held_at k t e a1 o He Ha Ho) as (h & Kh & Eh).
      destruct ev as [i|i ℓ c|i κ o' c|i j M|i j o' M|i j o'|i j o' b|u o1 o2|i σ];
        try (rewrite (rend_emap _ t id e a1 o); [|rewrite emap_id; apply (istep_other_eq _ _ _ t e (proj1 Hst));
          [done|intros ????; discriminate|done]|done|done]; cbn [id];
          unfold kpt; rewrite HK, (own_next_keep N _ (s_K (ak k)) t o h); [by rewrite Kh|done|intros ????; discriminate|done|done|done]).
      simpl in Ht. assert (t ≠ u) as Htu by set_solver.
      rewrite (rend_emap _ t (csub o1 o2) e a1 o); [|exact (istep_link_other _ _ _ _ _ t e (proj1 Hst) Htu He)|done|done].
      simpl in Hen. destruct Hen as (H1 & H2 & _).
      assert (o ≠ o1) by (eapply owns_ne; [exact Kh|exact Eh|exact H1|done]).
      assert (o ≠ o2) by (eapply owns_ne; [exact Kh|exact Eh|exact H2|done]).
      unfold kpt. rewrite HK. cbn [own_next]. change (delete o1 (delete o2 (s_K (ak k)))) with (kdel2 o1 o2 (s_K (ak k))).
      rewrite (kmapr_lookup _ _ o h); [by rewrite Kh|apply kinj_csub|]. by apply lookup_kdel2.
    - rewrite Heq, Hr. by rewrite (proj1 (ak_stutter k Hl)).
  Qed.

  (** ** An enabled pending thread stays enabled *)

  Lemma lf_pers k t : npend (r k) t → tenabled (r k) t → t ∉ lparts (l k) → tenabled (r (S k)) t.
  Proof.
    intros Hp Hen Ht. destruct (npend_end _ _ Hp) as (e & a1 & o & He & Ha & Ho & Hr).
    destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)]; [|by rewrite Heq].
    rewrite Hl in Ht. simpl in Ht.
    destruct Hen as (ev0 & q0 & [Hst0 Hτ0] & Ht0).
    destruct (ev_partner _ _ _ t e a1 o Hst0 Hτ0 Ht0 He Ha Ho) as (s & es & a2 & _ & Hst' & Hes & Ha2 & Ho2 & Hc).
    assert (Hs : s ∉ ev_parts ev).
    { intros Hsin. destruct (ev_partner _ _ _ s es a2 (edual o) (proj1 Hst) (proj2 Hst) Hsin Hes Ha2 Ho2)
        as (p & ep & a3 & Hpin & _ & Hep & Ha3 & Ho3 & _). rewrite edual_edual in Ho3.
      pose proof (held_at k p ep a3 o Hep Ha3 Ho3) as Hp'. pose proof (held_at k t e a1 o He Ha Ho) as Ht'.
      rewrite <-(owns_unique _ _ _ _ Ht' Hp') in Hpin. done. }
    destruct ev as [i|i ℓ c|i κ o' c|i j M|i j o' M|i j o'|i j o' b|u o1 o2|i σ];
      try (apply (compat_enabled' _ t s e es a1 a2); [done|exact (istep_other_eq _ _ _ t e (proj1 Hst) Ht ltac:(intros ????; discriminate) He)
        |exact (istep_other_eq _ _ _ s es (proj1 Hst) Hs ltac:(intros ????; discriminate) Hes)|done|done|done|];
        intros o'' ->; simpl in Ho; injection Ho as ->; apply (closed_at (S k) o t);
        apply (held_at (S k) t e (AClose o) o); [exact (istep_other_eq _ _ _ t e (proj1 Hst) Ht ltac:(intros ????; discriminate) He)|done|done]).
    simpl in Ht, Hs. assert (t ≠ u) as Htu by set_solver. assert (s ≠ u) as Hsu by set_solver.
    pose proof (ak_ev_ends k _ Hst) as Hen. simpl in Hen. destruct Hen as (H1 & H2 & _).
    destruct (held_at k t e a1 o He Ha Ho) as (h & Kh & Eh).
    destruct (held_at k s es a2 (edual o) Hes Ha2 Ho2) as (h' & Kh' & Eh').
    assert (o ≠ o1) by (eapply owns_ne; [exact Kh|exact Eh|exact H1|done]).
    assert (edual o ≠ o1) by (eapply owns_ne; [exact Kh'|exact Eh'|exact H1|done]).
    assert (Hgo : csub o1 o2 o = o).
    { apply csub_eq_off; [|done]. intros Hx. apply H0. by rewrite Hx, edual_edual. }
    assert (Hgo' : csub o1 o2 (edual o) = edual o).
    { apply csub_eq_off; [|done]. intros Hx. apply H. by apply edual_inj. }
    pose proof (istep_link_other _ _ _ _ _ t e (proj1 Hst) Htu He) as He'.
    pose proof (istep_link_other _ _ _ _ _ s es (proj1 Hst) Hsu Hes) as Hes'.
    apply (compat_enabled' _ t s _ _ (amap (csub o1 o2) a1) (amap (csub o1 o2) a2) (not_eq_sym Hst') He' Hes').
    - by rewrite act_emap, Ha.
    - by rewrite act_emap, Ha2.
    - exact (compat_amap _ _ _ _ Hc Ho Hgo Hgo').
    - intros o'' Hc'. destruct a1; simpl in Hc', Ho; try discriminate. injection Ho as ->. injection Hc' as <-.
      rewrite Hgo. apply (closed_at (S k) o t). apply (held_at (S k) t _ (AClose (csub o1 o2 o)) o He').
      + by rewrite act_emap, Ha.
      + simpl. by rewrite Hgo.
  Qed.

  (** ** The measure *)

  Lemma kval_tick (K K' : own) x h m h' :
    K !! x = Some h → h.(h_ctr) = Some m → 1 ≤ m → K' !! x = Some h' → h'.(h_ctr) = ftick h.(h_ctr) →
    kval K' x < kval K x.
  Proof. intros Kh Hm H1 Kh' Hh'. unfold kval. rewrite Kh, Kh', Hh', Hm. simpl. lia. Qed.

  Lemma act_end_of a1 o σ : aend a1 = Some o → offers a1 (LSess σ) → act_end σ = Some o.
  Proof. destruct a1, σ; simpl; intros [= <-]; try done; intros; destruct_and?; by subst. Qed.

  (** The partner of a pending end is not idle. *)
  Lemma partner_busy k t e a1 o (A : senv) (Π : penv) U :
    soup_inv N 1 W ∅ T (ak k) A Π U →
    (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    ∀ s, owns (s_K (ak k)) (edual o) s → ¬ idle_at (kres (s_K (ak k)) s Π) (edual o).
  Proof.
    intros Hs He Ha Ho s (h' & Kh' & Eh'). rewrite <-(ak_q k) in He.
    pose proof (s_fuel Hs t e He) as HF.
    destruct (aend_step e a1 o Ha Ho) as (σ & e' & Hst & _).
    assert (act_end σ = Some o) as Hae.
    { destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoff). rewrite Ha in Ha'. injection Ha' as <-.
      exact (act_end_of _ _ _ Ho Hoff). }
    destruct (fuel_wait _ _ _ _ _ _ HF σ e' o Hst Hae) as [Hni Hdom].
    rewrite dom_ctrs in Hdom. apply elem_of_dom_kth in Hdom as (h & Kh & Eh).
    pose proof (s_dom _ _ _ _ _ _ _ _ Hs) as Hd.
    assert (o ∈ dom Π) as HoΠ by (rewrite Hd; by apply elem_of_dom_2 in Kh).
    assert (edual o ∈ dom Π) as HoΠ' by (rewrite Hd; by apply elem_of_dom_2 in Kh').
    apply elem_of_dom in HoΠ as [P HP]. apply elem_of_dom in HoΠ' as [P' HP'].
    pose proof (s_pdual _ _ _ _ _ _ _ _ Hs o P P' HP HP') as Hpd.
    intros (S1 & HS1 & Hid). apply lookup_kres in HS1 as [HS1 _]. rewrite HP' in HS1. injection HS1 as <-.
    apply Hni. exists P. split; [apply lookup_kres; split; [done|eauto]|].
    by apply (idle_dual P P' Hpd).
  Qed.

  Lemma rend_of q t e a1 o : q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o → rend q t = Some o.
  Proof. intros He Ha Ho. unfold rend. by rewrite He; simpl; rewrite Ha. Qed.

  Lemma fspare_one Πs φs X x m : fspare Πs φs X → x ∈ X → φs !! x = Some (Some m) → ¬ idle_at Πs x → 1 ≤ m.
  Proof. intros H Hx Hφ Hi. pose proof (H x (Some m) Hx Hφ Hi) as Hle. simpl in Hle. lia. Qed.

  (** The measure falls, or stays while the holder steps administratively. *)
  Lemma lf_fuel k t : npend (r k) t → t ∉ lparts (l k) →
    lexlt (fu (S k) t) (fu k t) ∨
    (fu (S k) t = fu k t ∧ (∀ s, wt (S k) t s ↔ wt k t s) ∧
     ∀ s, wt k t s → s ∈ lparts (l k) → admin_at (r k) s).
  Proof.
    intros Hp Ht. destruct (npend_end _ _ Hp) as (e & a1 & o & He & Ha & Ho & Hr).
    destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)].
    2: { right. unfold fu, wt. rewrite Heq. destruct (ak_stutter k Hl) as [-> ->].
         split_and!; [done|done|]. intros s _ Hs. rewrite Hl in Hs. simpl in Hs. set_solver. }
    rewrite Hl in Ht. simpl in Ht.
    destruct (ak_next k ev Hl) as [HK Htk].
    destruct (ak_inv k 1) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    pose proof (ak_ev_ends k ev Hst) as Hen.
    destruct (held_at k t e a1 o He Ha Ho) as (ht & Kht & Eht).
    pose proof He as He0. rewrite <-Hq in He0.
    destruct (s_partner _ _ _ _ _ _ _ _ Hs HWs t e a1 o He0 Ha Ho) as (s & es & h' & Kh' & Eh' & Hes & Hst').
    pose proof (partner_busy k t e a1 o A Π U Hs He Ha Ho s (ex_intro _ h' (conj Kh' Eh'))) as Hbusy.
    destruct (sp_fin _ _ _ _ _ _ _ _ Hs (edual o) h' Kh') as [m Hm].
    assert (Hφs : ctrs (s_K (ak k)) s !! edual o = Some (Some m)).
    { apply lookup_ctrs. exists h'. split_and!; [done|done|done]. }
    assert (Hwt_s : ∀ s0, wt k t s0 → s0 = s).
    { intros s0 (_ & o0 & Ho0 & Hown). rewrite Hr in Ho0. injection Ho0 as <-.
      exact (owns_unique _ _ _ _ Hown (ex_intro _ h' (conj Kh' Eh'))). }
    assert (Hright : rend (r (S k)) t = Some o →
       ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k) →
       own_next N ev (s_K (ak k)) !! edual o = Some h' → (s ∈ ev_parts ev → admin_at (r k) s) →
       fu (S k) t = fu k t ∧ (∀ s0, wt (S k) t s0 ↔ wt k t s0) ∧
       ∀ s0, wt k t s0 → s0 ∈ lparts (l k) → admin_at (r k) s0).
    { intros Hr' Hks HK' Had. unfold fu, wt. rewrite Hr', Hr, Hks, HK. unfold kval. rewrite HK', Kh'.
      split_and!; [done| |].
      - intros s0. split.
        + intros (_ & o0 & Ho0 & Hown). injection Ho0 as <-. split; [exact (proj1 Hp)|]. exists o.
          split; [done|]. destruct Hown as (h0 & Kh0 & E0). rewrite HK' in Kh0. injection Kh0 as <-. by exists h'.
        + intros (_ & o0 & Ho0 & Hown). injection Ho0 as <-.
          split; [apply (run_pend r l Hmax); [rewrite Hl; simpl; set_solver|exact (proj1 Hp)]|].
          exists o. split; [done|]. destruct Hown as (h0 & Kh0 & E0). exists h0. rewrite HK'.
          rewrite Kh' in Kh0. by injection Kh0 as <-.
      - intros s0 (_ & o0 & Ho0 & Hown) Hsin. injection Ho0 as <-. rewrite (owns_unique _ _ _ _ Hown (ex_intro _ h' (conj Kh' Eh'))) in Hsin |- *. rewrite Hl in Hsin. by apply Had. }
    assert (Hdrop : rend (r (S k)) t = Some o →
       ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k) →
       kval (own_next N ev (s_K (ak k))) (edual o) < kval (s_K (ak k)) (edual o) → lexlt (fu (S k) t) (fu k t)).
    { intros Hr' Hks Hlt. unfold fu, lexlt. rewrite Hr', Hr, Hks, HK. simpl. right. split; [done|exact Hlt]. }
    assert (Hnl : (∀ u o1 o2, ev ≠ EvLink u o1 o2) → rend (r (S k)) t = Some o).
    { intros Hne. apply (rend_of _ t e a1 o); [|done|done].
      by apply (istep_other_eq _ _ _ t e (proj1 Hst) Ht). }
    assert (Hks : (∀ u j M, ev ≠ EvSpawn u j M) → s_tk (ak (S k)) = s_tk (ak k) →
                  ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k)).
    { intros Hns Htk'. apply ksum_ext; [exact (istep_dom _ _ _ (proj1 Hst) Hns)|]. intros t0 _. by rewrite Htk'. }
    destruct ev as [u|u ℓ c|u κ o' c|u j M|i j o' M|i j o'|i j o' b|u o1 o2|u σ].
    - right. apply Hright; [(apply Hnl; intros ????; discriminate)|(apply Hks; [intros ????; discriminate|by rewrite Htk])|exact Kh'|].
      intros Hsu. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu).
    - right. apply Hright; [(apply Hnl; intros ????; discriminate)|(apply Hks; [intros ????; discriminate|by rewrite Htk])| |].
      + cbn [own_next]. destruct Hen as [Hp1 Hp2]. unfold knew. pose proof (elem_of_dom_2 _ _ _ Kh') as Hd.
        rewrite !lookup_insert_ne; [done|intros Hx; rewrite <-Hx in Hd; done|intros Hx; rewrite <-Hx in Hd; done].
      + intros Hsu. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu).
    - right. apply Hright; [(apply Hnl; intros ????; discriminate)|(apply Hks; [intros ????; discriminate|by rewrite Htk])| |].
      + cbn [own_next]. destruct Hen as [Hp1 Hp2]. unfold knew. pose proof (elem_of_dom_2 _ _ _ Kh') as Hd.
        rewrite !lookup_insert_ne; [done|intros Hx; rewrite <-Hx in Hd; done|intros Hx; rewrite <-Hx in Hd; done].
      + intros Hsu. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu).
    - destruct (istep_spawn_inv _ _ _ _ _ (proj1 Hst)) as (eu & v & e' & Heu & Hsu & Hj & Hdom).
      assert (Hksp : ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k)).
      { rewrite Htk. cbn [tk_next]. apply ksum_spawn; [by apply elem_of_dom_2 in Heu|by apply not_elem_of_dom|done]. }
      destruct (decide (edual o ∈ M)) as [HM|HM].
      + left. apply Hdrop; [(apply Hnl; intros ????; discriminate)|done|].
        assert (s = u) as ->.
        { simpl in Hen. exact (owns_unique _ _ _ _ (ex_intro _ h' (conj Kh' Eh')) (Hen _ HM)). }
        rewrite <-Hq in Heu. pose proof (s_fuel Hs u eu Heu) as HF.
        destruct (fuel_spawn_hand _ _ _ _ _ _ HF M v e' Hsu) as [_ Hsp].
        pose proof (fspare_one _ _ _ _ _ Hsp HM Hφs Hbusy) as H1.
        apply (kval_tick _ _ _ h' m (Hold j h'.(h_pt) (ftick h'.(h_ctr))) Kh' Hm H1); [|done].
        cbn [own_next]. rewrite lookup_khand, Kh'. simpl. by rewrite decide_True.
      + right. apply Hright; [(apply Hnl; intros ????; discriminate)|done| |].
        * cbn [own_next]. rewrite lookup_khand, Kh'. simpl. by rewrite decide_False.
        * intros Hsu'. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu').
    - assert (Hks' : ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k)) by (apply Hks; [intros ????; discriminate|by rewrite Htk]).
      simpl in Hen. destruct Hen as (H1 & H2 & H3).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ????; discriminate)|done|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvMsg i j o' M) s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { apply (fspare_one _ _ _ (edual o) _ Htick); [|done|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        cbn [own_next]. destruct (ksync N i j o' (pt_shift 1 (kpt (s_K (ak k)) o'))
          (pt_shift 1 (kpt (s_K (ak k)) (edual o'))) M (s_K (ak k)) !! edual o) as [h1|] eqn:Eh1.
        * apply (kval_tick _ _ _ h' m h1 Kh' Hm Hm1 Eh1). rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done.
          simpl in Eh1. injection Eh1 as <-. case_decide; [done|]. rewrite decide_True; [done|]. by rewrite Eh'.
        * rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done. done.
      + right. apply Hright; [(apply Hnl; intros ????; discriminate)|done| |].
        * apply (own_next_keep N _ _ s); [split_and!; done|intros ????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - assert (Hks' : ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k)) by (apply Hks; [intros ????; discriminate|by rewrite Htk]).
      simpl in Hen. destruct Hen as (H1 & H2).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ????; discriminate)|done|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvClose i j o') s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { apply (fspare_one _ _ _ (edual o) _ Htick); [|done|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        apply (kval_tick _ _ _ h' m (htick h') Kh' Hm Hm1); [|done].
        cbn [own_next]. unfold ktick. rewrite lookup_kmod, !lookup_delete_ne by done. rewrite Kh'. simpl.
        rewrite decide_True; [done|]. rewrite Eh'. set_solver.
      + right. apply Hright; [(apply Hnl; intros ????; discriminate)|done| |].
        * apply (own_next_keep N _ _ s); [split; done|intros ????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - assert (Hks' : ksum (s_tk (ak (S k))) (r (S k)) = ksum (s_tk (ak k)) (r k)) by (apply Hks; [intros ????; discriminate|by rewrite Htk]).
      simpl in Hen. destruct Hen as (H1 & H2).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ????; discriminate)|done|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvChoice i j o' b) s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { apply (fspare_one _ _ _ (edual o) _ Htick); [|done|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        cbn [own_next]. destruct (ksync N i j o' (sel_pt (kpt (s_K (ak k)) o') b)
          (bra_pt (kpt (s_K (ak k)) (edual o')) b) ∅ (s_K (ak k)) !! edual o) as [h1|] eqn:Eh1.
        * apply (kval_tick _ _ _ h' m h1 Kh' Hm Hm1 Eh1). rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done.
          simpl in Eh1. injection Eh1 as <-. rewrite decide_False by set_solver. rewrite decide_True; [done|].
          by rewrite Eh'.
        * rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done. done.
      + right. apply Hright; [(apply Hnl; intros ????; discriminate)|done| |].
        * apply (own_next_keep N _ _ s); [split; done|intros ????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - left. left. unfold fu. cbn [fst]. rewrite Htk. cbn [tk_next].
      destruct (istep_link_inv _ _ _ _ _ (proj1 Hst)) as (eu & e' & Heu & Hsu).
      apply ksum_link; [by apply elem_of_dom_2 in Heu|exact (istep_dom _ _ _ (proj1 Hst) ltac:(intros ????; discriminate))|].
      rewrite <-Hq in Heu. pose proof (s_fuel Hs u eu Heu) as HF.
      by destruct (fuel_link _ _ _ _ _ _ HF _ e' Hsu) as [? _].
    - exfalso. by destruct Hst as [_ Hτ].
  Qed.
End run.