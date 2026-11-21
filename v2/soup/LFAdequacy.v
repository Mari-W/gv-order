(** * Adequacy of the lock-free judgment (stage S8, proposal §2.13, A.3)

      lf_adequacy        : ∅ ⊪^N _ W p : T → lock_free p
      lf_thread_progress : ∅ ⊪^N _ W p : T →
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
    - The measure of t is the counter of the partner end in K_k, ordered
      by < on ℕ. A step of the holder on another end ticks the counter,
      which F-Tick keeps at 1 or more because the partner is not idle
      (F-Wait of t and [idle_dual]), and a hand-over passes it on with one
      unit less. A link of the partner end gives t a new partner, whose
      counter lies below the old one by the tickets of the link
      (F-Link, [sp_cap], [sp_tsum], [lgt_tsum_lt]). Every other step keeps
      it.
    - No τ-divergence comes from the soup ([soup_no_tau_divergence]), and
      restricted links from the live relation of each thread. *)

From stdpp Require Import relations.
From GV Require Export soup.LFEvents soup.LFRunFacts soup.Relabel.

Lemma compat_enabled' q t s e es a1 a2 :
  t ≠ s → q.2 !! t = Some e → q.2 !! s = Some es → act e = Some a1 → act es = Some a2 → compat a1 a2 →
  (∀ o, a1 = AClose o → ech o ∈ q.1) → tenabled q t.
Proof. destruct q as [C M]. apply compat_enabled. Qed.

(** ** The measure *)


Section run.
  #[local] Set Default Proof Using "All".
  Context (N : nat) (W : world) (T : ty) (a0 : lfstate).
  Context (r : nat → config) (l : nat → option event).
  Context (Hr0 : s_q a0 = r 0) (Hmax : maximal r l).
  Context (tcs : nat → tchoice) (Hinv : ∀ k n, lf_run_state tcs a0 r l k ∈ S^{N,W} _ n⟦∅ ⊢ T⟧).
  Context (Hwch : ∀ k, wext (s_W (lf_run_state tcs a0 r l k)) (s_W (lf_run_state tcs a0 r l (S k)))).

  Local Abbreviation ak k := (lf_run_state tcs a0 r l k).

  (** The worlds of the run, a chain. *)
  Definition wk (k : nat) : world := s_W (ak k).

  Lemma ak_q k : s_q (ak k) = r k.
  Proof. by apply lf_run_state_q. Qed.

  Lemma ak_inv k n : ∃ A Π U, soup_inv N n (wk k) ∅ T (ak k) A Π U.
  Proof. exact (proj2 (Hinv k n)). Qed.

  Definition wt (k t s : nat) : Prop :=
    pend (r k) t ∧ ∃ o, rend (r k) t = Some o ∧ owns (s_K (ak k)) (edual o) s.

  Definition fu (k t : nat) : nat :=
    match rend (r k) t with Some o => kval (s_K (ak k)) (edual o) | None => 0 end.

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

  (** ** Local progress *)

  Lemma lp_end k : ∀ x t e a1 o, (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    kpt (s_K (ak k)) o = x → ∃ s, rtc (wt k) t s ∧ tenabled (r k) s.
  Proof.
    destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    intros x. induction x as [x IH] using (well_founded_ind (w_lt_wf (wk k))).
    intros t e a1 o He Ha Ho Hx. rewrite <-Hq in He.
    destruct (s_partner _ _ _ _ _ _ _ _ Hs t e a1 o He Ha Ho) as (s & es & h' & Kh' & Eh' & Hes & Hst).
    assert (Hwt : wt k t s).
    { split; [rewrite <-Hq; exists e, a1; split_and!; [done|done|by apply aend_sess in Ho as [? _]]|].
      exists o. split; [rewrite <-Hq; unfold rend; by rewrite He; simpl; rewrite Ha|by exists h']. }
    destruct (s_holder_act _ _ _ _ _ _ _ _ Hs s es (edual o) h' Kh' Eh' Hes) as [a2 Ha2].
    destruct (action_cases a2) as [Had|(o2 & Ho2)].
    - exists s. split; [by apply rtc_once|]. rewrite <-Hq.
      apply (admin_enabled _ s es a2 Hes Ha2 Had). intros o1 o3 ->.
      exact (s_link _ _ _ _ _ _ _ _ Hs s es o1 o3 Hes Ha2).
    - destruct (decide (o2 = edual o)) as [->|Hne].
      + exists t. split; [done|]. rewrite <-Hq.
        apply (compat_enabled' _ t s e es a1 a2); try done.
        * exact (s_compat _ _ _ _ _ _ _ _ Hs t e a1 o s es a2 He Ha Ho Hes Ha2 Ho2).
        * intros o' ->. simpl in Ho. injection Ho as ->.
          destruct (s_held_end _ _ _ _ _ _ _ _ Hs t e _ o He Ha eq_refl) as (S0 & x0 & Hx0 & _).
          destruct (owns_of _ _ _ _ _ Hx0) as (h & Kh & _).
          exact (s_closed _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)).
      + pose proof (s_rank _ _ _ _ _ _ _ _ Hs t e a1 o s es a2 o2 He Ha Ho (ex_intro _ h' (conj Kh' Eh'))
          Hes Ha2 Ho2 Hne) as Hlt.
        rewrite Hq in Hes. destruct (IH (kpt (s_K (ak k)) o2) ltac:(by rewrite <-Hx) s es a2 o2 Hes Ha2 Ho2 eq_refl)
          as (s' & Hch & Hen).
        exists s'. split; [by eapply rtc_l|done].
  Qed.

  Lemma lf_local_progress k t : pend (r k) t → ∃ s, rtc (wt k) t s ∧ tenabled (r k) s.
  Proof.
    intros Hp. destruct (pend_cases _ _ Hp) as (e & a1 & He & Ha & [(o1 & o2 & ->)|(o & Ho & _)]).
    - exists t. split; [done|]. destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
      apply (admin_enabled _ t e _ He Ha I). intros p1 p2 [= <- <-]. rewrite <-Hq in He |- *.
      exact (s_link _ _ _ _ _ _ _ _ Hs t e o1 o2 He Ha).
    - exact (lp_end k _ t e a1 o He Ha Ho eq_refl).
  Qed.

  (** ** The dependency *)

  Lemma wt_pend k t s : wt k t s → pend (r k) t.
  Proof. by intros [? _]. Qed.

  Lemma wt_holder k t s : wt k t s → ∃ es, (r k).2 !! s = Some es.
  Proof.
    intros (_ & o & _ & h & Kh & <-). destruct (ak_inv k ozero) as (A & Π & U & Hs).
    rewrite <-(ak_q k). exact (sp_owner _ _ _ _ _ _ _ _ _ Hs _ _ Kh).
  Qed.

  Lemma wt_uniq k t s s' : npend (r k) t → wt k t s → wt k t s' → s = s'.
  Proof.
    intros _ (_ & o & Ho & H1) (_ & o' & Ho' & H2). rewrite Ho in Ho'. injection Ho' as <-.
    exact (owns_unique _ _ _ _ H1 H2).
  Qed.

  (** ** The rank *)

  Lemma lf_rank k t s : npend (r k) t → wt k t s → npend (r k) s →
    tenabled (r k) t ∨ wchain_lt wk (we k s) (we k t).
  Proof.
    intros Hpt (_ & o & Ho & Hown) Hps.
    destruct (npend_end _ _ Hpt) as (e & a1 & o' & He & Ha & Ho1 & Hr). rewrite Ho in Hr. injection Hr as <-.
    destruct (npend_end _ _ Hps) as (es & a2 & o2 & Hes & Ha2 & Ho2 & Hr2).
    destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    unfold we. rewrite Ho, Hr2.
    rewrite <-Hq in He, Hes.
    destruct (decide (o2 = edual o)) as [->|Hne].
    - left. rewrite <-Hq.
      assert (t ≠ s) as Hts.
      { intros <-. rewrite He in Hes. injection Hes as <-. rewrite Ha in Ha2. injection Ha2 as <-.
        rewrite Ho1 in Ho2. injection Ho2 as Hx. by apply (edual_ne o). }
      apply (compat_enabled' _ t s e es a1 a2); try done.
      + exact (s_compat _ _ _ _ _ _ _ _ Hs t e a1 o s es a2 He Ha Ho1 Hes Ha2 Ho2).
      + intros o' ->. simpl in Ho1. injection Ho1 as ->.
        destruct (s_held_end _ _ _ _ _ _ _ _ Hs t e _ o He Ha eq_refl) as (S0 & x0 & Hx0 & _).
        destruct (owns_of _ _ _ _ _ Hx0) as (h & Kh & _).
        exact (s_closed _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)).
    - right. exists k. exact (s_rank _ _ _ _ _ _ _ _ Hs t e a1 o s es a2 o2 He Ha Ho1 Hown Hes Ha2 Ho2 Hne).
  Qed.

  (** ** One step of the run *)

  Lemma ak_next k ev : l k = Some ev → s_K (ak (S k)) = own_next (tcs k) ev (s_K (ak k)).
  Proof. intros Hl. simpl. unfold lf_upd. by rewrite Hl. Qed.

  Lemma ak_stutter k : l k = None → s_K (ak (S k)) = s_K (ak k).
  Proof. intros Hl. simpl. unfold lf_upd. by rewrite Hl. Qed.

  Lemma ak_ev_ends k ev : itstep (r k) ev (r (S k)) → ev_ends (s_K (ak k)) ev.
  Proof.
    intros [Hst Hτ]. destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    remember (ak k) as a eqn:Ea. clear Ea. destruct a as [[C Mq] K Wa]. simpl in Hq |- *. rewrite <-Hq in Hst.
    exact (s_ev_ends _ _ _ _ _ _ _ _ _ _ _ _ _ (onat_lt 0 1 ltac:(lia)) Hs Hst Hτ).
  Qed.

  Lemma rend_emap q t g e a1 o : q.2 !! t = Some (emap g e) → act e = Some a1 → aend a1 = Some o →
    rend q t = Some (g o).
  Proof. intros He Ha Ho. unfold rend. rewrite He. simpl. rewrite act_emap, Ha. simpl. by apply aend_amap. Qed.

  Lemma held_at k t e a1 o : (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    owns (s_K (ak k)) o t.
  Proof.
    intros He Ha Ho. destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). rewrite <-(ak_q k) in He.
    destruct (s_held_end _ _ _ _ _ _ _ _ Hs t e a1 o He Ha Ho) as (S0 & x & Hx & _).
    exact (owns_of _ _ _ _ _ Hx).
  Qed.

  Lemma closed_at k o t : owns (s_K (ak k)) o t → ech o ∈ (r k).1.
  Proof.
    intros (h & Kh & _). destruct (ak_inv k ozero) as (A & Π & U & Hs). rewrite <-(ak_q k).
    destruct (sp_closed _ _ _ _ _ _ _ _ _ Hs o (elem_of_dom_2 _ _ _ Kh)) as [?|Hd]; [done|].
    by rewrite dom_empty_L in Hd.
  Qed.

  (** ** The rank is stable *)

  Lemma lf_stab k t : npend (r k) t → t ∉ lparts (l k) → we (S k) t = we k t.
  Proof.
    intros Hp Ht. destruct (npend_end _ _ Hp) as (e & a1 & o & He & Ha & Ho & Hr).
    unfold we. rewrite Hr.
    destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)].
    - rewrite Hl in Ht. simpl in Ht. pose proof (ak_next k ev Hl) as HK.
      pose proof (ak_ev_ends k ev Hst) as Hen. destruct (held_at k t e a1 o He Ha Ho) as (h & Kh & Eh).
      destruct ev as [u α [|j|o1 o2]|i j σ|i σ];
        try (rewrite (rend_emap _ t id e a1 o); [|rewrite emap_id; apply (istep_other_eq _ _ _ t e (proj1 Hst));
          [done|intros ?????; discriminate|done]|done|done]; cbn [id];
          unfold kpt; rewrite HK, (own_next_keep (tcs k) _ (s_K (ak k)) t o h); [by rewrite Kh|done|intros ?????; discriminate|done|done|done]).
      simpl in Ht. assert (t ≠ u) as Htu by set_solver.
      rewrite (rend_emap _ t (csub o1 o2) e a1 o); [|exact (istep_link_other _ _ _ _ _ _ t e (proj1 Hst) Htu He)|done|done].
      simpl in Hen. destruct Hen as (H1 & H2 & _).
      assert (o ≠ o1) by (eapply owns_ne; [exact Kh|exact Eh|exact H1|done]).
      assert (o ≠ o2) by (eapply owns_ne; [exact Kh|exact Eh|exact H2|done]).
      unfold kpt. rewrite HK. cbn [own_next]. change (delete o1 (delete o2 (s_K (ak k)))) with (kdel2 o1 o2 (s_K (ak k))).
      rewrite (kmapr_lookup _ _ o h); [by rewrite Kh|apply kinj_csub|]. by apply lookup_kdel2.
    - rewrite Heq, Hr. by rewrite (ak_stutter k Hl).
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
    destruct ev as [u α [|j|o1 o2]|i j σ|i σ];
      try (apply (compat_enabled' _ t s e es a1 a2); [done|exact (istep_other_eq _ _ _ t e (proj1 Hst) Ht ltac:(intros ?????; discriminate) He)
        |exact (istep_other_eq _ _ _ s es (proj1 Hst) Hs ltac:(intros ?????; discriminate) Hes)|done|done|done|];
        intros o'' ->; simpl in Ho; injection Ho as ->; apply (closed_at (S k) o t);
        apply (held_at (S k) t e (AClose o) o); [exact (istep_other_eq _ _ _ t e (proj1 Hst) Ht ltac:(intros ?????; discriminate) He)|done|done]).
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
    pose proof (istep_link_other _ _ _ _ _ _ t e (proj1 Hst) Htu He) as He'.
    pose proof (istep_link_other _ _ _ _ _ _ s es (proj1 Hst) Hsu Hes) as Hes'.
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
    soup_inv N (onat 1) (wk k) ∅ T (ak k) A Π U →
    (r k).2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    ∀ s, owns (s_K (ak k)) (edual o) s → ¬ idle_at (kres (s_K (ak k)) s Π) (edual o).
  Proof.
    intros Hs He Ha Ho s (h' & Kh' & Eh'). rewrite <-(ak_q k) in He.
    pose proof (s_fuel Hs t e He) as HF.
    destruct (aend_step e a1 o Ha Ho) as (σ & e' & Hst & _).
    assert (act_end σ = Some o) as Hae.
    { destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoff). rewrite Ha in Ha'. injection Ha' as <-.
      exact (act_end_of _ _ _ Ho Hoff). }
    destruct (fuel_wait _ _ _ _ _ HF σ e' o Hst Hae) as [Hni Hdom].
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

  Lemma fspare_one Πs φs X x m c : fspare Πs φs X → x ∈ X → φs !! x = Some (Some m, c) → ¬ idle_at Πs x → 1 ≤ m.
  Proof. intros H Hx Hφ Hi. pose proof (H x (Some m, c) Hx Hφ Hi) as Hle. simpl in Hle. lia. Qed.

  (** The new partner after a link: the partner of o1 now holds o2. *)
  Lemma link_lookup (K : own) o1 o2 a :
    a ≠ o1 → a ≠ o2 → kmapr (csub o1 o2) (kdel2 o1 o2 K) !! csub o1 o2 a = K !! a.
  Proof.
    intros H1 H2. destruct (K !! a) as [h|] eqn:E.
    - apply kmapr_lookup; [apply kinj_csub|]. by apply lookup_kdel2.
    - destruct (kmapr (csub o1 o2) (kdel2 o1 o2 K) !! csub o1 o2 a) as [h|] eqn:E'; [|done].
      apply kmapr_lookup_inv in E' as (b & Hb & Hb'). apply lookup_kdel2 in Hb' as (Hb1 & Hb2 & Hb').
      assert (b = a) as ->.
      { unfold csub in Hb. repeat case_decide; subst; first [done|congruence]. }
      congruence.
  Qed.

  (** The measure falls, or stays while the holder steps administratively. *)
  Lemma lf_fuel k t : npend (r k) t → t ∉ lparts (l k) →
    fu (S k) t < fu k t ∨
    (fu (S k) t = fu k t ∧ (∀ s, wt (S k) t s ↔ wt k t s) ∧
     ∀ s, wt k t s → s ∈ lparts (l k) → admin_at (r k) s).
  Proof.
    intros Hp Ht. destruct (npend_end _ _ Hp) as (e & a1 & o & He & Ha & Ho & Hr).
    destruct (Hmax k) as [(ev & Hl & Hst)|(_ & Heq & Hl)].
    2: { right. unfold fu, wt. rewrite Heq. rewrite (ak_stutter k Hl).
         split_and!; [done|done|]. intros s _ Hs. rewrite Hl in Hs. simpl in Hs. set_solver. }
    rewrite Hl in Ht. simpl in Ht.
    pose proof (ak_next k ev Hl) as HK.
    destruct (ak_inv k (onat 1)) as (A & Π & U & Hs). pose proof (ak_q k) as Hq.
    pose proof (ak_ev_ends k ev Hst) as Hen.
    destruct (held_at k t e a1 o He Ha Ho) as (ht & Kht & Eht).
    pose proof He as He0. rewrite <-Hq in He0.
    destruct (s_partner _ _ _ _ _ _ _ _ Hs t e a1 o He0 Ha Ho) as (s & es & h' & Kh' & Eh' & Hes & Hst').
    pose proof (partner_busy k t e a1 o A Π U Hs He Ha Ho s (ex_intro _ h' (conj Kh' Eh'))) as Hbusy.
    destruct (sp_fin _ _ _ _ _ _ _ _ _ Hs (edual o) h' Kh') as [m Hm].
    assert (Hφs : ctrs (s_K (ak k)) s !! edual o = Some (Some m, h'.(h_cap))).
    { apply lookup_ctrs. exists h'. split_and!; [done|done|]. unfold hctr. by rewrite Hm. }
    assert (Hright : rend (r (S k)) t = Some o →
       own_next (tcs k) ev (s_K (ak k)) !! edual o = Some h' → (s ∈ ev_parts ev → admin_at (r k) s) →
       fu (S k) t = fu k t ∧ (∀ s0, wt (S k) t s0 ↔ wt k t s0) ∧
       ∀ s0, wt k t s0 → s0 ∈ lparts (l k) → admin_at (r k) s0).
    { intros Hr' HK' Had. unfold fu, wt. rewrite Hr', Hr, HK. unfold kval. rewrite HK', Kh'.
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
       kval (own_next (tcs k) ev (s_K (ak k))) (edual o) < kval (s_K (ak k)) (edual o) → fu (S k) t < fu k t).
    { intros Hr' Hlt. unfold fu. rewrite Hr', Hr, HK. exact Hlt. }
    assert (Hnl : (∀ u α o1 o2, ev ≠ EvSolo u α (PickLink o1 o2)) → rend (r (S k)) t = Some o).
    { intros Hne. apply (rend_of _ t e a1 o); [|done|done].
      by apply (istep_other_eq _ _ _ t e (proj1 Hst) Ht). }
    destruct (istep_event _ _ _ (proj1 Hst)) as [(u & ->)|[(u & c & ->)|[(u & j & v & ->)
      |[(i & j & o' & w & ->)|[(i & j & o' & ->)|[(i & j & o' & b & ->)|[(u & o1 & o2 & ->)|(u & σ & ->)]]]]]]].
    - right. apply Hright; [(apply Hnl; intros ?????; discriminate)|exact Kh'|].
      intros Hsu. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu).
    - right. apply Hright; [(apply Hnl; intros ?????; discriminate)| |].
      + cbn [own_next]. destruct Hen as [Hp1 Hp2]. unfold knew. pose proof (elem_of_dom_2 _ _ _ Kh') as Hd.
        rewrite !lookup_insert_ne; [done|intros Hx; rewrite <-Hx in Hd; done|intros Hx; rewrite <-Hx in Hd; done].
      + intros Hsu. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu).
    - destruct (istep_spawn_inv _ _ _ _ _ (proj1 Hst)) as (eu & e' & Heu & Hsu & Hj & Hdom).
      destruct (decide (edual o ∈ fends v)) as [HM|HM].
      + left. apply Hdrop; [(apply Hnl; intros ?????; discriminate)|].
        assert (s = u) as ->.
        { simpl in Hen. exact (owns_unique _ _ _ _ (ex_intro _ h' (conj Kh' Eh')) (Hen _ HM)). }
        rewrite <-Hq in Heu. pose proof (s_fuel Hs u eu Heu) as HF.
        destruct (fuel_spawn_hand _ _ _ _ _ HF v e' Hsu) as [_ Hsp].
        pose proof (fspare_one _ _ _ _ _ _ Hsp HM Hφs Hbusy) as H1.
        apply (kval_tick _ _ _ h' m (Hold j h'.(h_pt) (ftick h'.(h_ctr)) h'.(h_cap)) Kh' Hm H1); [|done].
        cbn [own_next]. rewrite lookup_khand, Kh'. simpl. by rewrite decide_True.
      + right. apply Hright; [(apply Hnl; intros ?????; discriminate)| |].
        * cbn [own_next]. rewrite lookup_khand, Kh'. simpl. by rewrite decide_False.
        * intros Hsu'. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu').
    - simpl in Hen. destruct Hen as (H1 & H2 & H3).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ?????; discriminate)|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvSync i j (SSend o' w)) s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { eapply (fspare_one _ _ _ (edual o) _ _ Htick); [|exact Hφs|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        cbn [own_next]. destruct (ksync i j o' (pt_shift 1 (kpt (s_K (ak k)) o'))
          (pt_shift 1 (kpt (s_K (ak k)) (edual o'))) (fends w) (s_K (ak k)) !! edual o) as [h1|] eqn:Eh1.
        * apply (kval_tick _ _ _ h' m h1 Kh' Hm Hm1 Eh1). rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done.
          simpl in Eh1. injection Eh1 as <-. case_decide; [done|]. rewrite decide_True; [done|]. by rewrite Eh'.
        * rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done. done.
      + right. apply Hright; [(apply Hnl; intros ?????; discriminate)| |].
        * apply (own_next_keep (tcs k) _ _ s); [split_and!; done|intros ?????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - simpl in Hen. destruct Hen as (H1 & H2).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ?????; discriminate)|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvSync i j (SClose o')) s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { eapply (fspare_one _ _ _ (edual o) _ _ Htick); [|exact Hφs|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        apply (kval_tick _ _ _ h' m (htick h') Kh' Hm Hm1); [|done].
        cbn [own_next]. unfold ktick. rewrite lookup_kmod, !lookup_delete_ne by done. rewrite Kh'. simpl.
        rewrite decide_True; [done|]. rewrite Eh'. set_solver.
      + right. apply Hright; [(apply Hnl; intros ?????; discriminate)| |].
        * apply (own_next_keep (tcs k) _ _ s); [split; done|intros ?????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - simpl in Hen. destruct Hen as (H1 & H2).
      destruct (decide (s = i ∨ s = j)) as [Hsij|Hsij].
      + left. apply Hdrop; [(apply Hnl; intros ?????; discriminate)|].
        assert (edual o ≠ o') as Hn1.
        { intros Hx. assert (owns (s_K (ak k)) o j) as Hoj by (rewrite <-(edual_edual o), Hx; exact H2).
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) Hoj) in Ht. set_solver. }
        assert (edual o ≠ edual o') as Hn2.
        { intros Hx. apply edual_inj in Hx. subst o'.
          rewrite <-(owns_unique _ _ _ _ (ex_intro _ ht (conj Kht Eht)) H1) in Ht. set_solver. }
        set (p := if decide (s = i) then o' else edual o').
        assert (ev_end (EvSync i j (SSel o' b)) s = Some p) as Hp'.
        { simpl. unfold p. destruct (decide (s = i)); [done|]. rewrite decide_True; [done|]. tauto. }
        assert ((r k).2 !! s = Some es) as Hes2 by (by rewrite <-Hq).
        destruct (istep_sync_step _ _ _ s es p (proj1 Hst) Hp' Hes2) as (σ & es' & Hσ & Hae).
        pose proof (s_fuel Hs s es Hes) as HF.
        pose proof (fuel_tick _ _ _ _ _ HF σ es' p Hσ Hae) as Htick.
        assert (edual o ≠ p) as Hnp by (unfold p; destruct (decide (s = i)); done).
        assert (1 ≤ m) as Hm1.
        { eapply (fspare_one _ _ _ (edual o) _ _ Htick); [|exact Hφs|done]. apply elem_of_difference.
          split; [by apply elem_of_dom_2 in Hφs|by rewrite elem_of_singleton]. }
        cbn [own_next]. destruct (ksync i j o' (sel_pt (kpt (s_K (ak k)) o') b)
          (bra_pt (kpt (s_K (ak k)) (edual o')) b) ∅ (s_K (ak k)) !! edual o) as [h1|] eqn:Eh1.
        * apply (kval_tick _ _ _ h' m h1 Kh' Hm Hm1 Eh1). rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done.
          simpl in Eh1. injection Eh1 as <-. rewrite decide_False by set_solver. rewrite decide_True; [done|].
          by rewrite Eh'.
        * rewrite lookup_ksync, !decide_False, Kh' in Eh1 by done. done.
      + right. apply Hright; [(apply Hnl; intros ?????; discriminate)| |].
        * apply (own_next_keep (tcs k) _ _ s); [split; done|intros ?????; discriminate|simpl; set_solver|done|done].
        * intros Hx. simpl in Hx. exfalso. apply Hsij. set_solver.
    - (* a link: no counter changes, the partner of a linked end changes *)
      simpl in Ht. assert (t ≠ u) as Htu by set_solver.
      simpl in Hen. destruct Hen as (H1 & H2 & H12).
      destruct (istep_link_inv _ _ _ _ _ _ (proj1 Hst)) as (eu & e' & Heu & Hsu).
      pose proof (istep_link_other _ _ _ _ _ _ t e (proj1 Hst) Htu He) as He'.
      assert (o ≠ o1) as Ho1 by (eapply owns_ne; [exact Kht|exact Eht|exact H1|done]).
      assert (o ≠ o2) as Ho2 by (eapply owns_ne; [exact Kht|exact Eht|exact H2|done]).
      cbn [own_next] in HK. change (delete o1 (delete o2 (s_K (ak k)))) with (kdel2 o1 o2 (s_K (ak k))) in HK.
      destruct H1 as (h1 & Kh1 & Eh1). destruct H2 as (h2 & Kh2 & Eh2).
      assert (Hcap : ∀ x h, s_K (ak k) !! x = Some h → fle h.(h_ctr) h.(h_cap) ∧ fle h.(h_cap) (Some N))
        by exact (s_cap _ _ _ _ _ _ _ _ Hs).
      assert (Hts : ∀ x h h0, s_K (ak k) !! x = Some h → s_K (ak k) !! edual x = Some h0 →
                tsum_ok (Some N) h.(h_cap) h0.(h_cap)) by exact (s_tsum _ _ _ _ _ _ _ _ Hs).
      assert (Hlok : lok (Some N) (ctrs (s_K (ak k)) u) ({[o1]} ∪ {[o2]})).
      { rewrite <-Hq in Heu. pose proof (s_fuel Hs u eu Heu) as HF.
        by destruct (fuel_link _ _ _ _ _ HF _ e' Hsu) as (_ & _ & ?). }
      assert (G1 : ctrs (s_K (ak k)) u !! o1 = Some (hctr h1)) by (apply lookup_ctrs; by exists h1).
      assert (G2 : ctrs (s_K (ak k)) u !! o2 = Some (hctr h2)) by (apply lookup_ctrs; by exists h2).
      destruct (Hlok o1 o2 _ _ eq_refl H12 G1 G2) as [L1 L2]. simpl in L1, L2.
      destruct (decide (edual o = o1)) as [Eo1|Ne1]; [|destruct (decide (edual o = o2)) as [Eo2|Ne2]].
      + (* t waits on the partner of o1, which now faces the partner of o2 *)
        left. subst o1. rewrite Kh' in Kh1. injection Kh1 as <-.
        assert (o2 ≠ edual (edual o)) as Hn2 by (rewrite edual_edual; done).
        assert (Hc : csub (edual o) o2 o = o2) by (unfold csub; rewrite edual_edual, decide_True; done).
        assert (rend (r (S k)) t = Some o2) as Hr'.
        { rewrite <-Hc. exact (rend_emap _ t (csub (edual o) o2) e a1 o He' Ha Ho). }
        assert (edual o2 ≠ edual o) as Hd1 by (intros Hx; apply Ho2; symmetry; by apply edual_inj).
        assert (edual o2 ≠ o2) as Hd2 by apply edual_ne.
        assert (Hc2 : csub (edual o) o2 (edual o2) = edual o2).
        { apply csub_eq_off; [|done]. rewrite edual_edual. intros Hx. apply H12. by rewrite <-Hx, edual_edual. }
        destruct (s_K (ak k) !! edual o2) as [r2|] eqn:Kr2.
        2: { exfalso. assert (edual o2 ∈ dom (s_K (ak k))) as Hd by (apply (s_pair _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh2).
             apply elem_of_dom in Hd as [? Hx]. congruence. }
        destruct (lgt_tsum_lt N m _ _ (eq_ind _ (λ x, lgt (Some N) x _) L1 _ Hm) (Hts o2 h2 r2 Kh2 Kr2)) as (kr & Ekr & Hkr).
        unfold fu. rewrite Hr', Hr, HK. unfold kval.
        rewrite <-Hc2, link_lookup by done. rewrite Kr2, Kh', Hm.
        destruct (Hcap _ r2 Kr2) as [Hc3 _]. rewrite Ekr in Hc3. simpl.
        destruct (h_ctr r2) as [c2|]; simpl in *; lia.
      + (* t waits on o2, whose partner is now the partner of o1 *)
        left. subst o2. rewrite Kh' in Kh2. injection Kh2 as <-.
        assert (o ≠ edual o1) as Hn1 by (intros Hx; apply Ne1; by rewrite Hx, edual_edual).
        assert (Hc : csub o1 (edual o) o = o) by (apply csub_eq_off; done).
        assert (rend (r (S k)) t = Some o) as Hr'.
        { rewrite <-Hc. exact (rend_emap _ t (csub o1 (edual o)) e a1 o He' Ha Ho). }
        assert (edual o1 ≠ o1) as Hd1 by apply edual_ne.
        assert (edual o1 ≠ edual o) as Hd2 by (intros Hx; apply Ho1; symmetry; by apply edual_inj).
        assert (Hc1 : csub o1 (edual o) (edual o1) = edual o) by (unfold csub; by rewrite decide_True).
        destruct (s_K (ak k) !! edual o1) as [r1|] eqn:Kr1.
        2: { exfalso. assert (edual o1 ∈ dom (s_K (ak k))) as Hd by (apply (s_pair _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh1).
             apply elem_of_dom in Hd as [? Hx]. congruence. }
        destruct (lgt_tsum_lt N m _ _ (eq_ind _ (λ x, lgt (Some N) x _) L2 _ Hm) (Hts o1 h1 r1 Kh1 Kr1)) as (kr & Ekr & Hkr).
        assert (Hlk : kmapr (csub o1 (edual o)) (kdel2 o1 (edual o) (s_K (ak k))) !! edual o = s_K (ak k) !! edual o1).
        { rewrite <-(link_lookup _ o1 (edual o) (edual o1)) by done. by rewrite Hc1. }
        unfold fu. rewrite Hr', Hr, HK. unfold kval.
        rewrite Hlk. rewrite Kr1, Kh', Hm.
        destruct (Hcap _ r1 Kr1) as [Hc3 _]. rewrite Ekr in Hc3. simpl.
        destruct (h_ctr r1) as [c1|]; simpl in *; lia.
      + (* the link does not touch the partner of t *)
        right. assert (o ≠ edual o1) as Hn1 by (intros Hx; apply Ne1; by rewrite Hx, edual_edual).
        assert (Hc : csub o1 o2 o = o) by (apply csub_eq_off; done).
        assert (edual o ≠ edual o1) as Hd by (intros Hx; apply Ho1; by apply edual_inj).
        assert (Hc' : csub o1 o2 (edual o) = edual o) by (apply csub_eq_off; done).
        apply Hright.
        * rewrite <-Hc. exact (rend_emap _ t (csub o1 o2) e a1 o He' Ha Ho).
        * cbn [own_next]. change (delete o1 (delete o2 (s_K (ak k)))) with (kdel2 o1 o2 (s_K (ak k))).
          rewrite <-Hc', link_lookup by done. exact Kh'.
        * intros Hsu'. exact (istep_admin_actor _ _ _ s (proj1 Hst) I Hsu').
    - exfalso. by destruct Hst as [_ Hτ].
  Qed.
End run.
(** ** The soup at every lifting *)

Lemma soup_lifting N W T a q :
  (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → erase q = erase (s_q a) →
  ∃ a', s_q a' = q ∧ ∀ n, a' ∈ S^{N,W} _ n⟦∅ ⊢ T⟧.
Proof.
  destruct a as [[C1 M1] K Wa], q as [C2 M2]. intros Hs Hq. unfold erase in Hq. simpl in Hq.
  injection Hq as -> HM. destruct (relabel_map M1 M2 (eq_sym HM)) as (f & g & H1 & H2).
  exists (LFState (C1, M2) (krelabel f K) Wa). split; [done|]. intros n.
  destruct (Hs n) as (HW & A & Π & U & Hsi). split; [done|].
  exists A, Π, (U ∘ g). exact (soup_relabel _ _ _ _ _ _ M1 M2 _ _ _ _ _ _ f g H1 H2 Hsi).
Qed.

Lemma soup_links_restricted N W T a :
  (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → links_restricted (erase (s_q a)).
Proof.
  intros Hs0 q E e o1 o2 Hq HE Ha. destruct (pred_star_lift _ _ Hq) as (q' & Hq' & <-).
  destruct (lfsoup_isteps N W T (s_q a) q' (λ n, ex_intro _ a (conj eq_refl (Hs0 n))) Hq' (onat 1))
    as (a' & <- & Hs').
  destruct Hs' as (_ & A & Π & U & Hs). simpl in HE.
  assert (e ∈ soup (s_q a').2) as Hin by (rewrite HE; multiset_solver).
  apply elem_of_soup in Hin as [t Ht]. exact (s_link _ _ _ _ _ _ _ _ Hs t e o1 o2 Ht Ha).
Qed.

(** ** Adequacy

    Excluded middle and functional choice are explicit hypotheses. They
    pick one soup state for every index and one choice of tickets per
    position of a run (relation/ExProp.v, soup/SoupRun.v). *)

Section adequacy.
  Context (EM : excluded_middle) (FC : functional_choice).

  (** The soup alone gives lock freedom. *)
  Theorem lf_adequacy_soup N W T a :
    (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → lock_free (erase (s_q a)).
  Proof.
    intros Hs r l Hr0 Hmax Hfair.
    destruct (soup_lifting N W T a (r 0) Hs Hr0) as (a0 & Ha0 & Hs0).
    destruct (lfsoup_run EM FC N W T a0 r l Hmax Ha0 Hs0) as (tcs & Hinv & Hch).
    refine (lf_run_criterion (erase (s_q a)) r l Hr0 Hmax Hfair (wt a0 r l tcs) _ _ _ _ _
      nat lt (fu a0 r l tcs) lt_wf _ _ _ point (wchain_lt (wk a0 r l tcs)) (we a0 r l tcs)
      (wchain_lt_wf _ Hch) _ _).
    - intros k t s. apply (wt_pend N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t s. apply (wt_holder N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t. apply (lf_local_progress N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - exact (soup_no_tau_divergence N W T a Hs).
    - exact (soup_links_restricted N W T a Hs).
    - intros k t s s'. apply (wt_uniq N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t. apply (lf_pers N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t. apply (lf_fuel N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t. apply (lf_stab N W T a0 r l Ha0 Hmax tcs Hinv Hch).
    - intros k t s. apply (lf_rank N W T a0 r l Ha0 Hmax tcs Hinv Hch).
  Qed.

  (** One soup state for every index. *)
  Lemma lf_sem_state N W Σ p T :
    Σ ⊪^N _ W p : T → ∃ a, erase (s_q a) = p ∧ ∀ n, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.
  Proof.
    intros HP.
    destruct (exist_prop EM FC lfstate (λ a n, erase (s_q a) = p ∧ a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧))
      as (a & Ha).
    - intros a n1 n2 Hn [H1 (HW & A & Π & U & Hs)]. split; [done|]. split; [done|]. exists A, Π, U.
      constructor; try apply Hs.
      + intros t e He. eapply Erel_down; [exact Hn|]. by apply (sp_rel _ _ _ _ _ _ _ _ _ Hs).
      + intros t e He. eapply FuelE_down; [exact Hn|]. by apply (sp_fuel _ _ _ _ _ _ _ _ _ Hs).
    - intros n. destruct (HP n) as (a & H1 & _ & H2). by exists a.
    - exists a. split; [exact (proj1 (Ha ozero))|]. intros n. exact (proj2 (Ha n)).
  Qed.

  (** ∅ ⊪^N _ W p : T ⟹ lock_free p. *)
  Theorem lf_adequacy N W T p : ∅ ⊪^N _ W p : T → lock_free p.
  Proof. intros HP. destruct (lf_sem_state N W ∅ p T HP) as (a & <- & Hs). by apply (lf_adequacy_soup N W T a). Qed.

  (** ∅ ⊪^N _ W p : T ⟹ every weakly fair maximal run makes every
      thread progress: from every position on, every thread later stops or
      takes part in a channel step. *)
  Theorem lf_thread_progress N W T p :
    ∅ ⊪^N _ W p : T →
    ∀ r l, erase (r 0) = p → maximal r l → wfair r l → thread_progress_run r l.
  Proof.
    intros HP. pose proof (lf_adequacy N W T p HP) as Hlf.
    destruct (lf_sem_state N W ∅ p T HP) as (a & <- & Hs).
    apply thread_progress; [done|exact (soup_no_tau_divergence N W T a Hs)|exact (soup_links_restricted N W T a Hs)].
  Qed.
End adequacy.
