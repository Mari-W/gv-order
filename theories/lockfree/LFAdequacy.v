(** * Adequacy of the lock-free judgment (lock-freedom plan §16.5, §17.3)

    [lf_adequacy] proves that a process in [LFP] is lock free when the
    order of the world is well founded. The proof instantiates the
    criterion ([lf_run_criterion]) along a run, with the soup at every
    position and every index, the points π_k ([prun]) and the points and
    counters of every thread ([frun]).

    A pending thread depends on the thread whose environment holds the
    partner of the end it acts on ([hwaits]). A term may name an end in
    code it never runs, so [lf_criterion] itself, which reads [waits] off
    the terms, does not apply. Its uniqueness clause fails as soon as a
    second thread names the partner end in such code.

    - Local progress is a fact of one soup ([lfc_local_progress]).
    - [we k t] is the point π_k of the end t acts on, ordered by [w_lt W].
      A thread that does not step keeps it ([stab_step]). A blocked holder
      of the partner end acts on an end below it ([s_rank]).
    - [fu k t] is the counter of the partner end in its holder's counters
      ([fu_at]). A channel step of the holder on another end ticks it,
      handing the end on passes the counter minus one, and a link hands
      the obligation to a peer whose budget lies below it ([fuel_step]).
    - [no_tau_divergence] comes from the live relation
      ([live_no_tau_divergence]) and [links_restricted] from the soup
      ([lf_links_restricted]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.LFSoup lockfree.ThreadProgress.
From LRGV Require Import lockfree.LFFuel.

Set Default Proof Using "Type".

(** ** The end a pending thread offers *)

Definition aend1 (a : action) : option cend :=
  match a with ARecv o | ASend o _ | AClos o | ASel o _ | ABra o => Some o | _ => None end.

Definition rend (q : config) (t : nat) : option cend :=
  match q.2 !! t with
  | Some e => match act e with Some a => aend1 a | None => None end
  | None => None
  end.

Lemma aend1_aends a o : aend1 a = Some o → aends a = Some {[o]}.
Proof. destruct a; simpl; intros H; simplify_eq; done. Qed.

Lemma npend_end q t :
  npend q t → ∃ e a o, q.2 !! t = Some e ∧ act e = Some a ∧ aend1 a = Some o ∧ rend q t = Some o.
Proof.
  intros [(e & a & He & Ha & Hs) Hna].
  assert (¬ is_admin a) as Hna' by (intros H; apply Hna; by exists e, a).
  destruct a; simpl in *; try done; (eexists _, _, _; split_and!; [done|done|done|]);
    unfold rend; by rewrite He, Ha.
Qed.

Lemma offers_aend1 a σ o : offers a (LSess σ) → aend1 a = Some o → sl_end σ = Some o.
Proof. destruct a, σ; simpl; intros H Ho; try done; destruct_and?; simplify_eq; done. Qed.

Lemma aend1_not_link e a o : act e = Some a → aend1 a = Some o → ¬ link_t e.
Proof.
  intros Ha Ho (cd & e' & Hst). destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoa).
  rewrite Ha in Ha'. injection Ha' as <-. destruct a; simpl in *; done.
Qed.

Definition pt_of (π : gmap cend point) (o : cend) : point :=
  match π !! o with Some x => x | None => pvar 0 end.

Lemma sess_end_step e a o : act e = Some a → aend1 a = Some o → ∃ σ e', tstep e (LSess σ) e' ∧ sl_end σ = Some o.
Proof.
  intros Ha Ho. assert (is_sess a) as Hs by (unfold is_sess; destruct a; simpl in *; try done; by eexists).
  destruct (sess_stable_step e a Ha Hs) as (σ & e' & Hst). exists σ, e'. split; [done|].
  destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoa). rewrite Ha in Ha'. injection Ha' as <-.
  by apply (offers_aend1 a σ o).
Qed.

Lemma rend_emap q q' t e g :
  q.2 !! t = Some e → q'.2 !! t = Some (emap g e) →
  rend q' t = (λ o : cend, (g o.1, o.2)) <$> rend q t.
Proof.
  intros He He'. unfold rend. rewrite He, He', act_emap.
  destruct (act e) as [a|]; [|done]. simpl. by destruct a.
Qed.

Lemma rend_some q t o :
  rend q t = Some o → ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ aend1 a = Some o.
Proof.
  unfold rend. destruct (q.2 !! t) as [e|] eqn:He; [|done]. destruct (act e) as [a|] eqn:Ha; [|done].
  intros H. by exists e, a.
Qed.

(** ** An actor holds the ends it acts on

    The live relation reads the end of every session action in the
    environment ([tenv_hd_end], O-Link), so a thread that acts on an end
    holds it, whatever its term names elsewhere. *)

Lemma hd_end_held Θ o u k Θ1 : tenv_hd_end Θ o u k Θ1 → tenv_bipol Θ → o ∈ tenv_ends Θ.
Proof.
  intros [(s & Hext & _) Hp] Hb. destruct o as [c b]. simpl in *. subst b.
  apply (tenv_end_ends _ _ (s, k)). by apply (tenv_end_ext_eq _ _ _ _ Hext Hb).
Qed.

Section held.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S n) W ∅ T π q A U).

  Lemma act_held t e σ e' o :
    q.2 !! t = Some e → tstep e (LSess σ) e' → sl_end σ = Some o → o ∈ tenv_ends (A t).
  Proof.
    intros He Hst Ho. pose proof (lfc_bipol _ _ _ _ _ _ _ Hc t e He) as Hb.
    pose proof (LErel_S_step _ _ _ _ _ _ _ _ (lf_rel _ _ _ _ _ _ _ _ Hc t e He) Hst) as Hob.
    destruct σ as [o0 w|o0 w|o0|cd|o0 b0|o0 b0]; simpl in Ho; try discriminate; injection Ho as <-;
      simpl in Hob.
    - destruct Hob as (Θ1 & ? & ? & ? & ? & Hhd & _).
      exact (hd_end_held _ _ _ _ _ Hhd Hb).
    - destruct Hob as (Θr & Θ1 & Θ2 & ? & ? & ? & ? & ? & Hhd & _).
      exact (hd_end_held _ _ _ _ _ Hhd Hb).
    - destruct Hob as (Θ1 & ? & Hhd & _).
      exact (hd_end_held _ _ _ _ _ Hhd Hb).
    - destruct Hob as (Θr & ? & ? & ? & ? & Hhd & _).
      exact (hd_end_held _ _ _ _ _ Hhd Hb).
    - destruct Hob as (Θr & ? & ? & ? & ? & Hhd & _).
      exact (hd_end_held _ _ _ _ _ Hhd Hb).
  Qed.

  Lemma link_held t e cd e' o :
    q.2 !! t = Some e → tstep e (LSess (SLink cd)) e' → o ∈ cd → o ∈ tenv_ends (A t).
  Proof.
    intros He Hst Hin. pose proof (lfc_bipol _ _ _ _ _ _ _ Hc t e He) as Hb.
    destruct (LErel_S_link _ _ _ _ _ _ _ _ (lf_rel _ _ _ _ _ _ _ _ Hc t e He) Hst)
      as (c1 & d1 & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & _ & Hk & _).
    pose proof (tenv_bipol_ext_l _ _ _ _ H2 Hb) as Hbm.
    destruct (tenv_ends_ext _ _ _ _ H2 Hb) as [Hu2 _]. destruct (tenv_ends_ext _ _ _ _ H1 Hbm) as [Hu1 _].
    cbn [snd] in Hu1, Hu2. rewrite Hu2, Hu1. set_solver.
  Qed.

  Lemma act_held_chan t e σ e' o :
    q.2 !! t = Some e → tstep e (LSess σ) e' → sl_end σ = Some o → o.1 ∈ dom (A t).
  Proof. intros He Hst Ho. apply dom_tenv_ends. exists o.2. destruct o. by eapply act_held. Qed.

  (** Every link redex has a restricted end. *)
  Lemma lfc_link_restricted t e c d : q.2 !! t = Some e → act e = Some (ALink c d) → c.1 ∈ q.1.
  Proof.
    intros He Ha.
    destruct (act_offer e (ALink c d) (LSess (SLink {[c; d]})) Ha eq_refl) as [e' Hst].
    apply (lfc_closed _ _ _ _ _ _ _ Hc t e He). apply dom_tenv_ends. exists c.2.
    destruct c as [c b]. apply (link_held t e _ e' (c, b) He Hst). set_solver.
  Qed.
End held.

(** ** Facts of one soup *)

Section soup1.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty).
  Context (Hc : LFconf (S n) W ∅ T π q A U).

  Lemma s_offered_end t e a o k ek :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    offered_t (A t) e k → tenv_entry (A t) k = Some ek → (k.1, pt_pol ek.2) = o.
  Proof.
    intros He Ha Ho (σ & e1 & Hst & Hsel) Hk. destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoa).
    rewrite Ha in Ha'. injection Ha' as <-. pose proof (offers_aend1 a σ o Hoa Ho) as Hso.
    destruct (selects_info _ _ _ _ _ Hsel Hk Hso) as (H1 & H2 & _). destruct o. simpl in *. by subst.
  Qed.

  Lemma s_offered t e a o :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    ∃ k ek, offered_t (A t) e k ∧ tenv_entry (A t) k = Some ek ∧ (k.1, pt_pol ek.2) = o ∧
      below_rest W (A t) (offered_t (A t) e) ∅.
  Proof.
    intros He Ha Ho.
    assert (is_sess a) as Hsa by (unfold is_sess; destruct a; simpl in *; try done; by eexists).
    assert (¬ irred e) as Hnirr.
    { intros Hirr. destruct (sess_stable_step e a Ha Hsa) as (σ & e' & Hst). by apply (Hirr _ _ Hst). }
    pose proof (LErel_S_ready n W (A t) (U t) ∅ e (lf_rel _ _ _ _ _ _ _ _ Hc t e He) Hnirr) as Hr.
    pose proof (LocalProgress.sess_stable e a Ha Hsa) as Hst.
    destruct (Hr Hst) as [_ [Hl|Hbr]]; [by destruct (aend1_not_link e a o Ha Ho)|].
    assert (¬ is_val e) as Hv by (intros Hv; rewrite act_val in Ha; done).
    destruct (offered_exists W (A t) ∅ e Hr Hst Hv) as [k Hk].
    destruct Hk as (σ & e1 & Hs1 & Hsel) eqn:Hk'.
    destruct (selects_entry _ _ _ Hsel) as [ek Hek].
    exists k, ek. split_and!; [done|done| |done]. by apply (s_offered_end t e a o).
  Qed.

  Lemma s_held t e a o : q.2 !! t = Some e → act e = Some a → aend1 a = Some o → o ∈ tenv_ends (A t).
  Proof.
    intros He Ha Ho. destruct (sess_end_step e a o Ha Ho) as (σ & e' & Hst & Hσ).
    by apply (act_held n W T π q A U Hc t e σ e' o).
  Qed.

  Lemma s_partner t e a o :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    ∃ s es, s ≠ t ∧ q.2 !! s = Some es ∧ cdual o ∈ tenv_ends (A s).
  Proof.
    intros He Ha Ho.
    destruct (proj1 (tenv_ends_end (A t) o) (s_held t e a o He Ha Ho)) as [x Hx].
    destruct (lfc_partner _ _ _ _ _ _ _ Hc t e o x He Hx) as (s & es & y & Hes & Hy & Hy2 & _).
    exists s, es. split_and!; [|done|by eapply tenv_end_ends].
    intros ->. rewrite He in Hes. injection Hes as <-.
    destruct (s_offered t e a o He Ha Ho) as (k & ek & Hok & Hk & Hko & Hbr).
    destruct (tenv_end_entry_inv _ _ _ Hy) as (k' & Hk' & Hk'1).
    assert (tenv_end (A t) o = Some ek) as Hek.
    { rewrite <-Hko. apply tenv_end_entry; [apply (lfc_bipol _ _ _ _ _ _ _ Hc t e He)|done]. }
    rewrite Hx in Hek. injection Hek as <-.
    assert (¬ offered_t (A t) e k') as Hno.
    { intros Ho'. pose proof (s_offered_end t e a o k' y He Ha Ho Ho' Hk') as Heq.
      rewrite Hk'1 in Heq. destruct o as [c b]. unfold cdual in Heq. simpl in Heq.
      rewrite Hy2, pt_pol_dual in Heq. injection Heq as Hb. pose proof (tenv_end_pol _ _ _ Hx) as Hp.
      simpl in Hp. rewrite Hp in Hb. by destruct b. }
    destruct (Hbr k x Hok Hk) as [Hb _]. specialize (Hb k' y Hk' Hno). unfold entry_head in Hb.
    rewrite Hy2, pt_dual_dual in Hb. by apply (proj2 HW x.2).
  Qed.

  Lemma s_uniq s s' es es' o :
    q.2 !! s = Some es → q.2 !! s' = Some es' → o ∈ tenv_ends (A s) → o ∈ tenv_ends (A s') → s = s'.
  Proof.
    intros Hs Hs' Ho Ho'. destruct (decide (s = s')) as [|Hne]; [done|].
    exfalso. by apply (lf_disj _ _ _ _ _ _ _ _ Hc s s' es es' Hne Hs Hs' o).
  Qed.

  Lemma s_rank t e a o s es a' o' :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    q.2 !! s = Some es → act es = Some a' → aend1 a' = Some o' →
    s ≠ t → cdual o ∈ tenv_ends (A s) →
    enabled q t ∨ w_lt W (pt_of π o') (pt_of π o).
  Proof.
    intros He Ha Ho Hes Ha' Ho' Hst Hdo.
    destruct (s_offered t e a o He Ha Ho) as (k & ek & Hok & Hk & Hko & _).
    destruct (s_offered s es a' o' Hes Ha' Ho') as (k0 & ek0 & Hok0 & Hk0 & Hko0 & Hbr).
    assert (tenv_end (A t) o = Some ek) as Hek.
    { rewrite <-Hko. apply tenv_end_entry; [apply (lfc_bipol _ _ _ _ _ _ _ Hc t e He)|done]. }
    destruct (proj1 (tenv_ends_end (A s) (cdual o)) Hdo) as [y Hy].
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc t e o ek s es y He Hek Hes Hy) as [Hy2 _].
    destruct (decide (o' = cdual o)) as [->|Hne].
    - assert (tenv_end (A s) (cdual o) = Some ek0) as Hek0.
      { rewrite <-Hko0. apply tenv_end_entry; [apply (lfc_bipol _ _ _ _ _ _ _ Hc s es Hes)|done]. }
      rewrite Hy in Hek0. injection Hek0 as <-.
      destruct (lp_meet n W HW T π q A U Hc t e s es k ek k0 y He Hes Hok Hok0 Hk Hk0) as [?|[_ Hl]].
      + assert (k0.1 = (cdual o).1) as -> by (rewrite <-Hko0; done). rewrite <-Hko. done.
      + intros [= -> _]. done.
      + done.
      + by left.
      + by destruct (aend1_not_link es a' _ Ha' Ho').
    - right. destruct (tenv_end_entry_inv _ _ _ Hy) as (k' & Hk' & Hk'1).
      assert (¬ offered_t (A s) es k') as Hno.
      { intros Hof. apply Hne. rewrite <-(s_offered_end s es a' o' k' y Hes Ha' Ho' Hof Hk').
        rewrite Hk'1. pose proof (tenv_end_pol _ _ _ Hy) as Hp. destruct o as [c b].
        unfold cdual in *. simpl in *. by rewrite Hp. }
      destruct (Hbr k0 ek0 Hok0 Hk0) as [Hb _]. specialize (Hb k' y Hk' Hno). unfold entry_head in Hb.
      rewrite Hy2, pt_dual_dual in Hb.
      assert (tenv_end (A s) o' = Some ek0) as Hek0.
      { rewrite <-Hko0. apply tenv_end_entry; [apply (lfc_bipol _ _ _ _ _ _ _ Hc s es Hes)|done]. }
      unfold pt_of. rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s es o' ek0 Hes Hek0).
      by rewrite (lf_pt _ _ _ _ _ _ _ _ Hc t e o ek He Hek).
  Qed.
End soup1.

(** ** Threads outside a step *)

(** The threads outside a step keep their terms up to a renaming, which
    fixes every channel no participant holds, and such a channel stays
    in the configuration. *)
Lemma istep_keeps n W T π q A U L q' c :
  LFconf (S n) W ∅ T π q A U → istep q L q' →
  (∀ u eu, u ∈ L → q.2 !! u = Some eu → c ∉ dom (A u)) →
  ∃ g, (∀ u eu, u ∉ L → q.2 !! u = Some eu → q'.2 !! u = Some (emap g eu)) ∧ g c = c ∧
    (c ∈ q.1 → c ∈ q'.1).
Proof.
  intros Hc Hst Hn.
  destruct Hst as [C M i e e' Hi Hs|C M i e c0 x e' Hi Hs HC Hcs|C M i j e v e' Hi Hs Hj
    |C M i j c0 b v e e' f f' Hij Hi Hj He Hf|C M i j c0 b e e' f f' Hij Hi Hj He Hf HC
    |C M i j c0 β b0 e e' f f' Hij Hi Hj He Hf|C M i e c0 bc d bd e' Hi Hs HC]; simpl in *.
  1-6: exists id; split_and!; [intros u eu Hu Heu; rewrite emap_id|done|].
  - rewrite lookup_insert_ne; [done|set_solver].
  - done.
  - rewrite lookup_insert_ne; [done|set_solver].
  - set_solver.
  - rewrite !lookup_insert_ne; [done|set_solver|]. intros ->. by rewrite Hj in Heu.
  - done.
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - done.
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - assert (c ≠ c0); [|set_solver]. intros ->. apply (Hn i e ltac:(set_solver) Hi).
    by apply (act_held_chan n W T π (C, M) A U Hc i e _ e' (c0, b) Hi He).
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - done.
  - assert (c ≠ c0) as Hcc.
    { intros ->. apply (Hn i e ltac:(set_solver) Hi). apply dom_tenv_ends. exists bc.
      apply (link_held n W T π (C, M) A U Hc i e _ e' (c0, bc) Hi Hs). set_solver. }
    exists (Instr.csub c0 d). split_and!.
    + intros u eu Hu Heu. rewrite lookup_fmap, lookup_insert_ne by set_solver. rewrite Heu. simpl.
      by rewrite chsubst_emap.
    + unfold Instr.csub. by rewrite decide_False.
    + set_solver.
Qed.

(** ** A thread that does not step keeps the point of its end *)
Lemma stab_step n W T π P F q A U L q' t o :
  strict W → LFconf (S (S n)) W ∅ T π q A U → lf_fuelc (S (S n)) W π P F A q →
  istep q L q' → t ∉ L → rend q t = Some o →
  ∃ o', rend q' t = Some o' ∧ pupd π q L q' !! o' = π !! o.
Proof.
  intros HW Hc HF Hst Ht Ho. destruct q as [C M].
  destruct (rend_some _ _ _ Ho) as (e & a & He & Ha & Ha1). simpl in He.
  pose proof (s_held (S n) W HW T π (C, M) A U Hc t e a o He Ha Ha1) as Hoe.
  assert (Hoc : o.1 ∈ dom (A t)) by (apply dom_tenv_ends; exists o.2; by destruct o).
  (* the channel of a synchronization between i and j is not t's *)
  assert (Hsync : ∀ i j ei ej σi σj ei' ej' c b,
            i ≠ t → j ≠ t → M !! i = Some ei → M !! j = Some ej →
            tstep ei (LSess σi) ei' → sl_end σi = Some (c, b) →
            tstep ej (LSess σj) ej' → sl_end σj = Some (c, negb b) → o.1 ≠ c).
  { intros i j ei ej σi σj ei' ej' c b Hit Hjt Hi Hj Hsi Hei Hsj Hej Hoc'.
    pose proof (act_held _ _ _ _ _ _ _ Hc i ei _ _ _ Hi Hsi Hei) as H1.
    pose proof (act_held _ _ _ _ _ _ _ Hc j ej _ _ _ Hj Hsj Hej) as H2.
    apply (st_cowner n W HW T π C M A U Hc P F HF i j ei ej c b t e Hi Hj H1 H2
      (not_eq_sym Hit) (not_eq_sym Hjt) He).
    by rewrite <-Hoc'. }
  inversion Hst as [C0 M0 i ei ei' Hi Hs|C0 M0 i ei c x ei' Hi Hs HC Hcs|C0 M0 i j ei v ei' Hi Hs Hj
    |C0 M0 i j c b v ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i j c b ei ei' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j c β b ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i ei c bc d bd ei' Hi Hs HC]; subst; simpl in Ht.
  - exists o. unfold rend. simpl. rewrite lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1.
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho'). rewrite Ha'. by apply offers_beta in Ho' as ->.
  - exists o. unfold rend. simpl. rewrite lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1.
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho'). rewrite Ha'. apply offers_new in Ho' as ->. simpl.
    assert ((C ∪ {[c]}) ∖ C = {[c]}) as -> by (clear -HC; set_solver). rewrite elements_singleton. simpl.
    assert (o.1 ≠ c) as Hoc'.
    { intros Heq. apply HC. rewrite <-Heq. by apply (st_closed n W HW T π C M A U Hc P F HF t e He). }
    rewrite !lookup_insert_ne; [done| |]; intros Heq; subst o; simpl in Hoc'; congruence.
  - exists o. unfold rend. simpl. assert (t ≠ j) by (intros ->; congruence).
    rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1.
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho'). rewrite Ha'. by apply offers_spawn in Ho' as ->.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c b ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc'.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_send in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_recv in Ho2 as ->.
    destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
      unfold pev2; rewrite ?Ha1', ?Ha2; simpl; rewrite !lookup_alter_ne; try done; intros Heq; subst o; simpl in Hoc'; congruence.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c b ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc'.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_clos in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_clos in Ho2 as ->.
    destruct (pev_of_pair (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
      unfold pev2; rewrite ?Ha1', ?Ha2; simpl; rewrite !lookup_delete_ne; try done; intros Heq; subst o; simpl in Hoc'; congruence.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c β ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc'.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_sel in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_bra in Ho2 as ->.
    assert (pev_of (C, M) {[i; j]} (C, <[j:=f']> (<[i:=ei']> M)) = PChoice (c, β) b) as ->.
    { destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
        unfold pev2; by rewrite ?Ha1', ?Ha2. }
    simpl. destruct (π !! (c, β)); [|done]. rewrite !lookup_insert_ne; try done; intros Heq; subst o; simpl in Hoc'; congruence.
  - (* link *)
    assert (t ≠ i) as Hti by set_solver.
    assert (rend (C ∖ {[c]}, chsubst c d <$> <[i:=ei']> M) t = Some (Instr.csub c d o.1, o.2)) as Hr'.
    { rewrite (rend_emap (C, M) _ t e (Instr.csub c d) He); [by rewrite Ho|].
      simpl. rewrite lookup_fmap, lookup_insert_ne, He by done. simpl. by rewrite chsubst_emap. }
    exists (Instr.csub c d o.1, o.2). split; [done|].
    assert (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i:=ei']> M) =
            delete (c, true) (delete (c, false) π)) as ->.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1.
      destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho'). rewrite Ha'. apply offers_link in Ho' as (o1 & o2 & -> & _).
      simpl. assert (C ∖ (C ∖ {[c]}) = {[c]}) as ->.
      { apply set_eq. intros y. destruct (decide (y = c)) as [->|Hy]; [clear -HC|clear -HC Hy]; set_solver. }
      by rewrite elements_singleton. }
    destruct (st_link_data n W HW T π C M A U Hc P F HF i ei c bc d bd ei' Hi Hs)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & _ & _ & _ & _ & _ & _ & _).
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd. simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    pose proof (tenv_end_ends _ _ _ Hxc) as Hci. pose proof (tenv_end_ends _ _ _ Hxd) as Hdi.
    pose proof (st_disj n W HW T π C M A U Hc P F HF t i e ei Hti He Hi) as Hd0.
    destruct o as [c0 b0]. unfold Instr.csub. simpl. destruct (decide (c0 = c)) as [->|Hc0].
    + assert (b0 = negb bc) as ->.
      { destruct (decide (b0 = bc)) as [->|Hb]; [by destruct (Hd0 (c, bc))|]. by destruct b0, bc. }
      destruct (decide (c = d)) as [<-|Hcd].
      { exfalso. rewrite Hbd in Hdi. by apply (Hd0 (c, negb bc)). }
      rewrite !lookup_delete_ne by (intros [=]; congruence).
      destruct (lfc_partner _ _ _ _ _ _ _ Hc i ei _ _ Hi Hxc) as (s & gs & ys & Hgs & Hys & Hys2 & _).
      change (c, negb bc) with (cdual (c, bc)).
      rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s gs _ _ Hgs Hys), <-Hbd, (lf_pt _ _ _ _ _ _ _ _ Hc i ei _ _ Hi Hxd).
      by rewrite Hys2, Hdx, pt_dual_dual.
    + rewrite !lookup_delete_ne; [done| |]; intros [=]; congruence.
Qed.

(** ** An enabled pending thread stays enabled while it does not step *)

(** Two threads ready to synchronize on the end o of t and its partner. *)
Definition synced (q : config) (t p : nat) (o : cend) : Prop :=
  ∃ e f, q.2 !! t = Some e ∧ q.2 !! p = Some f ∧ t ≠ p ∧
    ((∃ v e' f', tstep e (LSess (SSend o v)) e' ∧ tstep f (LSess (SRecv (cdual o) v)) f') ∨
     (∃ v e' f', tstep f (LSess (SSend (cdual o) v)) f' ∧ tstep e (LSess (SRecv o v)) e') ∨
     (∃ e' f', tstep e (LSess (SClos o)) e' ∧ tstep f (LSess (SClos (cdual o))) f' ∧ o.1 ∈ q.1) ∨
     (∃ b e' f', tstep e (LSess (SSel o b)) e' ∧ tstep f (LSess (SBra (cdual o) b)) f') ∨
     (∃ b e' f', tstep f (LSess (SSel (cdual o) b)) f' ∧ tstep e (LSess (SBra o b)) e')).

Lemma synced_enabled q t p o : synced q t p o → enabled q t.
Proof.
  destruct q as [C M]. destruct o as [c β]. unfold cdual. simpl.
  intros (e & f & He & Hf & Htp & H).
  destruct H as [(v & e' & f' & H1 & H2)|[(v & e' & f' & H1 & H2)|[(e' & f' & H1 & H2 & HC)
    |[(b & e' & f' & H1 & H2)|(b & e' & f' & H1 & H2)]]]].
  - eexists _, _. split; [by eapply (IMsg C M t p c β v e e' f f')|set_solver].
  - eexists _, _. split; [eapply (IMsg C M p t c (negb β) v f f' e e'); [done|done|done|done|]|set_solver].
    by rewrite negb_involutive.
  - eexists _, _. split; [by eapply (IClose C M t p c β e e' f f')|set_solver].
  - eexists _, _. split; [by eapply (IChoice C M t p c β b e e' f f')|set_solver].
  - eexists _, _. split; [eapply (IChoice C M p t c (negb β) b f f' e e'); [done|done|done|done|]|set_solver].
    by rewrite negb_involutive.
Qed.

Lemma admin_lbl_offers a α o : offers a α → admin_lbl α → aend1 a = Some o → False.
Proof. destruct a, α; simpl; try done; destruct σ; simpl; try done; intros; done. Qed.

Lemma enabled_synced q t e a o :
  q.2 !! t = Some e → act e = Some a → aend1 a = Some o → enabled q t →
  ∃ p, synced q t p o.
Proof.
  intros He Ha Ho (L & q' & Hst & HtL). destruct q as [C M]. simpl in He.
  assert (Hlbl : ∀ α e', tstep e α e' → offers a α) by
    (intros α e' Hs; destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoa); congruence).
  inversion Hst as [C0 M0 i ei ei' Hi Hs|C0 M0 i ei c x ei' Hi Hs HC Hcs|C0 M0 i j ei v ei' Hi Hs Hj
    |C0 M0 i j c b v ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i j c b ei ei' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j c β b ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i ei c bc d bd ei' Hi Hs HC]; subst;
    try (apply elem_of_singleton in HtL as ->; rewrite He in Hi; injection Hi as <-;
         exfalso; eapply admin_lbl_offers; [by apply (Hlbl _ _ Hs)|done|exact Ho]).
  all: apply elem_of_union in HtL as [HtL|HtL]; apply elem_of_singleton in HtL as ->.
  all: try (rewrite He in Hi; injection Hi as <-).
  all: try (rewrite He in Hj; injection Hj as <-).
  - pose proof (Hlbl _ _ He0) as Hoa. apply offers_send in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, e, f. split_and!; [done|done|done|]. left. by eexists _, _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_recv in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; left.
    eexists _, _, _. unfold cdual. simpl. rewrite negb_involutive. split; [exact He0|exact Hf].
  - pose proof (Hlbl _ _ He0) as Hoa. apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, e, f. split_and!; [done|done|done|]. right; right; left. by eexists _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; right; left.
    eexists _, _. unfold cdual. simpl. rewrite negb_involutive. split_and!; [exact Hf|exact He0|done].
  - pose proof (Hlbl _ _ He0) as Hoa. apply offers_sel in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, e, f. split_and!; [done|done|done|]. right; right; right; left. by eexists _, _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_bra in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; right; right; right.
    eexists _, _, _. unfold cdual. simpl. rewrite negb_involutive. split; [exact He0|exact Hf].
Qed.

(** The partner of a participant p acts on the partner of p's end. *)
Lemma sync_partner_act q L q' p ep ap op :
  istep q L q' → p ∈ L → q.2 !! p = Some ep → act ep = Some ap → aend1 ap = Some op →
  ∃ u eu σ eu', u ∈ L ∧ u ≠ p ∧ q.2 !! u = Some eu ∧ tstep eu (LSess σ) eu' ∧ sl_end σ = Some (cdual op).
Proof.
  intros Hst HpL Hp Ha Ho. destruct q as [C M]. simpl in Hp.
  assert (Hlbl : ∀ α e', tstep ep α e' → offers ap α) by
    (intros α e' Hs; destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoa); congruence).
  inversion Hst as [C0 M0 i ei ei' Hi Hs|C0 M0 i ei c x ei' Hi Hs HC Hcs|C0 M0 i j ei v ei' Hi Hs Hj
    |C0 M0 i j c b v ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i j c b ei ei' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j c β b ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i ei c bc d bd ei' Hi Hs HC]; subst;
    try (apply elem_of_singleton in HpL as ->; rewrite Hp in Hi; injection Hi as <-;
         exfalso; eapply admin_lbl_offers; [by apply (Hlbl _ _ Hs)|done|exact Ho]).
  all: apply elem_of_union in HpL as [HpL|HpL]; apply elem_of_singleton in HpL as ->.
  all: try (rewrite Hp in Hi; injection Hi as <-).
  all: try (rewrite Hp in Hj; injection Hj as <-).
  all: first [pose proof (Hlbl _ _ He0) as Hoa|pose proof (Hlbl _ _ Hf) as Hoa].
  - apply offers_send in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists j, f, _, f'. split_and!; [set_solver|done|done|exact Hf|done].
  - apply offers_recv in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists i, ei, _, ei'. split_and!; [set_solver|done|done|exact He0|].
    unfold cdual. simpl. by rewrite negb_involutive.
  - apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists j, f, _, f'. split_and!; [set_solver|done|done|exact Hf|done].
  - apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists i, ei, _, ei'. split_and!; [set_solver|done|done|exact He0|].
    unfold cdual. simpl. by rewrite negb_involutive.
  - apply offers_sel in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists j, f, _, f'. split_and!; [set_solver|done|done|exact Hf|done].
  - apply offers_bra in Hoa as ->. simpl in Ho. injection Ho as <-.
    eexists i, ei, _, ei'. split_and!; [set_solver|done|done|exact He0|].
    unfold cdual. simpl. by rewrite negb_involutive.
Qed.

Lemma synced_step q (L : gset nat) q' t p o (g : chan → chan) :
  synced q t p o → t ∉ L → p ∉ L →
  (∀ u eu, u ∉ L → q.2 !! u = Some eu → q'.2 !! u = Some (emap g eu)) → g o.1 = o.1 →
  (o.1 ∈ q.1 → o.1 ∈ q'.1) → synced q' t p o.
Proof.
  intros (e & f & He & Hf & Htp & H) Ht Hp Hg Hgo Hkept.
  pose proof (Hg t e Ht He) as He'. pose proof (Hg p f Hp Hf) as Hf'.
  assert (TauThread.omap g o = o) as Ho by (destruct o; unfold TauThread.omap; simpl in *; by rewrite Hgo).
  assert (TauThread.omap g (cdual o) = cdual o) as Hdo
    by (destruct o; unfold TauThread.omap, cdual; simpl in *; by rewrite Hgo).
  exists (emap g e), (emap g f). split_and!; [done|done|done|].
  destruct H as [(v & e1 & f1 & H1 & H2)|[(v & e1 & f1 & H1 & H2)|[(e1 & f1 & H1 & H2 & HC)
    |[(b & e1 & f1 & H1 & H2)|(b & e1 & f1 & H1 & H2)]]]];
    apply (tstep_emap g) in H1, H2; cbn [lmap smap] in H1, H2;
    try rewrite Ho in H1; try rewrite Ho in H2; try rewrite Hdo in H1; try rewrite Hdo in H2.
  - left. exists (emap g v), (emap g e1), (emap g f1). by split.
  - right; left. exists (emap g v), (emap g e1), (emap g f1). by split.
  - right; right; left. exists (emap g e1), (emap g f1). split_and!; [done|done|]. by apply Hkept.
  - right; right; right; left. exists b, (emap g e1), (emap g f1). by split.
  - right; right; right; right. exists b, (emap g e1), (emap g f1). by split.
Qed.

Lemma synced_partner_act q t p o f :
  synced q t p o → q.2 !! p = Some f →
  ∃ ap σ f', act f = Some ap ∧ aend1 ap = Some (cdual o) ∧ tstep f (LSess σ) f' ∧ sl_end σ = Some (cdual o).
Proof.
  intros (e0 & f0 & _ & Hf0 & _ & H) Hf. rewrite Hf in Hf0. injection Hf0 as <-.
  destruct H as [(v & e1 & f1 & H1 & H2)|[(v & e1 & f1 & H1 & H2)|[(e1 & f1 & H1 & H2 & _)
    |[(b & e1 & f1 & H1 & H2)|(b & e1 & f1 & H1 & H2)]]]].
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_recv in Hoa as ->. by eexists _, _, _.
  - destruct (act_step _ _ _ H1) as (ap & Hap & Hoa). apply offers_send in Hoa as ->. by eexists _, _, _.
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_clos in Hoa as ->. by eexists _, _, _.
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_bra in Hoa as ->. by eexists _, _, _.
  - destruct (act_step _ _ _ H1) as (ap & Hap & Hoa). apply offers_sel in Hoa as ->. by eexists _, _, _.
Qed.

Lemma synced_sym_t q t p o : synced q t p o → t ≠ p.
Proof. by intros (_ & _ & _ & _ & ? & _). Qed.

Lemma pers_step n W T π q A U L q' t :
  strict W → LFconf (S n) W ∅ T π q A U → istep q L q' → t ∉ L → npend q t → enabled q t → enabled q' t.
Proof.
  intros HW Hc Hst Ht Hp Hen. destruct (npend_end q t Hp) as (e & a & o & He & Ha & Ho & _).
  destruct (enabled_synced q t e a o He Ha Ho Hen) as [p Hsy].
  pose proof Hsy as (e0 & f & He0 & Hf & Htp & _).
  pose proof (s_held n W HW T π q A U Hc t e a o He Ha Ho) as Hto.
  destruct (synced_partner_act q t p o f Hsy Hf) as (ap & σp & f' & Hap & Hao & Hsp & Hσp).
  pose proof (act_held n W T π q A U Hc p f σp f' _ Hf Hsp Hσp) as Hpo.
  assert (Hholds : ∀ u eu, q.2 !! u = Some eu → o.1 ∈ dom (A u) → u = t ∨ u = p).
  { intros u eu Heu Hm. apply dom_tenv_ends in Hm as [b' Hb'].
    destruct (decide ((o.1, b') = o)) as [Heq|Hneq].
    - left. rewrite Heq in Hb'. by apply (s_uniq n W HW T π q A U Hc u t eu e o).
    - right. assert ((o.1, b') = cdual o) as Heq.
      { destruct o as [c β]. unfold cdual. simpl in *. f_equal.
        destruct b', β; simpl; try done; exfalso; by apply Hneq. }
      rewrite Heq in Hb'. by apply (s_uniq n W HW T π q A U Hc u p eu f (cdual o)). }
  assert (p ∉ L) as HpL.
  { intros HpL.
    destruct (sync_partner_act q L q' p f ap _ Hst HpL Hf Hap Hao) as (u & eu & σ & eu' & HuL & Hup & Heu & Hsu & Hσu).
    rewrite cdual_cdual in Hσu.
    pose proof (act_held n W T π q A U Hc u eu σ eu' _ Heu Hsu Hσu) as Huo.
    assert (u = t) as -> by (apply (s_uniq n W HW T π q A U Hc u t eu e o); done).
    done. }
  destruct (istep_keeps n W T π q A U L q' o.1 Hc Hst) as (g & Hg & Hgo & Hkept).
  { intros u eu HuL Heu Hm. destruct (Hholds u eu Heu Hm) as [->| ->]; done. }
  apply (synced_enabled q' t p o). by apply (synced_step q L q' t p o g).
Qed.

(** ** The soup along runs and reachable configurations *)

Lemma strict_of W : world_wf W → well_founded (w_lt W) → strict W.
Proof. intros HW Hwf. split; [done|]. intros x Hx. induction (Hwf x) as [x _ IH]. by apply (IH x). Qed.

Lemma erase_surj (p : proc) : ∃ q, erase q = p.
Proof.
  destruct p as [C E]. induction E as [|x E IH] using gmultiset_ind.
  - exists (C, ∅). unfold erase. simpl. by rewrite soup_empty.
  - destruct IH as [[C' M] Hq]. unfold erase in Hq. simpl in Hq. injection Hq as -> HE.
    set (j := fresh (dom M)). assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    exists (C, <[j := x]> M). unfold erase. simpl. rewrite soup_insert by done. rewrite HE.
    by rewrite (comm_L (⊎)).
Qed.

Lemma lf_links_restricted W T p :
  strict W → LFP W ∅ T p → links_restricted p.
Proof.
  intros HW HP q E e c d Hq HE Ha.
  destruct (erase_surj p) as [q0 Hq0].
  destruct (LFP_soup W ∅ T p q0 HP Hq0) as (π & P & F & Hs0).
  rewrite <-Hq0 in Hq. destruct (pred_star_lift q0 q Hq) as (q1 & Hq1 & <-).
  destruct (lfsoup_isteps W T π P F q0 q1 HW Hq1 Hs0) as (π' & P' & F' & Hs1).
  destruct (Hs1 1) as (A & U & Hc & _). simpl in HE.
  assert (e ∈ soup q1.2) as He by (rewrite HE; multiset_solver).
  apply elem_of_soup in He as [t Ht].
  left. by apply (lfc_link_restricted 0 W T π' q1 A U Hc t e c d).
Qed.

(** ** The counter of the partner end

    The holder of an end is the thread whose own points hold it ([P s]
    is kept on the ends of s's environment). [fu_at] reads the counter of
    the partner of the end a pending thread acts on, in its holder's
    counters. *)

Definition holder (P : nat → gmap cend point) (q : config) (o : cend) : option nat :=
  match list_find (λ se : nat * expr, o ∈ dom (P se.1)) (map_to_list q.2) with
  | Some (_, (s, _)) => Some s
  | None => None
  end.

Lemma holder_spec P q o s es :
  q.2 !! s = Some es → o ∈ dom (P s) →
  (∀ s' es', q.2 !! s' = Some es' → o ∈ dom (P s') → s' = s) → holder P q o = Some s.
Proof.
  intros Hs Ho Hu. unfold holder.
  destruct (list_find _ _) as [[i [s0 e0]]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hl & Hin & _). simpl in Hin.
    apply list_elem_of_lookup_2, elem_of_map_to_list in Hl. f_equal. by apply (Hu s0 e0).
  - apply list_find_None in Hf. rewrite Forall_forall in Hf. exfalso.
    apply (Hf (s, es)); [by apply elem_of_map_to_list|done].
Qed.

Definition fval (F : nat → gmap cend fuel) (s : nat) (o : cend) : nat :=
  match F s !! o with Some (Some m) => m | _ => 0 end.

Definition fu_at (q : config) (P : nat → gmap cend point) (F : nat → gmap cend fuel) (t : nat) : nat :=
  match rend q t with
  | Some o => match holder P q (cdual o) with Some s => fval F s (cdual o) | None => 0 end
  | None => 0
  end.

(** Distinct threads hold distinct ends. *)
Lemma P_uniq n W Σ T π q A U P F x y ex ey o :
  LFconf n W Σ T π q A U → lf_fuelc n W π P F A q →
  q.2 !! x = Some ex → q.2 !! y = Some ey → o ∈ dom (P x) → o ∈ dom (P y) → x = y.
Proof.
  intros Hc HF Hx Hy Hox Hoy. destruct (decide (x = y)) as [|Hne]; [done|]. exfalso.
  destruct (HF x ex Hx) as (_ & H2x & _). destruct (HF y ey Hy) as (_ & H2y & _).
  rewrite H2x in Hox. rewrite H2y in Hoy. by apply (lf_disj _ _ _ _ _ _ _ _ Hc x y ex ey Hne Hx Hy o).
Qed.

Lemma hwaits_end P q t e a o x :
  q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
  hwaits P q t x ↔ x ≠ t ∧ is_Some (q.2 !! x) ∧ cdual o ∈ dom (P x).
Proof.
  intros He Ha Ho. split.
  - intros (Hxt & e' & a' & S & o' & He' & Ha' & HS & Ho' & Hx & Hm).
    rewrite He in He'. injection He' as <-. rewrite Ha in Ha'. injection Ha' as <-.
    rewrite (aend1_aends a o Ho) in HS. injection HS as <-. apply elem_of_singleton in Ho' as ->.
    done.
  - intros (Hxt & Hx & Hm). split; [done|]. exists e, a, {[o]}, o.
    split_and!; try done; [by apply aend1_aends|set_solver].
Qed.

Section counters.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty) (P : nat → gmap cend point) (F : nat → gmap cend fuel).
  Context (Hc : LFconf (S (S n)) W ∅ T π q A U) (HF : lf_fuelc (S (S n)) W π P F A q).

  (** The partner end of a pending thread has a finite counter. *)
  Lemma holder_fin t e a o s es :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    q.2 !! s = Some es → s ≠ t → cdual o ∈ tenv_ends (A s) →
    ∃ m, F s !! cdual o = Some (Some m) ∧ fu_at q P F t = m.
  Proof.
    intros He Ha Ho Hes Hst Hso.
    destruct (HF t e He) as (H1t & H2t & H3t & H4t). destruct (HF s es Hes) as (H1s & H2s & H3s & H4s).
    destruct (sess_end_step e a o Ha Ho) as (σ & e1 & Hst1 & Hσ).
    destruct (fuel_wait (S n) W (P t) (F t) e H1t σ e1 o Hst1 Hσ) as (k & mb & Hk & Hb).
    pose proof (s_held (S n) W HW T π q A U Hc t e a o He Ha Ho) as Hto.
    destruct (proj1 (tenv_ends_end (A t) o) Hto) as [x Hx].
    destruct (proj1 (tenv_ends_end (A s) (cdual o)) Hso) as [y Hy].
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc t e o x s es y He Hx Hes Hy) as [Hy2 _].
    assert (P s !! cdual o = Some (pt_dual k)) as Hks.
    { rewrite H4s by done. rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s es _ _ Hes Hy), Hy2.
      rewrite H4t in Hk by done. rewrite (lf_pt _ _ _ _ _ _ _ _ Hc t e _ _ He Hx) in Hk. by injection Hk as ->. }
    assert (is_Some (F s !! cdual o)) as [f Hf] by (apply elem_of_dom; by rewrite H3s).
    destruct (fuel_cap (S n) W (P s) (F s) es H1s (cdual o) f Hf) as (k' & Hk' & Hle).
    rewrite Hks in Hk'. injection Hk' as <-. rewrite Hb in Hle. destruct f as [m|]; [|done].
    exists m. split; [done|]. unfold fu_at. unfold rend. rewrite He, Ha, Ho.
    rewrite (holder_spec P q (cdual o) s es Hes); [|by rewrite H2s|].
    - unfold fval. by rewrite Hf.
    - intros s' es' Hes' Hso'. apply (P_uniq _ _ _ _ _ _ _ _ _ _ s' s es' es (cdual o) Hc HF Hes' Hes Hso').
      by rewrite H2s.
  Qed.
End counters.

(** The goal of a step for the counter of t's partner, given the
    partner end o' of t after the step. *)
Definition fgoal (q q' : config) (P' : nat → gmap cend point) (F' : nat → gmap cend fuel) (L : gset nat)
    (t : nat) (o' : cend) (s : nat) (m : nat) : Prop :=
  ∃ s', is_Some (q'.2 !! s') ∧ s' ≠ t ∧ cdual o' ∈ dom (P' s') ∧
    (fval F' s' (cdual o') < m ∨ (fval F' s' (cdual o') = m ∧ s' = s ∧ (s ∈ L → admin_at q s))).

Lemma fuel_reduce n W T π q A U P F n' π' q' A' U' P' F' L t e a o e' a' o' s es m :
  LFconf n W ∅ T π q A U → lf_fuelc n W π P F A q →
  LFconf n' W ∅ T π' q' A' U' → lf_fuelc n' W π' P' F' A' q' →
  q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
  q.2 !! s = Some es → s ≠ t → cdual o ∈ dom (P s) → fu_at q P F t = m →
  q'.2 !! t = Some e' → act e' = Some a' → aend1 a' = Some o' →
  fgoal q q' P' F' L t o' s m →
  fu_at q' P' F' t < fu_at q P F t ∨
  (fu_at q' P' F' t = fu_at q P F t ∧ (∀ x, hwaits P' q' t x ↔ hwaits P q t x) ∧
   ∀ x, hwaits P q t x → x ∈ L → admin_at q x).
Proof.
  intros Hc HF Hc' HF' He Ha Ho Hes Hst Hso Hm He' Ha' Ho' (s' & [es' Hes'] & Hst' & Hso' & Hor).
  assert (fu_at q' P' F' t = fval F' s' (cdual o')) as Hfu'.
  { unfold fu_at, rend. rewrite He', Ha', Ho'.
    rewrite (holder_spec P' q' (cdual o') s' es' Hes' Hso'); [done|].
    intros x ex Hx Hxo. by apply (P_uniq _ _ _ _ _ _ _ _ _ _ x s' ex es' (cdual o') Hc' HF' Hx Hes'). }
  rewrite Hfu', Hm. destruct Hor as [Hlt|(Heq & -> & Had)]; [by left|right].
  split_and!; [done| |].
  - intros x. rewrite (hwaits_end P' q' t e' a' o' x He' Ha' Ho'), (hwaits_end P q t e a o x He Ha Ho).
    split.
    + intros (Hxt & [ex Hx] & Hxo). split_and!; [done| |].
      * assert (x = s) as -> by (by apply (P_uniq _ _ _ _ _ _ _ _ _ _ x s ex es' (cdual o') Hc' HF' Hx Hes')).
        by eexists.
      * assert (x = s) as -> by (by apply (P_uniq _ _ _ _ _ _ _ _ _ _ x s ex es' (cdual o') Hc' HF' Hx Hes')).
        done.
    + intros (Hxt & [ex Hx] & Hxo).
      assert (x = s) as -> by (by apply (P_uniq _ _ _ _ _ _ _ _ _ _ x s ex es (cdual o) Hc HF Hx Hes)).
      split_and!; [done|by eexists|done].
  - intros x Hw Hx. rewrite (hwaits_end P q t e a o x He Ha Ho) in Hw.
    destruct Hw as (_ & [ex Hex] & Hxo).
    assert (x = s) as -> by (by apply (P_uniq _ _ _ _ _ _ _ _ _ _ x s ex es (cdual o) Hc HF Hex Hes)).
    by apply Had.
Qed.

(** A bound by the cap of the new holder. *)
Lemma fgoal_cap n' W (HW : strict W) T π' q' A' U' P' F' q L t e2 a o s m m' :
  LFconf (S n') W ∅ T π' q' A' U' → lf_fuelc (S n') W π' P' F' A' q' →
  q'.2 !! t = Some e2 → act e2 = Some a → aend1 a = Some o →
  (∀ k, π' !! cdual o = Some k → w_bud W k = Some m') → m' < m → fgoal q q' P' F' L t o s m.
Proof.
  intros Hc' HF' He2 Ha Ho Hb Hlt.
  destruct (s_partner n' W HW T π' q' A' U' Hc' t e2 a o He2 Ha Ho) as (s' & es' & Hst' & Hes' & Hso').
  destruct (HF' s' es' Hes') as (H1 & H2 & H3 & H4).
  exists s'. split_and!; [by eexists|done|by rewrite H2|]. left.
  assert (is_Some (F' s' !! cdual o)) as [f Hf] by (apply elem_of_dom; by rewrite H3).
  destruct (fuel_cap n' W (P' s') (F' s') es' H1 (cdual o) f Hf) as (k & Hk & Hle).
  rewrite H4 in Hk by done. rewrite (Hb k Hk) in Hle. unfold fval. rewrite Hf.
  destruct f as [m''|]; simpl in Hle; [lia|done].
Qed.

(** ** The counter of the partner end along one step *)

Section fuel_exists.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (C : gset chan) (M : gmap nat expr) (A : nat → tenv) (U : nat → ty).
  Context (P : nat → gmap cend point) (F : nat → gmap cend fuel).
  Context (Hc : LFconf (S (S (S n))) W ∅ T π (C, M) A U) (HF : lf_fuelc (S (S (S n))) W π P F A (C, M)).
  Context (t : nat) (e : expr) (a : action) (o : cend) (He : M !! t = Some e) (Ha : act e = Some a)
    (Ho : aend1 a = Some o).
  Context (s : nat) (es : expr) (Hes : M !! s = Some es) (Hst : s ≠ t) (Hso : cdual o ∈ tenv_ends (A s)).
  Context (m : nat) (Hm : F s !! cdual o = Some (Some m)).

  Lemma fe_dom x ex : M !! x = Some ex → dom (P x) = tenv_ends (A x).
  Proof. intros Hx. by destruct (HF x ex Hx) as (_ & ? & _). Qed.

  Lemma fe_domF x ex : M !! x = Some ex → dom (F x) = tenv_ends (A x).
  Proof. intros Hx. by destruct (HF x ex Hx) as (_ & _ & ? & _). Qed.

  Lemma fe_uniq x ex : M !! x = Some ex → cdual o ∈ tenv_ends (A x) → x = s.
  Proof. intros Hx Hxo. by apply (s_uniq (S (S n)) W HW T π (C, M) A U Hc x s ex es (cdual o)). Qed.

  Lemma fe_to : o ∈ tenv_ends (A t).
  Proof. apply (s_held (S (S n)) W HW T π (C, M) A U Hc t e a o He Ha Ho). Qed.

  Lemma fe_Pso : cdual o ∈ dom (P s).
  Proof. by rewrite (fe_dom s es Hes). Qed.

  Lemma fe_tick y σ y' oy :
    M !! s = Some y → tstep y (LSess σ) y' → sl_end σ = Some oy → oy ≠ cdual o → 1 ≤ m.
  Proof.
    intros Hy Hs Hoy Hne. rewrite Hes in Hy. injection Hy as <-. destruct (HF s es Hes) as (H1 & _).
    apply (fuel_tick (S (S n)) W (P s) (F s) es H1 σ y' oy Hs Hoy (cdual o) m); [done|done].
  Qed.

  (** The counter of an end other than the acted one, after the action. *)
  Lemma fe_val_act x σ ox kx :
    sl_end σ = Some ox → mrem (sl_out σ) (P x) !! ox = Some kx → cdual o ∉ sl_out σ → cdual o ≠ ox →
    (∀ y, sl_next σ kx = Some y → y.1 ≠ cdual o) →
    (fupd W (P x) (F x) (LSess σ)).2 !! cdual o = ftick <$> F x !! cdual o.
  Proof.
    intros Hox Hk' Hout Hne Hnx.
    rewrite (fupd_act W σ (P x) (F x) ox kx Hox Hk').
    destruct (sl_next σ kx) as [[o1 k1]|] eqn:Hn; simpl.
    - rewrite lookup_insert_ne by (intros Heq; apply (Hnx (o1, k1)); [done|by rewrite Heq]).
      rewrite lookup_fmap, lookup_delete_ne by done. rewrite lookup_mrem, decide_False by done. done.
    - rewrite lookup_fmap, lookup_delete_ne by done. rewrite lookup_mrem, decide_False by done. done.
  Qed.

  (** The same end stays in the points of the actor. *)
  Lemma fe_dom_act x σ ox kx :
    sl_end σ = Some ox → mrem (sl_out σ) (P x) !! ox = Some kx → cdual o ∉ sl_out σ → cdual o ≠ ox →
    cdual o ∈ dom (P x) → cdual o ∈ dom (fupd W (P x) (F x) (LSess σ)).1.
  Proof.
    intros Hox Hk' Hout Hne Hin.
    rewrite (fupd_act W σ (P x) (F x) ox kx Hox Hk').
    destruct (sl_next σ kx) as [[o1 k1]|] eqn:Hn; simpl;
      rewrite ?dom_insert_L, dom_delete_L, dom_mrem; set_solver.
  Qed.

  Lemma fe_beta i ei ei' :
    M !! i = Some ei → tstep ei LBeta ei' → t ≠ i →
    fgoal (C, M) (C, <[i := ei']> M) (fstep W P F (C, M) {[i]} (C, <[i := ei']> M)).1
      (fstep W P F (C, M) {[i]} (C, <[i := ei']> M)).2 {[i]} t o s m.
  Proof.
    intros Hi Hs Hti. destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoa). apply offers_beta in Hoa as ->.
    assert (fstep W P F (C, M) {[i]} (C, <[i:=ei']> M) = (P, F)) as ->.
    { rewrite fstep_single. simpl. rewrite Hi. unfold fsingle. by rewrite Ha'. }
    exists s. split_and!; [|done|apply fe_Pso|].
    - simpl. apply lookup_insert_is_Some'. right. by eexists.
    - right. unfold fval. simpl. rewrite Hm. split_and!; [done|done|].
      intros ->%elem_of_singleton. rewrite Hes in Hi. injection Hi as <-. by exists es, ABeta.
  Qed.

  Lemma fe_new i ei c x ei' :
    M !! i = Some ei → tstep ei (LNew c x) ei' → c ∉ C → t ≠ i →
    fgoal (C, M) (C ∪ {[c]}, <[i := ei']> M)
      (fstep W P F (C, M) {[i]} (C ∪ {[c]}, <[i := ei']> M)).1
      (fstep W P F (C, M) {[i]} (C ∪ {[c]}, <[i := ei']> M)).2 {[i]} t o s m.
  Proof.
    pose proof fe_tick as Htick. pose proof fe_val_act as Hva. pose proof fe_dom_act as Hda.
    pose proof fe_Pso as HPso0. pose proof fe_dom as Hdom. pose proof fe_domF as HdomF.
    intros Hi Hs HC Hti.
    assert ((cdual o).1 ≠ c) as Hoc.
    { intros Heq. apply HC. rewrite <-Heq. apply (st_closed (S n) W HW T π C M A U Hc P F HF s es Hes).
      apply dom_tenv_ends. exists (cdual o).2. by destruct (cdual o). }
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoa). apply offers_new in Hoa as ->.
    assert (fstep W P F (C, M) {[i]} (C ∪ {[c]}, <[i:=ei']> M) =
      (eupd P i (<[(c, pt_pol x) := x]> (<[(c, negb (pt_pol x)) := pt_dual x]> (P i))),
       eupd F i (<[(c, pt_pol x) := w_bud W x]> (<[(c, negb (pt_pol x)) := w_bud W (pt_dual x)]> (F i)))))
      as ->.
    { rewrite fstep_single. simpl. rewrite Hi. unfold fsingle. rewrite Ha'. simpl.
      assert ((C ∪ {[c]}) ∖ C = {[c]}) as -> by (clear -HC; set_solver). by rewrite elements_singleton. }
    exists s. split_and!; [simpl; apply lookup_insert_is_Some'; right; by eexists|done| |].
    - simpl. unfold eupd. destruct (decide (s = i)) as [->|]; [|exact HPso0].
      rewrite !dom_insert_L. pose proof HPso0. set_solver.
    - right. unfold fval. simpl. unfold eupd. destruct (decide (s = i)) as [->|Hsi].
      + rewrite !lookup_insert_ne by (intros Heq; apply Hoc; rewrite <-Heq; done). rewrite Hm.
        split_and!; [done|done|]. intros _. by exists ei, (ANew x).
      + rewrite Hm. split_and!; [done|done|]. intros ->%elem_of_singleton. done.
  Qed.

  Lemma fe_spawn i j ei w ei' :
    M !! i = Some ei → tstep ei (LSpawn w) ei' → M !! j = None → t ≠ i →
    fgoal (C, M) (C, <[j := App w EUnit]> (<[i := ei']> M))
      (fstep W P F (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := ei']> M))).1
      (fstep W P F (C, M) {[i]} (C, <[j := App w EUnit]> (<[i := ei']> M))).2 {[i]} t o s m.
  Proof.
    pose proof fe_tick as Htick. pose proof fe_val_act as Hva. pose proof fe_dom_act as Hda.
    pose proof fe_Pso as HPso0. pose proof fe_dom as Hdom. pose proof fe_domF as HdomF.
    intros Hi Hs Hj Hti. assert (i ≠ j) as Hij by (intros ->; congruence).
    assert (t ≠ j) as Htj by (intros ->; congruence). assert (s ≠ j) as Hsj by (intros ->; congruence).
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoa). apply offers_spawn in Hoa as ->.
    assert (fstep W P F (C, M) {[i]} (C, <[j:=App w EUnit]> (<[i:=ei']> M)) =
            (eupd (eupd P i (mrem (fends w) (P i))) j (mres (fends w) (P i)),
             eupd (eupd F i (mrem (fends w) (F i))) j (ftick <$> mres (fends w) (F i)))) as ->.
    { rewrite fstep_single. simpl. rewrite Hi. unfold fsingle. rewrite Ha'. simpl.
      assert (dom (<[j:=App w EUnit]> (<[i:=ei']> M)) ∖ dom M = {[j]}) as ->.
      { rewrite !dom_insert_L. apply elem_of_dom_2 in Hi. apply not_elem_of_dom in Hj. clear -Hi Hj. set_solver. }
      by rewrite elements_singleton. }
    pose proof HPso0 as HPso. unfold fgoal. cbn [fst snd].
    destruct (decide (s = i ∧ cdual o ∈ fends w)) as [[-> Hw]|Hn].
    - exists j. split_and!.
      + rewrite lookup_insert_eq. by eexists.
      + done.
      + rewrite eupd_eq, dom_mres. set_solver.
      + left. unfold fval. rewrite eupd_eq, lookup_fmap, lookup_mres, decide_True by done. rewrite Hm. simpl.
        rewrite Hes in Hi. injection Hi as <-. destruct (HF i es Hes) as (H1 & _).
        pose proof (fuel_spawn_hand (S (S n)) W (P i) (F i) es H1 w ei' Hs (cdual o) m Hw Hm). lia.
    - exists s. split_and!.
      + rewrite lookup_insert_ne by done. apply lookup_insert_is_Some'. right. by eexists.
      + done.
      + rewrite eupd_ne by done. unfold eupd. destruct (decide (s = i)) as [->|]; [|done].
        rewrite dom_mrem. assert (cdual o ∉ fends w) by naive_solver. set_solver.
      + right. unfold fval. rewrite eupd_ne by done. unfold eupd. destruct (decide (s = i)) as [->|Hsi].
        * rewrite lookup_mrem, decide_False by naive_solver. rewrite Hm. split_and!; [done|done|].
          intros _. by exists ei, (ASpawn w).
        * rewrite Hm. split_and!; [done|done|]. intros ->%elem_of_singleton. done.
  Qed.

  (** The channel of a synchronization between i and j is not t's. *)
  Lemma fe_chan i j ei ej σi σj ei' ej' c b :
    i ≠ t → j ≠ t → M !! i = Some ei → M !! j = Some ej →
    tstep ei (LSess σi) ei' → sl_end σi = Some (c, b) →
    tstep ej (LSess σj) ej' → sl_end σj = Some (c, negb b) → o.1 ≠ c.
  Proof.
    intros Hit Hjt Hi Hj Hsi Hei Hsj Hej Hoc.
    pose proof (act_held _ _ _ _ _ _ _ Hc i ei _ _ _ Hi Hsi Hei) as H1.
    pose proof (act_held _ _ _ _ _ _ _ Hc j ej _ _ _ Hj Hsj Hej) as H2.
    apply (st_cowner (S n) W HW T π C M A U Hc P F HF i j ei ej c b t e Hi Hj H1 H2
      (not_eq_sym Hit) (not_eq_sym Hjt) He).
    pose proof fe_to as Hto. apply dom_tenv_ends. exists o.2. rewrite <-Hoc. by destruct o.
  Qed.

  Lemma fe_msg i j c b v ei ei' f f' :
    i ≠ j → M !! i = Some ei → M !! j = Some f →
    tstep ei (LSess (SSend (c, b) v)) ei' → tstep f (LSess (SRecv (c, negb b) v)) f' → t ≠ i → t ≠ j →
    fgoal (C, M) (C, <[j := f']> (<[i := ei']> M))
      (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := ei']> M))).1
      (fstep W P F (C, M) {[i; j]} (C, <[j := f']> (<[i := ei']> M))).2 {[i; j]} t o s m.
  Proof.
    pose proof fe_tick as Htick. pose proof fe_val_act as Hva. pose proof fe_dom_act as Hda.
    pose proof fe_Pso as HPso0. pose proof fe_dom as Hdom. pose proof fe_domF as HdomF.
    intros Hij Hi Hj Hse Hsf Hti Htj.
    pose proof (fe_chan i j ei f _ _ ei' f' c b (not_eq_sym Hti) (not_eq_sym Htj) Hi Hj Hse eq_refl Hsf eq_refl)
      as Hoc.
    destruct (act_step _ _ _ Hse) as (a1 & Ha1 & Ho1). apply offers_send in Ho1 as ->.
    destruct (act_step _ _ _ Hsf) as (a2 & Ha2 & Ho2). apply offers_recv in Ho2 as ->.
    assert (fstep W P F (C, M) {[i; j]} (C, <[j:=f']> (<[i:=ei']> M)) = fmsg W P F i j (c, b) (c, negb b) v)
      as ->.
    { destruct (fstep_pair W P F (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
        unfold fpair; by rewrite ?Ha1, ?Ha2. }
    pose proof (act_held _ _ _ _ _ _ _ Hc i ei _ _ _ Hi Hse eq_refl) as Hcb.
    pose proof (act_held _ _ _ _ _ _ _ Hc j f _ _ _ Hj Hsf eq_refl) as Hcnb.
    assert (is_Some (P i !! (c, b))) as [ki Hki] by (apply elem_of_dom; by rewrite (Hdom i ei Hi)).
    assert (is_Some (P j !! (c, negb b))) as [kj Hkj] by (apply elem_of_dom; by rewrite (Hdom j f Hj)).
    assert ((cdual o).1 ≠ c) as Hoc' by done.
    assert (Hne : ∀ b', cdual o ≠ (c, b')) by (intros b' Heq; apply Hoc'; by rewrite Heq).
    assert (Hk1 : mrem (sl_out (SRecv (c, negb b) v)) (P j) !! (c, negb b) = Some kj).
    { simpl. by rewrite lookup_mrem, decide_False by set_solver. }
    assert (Hk2 : mrem (sl_out (SSend (c, b) v)) (P i) !! (c, b) = Some ki).
    { simpl. rewrite lookup_mrem, decide_False; [done|].
      intros Hin.
      assert (fends v ⊆ tenv_ends (A i) ∖ {[(c, b)]}) as Hsub.
      { pose proof (st_sess (S n) W HW T π C M A U Hc P F HF i ei _ ei' Hi Hse)
          as (Θr & Θ1 & Θ2 & m0 & Uu & s0 & k0 & Θ' & Hhd & Hcomp & HV & _).
        destruct (st_rest (S n) W HW T π C M A U Hc P F HF i ei _ _ _ _ Hi Hhd) as (? & _ & _ & _ & _ & Hends & Hbr & _).
        destruct (tenv_ends_comp _ _ _ Hcomp Hbr) as [Hu12 _].
        destruct (LVrel_fit _ _ _ _ _ HV) as [HΘ2 _]. rewrite <-HΘ2, <-Hends, Hu12. set_solver. }
      set_solver. }
    unfold fgoal, fmsg, fval. cbn [fst snd].
    destruct (decide (s = j)) as [->|Hsj].
    - exists j. split_and!; [rewrite lookup_insert_eq; by eexists|done| |].
      + rewrite eupd_eq, dom_union_L. apply elem_of_union_l.
        apply (Hda j (SRecv (c, negb b) v) (c, negb b) kj eq_refl Hk1); [set_solver|apply Hne|exact HPso0].
      + left. rewrite eupd_eq. rewrite lookup_union_l'.
        2:{ rewrite (Hva j (SRecv (c, negb b) v) (c, negb b) kj eq_refl Hk1); [rewrite Hm; by eexists
            |set_solver|apply Hne|]. simpl. intros y [= <-]. simpl. apply not_eq_sym, Hne. }
        rewrite (Hva j (SRecv (c, negb b) v) (c, negb b) kj eq_refl Hk1); [rewrite Hm; simpl
          |set_solver|apply Hne|].
        * pose proof (Htick f _ f' (c, negb b) Hj Hsf eq_refl ltac:(apply not_eq_sym, Hne)). lia.
        * simpl. intros y [= <-]. simpl. apply not_eq_sym, Hne.
    - destruct (decide (s = i)) as [->|Hsi].
      + destruct (decide (cdual o ∈ fends v)) as [Hov|Hov].
        * exists j. split_and!; [rewrite lookup_insert_eq; by eexists|done| |].
          -- rewrite eupd_eq, dom_union_L. apply elem_of_union_r. rewrite dom_mres.
             pose proof HPso0. set_solver.
          -- left. rewrite eupd_eq. rewrite lookup_union_r.
             2:{ rewrite (fupd_act W (SRecv (c, negb b) v) (P j) (F j) (c, negb b) kj eq_refl Hk1).
                 simpl. rewrite lookup_insert_ne by (apply not_eq_sym, Hne).
                 rewrite lookup_fmap, lookup_delete_ne by (apply not_eq_sym, Hne).
                 rewrite lookup_mrem, decide_False by set_solver.
                 assert (cdual o ∉ tenv_ends (A j)) as Hnf.
                 { intros Hin. apply (st_disj (S n) W HW T π C M A U Hc P F HF i j es f Hij Hes Hj (cdual o));
                     done. }
                 rewrite <-(HdomF j f Hj) in Hnf. apply not_elem_of_dom in Hnf. by rewrite Hnf. }
             rewrite lookup_fmap, lookup_mres, decide_True by done. rewrite Hm. simpl.
             pose proof (Htick ei _ ei' (c, b) Hi Hse eq_refl ltac:(apply not_eq_sym, Hne)). lia.
        * exists i. split_and!.
          -- rewrite lookup_insert_ne by done. rewrite lookup_insert_eq. by eexists.
          -- done.
          -- rewrite eupd_ne, eupd_eq by done.
             apply (Hda i (SSend (c, b) v) (c, b) ki eq_refl Hk2); [done|apply Hne|exact HPso0].
          -- left. rewrite eupd_ne, eupd_eq by done.
             rewrite (Hva i (SSend (c, b) v) (c, b) ki eq_refl Hk2); [rewrite Hm; simpl|done|apply Hne|].
             ++ pose proof (Htick ei _ ei' (c, b) Hi Hse eq_refl ltac:(apply not_eq_sym, Hne)). lia.
             ++ simpl. intros y [= <-]. simpl. apply not_eq_sym, Hne.
      + exists s. rewrite !eupd_ne by done. split_and!; [|done|exact HPso0|].
        * rewrite !lookup_insert_ne by done. by eexists.
        * right. rewrite Hm. split_and!; [done|done|]. set_solver.
  Qed.

  (** Close and choice: both participants act on c, which is not t's channel. *)
  Lemma fe_two i j ei ei' f f' σi σj c :
    i ≠ j → M !! i = Some ei → M !! j = Some f → t ≠ i → t ≠ j →
    tstep ei (LSess σi) ei' → tstep f (LSess σj) f' → (cdual o).1 ≠ c →
    (∃ bi, sl_end σi = Some (c, bi)) → (∃ bj, sl_end σj = Some (c, bj)) →
    sl_out σi = ∅ → sl_out σj = ∅ →
    (∀ k y, sl_next σi k = Some y → y.1.1 = c) → (∀ k y, sl_next σj k = Some y → y.1.1 = c) →
    ∀ (q' : config), q'.2 = <[j := f']> (<[i := ei']> M) →
      fgoal (C, M) q' (f2 W P F i j σi σj).1 (f2 W P F i j σi σj).2 {[i; j]} t o s m.
  Proof.
    pose proof fe_tick as Htick. pose proof fe_val_act as Hva. pose proof fe_dom_act as Hda.
    pose proof fe_Pso as HPso0. pose proof fe_dom as Hdom. pose proof fe_domF as HdomF.
    intros Hij Hi Hj Hti Htj Hsi Hsj Hoc [bi Hbi] [bj Hbj] Hout1 Hout2 Hn1 Hn2 q' Hq.
    pose proof (act_held _ _ _ _ _ _ _ Hc i ei _ _ _ Hi Hsi Hbi) as Hci.
    pose proof (act_held _ _ _ _ _ _ _ Hc j f _ _ _ Hj Hsj Hbj) as Hcj.
    assert (is_Some (P i !! (c, bi))) as [ki Hki] by (apply elem_of_dom; by rewrite (Hdom i ei Hi)).
    assert (is_Some (P j !! (c, bj))) as [kj Hkj] by (apply elem_of_dom; by rewrite (Hdom j f Hj)).
    assert (Hne : ∀ b', cdual o ≠ (c, b')) by (intros b' Heq; apply Hoc; by rewrite Heq).
    assert (Hk1 : mrem (sl_out σi) (P i) !! (c, bi) = Some ki) by (by rewrite Hout1, lookup_mrem, decide_False by set_solver).
    assert (Hk2 : mrem (sl_out σj) (P j) !! (c, bj) = Some kj) by (by rewrite Hout2, lookup_mrem, decide_False by set_solver).
    unfold fgoal, f2, fval. cbn [fst snd].
    destruct (decide (s = j)) as [->|Hsj'].
    - exists j. split_and!; [rewrite Hq, lookup_insert_eq; by eexists|done| |].
      + rewrite eupd_eq. apply (Hda j _ (c, bj) kj Hbj Hk2); [rewrite Hout2; set_solver|apply Hne|exact HPso0].
      + left. rewrite eupd_eq.
        rewrite (Hva j σj (c, bj) kj Hbj Hk2); [rewrite Hm; simpl|rewrite Hout2; set_solver|apply Hne|].
        * pose proof (Htick f σj f' (c, bj) Hj Hsj Hbj ltac:(apply not_eq_sym, Hne)). lia.
        * intros y Hy. pose proof (Hn2 _ _ Hy) as Hyc. intros Heq. apply Hoc. by rewrite <-Heq.
    - destruct (decide (s = i)) as [->|Hsi2].
      + exists i. split_and!; [rewrite Hq, lookup_insert_ne, lookup_insert_eq by done; by eexists|done| |].
        * rewrite eupd_ne, eupd_eq by done. apply (Hda i _ (c, bi) ki Hbi Hk1);
            [rewrite Hout1; set_solver|apply Hne|exact HPso0].
        * left. rewrite eupd_ne, eupd_eq by done.
          rewrite (Hva i σi (c, bi) ki Hbi Hk1); [rewrite Hm; simpl|rewrite Hout1; set_solver|apply Hne|].
          -- pose proof (Htick ei σi ei' (c, bi) Hi Hsi Hbi ltac:(apply not_eq_sym, Hne)). lia.
          -- intros y Hy. pose proof (Hn1 _ _ Hy) as Hyc. intros Heq. apply Hoc. by rewrite <-Heq.
      + exists s. rewrite !eupd_ne by done. split_and!; [|done|exact HPso0|].
        * rewrite Hq, !lookup_insert_ne by done. by eexists.
        * right. rewrite Hm. split_and!; [done|done|]. set_solver.
  Qed.

  Lemma kren_keep {Y : Type} (c d : chan) (mm : gmap cend Y) (o0 : cend) (v : Y) :
    o0.1 ≠ c → o0.1 ≠ d → mm !! o0 = Some v → kren (JunkRenaming.csub c d) mm !! o0 = Some v.
  Proof.
    intros Hc0 Hd0 Hmm.
    replace o0 with (JunkRenaming.csub c d o0.1, o0.2) at 1 by (unfold JunkRenaming.csub; rewrite decide_False by done; by destruct o0).
    apply kren_lookup_safe; [|done]. intros [c3 b3] v3 _ Heq. destruct o0 as [c0 b0].
    unfold JunkRenaming.csub in Heq. simpl in *. rewrite (decide_False _ _ Hc0) in Heq.
    destruct (decide (c3 = c)) as [->|Hc3]; injection Heq as Hq1 Hq2; subst; done.
  Qed.

  Lemma fe_link i ei c bc d bd ei' A' U' :
    M !! i = Some ei → tstep ei (LSess (SLink {[(c, bc); (d, bd)]})) ei' → c ∈ C → t ≠ i →
    LFconf (S n) W ∅ T (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M))
      (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M) A' U' →
    lf_fuelc (S n) W (pupd π (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M))
      (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)).1
      (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)).2 A'
      (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M) →
    ∃ o', rend (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M) t = Some o' ∧
      fgoal (C, M) (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)).1
        (fstep W P F (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)).2 {[i]} t o' s m.
  Proof.
    intros Hi Hs HC Hti Hc' HF'.
    set (q' := (C ∖ {[c]}, chsubst c d <$> <[i := ei']> M)). fold q' in Hc', HF' |- *.
    destruct (st_link_data (S n) W HW T π C M A U Hc P F HF i ei c bc d bd ei' Hi Hs)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & Hsx & Hn1 & Hn2 & Hr & Hends & Hb1 & HE).
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd. simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    pose proof (tenv_end_ends _ _ _ Hxc) as Hci. pose proof (tenv_end_ends _ _ _ Hxd) as Hdi.
    pose proof fe_to as Hto.
    pose proof (st_disj (S n) W HW T π C M A U Hc P F HF t i e ei Hti He Hi) as Hdti.
    destruct (HF i ei Hi) as (H1i & H2i & H3i & H4i).
    assert (q'.2 !! t = Some (emap (Instr.csub c d) e)) as He'.
    { unfold q'. simpl. rewrite lookup_fmap, lookup_insert_ne, He by done. simpl. by rewrite chsubst_emap. }
    assert (act (emap (Instr.csub c d) e) = Some (amap (Instr.csub c d) a)) as Ha' by (by rewrite act_emap, Ha).
    set (o' := (Instr.csub c d o.1, o.2)).
    assert (aend1 (amap (Instr.csub c d) a) = Some o') as Ho' by (destruct a; simpl in *; by simplify_eq).
    assert (rend q' t = Some o') as Hro by (unfold rend; by rewrite He', Ha').
    exists o'. split; [done|].
    destruct (act_step _ _ _ Hs) as (al & Hal & Hoal). apply offers_link in Hoal as (o1 & o2 & -> & Hcd).
    assert (P i !! (c, bc) = Some xc.2) as Pc
      by (rewrite H4i by done; apply (lf_pt _ _ _ _ _ _ _ _ Hc i ei _ _ Hi Hxc)).
    assert (P i !! (d, bd) = Some xd.2) as Pd
      by (rewrite H4i by done; apply (lf_pt _ _ _ _ _ _ _ _ Hc i ei _ _ Hi Hxd)).
    pose proof (fuel_link (S (S n)) W (P i) (F i) ei H1i _ ei' Hs) as Hfl.
    assert (C ∖ (C ∖ {[c]}) = {[c]}) as HCc.
    { apply set_eq. intros y. destruct (decide (y = c)) as [->|Hy]; [clear -HC|clear -HC Hy]; set_solver. }
    assert (pupd π (C, M) {[i]} q' = delete (c, true) (delete (c, false) π)) as Hpu.
    { unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1. rewrite Hal. simpl.
      by rewrite HCc, elements_singleton. }
    rewrite Hpu in Hc', HF'.
    destruct (decide (cdual o = (c, bc))) as [Ho1|Ho1].
    { (* t holds the peer of the removed end *)
      assert (i = s) as Eis by (apply (fe_uniq i ei Hi); by rewrite Ho1). subst i.
      assert (o = (c, negb bc)) as Eo by (rewrite <-(cdual_cdual o), Ho1; done).
      assert (c ≠ d) as Hcd'.
      { intros <-. apply (Hdti o); [done|]. rewrite Eo, <-Hbd. done. }
      destruct (Hfl (c, bc) (d, bd) eq_refl Hne m) as (k2 & m' & Hk2 & Hb2 & Hlt); [by rewrite <-Ho1|].
      rewrite Pd in Hk2. injection Hk2 as <-.
      apply (fgoal_cap n W HW T _ q' A' U' _ _ (C, M) {[s]} t _ _ o' s m m' Hc' HF' He' Ha' Ho'); [|done].
      intros k Hk. unfold o' in Hk. rewrite Eo in Hk. unfold Instr.csub in Hk. simpl in Hk.
      rewrite decide_True in Hk by done. unfold cdual in Hk. simpl in Hk.
      rewrite !lookup_delete_ne in Hk by (intros [=]; congruence).
      destruct (lfc_partner _ _ _ _ _ _ _ Hc s ei _ _ Hi Hxd) as (u & gu & yu & Hgu & Hyu & Hyu2 & _).
      rewrite <-Hbd in Hk. change (d, negb bd) with (cdual (d, bd)) in Hk.
      rewrite (lf_pt _ _ _ _ _ _ _ _ Hc u gu _ _ Hgu Hyu) in Hk. injection Hk as <-. by rewrite Hyu2. }
    destruct (decide (cdual o = (d, bd))) as [Ho2|Ho2].
    { (* t holds the peer of the linker's end of d *)
      assert (i = s) as Eis by (apply (fe_uniq i ei Hi); by rewrite Ho2). subst i.
      assert (o = (d, negb bd)) as Eo by (rewrite <-(cdual_cdual o), Ho2; done).
      assert (c ≠ d) as Hcd'.
      { intros <-. apply (Hdti o); [done|]. rewrite Eo, Hbd, negb_involutive. done. }
      destruct (Hfl (d, bd) (c, bc) ltac:(by rewrite upair_comm) (not_eq_sym Hne) m) as (k2 & m' & Hk2 & Hb2 & Hlt);
        [by rewrite <-Ho2|].
      rewrite Pc in Hk2. injection Hk2 as <-.
      apply (fgoal_cap n W HW T _ q' A' U' _ _ (C, M) {[s]} t _ _ o' s m m' Hc' HF' He' Ha' Ho'); [|done].
      intros k Hk. unfold o' in Hk. rewrite Eo in Hk. unfold Instr.csub in Hk. simpl in Hk.
      rewrite decide_False in Hk by congruence. unfold cdual in Hk. simpl in Hk. rewrite negb_involutive in Hk.
      rewrite !lookup_delete_ne in Hk by (intros [=]; congruence).
      rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s ei _ _ Hi Hxd) in Hk. injection Hk as <-.
      rewrite Hdx, pt_dual_dual in Hb2. done. }
    (* otherwise the partner end is on neither channel *)
    assert ((cdual o).1 ≠ c ∧ (cdual o).1 ≠ d) as [Hoc Hod].
    { split; intros Heq; destruct (cdual o) as [c0 b0] eqn:Eo; simpl in Heq; subst c0.
      - destruct (decide (b0 = bc)) as [->|Hb]; [done|].
        apply (Hdti o); [done|]. rewrite <-(cdual_cdual o), Eo. unfold cdual. simpl.
        assert (negb b0 = bc) as -> by (by destruct b0, bc). done.
      - destruct (decide (b0 = bd)) as [->|Hb]; [done|].
        apply (Hdti o); [done|]. rewrite <-(cdual_cdual o), Eo. unfold cdual. simpl.
        assert (negb b0 = bd) as -> by (by destruct b0, bd). done. }
    assert (o' = o) as Eo'.
    { unfold o', Instr.csub. rewrite decide_False by (rewrite <-(cdual_fst o); done). by destruct o. }
    rewrite Eo'.
    assert ((if decide (o1.1 = c) then o2.1 else o1.1) = d) as Hd'.
    { destruct (upair_eq_inv _ _ _ _ Hcd Hne) as [[<- <-]|[<- <-]]; simpl.
      - by rewrite decide_True.
      - destruct (decide (d = c)) as [->|]; done. }
    assert (fstep W P F (C, M) {[i]} q' =
            (λ x, kren (JunkRenaming.csub c d) (eupd P i (mrem {[(c, bc); (d, bd)]} (P i)) x),
             λ x, kren (JunkRenaming.csub c d) (eupd F i (mrem {[(c, bc); (d, bd)]} (F i)) x))) as ->.
    { unfold q'. rewrite fstep_single. simpl. rewrite Hi. unfold fsingle. rewrite Hal. simpl.
      rewrite HCc, elements_singleton. simpl. rewrite Hd'. by rewrite <-Hcd. }
    unfold fgoal. cbn [fst snd]. pose proof fe_Pso as HPso.
    assert (Hnot : cdual o ∉ ({[(c, bc); (d, bd)]} : gset cend)) by set_solver.
    assert (is_Some (P s !! cdual o)) as [ks Hks] by (by apply elem_of_dom).
    assert (eupd P i (mrem {[(c, bc); (d, bd)]} (P i)) s !! cdual o = Some ks) as HPs.
    { unfold eupd. destruct (decide (s = i)) as [->|]; [|done]. by rewrite lookup_mrem, decide_False. }
    assert (eupd F i (mrem {[(c, bc); (d, bd)]} (F i)) s !! cdual o = Some (Some m)) as HFs.
    { unfold eupd. destruct (decide (s = i)) as [->|]; [|done]. by rewrite lookup_mrem, decide_False. }
    exists s. split_and!.
    - unfold q'. simpl. rewrite lookup_fmap. destruct (decide (s = i)) as [->|Hsi];
        [rewrite lookup_insert_eq|rewrite lookup_insert_ne, Hes by done]; by eexists.
    - done.
    - apply elem_of_dom. eexists. by apply kren_keep.
    - right. unfold fval. rewrite (kren_keep c d _ _ _ Hoc Hod HFs). split_and!; [done|done|].
      intros ->%elem_of_singleton. rewrite Hes in Hi. injection Hi as <-. by exists es, (ALink o1 o2).
  Qed.
End fuel_exists.

(** ** The counter of the partner end along one step *)

Lemma fuel_step n W T π P F q A U L q' A' U' t :
  strict W → LFconf (S (S (S n))) W ∅ T π q A U → lf_fuelc (S (S (S n))) W π P F A q →
  istep q L q' →
  LFconf (S n) W ∅ T (pupd π q L q') q' A' U' →
  lf_fuelc (S n) W (pupd π q L q') (fstep W P F q L q').1 (fstep W P F q L q').2 A' q' →
  t ∉ L → npend q t →
  fu_at q' (fstep W P F q L q').1 (fstep W P F q L q').2 t < fu_at q P F t ∨
  (fu_at q' (fstep W P F q L q').1 (fstep W P F q L q').2 t = fu_at q P F t ∧
   (∀ x, hwaits (fstep W P F q L q').1 q' t x ↔ hwaits P q t x) ∧
   ∀ x, hwaits P q t x → x ∈ L → admin_at q x).
Proof.
  intros HW Hc HF Hst Hc' HF' Ht Hp.
  destruct (npend_end q t Hp) as (e & a & o & He & Ha & Ho & _).
  destruct (s_partner (S (S n)) W HW T π q A U Hc t e a o He Ha Ho) as (s & es & Hst' & Hes & Hso).
  destruct (holder_fin (S n) W HW T π q A U P F Hc HF t e a o s es He Ha Ho Hes Hst' Hso) as (m & Hm & Hfu).
  assert (cdual o ∈ dom (P s)) as HPso by (by destruct (HF s es Hes) as (_ & -> & _)).
  (* the end of t after the step, and the fuel goal *)
  assert (∃ e2 a2 o2, q'.2 !! t = Some e2 ∧ act e2 = Some a2 ∧ aend1 a2 = Some o2 ∧
            fgoal q q' (fstep W P F q L q').1 (fstep W P F q L q').2 L t o2 s m) as (e2 & a2 & o2 & He2 & Ha2 & Ho2 & Hg).
  { clear Hfu. destruct q as [C M]. simpl in He, Hes.
    inversion Hst as [C0 M0 i ei ei' Hi Hs|C0 M0 i ei c x ei' Hi Hs HC Hcs|C0 M0 i j ei v ei' Hi Hs Hj
      |C0 M0 i j c b v ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i j c b ei ei' f f' Hij Hi Hj He0 Hf HC
      |C0 M0 i j c β b ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i ei c bc d bd ei' Hi Hs HC]; subst;
      simpl in Ht.
    - exists e, a, o. split_and!; [simpl; rewrite lookup_insert_ne; [done|set_solver]|done|done|].
      apply (fe_beta n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i ei ei' Hi Hs).
      set_solver.
    - exists e, a, o. split_and!; [simpl; rewrite lookup_insert_ne; [done|set_solver]|done|done|].
      apply (fe_new n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i ei c x ei' Hi Hs HC).
      set_solver.
    - assert (t ≠ j) by (intros ->; congruence).
      exists e, a, o. split_and!; [simpl; rewrite !lookup_insert_ne; [done|set_solver|done]|done|done|].
      apply (fe_spawn n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i j ei v ei' Hi Hs Hj).
      set_solver.
    - exists e, a, o. split_and!; [simpl; rewrite !lookup_insert_ne; [done|set_solver|set_solver]|done|done|].
      apply (fe_msg n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i j c b v ei ei' f f');
        try done; set_solver.
    - exists e, a, o. split_and!; [simpl; rewrite !lookup_insert_ne; [done|set_solver|set_solver]|done|done|].
      destruct (act_step _ _ _ He0) as (a1 & Ha1 & Ho1). apply offers_clos in Ho1 as ->.
      destruct (act_step _ _ _ Hf) as (a3 & Ha3 & Ho3). apply offers_clos in Ho3 as ->.
      assert (fstep W P F (C, M) {[i; j]} (C ∖ {[c]}, <[j:=f']> (<[i:=ei']> M)) =
              f2 W P F i j (SClos (c, b)) (SClos (c, negb b)) ∨
              fstep W P F (C, M) {[i; j]} (C ∖ {[c]}, <[j:=f']> (<[i:=ei']> M)) =
              f2 W P F j i (SClos (c, negb b)) (SClos (c, b))) as Hfs.
      { destruct (fstep_pair W P F (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
          unfold fpair; rewrite ?Ha1, ?Ha3; [by left|by right]. }
      pose proof (fe_chan n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm
        i j ei f _ _ ei' f' c b ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc.
      assert ((cdual o).1 ≠ c) as Hoc' by done.
      destruct Hfs as [-> | ->].
      + eapply (fe_two n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i j ei ei' f f');
          try done; try set_solver; try (by eexists).
        all: intros ? ? [=]; done.
      + rewrite (union_comm_L {[i]} {[j]}).
        eapply (fe_two n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm j i f f' ei ei');
          try done; try set_solver; try (by eexists).
        all: try (intros ? ? [=]; done).
        all: simpl; rewrite insert_insert_ne by done; done.
    - exists e, a, o. split_and!; [simpl; rewrite !lookup_insert_ne; [done|set_solver|set_solver]|done|done|].
      destruct (act_step _ _ _ He0) as (a1 & Ha1 & Ho1). apply offers_sel in Ho1 as ->.
      destruct (act_step _ _ _ Hf) as (a3 & Ha3 & Ho3). apply offers_bra in Ho3 as ->.
      assert (fstep W P F (C, M) {[i; j]} (C, <[j:=f']> (<[i:=ei']> M)) =
              f2 W P F i j (SSel (c, β) b) (SBra (c, negb β) b)) as ->.
      { destruct (fstep_pair W P F (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
          unfold fpair; by rewrite ?Ha1, ?Ha3. }
      pose proof (fe_chan n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm
        i j ei f _ _ ei' f' c β ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc.
      assert ((cdual o).1 ≠ c) as Hoc' by done.
      eapply (fe_two n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm i j ei ei' f f');
        try done; try set_solver; try (by eexists).
      all: intros k y [= <-]; done.
    - destruct (fe_link n W HW T π C M A U P F Hc HF t e a o He Ha Ho s es Hes Hst' Hso m Hm
        i ei c bc d bd ei' A' U' Hi Hs HC ltac:(set_solver) Hc' HF') as (o' & Hro & Hg).
      destruct (rend_some _ _ _ Hro) as (e2 & a2 & He2 & Ha2 & Ho2).
      exists e2, a2, o'. split_and!; done. }
  by apply (fuel_reduce _ W T π q A U P F _ _ q' A' U' _ _ L t e a o e2 a2 o2 s es m Hc HF Hc' HF').
Qed.

(** ** Adequacy *)

Theorem lf_adequacy W T p :
  world_wf W → well_founded (w_lt W) → LFP W ∅ T p → lock_free p.
Proof.
  intros Hwf Hwfo HP. pose proof (strict_of W Hwf Hwfo) as HW.
  pose proof (live_no_tau_divergence W T p (proj1 HP)) as Hnd.
  pose proof (lf_links_restricted W T p HW HP) as Hlr.
  intros r l Hr0 Hmax Hfair.
  destruct (LFP_soup W ∅ T p (r 0) HP Hr0) as (π & P & F & Hs0).
  pose proof (lfsoup_run W T π P F r l HW Hmax Hs0) as Hrun.
  set (Pk := λ k, (frun W P F r l k).1). set (Fk := λ k, (frun W P F r l k).2).
  apply (lf_run_criterion p r l Hr0 Hmax Hfair (λ k, hwaits (Pk k) (r k))) with
    (fu := λ k t, fu_at (r k) (Pk k) (Fk k) t) (E := point) (R := w_lt W)
    (we := λ k t, match rend (r k) t with Some o => pt_of (prun π r l k) o | None => pvar 0 end).
  - intros k t s (_ & e & a & S & o & He & Ha & HS & _). exists e, a. split_and!; [done|done|].
    unfold is_sess. apply aends_asubjs. by rewrite HS.
  - intros k t s (_ & _ & _ & _ & _ & _ & _ & _ & _ & [es Hes] & _). by exists es.
  - intros k t Hp. destruct (Hrun k 1) as (A & U & Hc & HF).
    apply (lfc_local_progress 0 W HW T _ _ A U Hc); [|done].
    intros t' e' He'. by destruct (HF t' e' He') as (_ & ? & _).
  - exact Hnd.
  - exact Hlr.
  - intros k t s s' Hp Hw Hw'. destruct (Hrun k 0) as (A & U & Hc & HF).
    destruct (npend_end _ _ Hp) as (e & a & o & He & Ha & Ho & _).
    apply (hwaits_end _ _ _ _ _ _ _ He Ha Ho) in Hw as (_ & [es Hes] & Hso).
    apply (hwaits_end _ _ _ _ _ _ _ He Ha Ho) in Hw' as (_ & [es' Hes'] & Hso').
    by apply (P_uniq _ _ _ _ _ _ _ _ _ _ s s' es es' (cdual o) Hc HF).
  - intros k t Hp Hen Ht. destruct (Hmax k) as [Hst|(_ & Heq & _)]; [|by rewrite Heq].
    destruct (Hrun k 1) as (A & U & Hc & _).
    by apply (pers_step 0 W T (prun π r l k) (r k) A U (l k) (r (S k))).
  - intros k t Hp Ht. destruct (Hmax k) as [Hst|(_ & Heq & Hl)].
    + destruct (Hrun k 3) as (A & U & Hc & HF). destruct (Hrun (S k) 1) as (A' & U' & Hc' & HF').
      exact (fuel_step 0 W T _ _ _ (r k) A U (l k) (r (S k)) A' U' t HW Hc HF Hst Hc' HF' Ht Hp).
    + right. unfold Pk, Fk.
      change (frun W P F r l (S k)) with
        (fstep W (frun W P F r l k).1 (frun W P F r l k).2 (r k) (l k) (r (S k))).
      rewrite Heq, Hl, fstep_stuck. split_and!; [done|done|set_solver].
  - exact Hwfo.
  - intros k t Hp Ht. destruct (npend_end _ _ Hp) as (e & a & o & He & Ha & Ho & Hr).
    cbv beta. rewrite Hr. destruct (Hmax k) as [Hst|(_ & Heq & Hl)].
    + destruct (Hrun k 2) as (A & U & Hc & HF).
      destruct (stab_step 0 W T _ _ _ (r k) A U (l k) (r (S k)) t o HW Hc HF Hst Ht Hr) as (o' & Hr' & Hπ').
      rewrite Hr'. unfold pt_of.
      change (prun π r l (S k)) with (pupd (prun π r l k) (r k) (l k) (r (S k))). by rewrite Hπ'.
    + change (prun π r l (S k)) with (pupd (prun π r l k) (r k) (l k) (r (S k))).
      rewrite Heq, Hl, pupd_stuck. by rewrite Hr.
  - intros k t s Hp Hw Hps. destruct (Hrun k 1) as (A & U & Hc & HF).
    destruct (npend_end _ _ Hp) as (e & a & o & He & Ha & Ho & Hr).
    destruct (npend_end _ _ Hps) as (es & a' & o' & Hes & Ha' & Ho' & Hr').
    apply (hwaits_end _ _ _ _ _ _ _ He Ha Ho) in Hw as (Hst & _ & Hso).
    destruct (HF s es Hes) as (_ & HPs & _).
    assert (cdual o ∈ tenv_ends (A s)) as Hso' by (rewrite <-HPs; exact Hso).
    cbv beta. rewrite Hr, Hr'. by apply (s_rank 0 W HW T _ _ A U Hc t e a o s es a' o').
Qed.

Corollary lf_adequacy_ex T p :
  (∃ W, world_wf W ∧ well_founded (w_lt W) ∧ LFP W ∅ T p) → lock_free p.
Proof. intros (W & Hwf & Hwfo & HP). by apply (lf_adequacy W T p). Qed.

Corollary lf_thread_progress W T p :
  world_wf W → well_founded (w_lt W) → LFP W ∅ T p →
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → thread_progress_run r l.
Proof.
  intros Hwf Hwfo HP. apply thread_progress.
  - by apply (lf_adequacy W T p).
  - apply (live_no_tau_divergence W T p (proj1 HP)).
  - apply (lf_links_restricted W T p (strict_of W Hwf Hwfo) HP).
Qed.
