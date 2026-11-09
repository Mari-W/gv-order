(** * Adequacy of the lock-free judgment (lock-freedom plan §16.5, §17.3)

    [lf_adequacy]: in a well-founded world, a process in [LFP] is lock
    free. The proof instantiates [lf_criterion] along a run, with the
    soup at every position at the points π_k ([prun]) and the counters
    of every thread ([frun]).

    - Local progress is a fact of one soup ([lfc_local_progress]).
    - [we k t] is the point π_k of the end t offers, ordered by [w_lt W].
      A thread that does not step keeps it, a link renames the end and
      keeps the point. The holder of the partner end, when blocked,
      offers an end below it (the gate of the holder).
    - [fu k t] is the counter of the partner end in its holder's map. A
      channel step of the holder on another end ticks it, handing the
      end on passes the counter minus one, and a link hands the
      obligation to a peer whose budget lies below it.
    - [no_tau_divergence] comes from [live_adequacy]. *)

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

  Lemma s_held t e a o : q.2 !! t = Some e → act e = Some a → aend1 a = Some o → o ∈ fends e.
  Proof. intros He Ha Ho. apply (act_aends_fends e a _ Ha (aend1_aends a o Ho)). set_solver. Qed.

  Lemma s_partner t e a o :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    ∃ s es, s ≠ t ∧ q.2 !! s = Some es ∧ cdual o ∈ fends es.
  Proof.
    intros He Ha Ho.
    destruct (proj1 (lfc_held _ _ _ _ _ _ _ Hc t e o He) (s_held t e a o He Ha Ho)) as [x Hx].
    destruct (lfc_partner _ _ _ _ _ _ _ Hc t e o x He Hx) as (s & es & y & Hes & Hy & Hy2 & _).
    exists s, es. split_and!; [|done|apply (lfc_held _ _ _ _ _ _ _ Hc s es _ Hes); by eexists].
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

  Lemma s_uniq s s' es es' o : q.2 !! s = Some es → q.2 !! s' = Some es' → o ∈ fends es → o ∈ fends es' → s = s'.
  Proof.
    intros Hs Hs' Ho Ho'. destruct (decide (s = s')) as [|Hne]; [done|].
    exfalso. by apply (lf_disj _ _ _ _ _ _ _ _ Hc s s' es es' Hne Hs Hs' o).
  Qed.

  Lemma s_waits t e a o s :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    waits q t s ↔ s ≠ t ∧ ∃ es, q.2 !! s = Some es ∧ cdual o ∈ fends es.
  Proof.
    intros He Ha Ho. split.
    - intros (Hst & e' & a' & S & o' & es & He' & Ha' & HS & Ho' & Hes & Hm).
      rewrite He in He'. injection He' as <-. rewrite Ha in Ha'. injection Ha' as <-.
      rewrite (aend1_aends a o Ho) in HS. injection HS as <-. apply elem_of_singleton in Ho' as ->.
      split; [done|]. by exists es.
    - intros (Hst & es & Hes & Hm). split; [done|]. exists e, a, {[o]}, o, es.
      split_and!; try done; [by apply aend1_aends|set_solver].
  Qed.

  Lemma s_rank t e a o s es a' o' :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    q.2 !! s = Some es → act es = Some a' → aend1 a' = Some o' →
    s ≠ t → cdual o ∈ fends es →
    enabled q t ∨ w_lt W (pt_of π o') (pt_of π o).
  Proof.
    intros He Ha Ho Hes Ha' Ho' Hst Hdo.
    destruct (s_offered t e a o He Ha Ho) as (k & ek & Hok & Hk & Hko & _).
    destruct (s_offered s es a' o' Hes Ha' Ho') as (k0 & ek0 & Hok0 & Hk0 & Hko0 & Hbr).
    assert (tenv_end (A t) o = Some ek) as Hek.
    { rewrite <-Hko. apply tenv_end_entry; [apply (lfc_bipol _ _ _ _ _ _ _ Hc t e He)|done]. }
    destruct (proj1 (lfc_held _ _ _ _ _ _ _ Hc s es (cdual o) Hes) Hdo) as [y Hy].
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

Lemma nonpart_terms q L q' :
  istep q L q' → ∃ g, (∀ u eu, u ∉ L → q.2 !! u = Some eu → q'.2 !! u = Some (emap g eu)) ∧
    (∀ c, (∀ u eu, u ∈ L → q.2 !! u = Some eu → c ∉ fchans eu) → g c = c).
Proof.
  intros Hst. destruct Hst as [C M i e e' Hi Hs|C M i e c0 x e' Hi Hs HC Hc|C M i j e v e' Hi Hs Hj
    |C M i j c0 b v e e' f f' Hij Hi Hj He Hf|C M i j c0 b e e' f f' Hij Hi Hj He Hf HC
    |C M i j c0 β b0 e e' f f' Hij Hi Hj He Hf|C M i e c0 bc d bd e' Hi Hs HC]; simpl.
  1-6: exists id; (split; [|done]); intros u eu Hu Heu; rewrite emap_id.
  - rewrite lookup_insert_ne; [done|set_solver].
  - rewrite lookup_insert_ne; [done|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|]. intros ->. by rewrite Hj in Heu.
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - exists (Instr.csub c0 d). split.
    + intros u eu Hu Heu. rewrite lookup_fmap, lookup_insert_ne by set_solver. rewrite Heu. simpl.
      by rewrite chsubst_emap.
    + intros c Hc. specialize (Hc i e ltac:(set_solver) Hi).
      destruct (act_step _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      pose proof (act_aends_fends e (ALink c1 d0) _ Hb eq_refl) as Hsub. rewrite <-Ho in Hsub.
      unfold Instr.csub. case_decide; [|done]. subst. exfalso. apply Hc.
      apply fchans_of_fends with (o := (c0, bc)). set_solver.
Qed.

Lemma rend_emap q q' t e g :
  q.2 !! t = Some e → q'.2 !! t = Some (emap g e) →
  rend q' t = (λ o : cend, (g o.1, o.2)) <$> rend q t.
Proof.
  intros He He'. unfold rend. rewrite He, He', act_emap.
  destruct (act e) as [a|]; [|done]. simpl. by destruct a.
Qed.

Lemma tstep_end_fends e σ e' o : tstep e (LSess σ) e' → sl_end σ = Some o → o ∈ fends e.
Proof.
  intros Hst Ho. destruct (act_step _ _ _ Hst) as (a & Ha & Hoa).
  assert (aend1 a = Some o) as Ha1.
  { destruct a, σ; simpl in *; try done; destruct_and?; simplify_eq; done. }
  apply (act_aends_fends e a _ Ha (aend1_aends a o Ha1)). set_solver.
Qed.

Lemma rend_some q t o :
  rend q t = Some o → ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ aend1 a = Some o.
Proof.
  unfold rend. destruct (q.2 !! t) as [e|] eqn:He; [|done]. destruct (act e) as [a|] eqn:Ha; [|done].
  intros H. by exists e, a.
Qed.

(** ** A thread that does not step keeps the point of its end *)
Lemma stab_step n W T π q A U L q' t o :
  strict W → LFconf (S (S n)) W ∅ T π q A U → istep q L q' → t ∉ L → rend q t = Some o →
  ∃ o', rend q' t = Some o' ∧ pupd π q L q' !! o' = π !! o.
Proof.
  intros HW Hc Hst Ht Ho. destruct q as [C M].
  destruct (rend_some _ _ _ Ho) as (e & a & He & Ha & Ha1). simpl in He.
  pose proof (act_aends_fends e a _ Ha (aend1_aends a o Ha1) o ltac:(set_solver)) as Hoe.
  (* the channel of a synchronization between i and j is not t's *)
  assert (Hsync : ∀ i j ei ej σi σj ei' ej' c b,
            i ≠ t → j ≠ t → M !! i = Some ei → M !! j = Some ej →
            tstep ei (LSess σi) ei' → sl_end σi = Some (c, b) →
            tstep ej (LSess σj) ej' → sl_end σj = Some (c, negb b) → o.1 ≠ c).
  { intros i j ei ej σi σj ei' ej' c b Hit Hjt Hi Hj Hsi Hei Hsj Hej Hoc.
    pose proof (tstep_end_fends _ _ _ _ Hsi Hei) as H1. pose proof (tstep_end_fends _ _ _ _ Hsj Hej) as H2.
    apply (st_cowner n W HW T π C M A U Hc i j ei ej c b t e Hi Hj H1 H2 (not_eq_sym Hit) (not_eq_sym Hjt) He).
    rewrite <-Hoc. by apply fchans_of_fends. }
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
    assert (o.1 ≠ c) as Hoc.
    { intros Heq. apply (st_fresh_mention n W HW T π C M A U Hc c t e Hcs He). rewrite <-Heq.
      by apply fchans_of_fends. }
    rewrite !lookup_insert_ne; [done| |]; intros Heq; subst o; simpl in Hoc; congruence.
  - exists o. unfold rend. simpl. assert (t ≠ j) by (intros ->; congruence).
    rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    unfold pupd. rewrite pev_of_single. simpl. rewrite Hi. unfold pev1.
    destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho'). rewrite Ha'. by apply offers_spawn in Ho' as ->.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c b ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_send in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_recv in Ho2 as ->.
    destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
      unfold pev2; rewrite ?Ha1', ?Ha2; simpl; rewrite !lookup_alter_ne; try done; intros Heq; subst o; simpl in Hoc; congruence.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c b ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_clos in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_clos in Ho2 as ->.
    destruct (pev_of_pair (C, M) (C ∖ {[c]}, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
      unfold pev2; rewrite ?Ha1', ?Ha2; simpl; rewrite !lookup_delete_ne; try done; intros Heq; subst o; simpl in Hoc; congruence.
  - exists o. unfold rend. simpl. rewrite !lookup_insert_ne by set_solver. rewrite He, Ha. split; [done|].
    pose proof (Hsync i j _ _ _ _ _ _ c β ltac:(set_solver) ltac:(set_solver) Hi Hj He0 eq_refl Hf eq_refl) as Hoc.
    unfold pupd. destruct (act_step _ _ _ He0) as (a1 & Ha1' & Ho1). apply offers_sel in Ho1 as ->.
    destruct (act_step _ _ _ Hf) as (a2 & Ha2 & Ho2). apply offers_bra in Ho2 as ->.
    assert (pev_of (C, M) {[i; j]} (C, <[j:=f']> (<[i:=ei']> M)) = PChoice (c, β) b) as ->.
    { destruct (pev_of_pair (C, M) (C, <[j:=f']> (<[i:=ei']> M)) i j ei f Hij Hi Hj) as [-> | ->];
        unfold pev2; by rewrite ?Ha1', ?Ha2. }
    simpl. destruct (π !! (c, β)); [|done]. rewrite !lookup_insert_ne; try done; intros Heq; subst o; simpl in Hoc; congruence.
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
    destruct (st_link_data n W HW T π C M A U Hc i ei c bc d bd ei' Hi Hs)
      as (Θ1 & xc & xd & Hne & Hxc & Hxd & Hdx & _ & _ & _ & _ & _ & _).
    pose proof (tenv_end_pol _ _ _ Hxc) as Hpc. pose proof (tenv_end_pol _ _ _ Hxd) as Hpd. simpl in Hpc, Hpd.
    assert (bd = negb bc) as Hbd by (rewrite <-Hpc, <-Hpd, Hdx, pt_pol_dual; by destruct (pt_pol xd.2)).
    pose proof (st_held n W HW T π C M A U Hc i ei _ _ Hi Hxc) as Hci.
    pose proof (st_held n W HW T π C M A U Hc i ei _ _ Hi Hxd) as Hdi.
    pose proof (st_disj n W HW T π C M A U Hc t i e ei Hti He Hi) as Hd0.
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
