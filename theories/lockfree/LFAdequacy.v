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
  ∃ p f, synced q t p o ∧ q.2 !! p = Some f ∧ cdual o ∈ fends f.
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
    exists j, f. split_and!; [|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
    exists e, f. split_and!; [done|done|done|]. left. by eexists _, _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_recv in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [| done |].
    + exists e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; left.
      eexists _, _, _. unfold cdual. simpl. rewrite negb_involutive. split; [exact He0|exact Hf].
    + unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
  - pose proof (Hlbl _ _ He0) as Hoa. apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, f. split_and!; [|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
    exists e, f. split_and!; [done|done|done|]. right; right; left. by eexists _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [| done |].
    + exists e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; right; left.
      eexists _, _. unfold cdual. simpl. rewrite negb_involutive. split_and!; [exact Hf|exact He0|done].
    + unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
  - pose proof (Hlbl _ _ He0) as Hoa. apply offers_sel in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, f. split_and!; [|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
    exists e, f. split_and!; [done|done|done|]. right; right; right; left. by eexists _, _, _.
  - pose proof (Hlbl _ _ Hf) as Hoa. apply offers_bra in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [| done |].
    + exists e, ei. split_and!; [done|done|by apply not_eq_sym|]. right; right; right; right.
      eexists _, _, _. unfold cdual. simpl. rewrite negb_involutive. split; [exact He0|exact Hf].
    + unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
Qed.

Lemma sync_partner_ends q L q' p ep ap op :
  istep q L q' → p ∈ L → q.2 !! p = Some ep → act ep = Some ap → aend1 ap = Some op →
  ∃ u eu, u ∈ L ∧ u ≠ p ∧ q.2 !! u = Some eu ∧ cdual op ∈ fends eu.
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
    exists j, f. split_and!; [set_solver|done|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
  - apply offers_recv in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [set_solver|done|done|].
    unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
  - apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, f. split_and!; [set_solver|done|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
  - apply offers_clos in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [set_solver|done|done|].
    unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
  - apply offers_sel in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists j, f. split_and!; [set_solver|done|done|apply (tstep_end_fends _ _ _ _ Hf eq_refl)].
  - apply offers_bra in Hoa as ->. simpl in Ho. injection Ho as <-.
    exists i, ei. split_and!; [set_solver|done|done|].
    unfold cdual. simpl. rewrite negb_involutive. apply (tstep_end_fends _ _ _ _ He0 eq_refl).
Qed.

Lemma chan_kept q L q' c :
  istep q L q' → c ∈ q.1 → (∀ u eu, u ∈ L → q.2 !! u = Some eu → c ∉ fchans eu) → c ∈ q'.1.
Proof.
  intros Hst HcC Hn. destruct q as [C M]. simpl in *.
  inversion Hst as [C0 M0 i ei ei' Hi Hs|C0 M0 i ei c0 x ei' Hi Hs HC Hcs|C0 M0 i j ei v ei' Hi Hs Hj
    |C0 M0 i j c0 b v ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i j c0 b ei ei' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j c0 β b ei ei' f f' Hij Hi Hj He0 Hf|C0 M0 i ei c0 bc d bd ei' Hi Hs HC]; subst; simpl;
    try done; try set_solver.
  - assert (c ≠ c0) as Hne.
    { intros ->. apply (Hn i ei ltac:(set_solver) Hi). apply fchans_of_fends with (o := (c0, b)).
      apply (tstep_end_fends _ _ _ _ He0 eq_refl). }
    set_solver.
  - assert (c ≠ c0) as Hne.
    { intros ->. apply (Hn i ei ltac:(set_solver) Hi). apply fchans_of_fends with (o := (c0, bc)).
      destruct (act_step _ _ _ Hs) as (a & Ha & Hoa). apply offers_link in Hoa as (o1 & o2 & -> & Hcd).
      apply (act_aends_fends ei (ALink o1 o2) _ Ha eq_refl). simpl. rewrite <-Hcd. set_solver. }
    set_solver.
Qed.

Lemma synced_step q L q' t p o :
  synced q t p o → istep q L q' → t ∉ L → p ∉ L →
  (∀ u eu, u ∈ L → q.2 !! u = Some eu → o.1 ∉ fchans eu) → synced q' t p o.
Proof.
  intros (e & f & He & Hf & Htp & H) Hst Ht Hp Hn.
  destruct (nonpart_terms _ _ _ Hst) as (g & Hg & Hgc). pose proof (Hgc o.1 Hn) as Hgo.
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
  - right; right; left. exists (emap g e1), (emap g f1). split_and!; [done|done|].
    apply (chan_kept _ _ _ _ Hst HC Hn).
  - right; right; right; left. exists b, (emap g e1), (emap g f1). by split.
  - right; right; right; right. exists b, (emap g e1), (emap g f1). by split.
Qed.

Lemma synced_partner_act q t p o f :
  synced q t p o → q.2 !! p = Some f → ∃ ap, act f = Some ap ∧ aend1 ap = Some (cdual o).
Proof.
  intros (e0 & f0 & _ & Hf0 & _ & H) Hf. rewrite Hf in Hf0. injection Hf0 as <-.
  destruct H as [(v & e1 & f1 & H1 & H2)|[(v & e1 & f1 & H1 & H2)|[(e1 & f1 & H1 & H2 & _)
    |[(b & e1 & f1 & H1 & H2)|(b & e1 & f1 & H1 & H2)]]]].
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_recv in Hoa as ->. by eexists.
  - destruct (act_step _ _ _ H1) as (ap & Hap & Hoa). apply offers_send in Hoa as ->. by eexists.
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_clos in Hoa as ->. by eexists.
  - destruct (act_step _ _ _ H2) as (ap & Hap & Hoa). apply offers_bra in Hoa as ->. by eexists.
  - destruct (act_step _ _ _ H1) as (ap & Hap & Hoa). apply offers_sel in Hoa as ->. by eexists.
Qed.

Lemma pers_step n W T π q A U L q' t :
  strict W → LFconf (S n) W ∅ T π q A U → istep q L q' → t ∉ L → npend q t → enabled q t → enabled q' t.
Proof.
  intros HW Hc Hst Ht Hp Hen. destruct (npend_end q t Hp) as (e & a & o & He & Ha & Ho & _).
  destruct (enabled_synced q t e a o He Ha Ho Hen) as (p & f & Hsy & Hf & Hpo).
  pose proof (s_held n W HW T π q A U Hc t e a o He Ha Ho) as Hto.
  assert (Hholds : ∀ u eu, q.2 !! u = Some eu → o.1 ∈ fchans eu → u = t ∨ u = p).
  { intros u eu Heu Hm. apply fends_of_fchans in Hm as [b' Hb'].
    destruct (decide ((o.1, b') = o)) as [Heq|Hneq].
    - left. rewrite Heq in Hb'. by apply (s_uniq n W HW T π q A U Hc u t eu e o).
    - right. assert ((o.1, b') = cdual o) as Heq.
      { destruct o as [c β]. unfold cdual. simpl in *. f_equal.
        destruct b', β; simpl; try done; exfalso; by apply Hneq. }
      rewrite Heq in Hb'. by apply (s_uniq n W HW T π q A U Hc u p eu f (cdual o)). }
  assert (p ∉ L) as HpL.
  { intros HpL. destruct (synced_partner_act q t p o f Hsy Hf) as (ap & Hap & Hao).
    destruct (sync_partner_ends q L q' p f ap _ Hst HpL Hf Hap Hao) as (u & eu & HuL & Hup & Heu & Hu).
    rewrite cdual_cdual in Hu. assert (u = t) as -> by (apply (s_uniq n W HW T π q A U Hc u t eu e o); done).
    done. }
  apply (synced_enabled q' t p o). apply (synced_step q L q' t p o Hsy Hst Ht HpL).
  intros u eu HuL Heu Hm. destruct (Hholds u eu Heu Hm) as [->| ->]; done.
Qed.

(** ** The soup along runs and reachable configurations *)

Lemma strict_of W : world_wf W → well_founded (w_lt W) → strict W.
Proof. intros HW Hwf. split; [done|]. intros x Hx. induction (Hwf x) as [x _ IH]. by apply (IH x). Qed.

Lemma lfconf_isteps W T π q0 q1 :
  strict W → isteps q0 q1 → (∀ n, ∃ A U, LFconf n W ∅ T π q0 A U) →
  ∃ π', ∀ n, ∃ A U, LFconf n W ∅ T π' q1 A U.
Proof.
  intros HW Hs. revert π. induction Hs as [q|q q2 q3 [L Hst] _ IH]; intros π H0; [by exists π|].
  apply (IH (pupd π q L q2)). intros n. destruct (H0 (S (S n))) as (A & U & Hc).
  by apply (lfconf_step n W T π q A U L q2).
Qed.

(** The soup of a judgment, at any lifting of the process. *)
Lemma LFP_soup W T p q :
  LFP W ∅ T p → erase q = p →
  ∃ π φ, (∀ n, ∃ A U, LFconf n W ∅ T π q A U) ∧ (∀ n, lf_fuel n W π φ q).
Proof.
  intros [_ (π & φ & HS)] Hq. exists π, φ. split; intros n; destruct (HS n) as (q1 & A & U & Hq1 & Hc & Hf);
    destruct q as [C M], q1 as [C1 M1]; unfold erase in Hq, Hq1; simpl in *; rewrite <-Hq in Hq1;
    injection Hq1 as -> HM.
  - by apply (LFconf_relabel n W ∅ T π C M1 M A U).
  - by apply (lf_fuel_relabel n W π φ C M1 M).
Qed.

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
  destruct (LFP_soup W T p q0 HP Hq0) as (π & φ & Hc0 & _).
  rewrite <-Hq0 in Hq. destruct (pred_star_lift q0 q Hq) as (q1 & Hq1 & <-).
  destruct (lfconf_isteps W T π q0 q1 HW Hq1 Hc0) as [π' Hc1].
  destruct (Hc1 1) as (A & U & Hc). simpl in HE.
  assert (e ∈ soup q1.2) as He by (rewrite HE; multiset_solver).
  apply elem_of_soup in He as [t Ht].
  pose proof (lf_closed _ _ _ _ _ _ _ _ Hc t e Ht) as Hcl.
  left. simpl. assert (c.1 ∈ fchans e) as Hce.
  { apply fchans_of_fends. apply (act_aends_fends e (ALink c d) {[c; d]} Ha eq_refl). set_solver. }
  set_solver.
Qed.

(** ** The counter of the partner end *)

Definition holder (q : config) (o : cend) : option nat :=
  match list_find (λ se : nat * expr, o ∈ fends se.2) (map_to_list q.2) with
  | Some (_, (s, _)) => Some s
  | None => None
  end.

Lemma holder_spec q o s es :
  q.2 !! s = Some es → o ∈ fends es →
  (∀ s' es', q.2 !! s' = Some es' → o ∈ fends es' → s' = s) → holder q o = Some s.
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

Definition fu_at (q : config) (F : nat → gmap cend fuel) (t : nat) : nat :=
  match rend q t with
  | Some o => match holder q (cdual o) with Some s => fval F s (cdual o) | None => 0 end
  | None => 0
  end.

Lemma sess_end_step e a o : act e = Some a → aend1 a = Some o → ∃ σ e', tstep e (LSess σ) e' ∧ sl_end σ = Some o.
Proof.
  intros Ha Ho. assert (is_sess a) as Hs by (unfold is_sess; destruct a; simpl in *; try done; by eexists).
  destruct (sess_stable_step e a Ha Hs) as (σ & e' & Hst). exists σ, e'. split; [done|].
  destruct (act_step _ _ _ Hst) as (a' & Ha' & Hoa). rewrite Ha in Ha'. injection Ha' as <-.
  by apply (offers_aend1 a σ o).
Qed.

Section counters.
  #[local] Set Default Proof Using "All".
  Context (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point).
  Context (q : config) (A : nat → tenv) (U : nat → ty) (P : nat → gmap cend point) (F : nat → gmap cend fuel).
  Context (Hc : LFconf (S (S n)) W ∅ T π q A U) (HF : lf_fuelc (S (S n)) W π P F q).

  (** The partner end of a pending thread has a finite counter. *)
  Lemma holder_fin t e a o s es :
    q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
    q.2 !! s = Some es → s ≠ t → cdual o ∈ fends es →
    ∃ m, F s !! cdual o = Some (Some m) ∧ fu_at q F t = m.
  Proof.
    intros He Ha Ho Hes Hst Hso.
    destruct (HF t e He) as (H1t & H2t & H3t & H4t). destruct (HF s es Hes) as (H1s & H2s & H3s & H4s).
    destruct (sess_end_step e a o Ha Ho) as (σ & e1 & Hst1 & Hσ).
    destruct (fuel_wait (S n) W (P t) (F t) e H1t σ e1 o Hst1 Hσ) as (k & mb & Hk & Hb).
    pose proof (s_held (S n) W HW T π q A U Hc t e a o He Ha Ho) as Hto.
    destruct (proj1 (lfc_held _ _ _ _ _ _ _ Hc t e o He) Hto) as [x Hx].
    destruct (proj1 (lfc_held _ _ _ _ _ _ _ Hc s es (cdual o) Hes) Hso) as [y Hy].
    destruct (lfc_partner_at _ _ _ _ _ _ _ Hc t e o x s es y He Hx Hes Hy) as [Hy2 _].
    assert (P s !! cdual o = Some (pt_dual k)) as Hks.
    { rewrite H4s by done. rewrite (lf_pt _ _ _ _ _ _ _ _ Hc s es _ _ Hes Hy), Hy2.
      rewrite H4t in Hk by done. rewrite (lf_pt _ _ _ _ _ _ _ _ Hc t e _ _ He Hx) in Hk. by injection Hk as ->. }
    assert (is_Some (F s !! cdual o)) as [f Hf] by (apply elem_of_dom; by rewrite H3s).
    destruct (fuel_cap (S n) W (P s) (F s) es H1s (cdual o) f Hf) as (k' & Hk' & Hle).
    rewrite Hks in Hk'. injection Hk' as <-. rewrite Hb in Hle. destruct f as [m|]; [|done].
    exists m. split; [done|]. unfold fu_at. unfold rend. rewrite He, Ha, Ho.
    rewrite (holder_spec q (cdual o) s es Hes Hso).
    - unfold fval. by rewrite Hf.
    - intros s' es' Hes' Hso'. by apply (s_uniq (S n) W HW T π q A U Hc s' s es' es (cdual o)).
  Qed.
End counters.

Lemma fuel_reduce (n : nat) (W : world) (HW : strict W) (T : ty) (π : gmap cend point) (q : config)
    (A : nat → tenv) (U : nat → ty) (n' : nat) (π' : gmap cend point) (q' : config) (A' : nat → tenv)
    (U' : nat → ty) (F F' : nat → gmap cend fuel) (L : gset nat) (t : nat) (e : expr) (a : action)
    (o : cend) (e' : expr) (a' : action) (o' : cend) (s : nat) (es : expr) (m : nat) :
  LFconf (S n) W ∅ T π q A U → LFconf (S n') W ∅ T π' q' A' U' →
  q.2 !! t = Some e → act e = Some a → aend1 a = Some o →
  q.2 !! s = Some es → s ≠ t → cdual o ∈ fends es → fu_at q F t = m →
  q'.2 !! t = Some e' → act e' = Some a' → aend1 a' = Some o' →
  (∃ s' es', q'.2 !! s' = Some es' ∧ s' ≠ t ∧ cdual o' ∈ fends es' ∧
     (fval F' s' (cdual o') < m ∨ (fval F' s' (cdual o') = m ∧ s' = s ∧ (s ∈ L → admin_at q s)))) →
  fu_at q' F' t < fu_at q F t ∨
  (fu_at q' F' t = fu_at q F t ∧ (∀ x, waits q' t x ↔ waits q t x) ∧ ∀ x, waits q t x → x ∈ L → admin_at q x).
Proof.
  intros Hc Hc' He Ha Ho Hes Hst Hso Hm He' Ha' Ho' (s' & es' & Hes' & Hst' & Hso' & Hor).
  assert (fu_at q' F' t = fval F' s' (cdual o')) as Hfu'.
  { unfold fu_at, rend. rewrite He', Ha', Ho'.
    rewrite (holder_spec q' (cdual o') s' es' Hes' Hso'); [done|].
    intros x ex Hx Hxo. by apply (s_uniq n' W HW T π' q' A' U' Hc' x s' ex es' (cdual o')). }
  rewrite Hfu', Hm. destruct Hor as [Hlt|(Heq & -> & Had)]; [by left|right].
  split_and!; [done| |].
  - intros x. rewrite (s_waits n' W HW T π' q' A' U' Hc' t e' a' o' x He' Ha' Ho').
    rewrite (s_waits n W HW T π q A U Hc t e a o x He Ha Ho). split.
    + intros (Hxt & ex & Hx & Hxo). split; [done|]. exists es.
      assert (x = s) as -> by (by apply (s_uniq n' W HW T π' q' A' U' Hc' x s ex es' (cdual o'))). done.
    + intros (Hxt & ex & Hx & Hxo). split; [done|]. exists es'.
      assert (x = s) as -> by (by apply (s_uniq n W HW T π q A U Hc x s ex es (cdual o))). done.
  - intros x Hw Hx. rewrite (s_waits n W HW T π q A U Hc t e a o x He Ha Ho) in Hw.
    destruct Hw as (_ & ex & Hex & Hxo).
    assert (x = s) as -> by (by apply (s_uniq n W HW T π q A U Hc x s ex es (cdual o))). by apply Had.
Qed.
