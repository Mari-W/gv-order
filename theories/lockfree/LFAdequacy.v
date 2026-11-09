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
