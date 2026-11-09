(** * Adequacy of the lock-free relation (lock-freedom plan §15.5)

    [lf_adequacy]: in a well-founded world, a process in [LFPrel N ω n]
    at every index is lock free. The proof instantiates [lf_criterion]
    along the annotated run that [aupd] computes from ω.

    - Local progress and [links_restricted] are facts of one annotated
      configuration ([LFconf 1]).
    - [fu k t] is the counter of the partner entry of t's channel. A
      step of the holder on another channel ticks it, and handing the
      entry on passes at most the counter minus one.
    - [we k t] is the point of t's entry, ordered by [w_lt W]. A thread
      that does not step keeps it. The gate of the holder puts the
      point of the holder's offer below it.
    - [no_tau_divergence] comes from [live_adequacy]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.LFRelation lockfree.ThreadProgress.

(** ** Channels of a redex *)

Lemma act_asubjs_fchans e a S : act e = Some a → asubjs a = Some S → S ⊆ fchans e.
Proof.
  induction e as [| | |c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
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

(** The channel of a session redex other than a link. *)
Definition rchan (a : action) : option chan :=
  match a with
  | ARecv c | ASend c _ | AClos c | ASel c _ | ABra c => Some c
  | _ => None
  end.

Lemma rchan_asubjs a c : rchan a = Some c → asubjs a = Some {[c]}.
Proof. destruct a; simpl; intros H; simplify_eq; done. Qed.

Lemma rchan_amap g a c : rchan a = Some c → rchan (amap g a) = Some (g c).
Proof. destruct a; simpl; intros H; simplify_eq; done. Qed.

Lemma npend_rchan q t :
  npend q t → ∃ e a c, q.2 !! t = Some e ∧ act e = Some a ∧ rchan a = Some c ∧ ¬ is_admin a.
Proof.
  intros [(e & a & He & Ha & Hs) Hna]. exists e, a.
  assert (¬ is_admin a) as Hna' by (intros H; apply Hna; by exists e, a).
  destruct a; simpl in *; try done; eexists; split_and!; done.
Qed.

Lemma offers_rchan a c σ : rchan a = Some c → offers a (LSess σ) → subjs σ = {[c]}.
Proof. intros Hr Ho. apply offers_asubjs in Ho. rewrite (rchan_asubjs a c Hr) in Ho.
  injection Ho as H. by rewrite H. Qed.

Lemma offered_rchan Θ e k a c : offered_t Θ e k → act e = Some a → rchan a = Some c → k.1 = c.
Proof.
  intros (σ & e' & Hst & Hsel) Ha Hr. destruct (act_step _ _ _ Hst) as (a' & Ha' & Ho).
  rewrite Ha in Ha'. injection Ha' as <-. apply selects_subj in Hsel.
  rewrite (offers_rchan a c σ Hr Ho) in Hsel. set_solver.
Qed.

Lemma rchan_not_link a c : rchan a = Some c → ¬ is_admin a.
Proof. destruct a; simpl; intros H; try discriminate; intros []. Qed.

(** ** Facts of one annotated configuration *)

Lemma entry_of_dom (Θ : tenv) c : c ∈ dom Θ → ∃ ek, tenv_entry Θ (c, false) = Some ek.
Proof.
  intros Hc. apply elem_of_dom in Hc as [o Ho]. unfold tenv_entry. simpl. rewrite Ho.
  destruct o; eauto.
Qed.

Lemma entry_dom (Θ : tenv) k ek : tenv_entry Θ k = Some ek → k.1 ∈ dom Θ.
Proof. apply tenv_entry_dom. Qed.

Lemma entry_one (Θ : tenv) c x k ek :
  Θ !! c = Some (One x) → tenv_entry Θ k = Some ek → k.1 = c → k = (c, false) ∧ ek = x.
Proof.
  intros Hc Hk <-. destruct k as [c' []]; unfold tenv_entry in Hk; simpl in *; rewrite Hc in Hk;
    by simplify_eq.
Qed.

Section conf.
  Context (W : world) (HW : world_wf W) (Hwf : well_founded (w_lt W)).
  Context (a : aconf) (Hc : LFconf 1 W ∅ a).

  Lemma c_thread t e : (ac_q a).2 !! t = Some e → LFErel 1 W (ac_env a t) (ac_fuel a t) e.
  Proof. intros He. by apply Hc. Qed.

  Lemma c_dom t e : (ac_q a).2 !! t = Some e → dom (ac_env a t) = fchans e.
  Proof. intros He. by destruct (c_thread t e He) as (_ & ? & _). Qed.

  Lemma c_ready t e : (ac_q a).2 !! t = Some e → ¬ irred e → ready_t W (ac_env a t) ∅ e.
  Proof.
    intros He Hnirr. destruct (c_thread t e He) as ([U HU] & _).
    apply LErel_S_iff in HU. destruct (HU W (wext_r_refl W)) as (_ & Hr & _). by apply Hr.
  Qed.

  Lemma c_irr t e k ek :
    (ac_q a).2 !! t = Some e → tenv_entry (ac_env a t) k = Some ek → ¬ irred e.
  Proof.
    intros He Hk Hirr. destruct (c_thread t e He) as (_ & _ & H0 & _).
    apply entry_dom in Hk. rewrite (H0 Hirr) in Hk. set_solver.
  Qed.

  Lemma c_closed t e : (ac_q a).2 !! t = Some e → fchans e ⊆ (ac_q a).1.
  Proof. intros He. destruct Hc as (_ & H & _). specialize (H t e He). set_solver. Qed.

  Lemma c_pair t e k ek :
    (ac_q a).2 !! t = Some e → tenv_entry (ac_env a t) k = Some ek →
    ∃ s es k' ek', (ac_q a).2 !! s = Some es ∧ tenv_entry (ac_env a s) k' = Some ek' ∧
      k'.1 = k.1 ∧ (s, k') ≠ (t, k) ∧ ek'.2 = pt_dual ek.2 ∧ sdual ek.1 ek'.1.
  Proof. intros He Hk. destruct Hc as (_ & _ & H & _). apply (H t e k ek He Hk). set_solver. Qed.

  Lemma c_three t1 t2 t3 e1 e2 e3 k1 k2 k3 x1 x2 x3 :
    (ac_q a).2 !! t1 = Some e1 → (ac_q a).2 !! t2 = Some e2 → (ac_q a).2 !! t3 = Some e3 →
    tenv_entry (ac_env a t1) k1 = Some x1 → tenv_entry (ac_env a t2) k2 = Some x2 →
    tenv_entry (ac_env a t3) k3 = Some x3 → k1.1 = k2.1 → k2.1 = k3.1 →
    (t1, k1) = (t2, k2) ∨ (t1, k1) = (t3, k3) ∨ (t2, k2) = (t3, k3).
  Proof. destruct Hc as (_ & _ & _ & H). apply H. Qed.

  (** The partner of an entry is the other entry of its channel. *)
  Lemma c_partner_of t e k ek s es k' ek' :
    (ac_q a).2 !! t = Some e → tenv_entry (ac_env a t) k = Some ek →
    (ac_q a).2 !! s = Some es → tenv_entry (ac_env a s) k' = Some ek' →
    k'.1 = k.1 → (s, k') ≠ (t, k) → ek'.2 = pt_dual ek.2 ∧ sdual ek.1 ek'.1.
  Proof.
    intros He Hk Hes Hk' H1 Hne.
    destruct (c_pair t e k ek He Hk) as (s0 & es0 & k0 & ek0 & Hs0 & Hk0 & H01 & Hne0 & Hd & Hsd).
    destruct (c_three t s s0 e es es0 k k' k0 ek ek' ek0 He Hes Hs0 Hk Hk' Hk0
      (eq_sym H1) (eq_trans H1 (eq_sym H01))) as [H|[H|H]]; [congruence|congruence|].
    injection H as <- <-. rewrite Hk' in Hk0. by injection Hk0 as <-.
  Qed.

  Lemma c_uniq t e s es s' es' c :
    (ac_q a).2 !! t = Some e → (ac_q a).2 !! s = Some es → (ac_q a).2 !! s' = Some es' →
    c ∈ dom (ac_env a t) → c ∈ dom (ac_env a s) → c ∈ dom (ac_env a s') →
    s ≠ t → s' ≠ t → s = s'.
  Proof.
    intros He Hes Hes' Ht Hs Hs' Hst Hs't.
    destruct (entry_of_dom _ _ Ht) as [x1 H1]. destruct (entry_of_dom _ _ Hs) as [x2 H2].
    destruct (entry_of_dom _ _ Hs') as [x3 H3].
    destruct (c_three t s s' e es es' _ _ _ x1 x2 x3 He Hes Hes' H1 H2 H3 eq_refl eq_refl)
      as [H|[H|H]]; simplify_eq; done.
  Qed.

  (** A link redex is enabled: its channels are restricted. *)
  Lemma c_link_enabled t e c d :
    (ac_q a).2 !! t = Some e → act e = Some (ALink c d) → enabled (ac_q a) t.
  Proof.
    intros He Ha. apply (admin_enabled (ac_q a) t e (ALink c d) He Ha I).
    intros c' d' [= <- <-]. left. apply (c_closed t e He).
    apply (act_asubjs_fchans e (ALink c d) {[c; d]} Ha eq_refl). set_solver.
  Qed.

  (** Two offers of one thread under one label are on dual entries,
      which no label selects twice. *)
  Lemma offered_twice_false Θ e k k' ek ek' :
    act e ≠ None → (∀ c d, act e ≠ Some (ALink c d)) →
    offered_t Θ e k → offered_t Θ e k' → tenv_entry Θ k = Some ek → tenv_entry Θ k' = Some ek' →
    k ≠ k' → k.1 = k'.1 → sdual ek.1 ek'.1 → False.
  Proof.
    intros _ Hnl (σ & e1 & Hst & Hsel) (σ' & e1' & Hst' & Hsel') Hk Hk' Hne H1 Hsd.
    destruct (act_step _ _ _ Hst) as (b & Hb & Ho). destruct (act_step _ _ _ Hst') as (b' & Hb' & Ho').
    rewrite Hb in Hb'. injection Hb' as <-.
    pose proof (sdual_kind _ _ Hsd) as Hkd.
    destruct b; destruct σ; try (simpl in Ho; contradiction);
      destruct σ'; try (simpl in Ho'; contradiction); simpl in Hsel, Hsel'.
    - destruct Hsel as (_ & x & m & T & s & Hx & Hu). destruct Hsel' as (_ & x' & m' & T' & s' & Hx' & Hu').
      rewrite Hk in Hx. injection Hx as <-. rewrite Hk' in Hx'. injection Hx' as <-.
      rewrite (hd_of _ _ Hu), (hd_of _ _ Hu') in Hkd. done.
    - destruct Hsel as (_ & x & m & T & s & Hx & Hu). destruct Hsel' as (_ & x' & m' & T' & s' & Hx' & Hu').
      rewrite Hk in Hx. injection Hx as <-. rewrite Hk' in Hx'. injection Hx' as <-.
      rewrite (hd_of _ _ Hu), (hd_of _ _ Hu') in Hkd. done.
    - destruct Hsel as (Hq1 & x & Hx & Hu & Hc1). destruct Hsel' as (Hq2 & x' & Hx' & Hu' & Hc2).
      rewrite Hk in Hx. injection Hx as <-. rewrite Hk' in Hx'. injection Hx' as <-.
      destruct k as [ck1 []], k' as [ck2 []]; simpl in *; subst; try done.
      + by apply (Hc1 eq_refl ek' Hk').
      + by apply (Hc2 eq_refl ek Hk).
    - exfalso. by apply (Hnl c d).
    - destruct Hsel as (_ & x & s1 & s2 & Hx & Hu). destruct Hsel' as (_ & x' & s1' & s2' & Hx' & Hu').
      rewrite Hk in Hx. injection Hx as <-. rewrite Hk' in Hx'. injection Hx' as <-.
      rewrite (hd_of _ _ Hu), (hd_of _ _ Hu') in Hkd. done.
    - destruct Hsel as (_ & x & s1 & s2 & Hx & Hu). destruct Hsel' as (_ & x' & s1' & s2' & Hx' & Hu').
      rewrite Hk in Hx. injection Hx as <-. rewrite Hk' in Hx'. injection Hx' as <-.
      rewrite (hd_of _ _ Hu), (hd_of _ _ Hu') in Hkd. done.
  Qed.

  (** Two dual offers on one channel, by two threads, make a step of both. *)
  Definition skind (σ : slabel) : hkind :=
    match σ with
    | SSend _ _ => KdSnd | SRecv _ _ => KdRcv | SClos _ => KdEnd
    | SSel _ _ => KdPlus | SBra _ _ => KdWith | SLink _ => KdStuck
    end.

  Lemma selects_kind Θ σ k ek :
    selects Θ σ k → tenv_entry Θ k = Some ek → (∀ cd, σ ≠ SLink cd) → kind (hd ek.1) = skind σ.
  Proof.
    intros Hsel Hk Hnl. destruct σ; simpl in Hsel.
    - destruct Hsel as (_ & x & m & T & s & Hx & Hu). rewrite Hk in Hx. injection Hx as <-.
      by rewrite (hd_of _ _ Hu).
    - destruct Hsel as (_ & x & m & T & s & Hx & Hu). rewrite Hk in Hx. injection Hx as <-.
      by rewrite (hd_of _ _ Hu).
    - destruct Hsel as (_ & x & Hx & Hu & _). rewrite Hk in Hx. injection Hx as <-.
      by rewrite (hd_of _ _ Hu).
    - by destruct (Hnl cd).
    - destruct Hsel as (_ & x & s1 & s2 & Hx & Hu). rewrite Hk in Hx. injection Hx as <-.
      by rewrite (hd_of _ _ Hu).
    - destruct Hsel as (_ & x & s1 & s2 & Hx & Hu). rewrite Hk in Hx. injection Hx as <-.
      by rewrite (hd_of _ _ Hu).
  Qed.

  Lemma offers_not_link e b σ e1 :
    act e = Some b → (∀ c d, b ≠ ALink c d) → tstep e (LSess σ) e1 → (∀ cd, σ ≠ SLink cd).
  Proof.
    intros Hb Hnl Hst cd ->. destruct (act_step _ _ _ Hst) as (b' & Hb' & Ho).
    rewrite Hb in Hb'. injection Hb' as <-. destruct b; simpl in Ho; try done. by apply (Hnl c d).
  Qed.

  Lemma meet_step t e s es k k' ek ek' :
    t ≠ s → (ac_q a).2 !! t = Some e → (ac_q a).2 !! s = Some es →
    (∀ c d, act e ≠ Some (ALink c d)) → (∀ c d, act es ≠ Some (ALink c d)) →
    offered_t (ac_env a t) e k → offered_t (ac_env a s) es k' →
    tenv_entry (ac_env a t) k = Some ek → tenv_entry (ac_env a s) k' = Some ek' →
    k'.1 = k.1 → sdual ek.1 ek'.1 →
    ∃ L q', istep (ac_q a) L q' ∧ t ∈ L ∧ s ∈ L.
  Proof.
    intros Hts He Hes Hnl Hnl' (σ & e1 & Hst & Hsel) (σ' & es1 & Hst' & Hsel') Hk Hk' H1 Hsd.
    destruct (act_step _ _ _ Hst) as (b & Hb & Ho).
    destruct (act_step _ _ _ Hst') as (b' & Hb' & Ho').
    assert (∀ c d, b ≠ ALink c d) as Hnlb by (intros c d ->; by apply (Hnl c d)).
    assert (∀ c d, b' ≠ ALink c d) as Hnlb' by (intros c d ->; by apply (Hnl' c d)).
    pose proof (selects_kind _ _ _ _ Hsel Hk (offers_not_link e b σ e1 Hb Hnlb Hst)) as K1.
    pose proof (selects_kind _ _ _ _ Hsel' Hk' (offers_not_link es b' σ' es1 Hb' Hnlb' Hst')) as K2.
    pose proof (sdual_kind _ _ Hsd) as Hkd. rewrite K1, K2 in Hkd.
    pose proof (selects_subj _ _ _ Hsel) as S1. pose proof (selects_subj _ _ _ Hsel') as S2.
    rewrite H1 in S2. pose proof (c_closed t e He) as Hcl.
    destruct (ac_q a) as [C M] eqn:Hq. simpl in *.
    destruct σ, σ'; simpl in Hkd; try discriminate;
      try (exfalso; by apply (offers_not_link e b _ e1 Hb Hnlb Hst cd)); simpl in S1, S2;
      apply elem_of_singleton in S1, S2; rewrite S2 in S1; subst;
      destruct b; simpl in Ho; try done; destruct b'; simpl in Ho'; try done;
      destruct_and?; subst.
    - (* t receives, s sends *)
      match goal with Hb' : act es = Some (ASend ?c ?v) |- _ =>
        destruct (act_offer e (ARecv c) (LSess (SRecv c v)) Hb) as [e2 He2];
        [split; [done|]; by eapply act_send_val|];
        eexists _, _; split; [eapply (IMsg C M s t c v); [done|done|done|done|exact He2]|]
      end. set_solver.
    - (* t sends, s receives *)
      match goal with Hb : act e = Some (ASend ?c ?v) |- _ =>
        destruct (act_offer es (ARecv c) (LSess (SRecv c v)) Hb') as [es2 Hes2];
        [split; [done|]; by eapply act_send_val|];
        eexists _, _; split; [eapply (IMsg C M t s c v); [done|done|done|done|exact Hes2]|]
      end. set_solver.
    - (* close *)
      match goal with Hb : act e = Some (AClos ?c) |- _ =>
        eexists _, _; split; [eapply (IClose C M t s c); [done|done|done|done|done|]|set_solver];
        apply Hcl; apply (act_asubjs_fchans e (AClos c) {[c]} Hb eq_refl); set_solver
      end.
    - (* t selects, s branches *)
      match goal with Hb : act e = Some (ASel ?c ?bb) |- _ =>
        destruct (act_offer es (ABra c) (LSess (SBra c bb)) Hb') as [es2 Hes2]; [done|];
        eexists _, _; split; [eapply (IChoice C M t s c bb); [done|done|done|done|exact Hes2]|]
      end. set_solver.
    - (* t branches, s selects *)
      match goal with Hb' : act es = Some (ASel ?c ?bb) |- _ =>
        destruct (act_offer e (ABra c) (LSess (SBra c bb)) Hb) as [e2 He2]; [done|];
        eexists _, _; split; [eapply (IChoice C M s t c bb); [done|done|done|done|exact He2]|]
      end. set_solver.
  Qed.

  (** Local progress of a configuration in [LFconf 1]. *)
  Lemma act_link_dec e : {c & {d | act e = Some (ALink c d)}} + {∀ c d, act e ≠ Some (ALink c d)}.
  Proof.
    destruct (act e) as [[]|]; try (right; intros ??; discriminate). left. by exists c, d.
  Defined.

  Lemma c_meet t e s es k ek k' ek' :
    (ac_q a).2 !! t = Some e → (ac_q a).2 !! s = Some es →
    offered_t (ac_env a t) e k → offered_t (ac_env a s) es k' →
    tenv_entry (ac_env a t) k = Some ek → tenv_entry (ac_env a s) k' = Some ek' →
    k'.1 = k.1 → (s, k') ≠ (t, k) → ek'.2 = pt_dual ek.2 →
    enabled (ac_q a) t ∨ enabled (ac_q a) s.
  Proof.
    intros He Hes Ho Ho' Hk Hk' H1 Hne Hd.
    destruct (act_link_dec e) as [(c & d & Hl)|Hnl]; [left; by eapply c_link_enabled|].
    destruct (act_link_dec es) as [(c & d & Hl)|Hnl']; [right; by eapply c_link_enabled|].
    destruct (c_partner_of t e k ek s es k' ek' He Hk Hes Hk' H1 Hne) as [_ Hsd].
    destruct (decide (s = t)) as [->|Hst].
    - exfalso. rewrite He in Hes. injection Hes as <-.
      apply (offered_twice_false (ac_env a t) e k k' ek ek'); try done.
      + destruct Ho as (σ & e1 & Hst & _). destruct (act_step _ _ _ Hst) as (b & Hb & _).
        by rewrite Hb.
      + intros ->. done.
    - left. destruct (meet_step t e s es k k' ek ek' (λ H, Hst (eq_sym H)) He Hes Hnl Hnl'
        Ho Ho' Hk Hk' H1 Hsd) as (L & q' & Hst' & HtL & _).
      by exists L, q'.
  Qed.

  Lemma c_local_progress : local_progress (ac_q a).
  Proof.
    assert (strict W) as HWs.
    { split; [done|]. intros x Hx. induction (Hwf x) as [x _ IH]. by apply (IH x). }
    apply (local_progress_ready (ac_q a) W (ac_env a) (λ _, ∅) HWs).
    - intros t e He Hnirr. by apply c_ready.
    - intros t e k ek He Hk. by eapply c_irr.
    - intros t e k ek He Hk. rewrite <-(c_dom t e He). by eapply entry_dom.
    - intros t e k ek He Hk. destruct (c_pair t e k ek He Hk) as (s & es & k' & ek' & ? & ? & ? & ? & ? & _).
      by exists s, es, k', ek'.
    - intros t e s es k ek k' ek' He Hes Ho Ho' Hk Hk' H1 Hne Hd. by eapply c_meet.
    - intros t e He (cd & e' & Hst). destruct (act_step _ _ _ Hst) as (b & Hb & Ho).
      destruct b; simpl in Ho; try done. by eapply c_link_enabled.
  Qed.

  (** A thread blocked on c holds one end of c. Holding both, its gate
      would put the offered point below itself. *)
  Lemma rchan_sess b c : rchan b = Some c → is_sess b.
  Proof. intros H. unfold is_sess. by rewrite (rchan_asubjs b c H). Qed.

  Lemma rchan_fchans e b c : act e = Some b → rchan b = Some c → c ∈ fchans e.
  Proof.
    intros Hb Hr. apply (act_asubjs_fchans e b {[c]} Hb (rchan_asubjs b c Hr)). set_solver.
  Qed.

  Lemma c_offered t e b c :
    (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
    ∃ k ek, offered_t (ac_env a t) e k ∧ tenv_entry (ac_env a t) k = Some ek ∧ k.1 = c ∧
      below_rest W (ac_env a t) (offered_t (ac_env a t) e) ∅.
  Proof.
    intros He Hb Hr.
    assert (c ∈ dom (ac_env a t)) as Hcd by (rewrite (c_dom t e He); by eapply rchan_fchans).
    destruct (entry_of_dom _ _ Hcd) as [x Hx].
    pose proof (c_irr t e _ x He Hx) as Hnirr.
    pose proof (sess_stable e b Hb (rchan_sess b c Hr)) as Hstab.
    destruct (c_ready t e He Hnirr Hstab) as [_ [(cd & e' & Hl)|Hbr]].
    { destruct (act_step _ _ _ Hl) as (b' & Hb' & Ho). rewrite Hb in Hb'. injection Hb' as <-.
      destruct b; simpl in Ho, Hr; done. }
    destruct (offered_exists W (ac_env a t) ∅ e (c_ready t e He Hnirr) Hstab
      (λ Hv, Hnirr (val_irred e Hv))) as [k Hk].
    destruct Hk as (σ & e1 & Hst & Hsel) eqn:Hk'.
    destruct (selects_entry _ _ _ Hsel) as [ek Hek].
    exists k, ek. split_and!; [done|done| |done]. by eapply offered_rchan.
  Qed.

  Lemma both_false t e b c x y :
    (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
    ac_env a t !! c = Some (Both x y) → False.
  Proof.
    intros He Hb Hr Hxy.
    destruct (c_offered t e b c He Hb Hr) as (k0 & ek0 & Ho0 & Hk0 & H0 & Hbr).
    set (k1 := (c, negb k0.2)).
    assert (∃ ek1, tenv_entry (ac_env a t) k1 = Some ek1) as [ek1 Hk1].
    { unfold k1, tenv_entry. simpl. rewrite Hxy. destruct k0.2; simpl; eauto. }
    assert (k1 ≠ k0) as Hne.
    { unfold k1. destruct k0 as [c0 b0]. simpl. intros [=]. by destruct b0. }
    assert (k1.1 = k0.1) as H10 by (unfold k1; simpl; by rewrite H0).
    destruct (c_partner_of t e k0 ek0 t e k1 ek1 He Hk0 He Hk1 H10) as [Hd Hsd]; [congruence|].
    destruct (decide (offered_t (ac_env a t) e k1)) as [Ho1|Hno1].
    - assert (act e ≠ None) as Hsome by (by rewrite Hb).
      assert (∀ c' d', act e ≠ Some (ALink c' d')) as Hnl.
      { intros c' d' Hl. rewrite Hb in Hl. injection Hl as ->. by simpl in Hr. }
      exact (offered_twice_false (ac_env a t) e k0 k1 ek0 ek1 Hsome Hnl Ho0 Ho1 Hk0 Hk1
        (λ H, Hne (eq_sym H)) (eq_sym H10) Hsd).
    - destruct (Hbr k0 ek0 Ho0 Hk0) as [Hb1 _]. specialize (Hb1 k1 ek1 Hk1 Hno1).
      unfold entry_head in Hb1. rewrite Hd, pt_dual_dual in Hb1.
      induction (Hwf ek0.2) as [z _ IH]. by apply (IH z).
  Qed.

  (** Waiting is holding the partner end. *)
  Lemma c_waits t e b c s :
    (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
    waits (ac_q a) t s ↔ s ≠ t ∧ ∃ es, (ac_q a).2 !! s = Some es ∧ c ∈ dom (ac_env a s).
  Proof.
    intros He Hb Hr. split.
    - intros (Hst & e' & b' & S & c' & es & He' & Hb' & HS & Hc' & Hes & Hm).
      rewrite He in He'. injection He' as <-. rewrite Hb in Hb'. injection Hb' as <-.
      rewrite (rchan_asubjs b c Hr) in HS. injection HS as <-. apply elem_of_singleton in Hc'.
      subst. split; [done|]. exists es. split; [done|]. by rewrite (c_dom s es Hes).
    - intros (Hst & es & Hes & Hcs). split; [done|]. exists e, b, {[c]}, c, es.
      split_and!; [done|done|by apply rchan_asubjs|set_solver|done|]. by rewrite <-(c_dom s es Hes).
  Qed.

  (** The rank of a blocked thread: the point of its entry. *)
  Definition ent_pt (o : option ends) : point :=
    match o with Some (One x) | Some (Both x _) => x.2 | None => pbot end.

  Lemma c_one t e b c :
    (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
    ∃ x, ac_env a t !! c = Some (One x).
  Proof.
    intros He Hb Hr.
    assert (c ∈ dom (ac_env a t)) as Hcd by (rewrite (c_dom t e He); by eapply rchan_fchans).
    apply elem_of_dom in Hcd as [[x|x y] Hx]; [by exists x|].
    exfalso. by apply (both_false t e b c x y).
  Qed.

  Lemma c_rank t e b c s es b' d :
    (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
    (ac_q a).2 !! s = Some es → act es = Some b' → rchan b' = Some d →
    s ≠ t → c ∈ dom (ac_env a s) →
    enabled (ac_q a) t ∨ w_lt W (ent_pt (ac_env a s !! d)) (ent_pt (ac_env a t !! c)).
  Proof.
    intros He Hb Hr Hes Hb' Hr' Hst Hcs.
    destruct (c_one t e b c He Hb Hr) as [x Hx].
    assert (∃ y, ac_env a s !! c = Some (One y)) as [y Hy].
    { apply elem_of_dom in Hcs as [[y|y1 y2] Hy]; [by exists y|exfalso].
      assert (tenv_entry (ac_env a s) (c, false) = Some y1) as H1 by (unfold tenv_entry; simpl; by rewrite Hy).
      assert (tenv_entry (ac_env a s) (c, true) = Some y2) as H2 by (unfold tenv_entry; simpl; by rewrite Hy).
      assert (tenv_entry (ac_env a t) (c, false) = Some x) as H3 by (unfold tenv_entry; simpl; by rewrite Hx).
      destruct (c_three s s t es es e (c, false) (c, true) (c, false) y1 y2 x Hes Hes He H1 H2 H3
        eq_refl eq_refl) as [H|[H|H]]; simplify_eq. }
    assert (tenv_entry (ac_env a t) (c, false) = Some x) as Htx by (unfold tenv_entry; simpl; by rewrite Hx).
    assert (tenv_entry (ac_env a s) (c, false) = Some y) as Hsy by (unfold tenv_entry; simpl; by rewrite Hy).
    destruct (c_partner_of t e (c, false) x s es (c, false) y He Htx Hes Hsy) as [Hd Hsd];
      [done|congruence|].
    destruct (c_offered s es b' d Hes Hb' Hr') as (k0 & ek0 & Ho0 & Hk0 & H0 & Hbr).
    destruct (c_one s es b' d Hes Hb' Hr') as [z Hz].
    destruct (entry_one _ d z k0 ek0 Hz Hk0 H0) as [-> ->].
    destruct (decide (d = c)) as [->|Hdc].
    - left. destruct (c_offered t e b c He Hb Hr) as (kt & ekt & Hot & Hkt & Ht0 & _).
      destruct (entry_one _ c x kt ekt Hx Hkt Ht0) as [-> ->].
      rewrite Hy in Hz. injection Hz as <-.
      destruct (meet_step t e s es (c, false) (c, false) x y (λ H, Hst (eq_sym H)) He Hes)
        as (L & q' & Hst' & HtL & _); try done.
      + intros c' d' Hl. rewrite Hb in Hl. injection Hl as ->. by simpl in Hr.
      + intros c' d' Hl. rewrite Hb' in Hl. injection Hl as ->. by simpl in Hr'.
      + by exists L, q'.
    - right. rewrite Hz, Hx. simpl.
      assert (¬ offered_t (ac_env a s) es (c, false)) as Hno.
      { intros Ho. apply Hdc. symmetry. exact (offered_rchan _ _ _ b' d Ho Hb' Hr'). }
      destruct (Hbr (d, false) z Ho0 Hk0) as [Hb1 _]. specialize (Hb1 (c, false) y Hsy Hno).
      unfold entry_head in Hb1. by rewrite Hd, pt_dual_dual in Hb1.
  Qed.
End conf.

(** ** The counter of the partner entry *)

Definition holder_fuel (a : aconf) (t : nat) (c : chan) : nat :=
  match list_find (λ se : nat * expr, se.1 ≠ t ∧ c ∈ dom (ac_env a se.1)) (map_to_list (ac_q a).2) with
  | Some (_, (s, _)) => ac_fuel a s c
  | None => 0
  end.

Lemma holder_fuel_spec W a t e c s es :
  LFconf 1 W ∅ a → (ac_q a).2 !! t = Some e → c ∈ dom (ac_env a t) →
  (ac_q a).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env a s) → holder_fuel a t c = ac_fuel a s c.
Proof.
  intros Hc He Ht Hes Hst Hs. unfold holder_fuel.
  destruct (list_find _ _) as [[i [s0 e0]]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hl & [Hs0t Hs0c] & _). simpl in *.
    apply list_elem_of_lookup_2, elem_of_map_to_list in Hl.
    by rewrite (c_uniq W a Hc t e s0 e0 s es c He Hl Hes Ht Hs0c Hs Hs0t Hst).
  - apply list_find_None in Hf. rewrite Forall_forall in Hf.
    exfalso. apply (Hf (s, es)); [by apply elem_of_map_to_list|]. done.
Qed.

Lemma holder_fuel_none a t c :
  (∀ s es, (ac_q a).2 !! s = Some es → s ≠ t → c ∉ dom (ac_env a s)) → holder_fuel a t c = 0.
Proof.
  intros H. unfold holder_fuel. destruct (list_find _ _) as [[i [s0 e0]]|] eqn:Hf; [|done].
  apply list_find_Some in Hf as (Hl & [Hs0t Hs0c] & _). simpl in *.
  apply list_elem_of_lookup_2, elem_of_map_to_list in Hl. by destruct (H s0 e0 Hl Hs0t).
Qed.

Definition rchan_of (a : aconf) (t : nat) : option chan :=
  match (ac_q a).2 !! t with
  | Some e => match act e with Some b => rchan b | None => None end
  | None => None
  end.

Definition partner_fuel (a : aconf) (t : nat) : nat :=
  match rchan_of a t with Some c => holder_fuel a t c | None => 0 end.

Definition rank_pt (a : aconf) (t : nat) : point :=
  match rchan_of a t with Some c => ent_pt (ac_env a t !! c) | None => pbot end.

Lemma rchan_of_eq a t e b c :
  (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c → rchan_of a t = Some c.
Proof. intros He Hb Hr. unfold rchan_of. by rewrite He, Hb. Qed.
