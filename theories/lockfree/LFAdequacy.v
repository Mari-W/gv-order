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
  #[local] Set Default Proof Using "All".
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

Lemma holder_fuel_spec W (HW : world_wf W) (Hwf : well_founded (w_lt W)) a t e c s es :
  LFconf 1 W ∅ a → (ac_q a).2 !! t = Some e → c ∈ dom (ac_env a t) →
  (ac_q a).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env a s) → holder_fuel a t c = ac_fuel a s c.
Proof.
  intros Hc He Ht Hes Hst Hs. unfold holder_fuel.
  destruct (list_find _ _) as [[i [s0 e0]]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hl & [Hs0t Hs0c] & _). simpl in *.
    apply list_elem_of_lookup_2, elem_of_map_to_list in Hl.
    by rewrite (c_uniq W HW Hwf a Hc t e s0 e0 s es c He Hl Hes Ht Hs0c Hs Hs0t Hst).
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

(** ** What an update does, step by step *)

Lemma pick1_singleton i : pick1 {[i]} = Some i.
Proof. unfold pick1. by rewrite elements_singleton. Qed.

Lemma elements_pair (i j : nat) : i ≠ j → elements ({[i; j]} : gset nat) = [i; j] ∨ elements ({[i; j]} : gset nat) = [j; i].
Proof.
  intros Hij. apply Permutation_length_2_inv. symmetry.
  rewrite elements_union_singleton by set_solver. by rewrite elements_singleton.
Qed.

Lemma pick1_pair i j : i ≠ j → pick1 {[i; j]} = None.
Proof. intros Hij. unfold pick1. by destruct (elements_pair i j Hij) as [->| ->]. Qed.

Lemma pick2_pair i j : i ≠ j → pick2 {[i; j]} = Some (i, j) ∨ pick2 {[i; j]} = Some (j, i).
Proof. intros Hij. unfold pick2. destruct (elements_pair i j Hij) as [->| ->]; auto. Qed.

Lemma pair_set_eq (a b c d : chan) : ({[a; b]} : gset chan) = {[c; d]} → (a = c ∧ b = d) ∨ (a = d ∧ b = c).
Proof.
  intros H.
  assert (a ∈ ({[c; d]} : gset chan)) as Ha by (rewrite <-H; set_solver).
  assert (b ∈ ({[c; d]} : gset chan)) as Hb by (rewrite <-H; set_solver).
  assert (c ∈ ({[a; b]} : gset chan)) as Hc by (rewrite H; set_solver).
  assert (d ∈ ({[a; b]} : gset chan)) as Hd by (rewrite H; set_solver).
  set_unfold. naive_solver.
Qed.

Definition keep (a a' : aconf) (u : nat) : Prop :=
  ac_env a' u = ac_env a u ∧ ∀ x, ac_fuel a' u x = ac_fuel a u x.

Definition msg_fuel (N : nat) (A : nat → tenv) (Φ : nat → chan → nat) (s t : nat) (c : chan)
    (give : tenv) (x : chan) : nat :=
  if decide (x = c) then N
  else if decide (x ∈ dom give) then
    (if decide (x ∈ dom (A t)) then min (pred (Φ t x)) (pred (Φ s x)) else pred (Φ s x))
  else pred (Φ t x).

Section cases.
  Context (ω : oracle) (N : nat) (a : aconf) (L : gset nat) (q' : config).
  Context (Hst : istep (ac_q a) L q').
  Abbreviation C := (ac_q a).1.
  Abbreviation M := (ac_q a).2.
  Abbreviation A := (ac_env a).
  Abbreviation Φ := (ac_fuel a).
  Abbreviation a' := (aupd ω N a L q').

  Lemma act_of e α e' : tstep e α e' → ∃ b, act e = Some b ∧ offers b α.
  Proof. apply act_step. Qed.

  Lemma aupd_cases :
    (∃ i e e', L = {[i]} ∧ M !! i = Some e ∧ act e = Some ABeta ∧ tstep e LBeta e' ∧
       q' = (C, <[i := e']> M) ∧ ∀ u, keep a a' u) ∨
    (∃ i e c e', L = {[i]} ∧ M !! i = Some e ∧ act e = Some ANew ∧ tstep e (LNew c) e' ∧
       (c ∉ C) ∧ q' = (C ∪ {[c]}, <[i := e']> M) ∧ (∀ u, u ≠ i → keep a a' u) ∧
       ac_env a' i = <[c := Both (pl_s (or_pick ω (A i) e), pl_pt (or_pick ω (A i) e))
                             (pl_s' (or_pick ω (A i) e), pt_dual (pl_pt (or_pick ω (A i) e)))]> (A i) ∧
       ∀ x, ac_fuel a' i x = if decide (x = c) then N else Φ i x) ∨
    (∃ i j e v e', L = {[i]} ∧ M !! i = Some e ∧ act e = Some (ASpawn v) ∧ tstep e (LSpawn v) e' ∧
       M !! j = None ∧ q' = (C, <[j := App v EUnit]> (<[i := e']> M)) ∧
       (∀ u, u ≠ i → u ≠ j → keep a a' u) ∧
       ac_env a' i = tenv_minus (A i) (pl_give (or_pick ω (A i) e)) ∧
       ac_env a' j = pl_give (or_pick ω (A i) e) ∧
       (∀ x, ac_fuel a' i x = Φ i x) ∧ (∀ x, ac_fuel a' j x = pred (Φ i x))) ∨
    (∃ i e r o e', L = {[i]} ∧ M !! i = Some e ∧ (act e = Some (ALink r o) ∨ act e = Some (ALink o r)) ∧
       tstep e (LSess (SLink {[r; o]})) e' ∧ r ∈ C ∧
       q' = (C ∖ {[r]}, chsubst r o <$> <[i := e']> M) ∧
       ac_env a' i = delete r (delete o (A i)) ∧ (∀ u, u ≠ i → ac_env a' u = tenv_rename r o (A u)) ∧
       ∀ u x, ac_fuel a' u x = link_fuel A Φ i r o u x) ∨
    (∃ s t c v es es' et et', s ≠ t ∧ L = {[s; t]} ∧ M !! s = Some es ∧ M !! t = Some et ∧
       act es = Some (ASend c v) ∧ act et = Some (ARecv c) ∧
       tstep es (LSess (SSend c v)) es' ∧ tstep et (LSess (SRecv c v)) et' ∧
       q' = (C, <[t := et']> (<[s := es']> M)) ∧ (∀ u, u ≠ s → u ≠ t → keep a a' u) ∧
       ac_env a' s = step_entry snd_next c (tenv_minus (A s) (pl_give (or_pick ω (A s) es))) ∧
       ac_env a' t = tenv_union (step_entry rcv_next c (A t)) (pl_give (or_pick ω (A s) es)) ∧
       (∀ x, ac_fuel a' s x = tick N c (Φ s) x) ∧
       (∀ x, ac_fuel a' t x = msg_fuel N A Φ s t c (pl_give (or_pick ω (A s) es)) x)) ∨
    (∃ s t c es es' et et', s ≠ t ∧ L = {[s; t]} ∧ M !! s = Some es ∧ M !! t = Some et ∧
       act es = Some (AClos c) ∧ act et = Some (AClos c) ∧
       tstep es (LSess (SClos c)) es' ∧ tstep et (LSess (SClos c)) et' ∧ c ∈ C ∧
       q' = (C ∖ {[c]}, <[t := et']> (<[s := es']> M)) ∧ (∀ u, u ≠ s → u ≠ t → keep a a' u) ∧
       ac_env a' s = delete c (A s) ∧ ac_env a' t = delete c (A t) ∧
       (∀ x, ac_fuel a' s x = tick N c (Φ s) x) ∧ (∀ x, ac_fuel a' t x = tick N c (Φ t) x)) ∨
    (∃ s t c b es es' et et', s ≠ t ∧ L = {[s; t]} ∧ M !! s = Some es ∧ M !! t = Some et ∧
       act es = Some (ASel c b) ∧ act et = Some (ABra c) ∧
       tstep es (LSess (SSel c b)) es' ∧ tstep et (LSess (SBra c b)) et' ∧
       q' = (C, <[t := et']> (<[s := es']> M)) ∧ (∀ u, u ≠ s → u ≠ t → keep a a' u) ∧
       ac_env a' s = step_entry (sel_next b) c (A s) ∧ ac_env a' t = step_entry (bra_next b) c (A t) ∧
       (∀ x, ac_fuel a' s x = tick N c (Φ s) x) ∧ (∀ x, ac_fuel a' t x = tick N c (Φ t) x)).
  Proof.
    destruct a as [[C0 M0] A0 Φ0]. simpl in *. unfold keep, aupd. simpl.
    remember (C0, M0) as q0 eqn:Hq0.
    destruct Hst as [C M i e e' Hi Hs|C M i e c e' Hi Hs HC Hc|C M i j e v e' Hi Hs Hj
      |C M i j c v e e' f f' Hij Hi Hj He Hf|C M i j c e e' f f' Hij Hi Hj He Hf HC
      |C M i j c b e e' f f' Hij Hi Hj He Hf|C M i e c d e' Hi Hs HC]; injection Hq0 as <- <-.
    - (* β *)
      destruct (act_of _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      left. exists i, e, e'. split_and!; try done. rewrite pick1_singleton. unfold upd1.
      rewrite Hi, Hb. simpl. done.
    - (* new *)
      destruct (act_of _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      right; left. exists i, e, c, e'. rewrite pick1_singleton. unfold upd1. rewrite Hi, Hb. simpl.
      assert ((C ∪ {[c]}) ∖ C = {[c]}) as -> by set_solver.
      rewrite elements_singleton. simpl. unfold eupd, fupd.
      split_and!; try done.
      + intros u Hu. by rewrite !decide_False.
      + by rewrite decide_True.
      + intros x. by rewrite decide_True.
    - (* spawn *)
      destruct (act_of _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done. subst v0.
      assert (i ≠ j) as Hij by (intros ->; congruence).
      right; right; left. exists i, j, e, v, e'. rewrite pick1_singleton. unfold upd1. rewrite Hi, Hb. simpl.
      assert (dom (<[j:=App v EUnit]> (<[i:=e']> M)) ∖ dom M = {[j]}) as ->.
      { rewrite !dom_insert_L. apply elem_of_dom_2 in Hi. apply not_elem_of_dom in Hj. set_solver. }
      rewrite elements_singleton. simpl. unfold eupd, fupd.
      split_and!; try done.
      + intros u Hu Hu'. by rewrite !decide_False.
      + rewrite decide_False by done. by rewrite decide_True.
      + by rewrite decide_True.
      + intros x. by rewrite decide_False.
      + intros x. by rewrite decide_True.
    - (* message *)
      destruct (act_of _ _ _ He) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      destruct Ho as [-> ->].
      destruct (act_of _ _ _ Hf) as (b' & Hb' & Ho'). destruct b'; simpl in Ho'; try done.
      destruct Ho' as [-> _].
      do 4 right; left. exists i, j, c, v, e, e', f, f'.
      rewrite pick1_pair by done. unfold eupd, fupd, sync_msg, msg_fuel.
      split_and!; try done; destruct (pick2_pair i j Hij) as [->| ->]; unfold upd2;
        rewrite ?Hi, ?Hj, ?Hb, ?Hb'; simpl; unfold eupd, fupd.
      all: try (intros u Hu Hu'; by rewrite !decide_False).
      all: try (by rewrite decide_False, decide_True by done).
      all: try (by rewrite decide_True).
      all: try (intros x; by rewrite decide_False, decide_True by done).
      all: try (intros x; by rewrite decide_True).
    - (* close *)
      destruct (act_of _ _ _ He) as (b & Hb & Ho). destruct b; simpl in Ho; try done. subst c0.
      destruct (act_of _ _ _ Hf) as (b' & Hb' & Ho'). destruct b'; simpl in Ho'; try done. subst c0.
      do 5 right; left. exists i, j, c, e, e', f, f'.
      rewrite pick1_pair by done.
      split_and!; try done; destruct (pick2_pair i j Hij) as [->| ->]; unfold upd2;
        rewrite ?Hi, ?Hj, ?Hb, ?Hb'; simpl; unfold eupd, fupd.
      all: try (intros u Hu Hu'; by rewrite !decide_False).
      all: try (by rewrite decide_False, decide_True by done).
      all: try (by rewrite decide_True).
      all: try (intros x; by rewrite decide_False, decide_True by done).
      all: try (intros x; by rewrite decide_True).
    - (* choice *)
      destruct (act_of _ _ _ He) as (bb & Hb & Ho). destruct bb; simpl in Ho; try done.
      destruct Ho as [-> ->].
      destruct (act_of _ _ _ Hf) as (bb' & Hb' & Ho'). destruct bb'; simpl in Ho'; try done. subst c0.
      do 6 right. exists i, j, c, b, e, e', f, f'.
      rewrite pick1_pair by done.
      split_and!; try done; destruct (pick2_pair i j Hij) as [->| ->]; unfold upd2;
        rewrite ?Hi, ?Hj, ?Hb, ?Hb'; simpl; unfold eupd, fupd.
      all: try (intros u Hu Hu'; by rewrite !decide_False).
      all: try (by rewrite decide_False, decide_True by done).
      all: try (by rewrite decide_True).
      all: try (intros x; by rewrite decide_False, decide_True by done).
      all: try (intros x; by rewrite decide_True).
    - (* link *)
      destruct (act_of _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      rename c0 into c1, d0 into d1.
      do 3 right; left. exists i, e, c, d, e'.
      assert ((if bool_decide (c1 ∈ C ∧ c1 ∉ C ∖ {[c]}) then c1 else d1) = c ∧
              (if bool_decide (c1 ∈ C ∧ c1 ∉ C ∖ {[c]}) then d1 else c1) = d) as [Hr Ho2].
      { destruct (pair_set_eq c d c1 d1 Ho) as [[<- <-]|[<- <-]].
        - rewrite bool_decide_true by set_solver. done.
        - destruct (decide (d = c)) as [->|Hdc]; [by case_bool_decide|].
          rewrite bool_decide_false by set_solver. done. }
      rewrite pick1_singleton. unfold upd1. rewrite Hi, Hb. simpl. rewrite Hr, Ho2.
      split_and!; try done.
      + destruct (pair_set_eq c d c1 d1 Ho) as [[<- <-]|[<- <-]]; auto.
      + by rewrite decide_True.
      + intros u Hu. by rewrite decide_False.
  Qed.
End cases.

(** ** Domains under the operations of an update *)

Lemma dom_step_entry f c (Θ : tenv) x : x ∈ dom (step_entry f c Θ) ↔ x ∈ dom Θ.
Proof.
  unfold step_entry. destruct (Θ !! c) as [[]|] eqn:Hc; try done.
  rewrite dom_insert_L. apply elem_of_dom_2 in Hc. set_solver.
Qed.

Lemma lookup_tenv_minus (Θ Θ1 : tenv) x :
  tenv_minus Θ Θ1 !! x = Θ !! x ≫= λ o, match Θ1 !! x with None => Some o | Some o1 => ends_minus o o1 end.
Proof. unfold tenv_minus. by rewrite map_lookup_imap. Qed.

Lemma dom_tenv_minus_keep (Θ Θ1 : tenv) x : x ∉ dom Θ1 → (x ∈ dom (tenv_minus Θ Θ1) ↔ x ∈ dom Θ).
Proof.
  intros Hx. apply not_elem_of_dom in Hx. rewrite !elem_of_dom, lookup_tenv_minus, Hx.
  destruct (Θ !! x); simpl; split; intros [? ?]; eauto; discriminate.
Qed.

Lemma dom_tenv_minus_sub (Θ Θ1 : tenv) x : x ∈ dom (tenv_minus Θ Θ1) → x ∈ dom Θ.
Proof.
  rewrite !elem_of_dom, lookup_tenv_minus. destruct (Θ !! x); simpl; [eauto|]. by intros [? ?].
Qed.

Lemma dom_tenv_minus_one (Θ Θ1 : tenv) x y :
  Θ !! x = Some (One y) → x ∈ dom Θ1 → x ∉ dom (tenv_minus Θ Θ1).
Proof.
  intros Hx Hx1. apply elem_of_dom in Hx1 as [o1 Ho1].
  rewrite not_elem_of_dom, lookup_tenv_minus, Hx, Ho1. simpl. done.
Qed.

Lemma dom_tenv_union (Θ Θ1 : tenv) x : x ∈ dom (tenv_union Θ Θ1) ↔ x ∈ dom Θ ∨ x ∈ dom Θ1.
Proof.
  unfold tenv_union. rewrite !elem_of_dom, lookup_union_with.
  destruct (Θ !! x), (Θ1 !! x); simpl; split; try (intros [[? ?]|[? ?]]); try intros [? ?];
    try discriminate; eauto.
Qed.

Lemma lookup_tenv_rename_ne r o (Θ : tenv) x : x ≠ r → x ≠ o → tenv_rename r o Θ !! x = Θ !! x.
Proof.
  intros Hr Ho. unfold tenv_rename. destruct (Θ !! r) as [y|] eqn:Hy; [|done].
  unfold tenv_union. rewrite lookup_union_with, lookup_delete_ne, lookup_singleton_ne by done.
  by destruct (Θ !! x).
Qed.

Lemma dom_tenv_rename_o r o (Θ : tenv) : o ∈ dom (tenv_rename r o Θ) → r ∈ dom Θ ∨ o ∈ dom Θ.
Proof.
  unfold tenv_rename. destruct (Θ !! r) as [y|] eqn:Hy; [|by right].
  left. by apply elem_of_dom_2 in Hy.
Qed.

Lemma dom_tenv_rename_ne r o (Θ : tenv) x : x ≠ r → x ≠ o → (x ∈ dom (tenv_rename r o Θ) ↔ x ∈ dom Θ).
Proof. intros Hr Ho. by rewrite !elem_of_dom, lookup_tenv_rename_ne. Qed.

Lemma dom_tenv_rename_sub r o (Θ : tenv) x : x ∈ dom (tenv_rename r o Θ) → x = o ∨ x ∈ dom Θ.
Proof.
  destruct (decide (x = o)) as [->|Ho]; [by left|]. intros H. right.
  destruct (decide (x = r)) as [->|Hr].
  - unfold tenv_rename in H. destruct (Θ !! r) as [y|] eqn:Hy; [|exact H].
    by apply elem_of_dom_2 in Hy.
  - by rewrite dom_tenv_rename_ne in H.
Qed.

(** A counter at 0 forces an action on its channel. *)
Lemma fuel_pos W (HW : world_wf W) (Hwf : well_founded (w_lt W)) a s es b c :
  LFconf 1 W ∅ a → (ac_q a).2 !! s = Some es → c ∈ dom (ac_env a s) → act es = Some b →
  (is_admin b ∨ ∃ d, rchan b = Some d ∧ d ≠ c) → 0 < ac_fuel a s c.
Proof.
  intros Hc Hes Hcs Hb Hor. destruct (decide (ac_fuel a s c = 0)) as [H0|H0]; [|lia].
  destruct (c_thread W HW Hwf a Hc s es Hes) as (_ & _ & _ & Hf).
  destruct (Hf c Hcs H0) as (b' & S & Hb' & Hna & HS & HcS). rewrite Hb in Hb'. injection Hb' as <-.
  destruct Hor as [Had|(d & Hr & Hd)]; [done|].
  rewrite (rchan_asubjs b d Hr) in HS. injection HS as <-. set_solver.
Qed.

Lemma holder_fuel_lt a t c X :
  0 < X → (∀ u eu, (ac_q a).2 !! u = Some eu → u ≠ t → c ∈ dom (ac_env a u) → ac_fuel a u c < X) →
  holder_fuel a t c < X.
Proof.
  intros HX H. unfold holder_fuel. destruct (list_find _ _) as [[i [s0 e0]]|] eqn:Hf; [|done].
  apply list_find_Some in Hf as (Hl & [Hs0t Hs0c] & _). simpl in *.
  apply list_elem_of_lookup_2, elem_of_map_to_list in Hl. by apply (H s0 e0).
Qed.

Lemma c_waits_holder W (HW : world_wf W) (Hwf : well_founded (w_lt W)) a t e b c s es :
  LFconf 1 W ∅ a → (ac_q a).2 !! t = Some e → act e = Some b → rchan b = Some c →
  (ac_q a).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env a s) →
  ∀ u, waits (ac_q a) t u ↔ u = s.
Proof.
  intros Hc He Hb Hr Hes Hst Hcs u. rewrite (c_waits W HW Hwf a Hc t e b c u He Hb Hr).
  assert (c ∈ dom (ac_env a t)) as Hct.
  { rewrite (c_dom W HW Hwf a Hc t e He). by eapply (rchan_fchans W HW Hwf a Hc). }
  split.
  - intros (Hut & eu & Heu & Hcu). by apply (c_uniq W HW Hwf a Hc t e u eu s es c).
  - intros ->. eauto.
Qed.

(** ** A synchronization has a partner on the same channel *)
Lemma sync_partner q L q' p e b c :
  istep q L q' → p ∈ L → q.2 !! p = Some e → act e = Some b → rchan b = Some c →
  ∃ u eu bu, u ∈ L ∧ u ≠ p ∧ q.2 !! u = Some eu ∧ act eu = Some bu ∧ rchan bu = Some c.
Proof.
  intros Hst HpL He Hb Hr.
  destruct Hst as [C M i e0 e' Hi Hs|C M i e0 c0 e' Hi Hs HC Hc|C M i j e0 v e' Hi Hs Hj
    |C M i j c0 v e0 e' f f' Hij Hi Hj He0 Hf|C M i j c0 e0 e' f f' Hij Hi Hj He0 Hf HC
    |C M i j c0 b0 e0 e' f f' Hij Hi Hj He0 Hf|C M i e0 c0 d e' Hi Hs HC]; simpl in *.
  all: try (apply elem_of_singleton in HpL; subst p; rewrite He in Hi; injection Hi as <-;
            destruct (act_step _ _ _ Hs) as (b' & Hb' & Ho); rewrite Hb in Hb'; injection Hb' as <-;
            destruct b; simpl in Ho, Hr; done).
  all: destruct (act_step _ _ _ He0) as (b1 & Hb1 & Ho1); destruct (act_step _ _ _ Hf) as (b2 & Hb2 & Ho2).
  all: apply elem_of_union in HpL as [HpL|HpL]; apply elem_of_singleton in HpL; subst p.
  all: try (rewrite He in Hi; injection Hi as <-; rewrite Hb in Hb1; injection Hb1 as <-).
  all: try (rewrite He in Hj; injection Hj as <-; rewrite Hb in Hb2; injection Hb2 as <-).
  - exists j, f, b2. destruct b, b2; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|done|done|done|done].
  - exists i, e0, b1. destruct b1, b; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|congruence|done|done|done].
  - exists j, f, b2. destruct b, b2; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|done|done|done|done].
  - exists i, e0, b1. destruct b1, b; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|congruence|done|done|done].
  - exists j, f, b2. destruct b, b2; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|done|done|done|done].
  - exists i, e0, b1. destruct b1, b; simpl in Ho1, Ho2, Hr; destruct_and?; simplify_eq; try done.
    split_and!; [set_solver|congruence|done|done|done].
Qed.

(** Threads outside a step keep their term up to one renaming, which
    fixes every channel the participants do not mention. *)
Lemma nonpart_terms q L q' :
  istep q L q' → ∃ g, (∀ u eu, u ∉ L → q.2 !! u = Some eu → q'.2 !! u = Some (emap g eu)) ∧
    (∀ c, (∀ u eu, u ∈ L → q.2 !! u = Some eu → c ∉ fchans eu) → g c = c).
Proof.
  intros Hst. destruct Hst as [C M i e e' Hi Hs|C M i e c0 e' Hi Hs HC Hc|C M i j e v e' Hi Hs Hj
    |C M i j c0 v e e' f f' Hij Hi Hj He Hf|C M i j c0 e e' f f' Hij Hi Hj He Hf HC
    |C M i j c0 b0 e e' f f' Hij Hi Hj He Hf|C M i e c0 d e' Hi Hs HC]; simpl.
  1-6: exists id; (split; [|done]); intros u eu Hu Heu; rewrite emap_id.
  - rewrite lookup_insert_ne; [done|set_solver].
  - rewrite lookup_insert_ne; [done|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|]. intros ->. by rewrite Hj in Heu.
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - rewrite !lookup_insert_ne; [done|set_solver|set_solver].
  - exists (csub c0 d). split.
    + intros u eu Hu Heu. rewrite lookup_fmap, lookup_insert_ne by set_solver. rewrite Heu. simpl.
      by rewrite chsubst_emap.
    + intros c Hc. specialize (Hc i e ltac:(set_solver) Hi).
      destruct (act_step _ _ _ Hs) as (b & Hb & Ho). destruct b; simpl in Ho; try done.
      pose proof (act_asubjs_fchans e (ALink c1 d0) _ Hb eq_refl) as Hsub. rewrite <-Ho in Hsub.
      unfold csub. case_decide; [subst; set_solver|done].
Qed.

(** The holder of the partner end holds one end of the channel. *)
Lemma holder_one W (HW : world_wf W) (Hwf : well_founded (w_lt W)) a t e x c s es :
  LFconf 1 W ∅ a → (ac_q a).2 !! t = Some e → ac_env a t !! c = Some (One x) →
  (ac_q a).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env a s) → ∃ y, ac_env a s !! c = Some (One y).
Proof.
  intros Hc He Hx Hes Hst Hcs.
  apply elem_of_dom in Hcs as [[y|y1 y2] Hy]; [by exists y|exfalso].
  assert (tenv_entry (ac_env a s) (c, false) = Some y1) as H1 by (unfold tenv_entry; simpl; by rewrite Hy).
  assert (tenv_entry (ac_env a s) (c, true) = Some y2) as H2 by (unfold tenv_entry; simpl; by rewrite Hy).
  assert (tenv_entry (ac_env a t) (c, false) = Some x) as H3 by (unfold tenv_entry; simpl; by rewrite Hx).
  destruct (c_three W HW Hwf a Hc s s t es es e (c, false) (c, true) (c, false) y1 y2 x Hes Hes He
    H1 H2 H3 eq_refl eq_refl) as [H|[H|H]]; simplify_eq.
Qed.

(** The holder exists. *)
Lemma holder_exists W (HW : world_wf W) (Hwf : well_founded (w_lt W)) a t e x c :
  LFconf 1 W ∅ a → (ac_q a).2 !! t = Some e → ac_env a t !! c = Some (One x) →
  ∃ s es, (ac_q a).2 !! s = Some es ∧ s ≠ t ∧ c ∈ dom (ac_env a s).
Proof.
  intros Hc He Hx.
  assert (tenv_entry (ac_env a t) (c, false) = Some x) as H3 by (unfold tenv_entry; simpl; by rewrite Hx).
  destruct (c_pair W HW Hwf a Hc t e (c, false) x He H3) as (s & es & k' & ek' & Hes & Hk' & H1 & Hne & _).
  exists s, es. split_and!; [done| |].
  - intros ->. destruct k' as [c' []]; simpl in H1; subst c'; [|done].
    unfold tenv_entry in Hk'. simpl in Hk'. by rewrite Hx in Hk'.
  - simpl in H1. rewrite <-H1. by eapply entry_dom.
Qed.

Lemma rank_pt_eq a a' t :
  (ac_q a').2 !! t = (ac_q a).2 !! t → ac_env a' t = ac_env a t → rank_pt a' t = rank_pt a t.
Proof. intros Hq HA. unfold rank_pt, rchan_of. by rewrite Hq, HA. Qed.

(** ** The annotated run *)

Section run.
  #[local] Set Default Proof Using "All".
  Context (ω : oracle) (N : nat) (W : world) (HW : world_wf W) (Hwf : well_founded (w_lt W)).
  Context (r : nat → config) (l : nat → gset nat) (Hmax : maximal r l).
  Context (HL : ∀ a, areach ω N (ainit ω N (r 0)) a → LFconf 1 W ∅ a).

  Fixpoint arun (k : nat) : aconf :=
    match k with 0 => ainit ω N (r 0) | S k' => aupd ω N (arun k') (l k') (r (S k')) end.

  Lemma arun_q k : ac_q (arun k) = r k.
  Proof. by destruct k. Qed.

  Lemma arun_stuck k : r (S k) = r k → l k = ∅ → arun (S k) = arun k.
  Proof.
    intros Hr Hl. simpl. rewrite Hl, Hr. unfold aupd, pick1, pick2. rewrite elements_empty.
    simpl. pose proof (arun_q k) as Hq. destruct (arun k) as [q A Φ]. simpl in *. by subst.
  Qed.

  Lemma arun_reach k : areach ω N (ainit ω N (r 0)) (arun k).
  Proof.
    induction k as [|k IH]; [done|].
    destruct (Hmax k) as [Hs|(_ & Hr & Hl)].
    - eapply rtc_r; [exact IH|]. exists (l k), (r (S k)). rewrite arun_q. by split.
    - by rewrite arun_stuck.
  Qed.

  Lemma arun_conf k : LFconf 1 W ∅ (arun k).
  Proof. apply HL, arun_reach. Qed.

  Definition fu (k t : nat) : nat := partner_fuel (arun k) t.
  Definition we (k t : nat) : point := rank_pt (arun k) t.

  Lemma npend_arun k t : npend (r k) t →
    ∃ e b c, (ac_q (arun k)).2 !! t = Some e ∧ act e = Some b ∧ rchan b = Some c ∧ ¬ is_admin b.
  Proof. rewrite <-(arun_q k). apply npend_rchan. Qed.

  (** Uniqueness of the holder, and the rank clause. *)
  Lemma run_uniq k t s s' : npend (r k) t → waits (r k) t s → waits (r k) t s' → s = s'.
  Proof.
    intros Hp Hw Hw'. destruct (npend_arun k t Hp) as (e & b & c & He & Hb & Hr & _).
    rewrite <-(arun_q k) in Hw, Hw'.
    destruct (proj1 (c_waits W HW Hwf _ (arun_conf k) t e b c s He Hb Hr) Hw) as (Hst & es & Hes & Hcs).
    symmetry. by apply (c_waits_holder W HW Hwf _ t e b c s es (arun_conf k) He Hb Hr Hes Hst Hcs s').
  Qed.

  Lemma run_rank k t s : npend (r k) t → waits (r k) t s → npend (r k) s →
    enabled (r k) t ∨ w_lt W (we k s) (we k t).
  Proof.
    intros Hp Hw Hps. destruct (npend_arun k t Hp) as (e & b & c & He & Hb & Hr & _).
    destruct (npend_arun k s Hps) as (es & b' & d & Hes & Hb' & Hr' & _).
    rewrite <-(arun_q k) in Hw |- *.
    destruct (proj1 (c_waits W HW Hwf _ (arun_conf k) t e b c s He Hb Hr) Hw) as (Hst & es0 & Hes0 & Hcs).
    unfold we, rank_pt. rewrite (rchan_of_eq _ t e b c He Hb Hr), (rchan_of_eq _ s es b' d Hes Hb' Hr').
    exact (c_rank W HW Hwf _ (arun_conf k) t e b c s es b' d He Hb Hr Hes Hb' Hr' Hst Hcs).
  Qed.

  (** An enabled blocked thread stays enabled while it does not step:
      its partner offers the dual action and cannot step without it. *)
  Lemma run_pers k t : npend (r k) t → enabled (r k) t → t ∉ l k → enabled (r (S k)) t.
  Proof.
    intros Hp Hen HtL. destruct (npend_arun k t Hp) as (e & b & c & He & Hb & Hr & Hna).
    destruct (Hmax k) as [Hst|(_ & Heq & _)]; [|by rewrite Heq].
    pose proof (arun_conf k) as Hc. pose proof (arun_conf (S k)) as Hc'.
    rewrite <-(arun_q k) in Hen, Hst. rewrite <-(arun_q (S k)).
    destruct Hen as (L0 & q0 & Hst0 & HtL0).
    destruct (sync_partner _ L0 q0 t e b c Hst0 HtL0 He Hb Hr) as (p & ep & bp & _ & Hpt & Hep & Hbp & Hrp).
    assert (c ∈ dom (ac_env (arun k) t)) as Hct.
    { rewrite (c_dom W HW Hwf _ Hc t e He). by eapply (rchan_fchans W HW Hwf _ Hc). }
    assert (c ∈ dom (ac_env (arun k) p)) as Hcp.
    { rewrite (c_dom W HW Hwf _ Hc p ep Hep). by eapply (rchan_fchans W HW Hwf _ Hc). }
    (* no participant of the actual step mentions c *)
    assert (∀ u eu, u ∈ l k → (ac_q (arun k)).2 !! u = Some eu → c ∉ fchans eu) as Hnm.
    { intros u eu Hu Heu Hcu. rewrite <-(c_dom W HW Hwf _ Hc u eu Heu) in Hcu.
      assert (u ≠ t) as Hut by (intros ->; done).
      destruct (decide (u = p)) as [->|Hup].
      - destruct (sync_partner _ (l k) (r (S k)) p ep bp c Hst Hu Hep Hbp Hrp)
          as (u' & eu' & bu' & Hu'L & Hu'p & Heu' & Hbu' & Hru').
        assert (c ∈ dom (ac_env (arun k) u')) as Hcu'.
        { rewrite (c_dom W HW Hwf _ Hc u' eu' Heu'). exact (rchan_fchans W HW Hwf _ Hc eu' bu' c Hbu' Hru'). }
        assert (u' ≠ t) by (intros ->; done).
        by apply Hu'p, (c_uniq W HW Hwf _ Hc t e u' eu' p ep c).
      - by apply Hup, (c_uniq W HW Hwf _ Hc t e u eu p ep c). }
    assert (p ∉ l k) as HpL.
    { intros HpL. by apply (Hnm p ep HpL Hep), (rchan_fchans W HW Hwf _ Hc ep bp c). }
    destruct (nonpart_terms _ _ _ Hst) as (g & Hg & Hgc).
    pose proof (Hgc c Hnm) as Hgc'.
    pose proof (Hg t e HtL He) as He'. pose proof (Hg p ep HpL Hep) as Hep'.
    rewrite <-(arun_q (S k)) in He', Hep'.
    assert (act (emap g e) = Some (amap g b)) as Hb2 by (by rewrite act_emap, Hb).
    assert (act (emap g ep) = Some (amap g bp)) as Hbp2 by (by rewrite act_emap, Hbp).
    pose proof (rchan_amap g b c Hr) as Hr2. pose proof (rchan_amap g bp c Hrp) as Hrp2.
    rewrite Hgc' in Hr2, Hrp2.
    destruct (c_offered W HW Hwf _ Hc' t _ _ c He' Hb2 Hr2) as (kt & ekt & Hot & Hkt & Ht0 & _).
    destruct (c_offered W HW Hwf _ Hc' p _ _ c Hep' Hbp2 Hrp2) as (kp & ekp & Hop & Hkp & Hp0 & _).
    destruct (c_one W HW Hwf _ Hc' t _ _ c He' Hb2 Hr2) as [x Hx].
    destruct (c_one W HW Hwf _ Hc' p _ _ c Hep' Hbp2 Hrp2) as [y Hy].
    destruct (entry_one _ c x kt ekt Hx Hkt Ht0) as [-> ->].
    destruct (entry_one _ c y kp ekp Hy Hkp Hp0) as [-> ->].
    destruct (c_partner_of W HW Hwf _ Hc' t _ (c, false) x p _ (c, false) y He' Hkt Hep' Hkp)
      as [_ Hsd]; [done|congruence|].
    destruct (meet_step W HW Hwf _ Hc' t _ p _ (c, false) (c, false) x y (λ H, Hpt (eq_sym H))
      He' Hep') as (L & q' & Hst' & HtL' & _); try done.
    - intros c' d' Hl. rewrite Hb2 in Hl. injection Hl as Hl. rewrite Hl in Hr2. done.
    - intros c' d' Hl. rewrite Hbp2 in Hl. injection Hl as Hl. rewrite Hl in Hrp2. done.
    - by exists L, q'.
  Qed.

  (** A thread that does not step keeps the point of its entry. *)
  Lemma run_stab k t : npend (r k) t → t ∉ l k → we (S k) t = we k t.
  Proof.
    intros Hp HtL. destruct (npend_arun k t Hp) as (e & b & c & He & Hb & Hr & Hna).
    destruct (Hmax k) as [Hst|(_ & Heq & Hl)]; [|unfold we; by rewrite arun_stuck].
    pose proof (arun_conf k) as Hc. pose proof (arun_conf (S k)) as Hc'.
    rewrite <-(arun_q k) in Hst. unfold we.
    change (arun (S k)) with (aupd ω N (arun k) (l k) (r (S k))) in Hc' |- *.
    destruct (aupd_cases ω N (arun k) (l k) (r (S k)) Hst) as
      [(i & ei & ei' & HL' & Hi & _ & _ & Hq & Hkeep)
      |[(i & ei & cn & ei' & HL' & Hi & _ & _ & _ & Hq & Hkeep & _)
      |[(i & j & ei & v & ei' & HL' & Hi & _ & _ & Hj & Hq & Hkeep & _)
      |[(i & ei & ro & oo & ei' & HL' & Hi & Hbi & _ & HC & Hq & _ & Hren & _)
      |[(s1 & t1 & c1 & v & es & es' & et & et' & Hne & HL' & _ & _ & _ & _ & _ & _ & Hq & Hkeep & _)
      |[(s1 & t1 & c1 & es & es' & et & et' & Hne & HL' & _ & _ & _ & _ & _ & _ & _ & Hq & Hkeep & _)
       |(s1 & t1 & c1 & b1 & es & es' & et & et' & Hne & HL' & _ & _ & _ & _ & _ & _ & Hq & Hkeep & _)
      ]]]]]]; rewrite HL' in HtL.
    - apply rank_pt_eq; [rewrite Hq; simpl; rewrite lookup_insert_ne; set_solver|].
      by destruct (Hkeep t) as [-> _].
    - apply rank_pt_eq; [rewrite Hq; simpl; rewrite lookup_insert_ne; set_solver|].
      destruct (Hkeep t) as [-> _]; set_solver.
    - assert (t ≠ j) by (intros ->; congruence).
      apply rank_pt_eq; [rewrite Hq; simpl; rewrite !lookup_insert_ne; set_solver|].
      destruct (Hkeep t) as [-> _]; set_solver.
    - (* a link renames *)
      assert (t ≠ i) as Hti by set_solver.
      assert ((ac_q (aupd ω N (arun k) (l k) (r (S k)))).2 !! t = Some (chsubst ro oo e)) as He'.
      { simpl. rewrite Hq. simpl. rewrite lookup_fmap, lookup_insert_ne by done. by rewrite He. }
      assert (act (chsubst ro oo e) = Some (amap (csub ro oo) b)) as Hb' by (by rewrite act_chsubst, Hb).
      pose proof (rchan_amap (csub ro oo) b c Hr) as Hr'.
      unfold rank_pt. rewrite (rchan_of_eq _ t _ _ _ He' Hb' Hr'), (rchan_of_eq _ t e b c He Hb Hr).
      rewrite (Hren t Hti).
      destruct (c_one W HW Hwf _ Hc t e b c He Hb Hr) as [x Hx].
      unfold csub. destruct (decide (c = ro)) as [->|Hcr].
      + unfold tenv_rename. rewrite Hx. unfold tenv_union. rewrite lookup_union_with.
        destruct (decide (oo = ro)) as [->|Hor].
        * by rewrite lookup_delete_eq, lookup_singleton_eq.
        * rewrite lookup_delete_ne, lookup_singleton_eq by done.
          destruct (ac_env (arun k) t !! oo) as [o'|] eqn:Ho'; simpl; [|done].
          exfalso.
          assert (∃ z1 z2, tenv_rename ro oo (ac_env (arun k) t) !! oo = Some (Both z1 z2)) as (z1 & z2 & Hz).
          { unfold tenv_rename. rewrite Hx. unfold tenv_union. rewrite lookup_union_with.
            rewrite lookup_delete_ne, lookup_singleton_eq, Ho' by done. simpl. destruct o'; eauto. }
          rewrite <-(Hren t Hti) in Hz.
          pose proof (rchan_amap (csub ro oo) b ro Hr) as Hr2. unfold csub in Hr2.
          rewrite decide_True in Hr2 by done.
          exact (both_false W HW Hwf _ Hc' t _ _ oo z1 z2 He' Hb' Hr2 Hz).
      + destruct (decide (c = oo)) as [->|Hco]; [|by rewrite (lookup_tenv_rename_ne ro oo)].
        unfold tenv_rename. destruct (ac_env (arun k) t !! ro) as [y|] eqn:Hy; [|done].
        unfold tenv_union. rewrite lookup_union_with, lookup_delete_ne, lookup_singleton_eq, Hx
          by done.
        simpl. by destruct y.
    - apply rank_pt_eq; [rewrite Hq; simpl; rewrite !lookup_insert_ne; set_solver|].
      destruct (Hkeep t) as [-> _]; set_solver.
    - apply rank_pt_eq; [rewrite Hq; simpl; rewrite !lookup_insert_ne; set_solver|].
      destruct (Hkeep t) as [-> _]; set_solver.
    - apply rank_pt_eq; [rewrite Hq; simpl; rewrite !lookup_insert_ne; set_solver|].
      destruct (Hkeep t) as [-> _]; set_solver.
  Qed.

  (** The two outcomes of a step for the counter of t's partner. *)
  Lemma fuel_eq_case k t e b c s es :
    (ac_q (arun k)).2 !! t = Some e → act e = Some b → rchan b = Some c →
    (ac_q (arun k)).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env (arun k) s) →
    rchan_of (arun (S k)) t = Some c →
    (∃ es', (ac_q (arun (S k))).2 !! s = Some es') → c ∈ dom (ac_env (arun (S k)) s) →
    ac_fuel (arun (S k)) s c = ac_fuel (arun k) s c →
    (s ∈ l k → admin_at (r k) s) →
    fu (S k) t = fu k t ∧ (∀ u, waits (r (S k)) t u ↔ waits (r k) t u) ∧
    (∀ u, waits (r k) t u → u ∈ l k → admin_at (r k) u).
  Proof.
    intros He Hb Hr Hes Hst Hcs Hrt [es' Hes'] Hcs' Hfs Had.
    pose proof (arun_conf k) as Hc. pose proof (arun_conf (S k)) as Hc'.
    assert (c ∈ dom (ac_env (arun k) t)) as Hct.
    { rewrite (c_dom W HW Hwf _ Hc t e He). by eapply (rchan_fchans W HW Hwf _ Hc). }
    unfold rchan_of in Hrt.
    destruct ((ac_q (arun (S k))).2 !! t) as [e''|] eqn:He''; [|done].
    destruct (act e'') as [b''|] eqn:Hb''; [|done].
    assert (c ∈ dom (ac_env (arun (S k)) t)) as Hct'.
    { rewrite (c_dom W HW Hwf _ Hc' t e'' He''). by eapply (rchan_fchans W HW Hwf _ Hc'). }
    unfold fu, partner_fuel. rewrite (rchan_of_eq _ t e b c He Hb Hr).
    rewrite (rchan_of_eq _ t e'' b'' c He'' Hb'' Hrt).
    rewrite (holder_fuel_spec W HW Hwf _ t e c s es Hc He Hct Hes Hst Hcs).
    rewrite (holder_fuel_spec W HW Hwf _ t e'' c s es' Hc' He'' Hct' Hes' Hst Hcs').
    split; [done|]. rewrite <-(arun_q k), <-(arun_q (S k)). split.
    - intros u. rewrite (c_waits_holder W HW Hwf _ t e'' b'' c s es' Hc' He'' Hb'' Hrt Hes' Hst Hcs' u).
      by rewrite (c_waits_holder W HW Hwf _ t e b c s es Hc He Hb Hr Hes Hst Hcs u).
    - intros u Hw Hu. rewrite (c_waits_holder W HW Hwf _ t e b c s es Hc He Hb Hr Hes Hst Hcs u) in Hw.
      subst u. rewrite arun_q. by apply Had.
  Qed.

  Lemma fuel_lt_case k t e b c s es c' :
    (ac_q (arun k)).2 !! t = Some e → act e = Some b → rchan b = Some c →
    (ac_q (arun k)).2 !! s = Some es → s ≠ t → c ∈ dom (ac_env (arun k) s) →
    rchan_of (arun (S k)) t = Some c' → 0 < ac_fuel (arun k) s c →
    (∀ u eu, (ac_q (arun (S k))).2 !! u = Some eu → u ≠ t → c' ∈ dom (ac_env (arun (S k)) u) →
       ac_fuel (arun (S k)) u c' < ac_fuel (arun k) s c) →
    fu (S k) t < fu k t.
  Proof.
    intros He Hb Hr Hes Hst Hcs Hrt Hpos Hlt. pose proof (arun_conf k) as Hc.
    assert (c ∈ dom (ac_env (arun k) t)) as Hct.
    { rewrite (c_dom W HW Hwf _ Hc t e He). by eapply (rchan_fchans W HW Hwf _ Hc). }
    unfold fu, partner_fuel. rewrite (rchan_of_eq _ t e b c He Hb Hr), Hrt.
    rewrite (holder_fuel_spec W HW Hwf _ t e c s es Hc He Hct Hes Hst Hcs).
    by apply holder_fuel_lt.
  Qed.

  Ltac holds_of Hc Heu Hbu Hru :=
    rewrite (c_dom _ HW Hwf _ Hc _ _ Heu); exact (rchan_fchans _ HW Hwf _ Hc _ _ _ Hbu Hru).

  (** The fuel clause of the criterion. *)
  Lemma run_fuel k t : npend (r k) t → t ∉ l k →
    fu (S k) t < fu k t ∨
    (fu (S k) t = fu k t ∧ (∀ s, waits (r (S k)) t s ↔ waits (r k) t s) ∧
     ∀ s, waits (r k) t s → s ∈ l k → admin_at (r k) s).
  Proof.
    intros Hp HtL. destruct (npend_arun k t Hp) as (e & b & c & He & Hb & Hr & Hna).
    pose proof (arun_conf k) as Hc.
    destruct (c_one W HW Hwf _ Hc t e b c He Hb Hr) as [x Hx].
    destruct (holder_exists W HW Hwf _ t e x c Hc He Hx) as (s & es & Hes & Hst & Hcs).
    destruct (holder_one W HW Hwf _ t e x c s es Hc He Hx Hes Hst Hcs) as [y Hy].
    assert (c ∈ dom (ac_env (arun k) t)) as Hct by (holds_of Hc He Hb Hr).
    assert (c ∈ (ac_q (arun k)).1) as HcC.
    { apply (c_closed W HW Hwf _ Hc t e He). by eapply (rchan_fchans W HW Hwf _ Hc). }
    assert (∀ u eu, (ac_q (arun k)).2 !! u = Some eu → u ≠ t → c ∈ dom (ac_env (arun k) u) → u = s)
      as Huniq.
    { intros u eu Heu Hut Hcu. exact (c_uniq W HW Hwf _ Hc t e u eu s es c He Heu Hes Hct Hcu Hcs Hut Hst). }
    destruct (Hmax k) as [Hst0|(_ & Heq & Hl)].
    2:{ right. unfold fu. rewrite arun_stuck by done. split_and!; [done|by rewrite Heq|].
        intros u _ Hu. rewrite Hl in Hu. set_solver. }
    pose proof (arun_conf (S k)) as Hc'.
    rewrite <-(arun_q k) in Hst0.
    pose proof (aupd_cases ω N (arun k) (l k) (r (S k)) Hst0) as Hcases.
    change (aupd ω N (arun k) (l k) (r (S k))) with (arun (S k)) in Hcases.
    pose proof (arun_q (S k)) as Hq'.
    assert (∀ u, admin_at (ac_q (arun k)) u → admin_at (r k) u) as Hadm by (intros u; by rewrite arun_q).
    destruct Hcases as
      [(i & ei & ei' & HL' & Hi & Hbi & _ & Hq & Hkeep)
      |[(i & ei & cn & ei' & HL' & Hi & Hbi & _ & Hcn & Hq & Hkeep & Henv & Hfl)
      |[(i & j & ei & v & ei' & HL' & Hi & Hbi & _ & Hj & Hq & Hkeep & Henvi & Henvj & Hfi & Hfj)
      |[(i & ei & ro & oo & ei' & HL' & Hi & Hbi & _ & HroC & Hq & Henvi & Hren & Hfl)
      |[(s1 & t1 & c1 & v & es1 & es1' & et1 & et1' & Hne & HL' & Hs1 & Ht1 & Hbs1 & Hbt1 & _ & _ & Hq
          & Hkeep & Henvs & Henvt & Hfs & Hft)
      |[(s1 & t1 & c1 & es1 & es1' & et1 & et1' & Hne & HL' & Hs1 & Ht1 & Hbs1 & Hbt1 & _ & _ & _ & Hq
          & Hkeep & Henvs & Henvt & Hfs & Hft)
       |(s1 & t1 & c1 & b1 & es1 & es1' & et1 & et1' & Hne & HL' & Hs1 & Ht1 & Hbs1 & Hbt1 & _ & _ & Hq
          & Hkeep & Henvs & Henvt & Hfs & Hft)
      ]]]]]]; rewrite HL' in HtL.
    - (* β *)
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite lookup_insert_ne; set_solver. }
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
      + rewrite Hq', Hq. simpl. destruct (decide (s = i)) as [->|Hsi].
        * rewrite lookup_insert_eq. eauto.
        * rewrite lookup_insert_ne by done. eauto.
      + by destruct (Hkeep s) as [-> _].
      + by destruct (Hkeep s) as [_ ->].
      + intros Hs. rewrite HL' in Hs. apply elem_of_singleton in Hs. subst. apply Hadm.
        by exists ei, ABeta.
    - (* new *)
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite lookup_insert_ne; set_solver. }
      assert (c ≠ cn) as Hccn by (intros ->; done).
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
      + rewrite Hq', Hq. simpl. destruct (decide (s = i)) as [->|Hsi].
        * rewrite lookup_insert_eq. eauto.
        * rewrite lookup_insert_ne by done. eauto.
      + destruct (decide (s = i)) as [->|Hsi]; [rewrite Henv, dom_insert_L; set_solver|].
        by destruct (Hkeep s Hsi) as [-> _].
      + destruct (decide (s = i)) as [->|Hsi]; [rewrite Hfl; by rewrite decide_False|].
        by destruct (Hkeep s Hsi) as [_ ->].
      + intros Hs. rewrite HL' in Hs. apply elem_of_singleton in Hs. subst. apply Hadm.
        by exists ei, ANew.
    - (* spawn *)
      assert (t ≠ j) by (intros ->; congruence).
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne; set_solver. }
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      destruct (decide (s = i)) as [->|Hsi].
      + destruct (decide (c ∈ dom (pl_give (or_pick ω (ac_env (arun k) i) ei)))) as [Hg|Hg].
        * left. pose proof (fuel_pos W HW Hwf _ i es (ASpawn v) c Hc Hes Hcs ltac:(congruence) (or_introl I)) as Hpos.
          apply (fuel_lt_case k t e b c i es c He Hb Hr Hes Hst Hcs Hrt Hpos).
          intros u eu Heu Hut Hcu.
          destruct (decide (u = j)) as [->|Huj]; [rewrite Hfj; lia|].
          destruct (decide (u = i)) as [->|Hui].
          { exfalso. rewrite Henvi in Hcu. by apply (dom_tenv_minus_one _ _ c y Hy Hg). }
          exfalso. destruct (Hkeep u Hui Huj) as [Henvu _]. rewrite Henvu in Hcu.
          rewrite Hq', Hq in Heu. simpl in Heu. rewrite !lookup_insert_ne in Heu by done.
          by apply Hui, (Huniq u eu).
        * right. apply (fuel_eq_case k t e b c i es He Hb Hr Hes Hst Hcs Hrt).
          { rewrite Hq', Hq. simpl. rewrite lookup_insert_ne by congruence. rewrite lookup_insert_eq. eauto. }
          { rewrite Henvi. by rewrite dom_tenv_minus_keep. }
          { by rewrite Hfi. }
          { intros _. apply Hadm. by exists ei, (ASpawn v). }
      + assert (s ≠ j) by (intros ->; congruence).
        right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
        * rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne by done. eauto.
        * by destruct (Hkeep s Hsi H0) as [-> _].
        * by destruct (Hkeep s Hsi H0) as [_ ->].
        * intros Hs. rewrite HL' in Hs. set_solver.
    - (* link *)
      assert (t ≠ i) as Hti by set_solver.
      assert ((ac_q (arun (S k))).2 !! t = Some (chsubst ro oo e)) as He'.
      { rewrite Hq', Hq. simpl. rewrite lookup_fmap, lookup_insert_ne by done. by rewrite He. }
      assert (act (chsubst ro oo e) = Some (amap (csub ro oo) b)) as Hb' by (by rewrite act_chsubst, Hb).
      pose proof (rchan_of_eq _ t _ _ _ He' Hb' (rchan_amap (csub ro oo) b c Hr)) as Hrt.
      assert (ro ∈ dom (ac_env (arun k) i) ∧ oo ∈ dom (ac_env (arun k) i)) as [Hroi Hooi].
      { rewrite (c_dom W HW Hwf _ Hc i ei Hi).
        destruct Hbi as [Hbi|Hbi]; pose proof (act_asubjs_fchans ei _ _ Hbi eq_refl); set_solver. }
      assert (is_admin (if bool_decide True then ALink ro oo else ALink ro oo)) as Hadl by done.
      assert (∃ bi, act ei = Some bi ∧ is_admin bi) as (bi & Hbi' & Hadbi).
      { destruct Hbi as [Hbi|Hbi]; eexists; split; [exact Hbi|done|exact Hbi|done]. }
      destruct (decide (s = i)) as [->|Hsi].
      + destruct (decide (c = ro ∨ c = oo)) as [Hco|Hco].
        * left. pose proof (fuel_pos W HW Hwf _ i es bi c Hc Hes Hcs ltac:(congruence) (or_introl Hadbi)) as Hpos.
          apply (fuel_lt_case k t e b c i es (csub ro oo c) He Hb Hr Hes Hst Hcs Hrt Hpos).
          intros u eu Heu Hut Hcu.
          assert (csub ro oo c = oo) as Hco'.
          { unfold csub. destruct Hco as [->| ->]; case_decide; congruence. }
          rewrite Hco' in Hcu |- *.
          destruct (decide (u = i)) as [->|Hui].
          { exfalso. rewrite Henvi in Hcu. set_solver. }
          rewrite Hfl. unfold link_fuel. rewrite (Hren u Hui) in Hcu.
          rewrite decide_True by (split_and!; [done|done|by apply dom_tenv_rename_o]).
          match goal with |- min ?X ?m < _ => pose proof (Nat.le_min_r X m) end.
          destruct Hco as [-> | ->]; lia.
        * right. assert (csub ro oo c = c) as Hcc by (unfold csub; case_decide; naive_solver).
          rewrite Hcc in Hrt.
          apply (fuel_eq_case k t e b c i es He Hb Hr Hes Hst Hcs Hrt).
          { rewrite Hq', Hq. simpl. rewrite lookup_fmap, lookup_insert_eq. simpl. eauto. }
          { rewrite Henvi. rewrite !dom_delete_L. set_solver. }
          { rewrite Hfl. unfold link_fuel. by rewrite decide_False by naive_solver. }
          { intros _. apply Hadm. by exists ei, bi. }
      + assert (c ≠ ro) as Hcr.
        { intros ->. apply Hsi. symmetry. apply (Huniq i ei Hi); [done|done]. }
        assert (c ≠ oo) as Hco.
        { intros ->. apply Hsi. symmetry. apply (Huniq i ei Hi); [done|done]. }
        assert (csub ro oo c = c) as Hcc by (unfold csub; case_decide; naive_solver).
        rewrite Hcc in Hrt. right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
        * rewrite Hq', Hq. simpl. rewrite lookup_fmap, lookup_insert_ne by done. rewrite Hes. simpl. eauto.
        * rewrite (Hren s Hsi). by rewrite dom_tenv_rename_ne.
        * rewrite Hfl. unfold link_fuel. by rewrite decide_False by naive_solver.
        * intros Hs. rewrite HL' in Hs. set_solver.
    - (* message *)
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne; set_solver. }
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      assert (c1 ∈ dom (ac_env (arun k) s1)) as Hc1s by (holds_of Hc Hs1 Hbs1 (eq_refl (Some c1))).
      assert (c1 ∈ dom (ac_env (arun k) t1)) as Hc1t by (holds_of Hc Ht1 Hbt1 (eq_refl (Some c1))).
      assert (c1 ≠ c) as Hc1c.
      { intros ->. apply Hne. rewrite (Huniq s1 es1 Hs1); [|set_solver|done].
        by rewrite (Huniq t1 et1 Ht1); [|set_solver|done]. }
      destruct (decide (s = s1)) as [->|Hss1]; [|destruct (decide (s = t1)) as [->|Hst1]].
      + left. pose proof (fuel_pos W HW Hwf _ s1 es (ASend c1 v) c Hc Hes Hcs ltac:(congruence)
          (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))) as Hpos.
        apply (fuel_lt_case k t e b c s1 es c He Hb Hr Hes Hst Hcs Hrt Hpos).
        intros u eu Heu Hut Hcu.
        destruct (decide (u = s1)) as [->|Hus1]; [rewrite Hfs; unfold tick; rewrite decide_False by done; lia|].
        destruct (decide (u = t1)) as [->|Hut1].
        * rewrite Hft. unfold msg_fuel. rewrite decide_False by done.
          case_decide; [case_decide; lia|].
          exfalso. rewrite Henvt, dom_tenv_union, dom_step_entry in Hcu.
          destruct Hcu as [Hcu|Hcu]; [|done]. apply Hne. symmetry. by apply (Huniq t1 et1).
        * exfalso. destruct (Hkeep u Hus1 Hut1) as [Henvu _]. rewrite Henvu in Hcu.
          rewrite Hq', Hq in Heu. simpl in Heu. rewrite !lookup_insert_ne in Heu by done.
          by apply Hus1, (Huniq u eu).
      + left. pose proof (fuel_pos W HW Hwf _ t1 es (ARecv c1) c Hc Hes Hcs ltac:(congruence)
          (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))) as Hpos.
        apply (fuel_lt_case k t e b c t1 es c He Hb Hr Hes Hst Hcs Hrt Hpos).
        intros u eu Heu Hut Hcu.
        destruct (decide (u = t1)) as [->|Hut1].
        * rewrite Hft. unfold msg_fuel. rewrite decide_False by done.
          case_decide; [rewrite decide_True by done; lia|lia].
        * destruct (decide (u = s1)) as [->|Hus1].
          { exfalso. rewrite Henvs, dom_step_entry in Hcu. apply dom_tenv_minus_sub in Hcu.
            by apply Hne, (Huniq s1 es1). }
          exfalso. destruct (Hkeep u Hus1 Hut1) as [Henvu _]. rewrite Henvu in Hcu.
          rewrite Hq', Hq in Heu. simpl in Heu. rewrite !lookup_insert_ne in Heu by done.
          by apply Hut1, (Huniq u eu).
      + right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
        * rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne by done. eauto.
        * by destruct (Hkeep s Hss1 Hst1) as [-> _].
        * by destruct (Hkeep s Hss1 Hst1) as [_ ->].
        * intros Hs. rewrite HL' in Hs. set_solver.
    - (* close *)
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne; set_solver. }
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      assert (c1 ∈ dom (ac_env (arun k) s1)) as Hc1s by (holds_of Hc Hs1 Hbs1 (eq_refl (Some c1))).
      assert (c1 ∈ dom (ac_env (arun k) t1)) as Hc1t by (holds_of Hc Ht1 Hbt1 (eq_refl (Some c1))).
      assert (c1 ≠ c) as Hc1c.
      { intros ->. apply Hne. rewrite (Huniq s1 es1 Hs1); [|set_solver|done].
        by rewrite (Huniq t1 et1 Ht1); [|set_solver|done]. }
      assert (∀ u eu, (ac_q (arun (S k))).2 !! u = Some eu → u ≠ t → u ≠ s →
                c ∈ dom (ac_env (arun (S k)) u) → False) as Hnot.
      { intros u eu Heu Hut Hus Hcu.
        destruct (decide (u = s1)) as [->|Hus1].
        { rewrite Henvs, dom_delete_L in Hcu. by apply Hus, (Huniq s1 es1 Hs1); [|set_solver]. }
        destruct (decide (u = t1)) as [->|Hut1].
        { rewrite Henvt, dom_delete_L in Hcu. by apply Hus, (Huniq t1 et1 Ht1); [|set_solver]. }
        destruct (Hkeep u Hus1 Hut1) as [Henvu _]. rewrite Henvu in Hcu.
        rewrite Hq', Hq in Heu. simpl in Heu. rewrite !lookup_insert_ne in Heu by done.
        by apply Hus, (Huniq u eu). }
      destruct (decide (s = s1 ∨ s = t1)) as [Hsp|Hsp].
      + left. assert (0 < ac_fuel (arun k) s c) as Hpos.
        { destruct Hsp as [->| ->].
          - exact (fuel_pos W HW Hwf _ s1 es1 (AClos c1) c Hc Hs1 Hcs Hbs1
              (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))).
          - exact (fuel_pos W HW Hwf _ t1 et1 (AClos c1) c Hc Ht1 Hcs Hbt1
              (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))). }
        apply (fuel_lt_case k t e b c s es c He Hb Hr Hes Hst Hcs Hrt Hpos).
        intros u eu Heu Hut Hcu. destruct (decide (u = s)) as [->|Hus]; [|by destruct (Hnot u eu Heu Hut Hus Hcu)].
        destruct Hsp as [->| ->]; [rewrite Hfs|rewrite Hft]; unfold tick; rewrite decide_False by done; lia.
      + right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
        * rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne by naive_solver. eauto.
        * by destruct (Hkeep s ltac:(naive_solver) ltac:(naive_solver)) as [-> _].
        * by destruct (Hkeep s ltac:(naive_solver) ltac:(naive_solver)) as [_ ->].
        * intros Hs. rewrite HL' in Hs. set_solver.
    - (* choice *)
      assert ((ac_q (arun (S k))).2 !! t = Some e) as He'.
      { rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne; set_solver. }
      pose proof (rchan_of_eq _ t e b c He' Hb Hr) as Hrt.
      assert (c1 ∈ dom (ac_env (arun k) s1)) as Hc1s by (holds_of Hc Hs1 Hbs1 (eq_refl (Some c1))).
      assert (c1 ∈ dom (ac_env (arun k) t1)) as Hc1t by (holds_of Hc Ht1 Hbt1 (eq_refl (Some c1))).
      assert (c1 ≠ c) as Hc1c.
      { intros ->. apply Hne. rewrite (Huniq s1 es1 Hs1); [|set_solver|done].
        by rewrite (Huniq t1 et1 Ht1); [|set_solver|done]. }
      assert (∀ u eu, (ac_q (arun (S k))).2 !! u = Some eu → u ≠ t → u ≠ s →
                c ∈ dom (ac_env (arun (S k)) u) → False) as Hnot.
      { intros u eu Heu Hut Hus Hcu.
        destruct (decide (u = s1)) as [->|Hus1].
        { rewrite Henvs, dom_step_entry in Hcu. by apply Hus, (Huniq s1 es1 Hs1). }
        destruct (decide (u = t1)) as [->|Hut1].
        { rewrite Henvt, dom_step_entry in Hcu. by apply Hus, (Huniq t1 et1 Ht1). }
        destruct (Hkeep u Hus1 Hut1) as [Henvu _]. rewrite Henvu in Hcu.
        rewrite Hq', Hq in Heu. simpl in Heu. rewrite !lookup_insert_ne in Heu by done.
        by apply Hus, (Huniq u eu). }
      destruct (decide (s = s1 ∨ s = t1)) as [Hsp|Hsp].
      + left. assert (0 < ac_fuel (arun k) s c) as Hpos.
        { destruct Hsp as [->| ->].
          - exact (fuel_pos W HW Hwf _ s1 es1 (ASel c1 b1) c Hc Hs1 Hcs Hbs1
              (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))).
          - exact (fuel_pos W HW Hwf _ t1 et1 (ABra c1) c Hc Ht1 Hcs Hbt1
              (or_intror (ex_intro _ c1 (conj eq_refl Hc1c)))). }
        apply (fuel_lt_case k t e b c s es c He Hb Hr Hes Hst Hcs Hrt Hpos).
        intros u eu Heu Hut Hcu. destruct (decide (u = s)) as [->|Hus]; [|by destruct (Hnot u eu Heu Hut Hus Hcu)].
        destruct Hsp as [->| ->]; [rewrite Hfs|rewrite Hft]; unfold tick; rewrite decide_False by done; lia.
      + right. apply (fuel_eq_case k t e b c s es He Hb Hr Hes Hst Hcs Hrt).
        * rewrite Hq', Hq. simpl. rewrite !lookup_insert_ne by naive_solver. eauto.
        * by destruct (Hkeep s ltac:(naive_solver) ltac:(naive_solver)) as [-> _].
        * by destruct (Hkeep s ltac:(naive_solver) ltac:(naive_solver)) as [_ ->].
        * intros Hs. rewrite HL' in Hs. set_solver.
  Qed.
End run.
