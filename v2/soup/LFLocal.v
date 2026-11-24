(** * One soup, locally (stage S8, proposal §2.13)

    Facts of a closed soup at a positive index that adequacy reads at
    every position of a run. A thread whose redex is a session action
    other than a link acts on an end o it holds ([s_held_end]). Its
    readiness puts the point of o below the partner point of every other
    end it holds ([s_ready]). The partner of o is held by another thread
    ([s_partner]), and when that thread's redex acts on the partner, the
    two redexes fit and the thread is enabled ([compat_enabled]). A
    thread that holds an end is not a value ([s_value_empty]). *)

From stdpp Require Import relations.
From GV Require Export soup.SoupTau.

(** ** The end of a session redex *)

Definition aend (a : action) : option cend :=
  match a with ARecv o | ASend o _ | AClose o | ASel o _ | ABra o => Some o | _ => None end.

Definition rend (q : config) (t : nat) : option cend :=
  q.2 !! t ≫= λ e, act e ≫= aend.

Lemma aend_sess a o : aend a = Some o → is_sess a ∧ ¬ is_admin a.
Proof. destruct a; simpl; intros H; try discriminate; (split; [unfold is_sess; simpl; by eexists|by intros []]). Qed.

Lemma aend_offers a α o : aend a = Some o → offers a α → ∃ σ, α = LSess σ ∧ sends σ = {[o]}.
Proof.
  destruct a, α as [| | | |[]]; simpl; intros [= <-] Ho; try done; destruct_and?; subst; eauto.
Qed.

Lemma aend_step e a o : act e = Some a → aend a = Some o → ∃ σ e', tstep e (LSess σ) e' ∧ sends σ = {[o]}.
Proof.
  intros Ha Ho. destruct a; simpl in Ho; simplify_eq.
  - destruct (act_offer e (ARecv o) (LSess (SRecv o EUnit)) Ha (conj eq_refl I)) as [e' He']. eauto.
  - destruct (act_offer e (ASend o v) (LSess (SSend o v)) Ha (conj eq_refl eq_refl))
      as [e' He']. eauto.
  - destruct (act_offer e (AClose o) (LSess (SClose o)) Ha eq_refl) as [e' He']. eauto.
  - destruct (act_offer e (ASel o i) (LSess (SSel o i)) Ha (conj eq_refl eq_refl)) as [e' He']. eauto.
  - destruct (act_offer e (ABra o) (LSess (SBra o false)) Ha eq_refl) as [e' He']. eauto.
Qed.

(** The kind of a redex against the session type of its end. *)
Definition akind (a : action) (S0 : sty) : Prop :=
  match a with
  | ASend _ _ => ∃ m U S, unfoldS S0 = SSeq (SSnd m U) S
  | ARecv _ => ∃ m U S, unfoldS S0 = SSeq (SRcv m U) S
  | AClose _ => unfoldS S0 = SEnd
  | ASel _ _ => ∃ S1 S2, unfoldS S0 = SPlus S1 S2
  | ABra _ => ∃ S1 S2, unfoldS S0 = SWith S1 S2
  | _ => True
  end.

(** Two redexes that fit on the two ends of a channel. *)
Definition compat (a1 a2 : action) : Prop :=
  match a1, a2 with
  | ASend o _, ARecv o' | ARecv o, ASend o' _ | AClose o, AClose o' | ASel o _, ABra o'
  | ABra o, ASel o' _ => o' = edual o
  | _, _ => False
  end.

Lemma sdual_compat a1 a2 S0 S0' o :
  sdual S0 S0' → akind a1 S0 → akind a2 S0' → aend a1 = Some o → aend a2 = Some (edual o) → compat a1 a2.
Proof.
  intros Hd H1 H2 Ho1 Ho2. unfold sdual in Hd.
  destruct a1; simpl in Ho1; simplify_eq; destruct a2; simpl in Ho2; simplify_eq; simpl; try done;
    simpl in H1, H2; exfalso.
  all: repeat match goal with H : ∃ _, _ |- _ => destruct H end.
  all: match goal with Hd : seqv _ (dual ?s), H1 : unfoldS ?s = ?u |- _ =>
         assert (unfoldS (dual s) = dual u) as Hdu by (by rewrite <-dual_unfoldS, H1); simpl in Hdu end.
  all: first [ destruct (seqv_unfold_rcv _ _ _ _ _ Hd Hdu) as (? & ? & ? & Hx & _)
             | destruct (seqv_unfold_snd _ _ _ _ _ Hd Hdu) as (? & ? & ? & Hx & _)
             | pose proof (seqv_unfold_end _ _ Hd Hdu) as Hx
             | destruct (seqv_unfold_with _ _ _ _ Hd Hdu) as (? & ? & Hx & _)
             | destruct (seqv_unfold_plus _ _ _ _ Hd Hdu) as (? & ? & Hx & _) ].
  all: congruence.
Qed.

Lemma compat_enabled C M t s e es a1 a2 :
  t ≠ s → M !! t = Some e → M !! s = Some es → act e = Some a1 → act es = Some a2 → compat a1 a2 →
  (∀ o, a1 = AClose o → ech o ∈ C) → tenabled (C, M) t.
Proof.
  intros Hts He Hes Ha1 Ha2 Hc Hcl.
  destruct a1 as [| | | |o|o w|o|o1 o2|o b|o]; destruct a2 as [| | | |o'|o' w'|o'|o1' o2'|o' b'|o']; simpl in Hc;
    try done; subst.
  - (* t receives, s sends *)
    pose proof (act_send_val _ _ _ Ha2) as Hv.
    destruct (act_offer es (ASend (edual o) w') (LSess (SSend (edual o) w')) Ha2
      (conj eq_refl eq_refl)) as [es' Hs'].
    destruct (act_offer e (ARecv o) (LSess (SRecv o w')) Ha1 (conj eq_refl Hv)) as [e' He'].
    eexists _, _. split; [split; [eapply (p_act_msg C M s t (edual o)); [done|done|done|exact Hs'|]|done]|].
    + by rewrite edual_edual.
    + simpl. set_solver.
  - pose proof (act_send_val _ _ _ Ha1) as Hv.
    destruct (act_offer e (ASend o w) (LSess (SSend o w)) Ha1
      (conj eq_refl eq_refl)) as [e' He'].
    destruct (act_offer es (ARecv (edual o)) (LSess (SRecv (edual o) w)) Ha2 (conj eq_refl Hv)) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_msg C M t s o); [done|done|done|exact He'|exact Hs']|done]|].
    simpl. set_solver.
  - destruct (act_offer e (AClose o) (LSess (SClose o)) Ha1 eq_refl) as [e' He'].
    destruct (act_offer es (AClose (edual o)) (LSess (SClose (edual o))) Ha2 eq_refl) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_close C M t s o); [done|done|done|exact He'|exact Hs'|by apply Hcl]|done]|].
    simpl. set_solver.
  - destruct (act_offer e (ASel o b) (LSess (SSel o b)) Ha1 (conj eq_refl eq_refl)) as [e' He'].
    destruct (act_offer es (ABra (edual o)) (LSess (SBra (edual o) b)) Ha2 eq_refl) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_choice C M t s o b); [done|done|done|exact He'|exact Hs']|done]|].
    simpl. set_solver.
  - destruct (act_offer es (ASel (edual o) b') (LSess (SSel (edual o) b')) Ha2 (conj eq_refl eq_refl)) as [es' Hs'].
    destruct (act_offer e (ABra o) (LSess (SBra o b')) Ha1 eq_refl) as [e' He'].
    eexists _, _. split; [split; [eapply (p_act_choice C M s t (edual o) b'); [done|done|done|exact Hs'|]|done]|].
    + by rewrite edual_edual.
    + simpl. set_solver.
Qed.

Lemma action_cases a : is_admin a ∨ ∃ o, aend a = Some o.
Proof. destruct a; simpl; eauto. Qed.

Lemma aend_not_link a o os : aend a = Some o → offers a (LSess (SLink os)) → False.
Proof. by destruct a. Qed.

(** V at a primitive type holds no end. *)
(** ** The facts of one soup *)

Section local.
  #[local] Set Default Proof Using "All".
  Context (N : nat) (n : Ix) (W : world) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W ∅ T a A Π U).

  Local Abbreviation q := (s_q a).
  Local Abbreviation K := (s_K a).

  Lemma l_E t e : q.2 !! t = Some e → e ∈ E[live]^W _ n⟦kres K t A ⊢ U t⟧^∅.
  Proof. apply (s_rel Hs). Qed.

  Lemma l_obl t e α e' : q.2 !! t = Some e → tstep e α e' →
    Eobl live n (Vrel live) (Erel live) (Vrel live n) (Erel live n) W (kres K t A) (U t) ∅ α e'.
  Proof. intros He Hst. exact (Erel_step live n W W _ _ _ _ _ _ (l_E t e He) (wext_refl W) Hst). Qed.

  (** A session redex acts on an end its thread holds, at a session type
      of the redex's kind. *)
  Lemma s_held_end t e a1 o : q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    ∃ S0 x, kres K t A !! o = Some (S0, x) ∧ akind a1 S0.
  Proof.
    intros He Ha Ho. destruct a1 as [| | | |o'|o' w|o'|o1 o2|o' b|o']; simpl in Ho; simplify_eq.
    - destruct (act_offer e (ARecv o) (LSess (SRecv o EUnit)) Ha (conj eq_refl I)) as [e' He'].
      pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
      destruct H as (S0 & x & m & U0 & S & Ho & Hu & _). exists S0, x. split; [done|]. simpl. eauto.
    - destruct (act_offer e (ASend o w) (LSess (SSend o w)) Ha (conj eq_refl eq_refl))
        as [e' He'].
      pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
      destruct H as (S0 & x & m & U0 & S & ΘM & Θr & Ho & Hu & _). exists S0, x. split; [done|]. simpl. eauto.
    - destruct (act_offer e (AClose o) (LSess (SClose o)) Ha eq_refl) as [e' He'].
      pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
      destruct H as (S0 & x & Ho & Hu & _). exists S0, x. done.
    - destruct (act_offer e (ASel o b) (LSess (SSel o b)) Ha (conj eq_refl eq_refl)) as [e' He'].
      pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
      destruct H as (S0 & x & S1 & S2 & Ho & Hu & _). exists S0, x. split; [done|]. simpl. eauto.
    - destruct (act_offer e (ABra o) (LSess (SBra o false)) Ha eq_refl) as [e' He'].
      pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
      destruct H as (S0 & x & S1 & S2 & Ho & Hu & _). exists S0, x. split; [done|]. simpl. eauto.
  Qed.

  Lemma s_owner_of t o v : kres K t A !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

  (** A value holds no end. *)
  Lemma s_value_empty t e : q.2 !! t = Some e → act e = None → kres K t A = ∅.
  Proof.
    intros He Ha. pose proof (l_E t e He) as HE. apply Erel_iff in HE.
    destruct (HE W (wext_refl W)) as (Hstop & _ & _).
    pose proof (Hstop (proj2 (irred_act e) Ha)) as HV.
    destruct (s_ty Hs t e He) as [Ht|Ht]; rewrite Ht in HV.
    - exact (Vrel_tfree_empty _ _ _ _ _ _ (sp_tfree _ _ _ _ _ _ _ _ _ _ Hs) HV).
    - by apply Vrel_unit_iff in HV as [-> _].
  Qed.

  (** Readiness: the end a thread acts on lies below the partner point of
      every other end it holds. *)
  Lemma s_ready t e a1 o S0 x o' S' x' :
    q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    kres K t A !! o = Some (S0, x) → kres K t A !! o' = Some (S', x') → o' ≠ o → W ⊢ x ≺ pt_dual x'.
  Proof.
    intros He Ha Ho Hx Hx' Hne. pose proof (l_E t e He) as HE. apply Erel_iff in HE.
    destruct (HE W (wext_refl W)) as (_ & Hready & _).
    assert (¬ irred e) as Hni by (rewrite irred_act, Ha; done).
    assert (Hsends : ∀ σ e', tstep e (LSess σ) e' → sends σ = {[o]}).
    { intros σ e' Hst. destruct (act_step _ _ _ Hst) as (a2 & Ha2 & Hoff). rewrite Ha in Ha2. simplify_eq.
      destruct (aend_offers _ _ _ Ho Hoff) as (σ' & [= <-] & Hs'). done. }
    assert (stable_t e) as Hst.
    { intros α e' Hs'. destruct (act_step _ _ _ Hs') as (a2 & Ha2 & Hoff). rewrite Ha in Ha2. simplify_eq.
      destruct (aend_offers _ _ _ Ho Hoff) as (σ' & -> & _). by exists σ'. }
    destruct (Hready Hni Hst) as [_ [Hlink|Hbr]].
    { exfalso. destruct Hlink as (os & e' & Hs'). destruct (act_step _ _ _ Hs') as (a2 & Ha2 & Hoff).
      rewrite Ha in Ha2. simplify_eq. exact (aend_not_link _ _ _ Ho Hoff). }
    assert (offered_t (kres K t A) e o) as Hoff.
    { split; [by apply elem_of_dom_2 in Hx|]. destruct (aend_step e a1 o Ha Ho) as (σ & e' & Hs' & Hσ).
      exists σ, e'. split; [done|]. rewrite Hσ. set_solver. }
    destruct (Hbr o S0 x Hoff Hx) as [Hrest _]. apply (Hrest o' S' x' Hx').
    intros [_ (σ & e' & Hs' & Hin)]. rewrite (Hsends σ e' Hs') in Hin. apply elem_of_singleton in Hin. done.
  Qed.

  (** The partner of the end a thread acts on is held by another thread. *)
  Lemma s_partner t e a1 o : q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    ∃ s es h', K !! edual o = Some h' ∧ h'.(h_th) = s ∧ q.2 !! s = Some es ∧ s ≠ t.
  Proof.
    intros He Ha Ho. destruct (s_held_end t e a1 o He Ha Ho) as (S0 & x & Hx & _).
    destruct (s_owner_of _ _ _ Hx) as (h & Kh & Eh).
    assert (edual o ∈ dom K) as Hd.
    { apply (s_pair _ _ _ _ _ _ _ _ Hs). by apply elem_of_dom_2 in Kh. }
    apply elem_of_dom in Hd as [h' Kh']. destruct (s_owner _ _ _ _ _ _ _ _ Hs _ _ Kh') as [es Hes].
    exists h'.(h_th), es, h'. split_and!; [done|done|done|]. intros Hst.
    assert (edual o ∈ dom A) as HdA by (rewrite (s_domA _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh').
    apply elem_of_dom in HdA as [[S' x'] HA'].
    assert (kres K t A !! edual o = Some (S', x')) as Hx'.
    { apply lookup_kres. split; [done|]. exists h'. split; [done|congruence]. }
    pose proof (lookup_kres K t A o (S0, x)) as Hk. apply Hk in Hx as [HA _].
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S' x' HA HA') as [-> _].
    pose proof (s_ready t e a1 o S0 x (edual o) S' (pt_dual x) He Ha Ho (proj2 (lookup_kres K t A o (S0, x))
      (conj HA (ex_intro _ h (conj Kh Eh)))) Hx' (edual_ne o)) as Hlt.
    rewrite pt_dual_dual in Hlt. exact (w_lt_irrefl W x Hlt).
  Qed.

  (** A holder of an end is not a value. *)
  Lemma s_holder_act s es o h : K !! o = Some h → h.(h_th) = s → q.2 !! s = Some es → ∃ a2, act es = Some a2.
  Proof.
    intros Kh Eh Hes. destruct (act es) as [a2|] eqn:Ha; [by eexists|]. exfalso.
    pose proof (s_value_empty s es Hes Ha) as Hemp.
    assert (o ∈ dom A) as HdA by (rewrite (s_domA _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh).
    apply elem_of_dom in HdA as [v HA].
    assert (kres K s A !! o = Some v) as Hx by (apply lookup_kres; split; [done|eauto]).
    by rewrite Hemp, lookup_empty in Hx.
  Qed.

  (** Two redexes on the two ends of a channel fit. *)
  Lemma s_compat t e a1 o s es a2 : q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    q.2 !! s = Some es → act es = Some a2 → aend a2 = Some (edual o) → compat a1 a2.
  Proof.
    intros He Ha Ho Hes Ha2 Ho2.
    destruct (s_held_end t e a1 o He Ha Ho) as (S0 & x & Hx & Hk1).
    destruct (s_held_end s es a2 (edual o) Hes Ha2 Ho2) as (S0' & x' & Hx' & Hk2).
    apply lookup_kres in Hx as [HA _]. apply lookup_kres in Hx' as [HA' _].
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S0' x' HA HA') as [_ Hd].
    exact (sdual_compat a1 a2 S0 S0' o Hd Hk1 Hk2 Ho Ho2).
  Qed.

  (** A holder blocked on another end waits on an end below. *)
  Lemma s_rank t e a1 o s es a2 o2 :
    q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
    (∃ h', K !! edual o = Some h' ∧ h'.(h_th) = s) →
    q.2 !! s = Some es → act es = Some a2 → aend a2 = Some o2 → o2 ≠ edual o →
    W ⊢ kpt K o2 ≺ kpt K o.
  Proof.
    intros He Ha Ho (h' & Kh' & Eh') Hes Ha2 Ho2 Hne.
    destruct (s_held_end t e a1 o He Ha Ho) as (S0 & x & Hx & _).
    destruct (s_held_end s es a2 o2 Hes Ha2 Ho2) as (S2 & x2 & Hx2 & _).
    assert (edual o ∈ dom A) as HdA by (rewrite (s_domA _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh').
    apply elem_of_dom in HdA as [[S' x'] HA'].
    assert (kres K s A !! edual o = Some (S', x')) as Hx' by (apply lookup_kres; split; [done|eauto]).
    pose proof (s_ready s es a2 o2 S2 x2 (edual o) S' x' Hes Ha2 Ho2 Hx2 Hx' (not_eq_sym Hne)) as Hlt.
    apply lookup_kres in Hx as [HA _]. apply lookup_kres in Hx2 as [HA2 _].
    destruct (s_sdual _ _ _ _ _ _ _ _ Hs o S0 x S' x' HA HA') as [-> _].
    rewrite pt_dual_dual in Hlt.
    rewrite (s_kpt _ _ _ _ _ _ _ _ Hs o2 S2 x2 HA2), (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x HA). done.
  Qed.

  (** A link redex has a restricted end. *)
  Lemma s_link t e o1 o2 : q.2 !! t = Some e → act e = Some (ALink o1 o2) → ech o1 ∈ q.1 ∨ ech o2 ∈ q.1.
  Proof.
    intros He Ha. destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e' He'].
    pose proof (l_obl t e _ e' He He') as H. cbn [Eobl] in H.
    destruct H as (p1 & p2 & S1 & S2 & x & Hos & _ & Hp1 & _).
    destruct (s_owner_of _ _ _ Hp1) as (h & Kh & _).
    assert (ech p1 ∈ q.1) as Hc by (apply (s_closed _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in Kh).
    assert (p1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as Hin by (rewrite Hos; set_solver).
    apply elem_of_union in Hin as [Hin|Hin]; apply elem_of_singleton in Hin as ->; auto.
  Qed.
End local.
