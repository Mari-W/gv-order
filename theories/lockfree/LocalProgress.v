(** * Local progress from readiness (lock-freedom plan §3.3, stage 1 item 3)

    [local_progress_ready]: in a configuration whose threads are ready
    in one strict world (ready_t of Readiness.v, one environment Θ t
    and one future F t per thread), the chain of waits from every
    pending thread ends in an enabled thread. A blocked thread offers
    an entry at x. The holder of the partner entry, at x̄, either
    offers it, and then the two meet, or holds it unoffered, and then
    by below_rest it offers an entry strictly below x. The heads held in
    the configuration are finitely many and the world is strict, so the
    descent stops.

    The per-thread readiness is a hypothesis. It does not follow from
    [∀ n, LPrel n W ∅ T p]: at Σ = ∅ the process relation compares no
    internal entries, so a closed related process can contain a
    blocked thread whose partner never exists. See
    theories/lockfree/open/LocalProgressLR.v, outside the build. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Fair relation.Readiness.

(** ** Offered entries are decidable *)

Definition is_snd (s : sty) : bool := match s with SSeq (SSnd _ _) _ => true | _ => false end.
Definition is_rcv (s : sty) : bool := match s with SSeq (SRcv _ _) _ => true | _ => false end.
Definition is_end (s : sty) : bool := match s with SEnd => true | _ => false end.
Definition is_plus (s : sty) : bool := match s with SPlus _ _ => true | _ => false end.
Definition is_with (s : sty) : bool := match s with SWith _ _ => true | _ => false end.

(** An entry at k whose point has polarity b and whose type passes f. *)
Definition ent_ok (Θ : tenv) (k : ekey) (b : bool) (f : sty → bool) : bool :=
  match tenv_entry Θ k with
  | Some e => bool_decide (pt_pol e.2 = b) && f (unfoldS e.1)
  | None => false
  end.

Definition selb (Θ : tenv) (σ : slabel) (k : ekey) : bool :=
  match σ with
  | SSend c _ => bool_decide (k.1 = c.1) && ent_ok Θ k c.2 is_snd
  | SRecv c _ => bool_decide (k.1 = c.1) && ent_ok Θ k c.2 is_rcv
  | SClos c => bool_decide (k.1 = c.1) && ent_ok Θ k c.2 is_end &&
      (negb k.2 || negb (ent_ok Θ (c.1, false) c.2 is_end))
  | SLink cd =>
      match tenv_entry Θ k with Some e => bool_decide ((k.1, pt_pol e.2) ∈ cd) | None => false end
  | SSel c _ => bool_decide (k.1 = c.1) && ent_ok Θ k c.2 is_plus
  | SBra c _ => bool_decide (k.1 = c.1) && ent_ok Θ k c.2 is_with
  end.

Lemma ent_ok_snd Θ k b :
  (∃ e m T s, tenv_entry Θ k = Some e ∧ pt_pol e.2 = b ∧ unfoldS e.1 = SSeq (SSnd m T) s)
  ↔ ent_ok Θ k b is_snd = true.
Proof.
  unfold ent_ok. destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
  rewrite andb_true_iff, bool_decide_eq_true.
  split; [intros (? & m & T & s & [=<-] & Hb & ->); done|].
  intros [Hb Hu]. destruct (unfoldS e.1) as [| | | | | | |s1 s2| |] eqn:Hu'; try done.
  destruct s1; try done. by eexists _, _, _, _.
Qed.

Lemma ent_ok_rcv Θ k b :
  (∃ e m T s, tenv_entry Θ k = Some e ∧ pt_pol e.2 = b ∧ unfoldS e.1 = SSeq (SRcv m T) s)
  ↔ ent_ok Θ k b is_rcv = true.
Proof.
  unfold ent_ok. destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
  rewrite andb_true_iff, bool_decide_eq_true.
  split; [intros (? & m & T & s & [=<-] & Hb & ->); done|].
  intros [Hb Hu]. destruct (unfoldS e.1) as [| | | | | | |s1 s2| |] eqn:Hu'; try done.
  destruct s1; try done. by eexists _, _, _, _.
Qed.

Lemma ent_ok_plus Θ k b :
  (∃ e s1 s2, tenv_entry Θ k = Some e ∧ pt_pol e.2 = b ∧ unfoldS e.1 = SPlus s1 s2)
  ↔ ent_ok Θ k b is_plus = true.
Proof.
  unfold ent_ok. destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
  rewrite andb_true_iff, bool_decide_eq_true.
  split; [intros (? & s1 & s2 & [=<-] & Hb & ->); done|].
  intros [Hb Hu]. destruct (unfoldS e.1) eqn:Hu'; try done. by eexists _, _, _.
Qed.

Lemma ent_ok_with Θ k b :
  (∃ e s1 s2, tenv_entry Θ k = Some e ∧ pt_pol e.2 = b ∧ unfoldS e.1 = SWith s1 s2)
  ↔ ent_ok Θ k b is_with = true.
Proof.
  unfold ent_ok. destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
  rewrite andb_true_iff, bool_decide_eq_true.
  split; [intros (? & s1 & s2 & [=<-] & Hb & ->); done|].
  intros [Hb Hu]. destruct (unfoldS e.1) eqn:Hu'; try done. by eexists _, _, _.
Qed.

Lemma is_end_spec s : is_end s = true ↔ s = SEnd.
Proof. destruct s; naive_solver. Qed.

Lemma ent_ok_end Θ k b :
  (∃ e, tenv_entry Θ k = Some e ∧ pt_pol e.2 = b ∧ unfoldS e.1 = SEnd)
  ↔ ent_ok Θ k b is_end = true.
Proof.
  unfold ent_ok. destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
  rewrite andb_true_iff, bool_decide_eq_true, is_end_spec. naive_solver.
Qed.

Lemma selb_spec Θ σ k : selects Θ σ k ↔ selb Θ σ k = true.
Proof.
  destruct σ as [c v|c v|c|cd|c b|c b]; simpl; rewrite ?andb_true_iff, ?bool_decide_eq_true.
  - rewrite <-ent_ok_rcv. done.
  - rewrite <-ent_ok_snd. done.
  - rewrite orb_true_iff, !negb_true_iff, <-ent_ok_end.
    split.
    + intros (Hc & e & He & Hp & Hu & Hk). split_and!; [done|by exists e|].
      destruct k as [c' []]; simpl in *; [right|by left].
      destruct (ent_ok Θ (c.1, false) c.2 is_end) eqn:He'; [|done].
      apply ent_ok_end in He' as (e' & He' & Hp' & Hu'). exfalso. by apply (Hk eq_refl e').
    + intros [[Hc (e & He & Hp & Hu)] Hk]. split; [done|]. exists e. split_and!; [done|done|done|].
      intros Hk2 e' He' Hp' Hu'. destruct Hk as [Hk|Hk]; [by rewrite Hk2 in Hk|].
      assert (ent_ok Θ (c.1, false) c.2 is_end = true) as Hok by (apply ent_ok_end; eauto).
      congruence.
  - destruct (tenv_entry Θ k) as [e|]; [|naive_solver].
    rewrite bool_decide_eq_true. naive_solver.
  - rewrite <-ent_ok_plus. done.
  - rewrite <-ent_ok_with. done.
Qed.

Global Instance selects_dec Θ σ k : Decision (selects Θ σ k).
Proof. destruct (decide (selb Θ σ k = true)); [left|right]; by rewrite selb_spec. Defined.

Definition lbl_of (a : action) : option slabel :=
  match a with
  | ARecv c => Some (SRecv c EUnit)
  | ASend c v => Some (SSend c v)
  | AClos c => Some (SClos c)
  | ALink c d => Some (SLink {[c; d]})
  | ASel c b => Some (SSel c b)
  | ABra c => Some (SBra c false)
  | _ => None
  end.

Lemma offered_act Θ e k :
  offered_t Θ e k ↔ ∃ a σ, act e = Some a ∧ lbl_of a = Some σ ∧ selects Θ σ k.
Proof.
  split.
  - intros (σ0 & e' & Hst & Hsel). destruct (act_step _ _ _ Hst) as (a & Ha & Ho).
    exists a. destruct a, σ0; simpl in Ho; try done; eexists; split_and!; try done.
    all: destruct_and?; subst; done.
  - intros (a & σ & Ha & Hl & Hsel). exists σ.
    destruct (act_offer e a (LSess σ)) as [e' He']; [done| |by exists e'].
    destruct a; simpl in Hl; simplify_eq; simpl; done.
Qed.

Global Instance offered_t_dec Θ e k : Decision (offered_t Θ e k).
Proof.
  destruct (act e) as [a|] eqn:Ha.
  - destruct (lbl_of a) as [σ|] eqn:Hl.
    + destruct (decide (selects Θ σ k)) as [Hs|Hs]; [left|right]; rewrite offered_act.
      * eauto.
      * intros (a' & σ' & Ha' & Hl' & Hs'). simplify_eq. done.
    + right. rewrite offered_act. intros (a' & σ' & Ha' & Hl' & _). simplify_eq.
  - right. rewrite offered_act. intros (a' & σ' & Ha' & _). simplify_eq.
Defined.

(** ** Facts about offered entries *)

Lemma selects_entry Θ σ k : selects Θ σ k → ∃ e, tenv_entry Θ k = Some e.
Proof.
  destruct σ; simpl; naive_solver.
Qed.

Lemma selects_subj Θ σ k : selects Θ σ k → k.1 ∈ subjs σ.
Proof.
  destruct σ; simpl; try set_solver.
  intros (e & _ & H). apply elem_of_map. by exists (k.1, pt_pol e.2).
Qed.

Lemma tenv_entry_dom Θ k e : tenv_entry Θ k = Some e → k.1 ∈ dom Θ.
Proof.
  unfold tenv_entry. intros H. apply elem_of_dom.
  destruct (Θ !! k.1); [done|]. by destruct k.2.
Qed.

Lemma act_val e : is_val e → act e = None.
Proof.
  induction e; simpl; try done; intros Hv; try by apply IHe.
  apply andb_True in Hv as [H1 H2]. rewrite (is_val_true _ H1). by apply IHe2.
Qed.

Lemma sess_stable e a : act e = Some a → is_sess a → stable_t e.
Proof.
  intros Ha Hs α e' Hst. destruct (act_step _ _ _ Hst) as (a' & Ha' & Ho).
  rewrite Ha in Ha'. injection Ha' as <-. destruct α; try done; exfalso.
  all: destruct a; simpl in Ho; try done; destruct Hs as [? Hs]; discriminate.
Qed.

(** A session redex has a session step. *)
Lemma sess_stable_step e a : act e = Some a → is_sess a → ∃ σ e', tstep e (LSess σ) e'.
Proof.
  intros Ha [S HS]. destruct a; simpl in HS; try discriminate.
  - destruct (act_offer e (ARecv c) (LSess (SRecv c EUnit)) Ha) as [e' He']; [done|]. eauto.
  - destruct (act_offer e (ASend c v) (LSess (SSend c v)) Ha) as [e' He']; [done|]. eauto.
  - destruct (act_offer e (AClos c) (LSess (SClos c)) Ha) as [e' He']; [done|]. eauto.
  - destruct (act_offer e (ALink c d) (LSess (SLink {[c; d]})) Ha) as [e' He']; [done|]. eauto.
  - destruct (act_offer e (ASel c b) (LSess (SSel c b)) Ha) as [e' He']; [done|]. eauto.
  - destruct (act_offer e (ABra c) (LSess (SBra c false)) Ha) as [e' He']; [done|]. eauto.
Qed.

Lemma offered_pend Θ e k : offered_t Θ e k → ∃ a S, act e = Some a ∧ asubjs a = Some S ∧ k.1 ∈ S.
Proof.
  intros (σ & e' & Hst & Hsel). destruct (act_step _ _ _ Hst) as (a & Ha & Ho).
  exists a, (subjs σ). split_and!; [done|by apply offers_asubjs|by apply (selects_subj Θ)].
Qed.

(** The end of an offered entry is an end of the redex. *)
Lemma offered_aends Θ e k ek :
  offered_t Θ e k → tenv_entry Θ k = Some ek →
  ∃ a S, act e = Some a ∧ aends a = Some S ∧ (k.1, pt_pol ek.2) ∈ S.
Proof.
  intros (σ & e' & Hst & Hsel) Hk. destruct (act_step _ _ _ Hst) as (a & Ha & Ho).
  exists a. destruct σ as [o w|o w|o|cd|o b|o b]; simpl in Hsel.
  - apply offers_recv in Ho as ->. exists {[o]}. split_and!; [done|done|].
    destruct Hsel as (H1 & x & m & T & s & Hx & Hp & _). rewrite Hk in Hx. injection Hx as <-.
    destruct o as [c b]; simpl in *; subst. set_solver.
  - apply offers_send in Ho as ->. exists {[o]}. split_and!; [done|done|].
    destruct Hsel as (H1 & x & m & T & s & Hx & Hp & _). rewrite Hk in Hx. injection Hx as <-.
    destruct o as [c b]; simpl in *; subst. set_solver.
  - apply offers_clos in Ho as ->. exists {[o]}. split_and!; [done|done|].
    destruct Hsel as (H1 & x & Hx & Hp & _). rewrite Hk in Hx. injection Hx as <-.
    destruct o as [c b]; simpl in *; subst. set_solver.
  - apply offers_link in Ho as (c & d & -> & Hcd). exists {[c; d]}. split_and!; [done|done|].
    destruct Hsel as (x & Hx & Hin). rewrite Hk in Hx. injection Hx as <-. by rewrite <-Hcd.
  - apply offers_sel in Ho as ->. exists {[o]}. split_and!; [done|done|].
    destruct Hsel as (H1 & x & s1 & s2 & Hx & Hp & _). rewrite Hk in Hx. injection Hx as <-.
    destruct o as [c b']; simpl in *; subst. set_solver.
  - apply offers_bra in Ho as ->. exists {[o]}. split_and!; [done|done|].
    destruct Hsel as (H1 & x & s1 & s2 & Hx & Hp & _). rewrite Hk in Hx. injection Hx as <-.
    destruct o as [c b']; simpl in *; subst. set_solver.
Qed.

(** An offered entry exists when the thread is not a value. *)
Lemma offered_exists W Θ F e :
  ready_t W Θ F e → stable_t e → ¬ is_val e →
  ∃ k, offered_t Θ e k.
Proof.
  intros Hr Hs Hv. destruct (Hr Hs) as [Hnone _].
  set (keys := mbind (λ c : chan, [(c, false); (c, true)]) (elements (dom Θ))).
  destruct (decide (Exists (offered_t Θ e) keys)) as [Hex|Hn].
  - apply Exists_exists in Hex as (k & _ & Hk). by exists k.
  - exfalso. apply Hv, Hnone. intros k Hk. apply Hn, Exists_exists. exists k. split; [|done].
    destruct Hk as (σ & e' & _ & Hsel). destruct (selects_entry _ _ _ Hsel) as [ek Hek].
    apply tenv_entry_dom, elem_of_elements in Hek.
    apply list_elem_of_bind. exists k.1. split; [|done].
    destruct k as [c []]; simpl; set_solver.
Qed.

(** ** Strict orders on finite sets are well founded *)

Lemma strict_finite_acc (lt : point → point → Prop) (P : gset point) :
  (∀ x y z, lt x y → lt y z → lt x z) → (∀ x, ¬ lt x x) →
  ∀ x, Acc (λ y x, y ∈ P ∧ lt y x) x.
Proof.
  intros Htr Hirr.
  assert (∀ n (S : gset point), size S ≤ n → ∀ x, (∀ y, y ∈ P → lt y x → y ∈ S) →
            Acc (λ y x, y ∈ P ∧ lt y x) x) as H.
  { induction n as [|n IH]; intros S HS x Hx; constructor; intros y [HyP Hyx].
    - apply Nat.le_0_r, size_empty_inv in HS. apply leibniz_equiv in HS. subst S.
      specialize (Hx y HyP Hyx). set_solver.
    - apply (IH (S ∖ {[y]})).
      + assert (y ∈ S) as HyS by auto. rewrite size_difference by set_solver.
        rewrite size_singleton. lia.
      + intros z HzP Hzy. apply elem_of_difference. split.
        * apply Hx; [done|]. by apply (Htr _ y).
        * intros Hz%elem_of_singleton. subst z. by apply (Hirr y). }
  intros x. by apply (H (size P) P).
Qed.

(** ** The lemma *)

Definition ends_pts (o : ends) : gset point :=
  match o with One e => {[e.2]} | Both e1 e2 => {[e1.2; e2.2]} end.

Definition tenv_pts (Θ : tenv) : gset point := ⋃ ((λ ce, ends_pts ce.2) <$> map_to_list Θ).

Lemma tenv_pts_entry Θ k e : tenv_entry Θ k = Some e → e.2 ∈ tenv_pts Θ.
Proof.
  unfold tenv_entry, tenv_pts. intros H. apply elem_of_union_list.
  destruct (Θ !! k.1) as [o|] eqn:Ho; [|by destruct k.2].
  exists (ends_pts o). split.
  - apply list_elem_of_fmap. exists (k.1, o). split; [done|]. by apply elem_of_map_to_list.
  - destruct o, k.2; simplify_eq; simpl; set_solver.
Qed.

Section local_progress.
  Context (q : config) (W : world) (Θ : nat → tenv) (F : nat → gset point).
  Context (HW : strict W).
  Context (Hready : ∀ t e, q.2 !! t = Some e → ¬ irred e → ready_t W (Θ t) (F t) e).
  Context (Hirr : ∀ t e k ek, q.2 !! t = Some e → tenv_entry (Θ t) k = Some ek → ¬ irred e).
  Context (Hmention : ∀ t e k ek, q.2 !! t = Some e → tenv_entry (Θ t) k = Some ek →
             (k.1, pt_pol ek.2) ∈ fends e).
  Context (Hpartner : ∀ t e k ek, q.2 !! t = Some e → tenv_entry (Θ t) k = Some ek →
             ∃ s es k' ek', q.2 !! s = Some es ∧ tenv_entry (Θ s) k' = Some ek' ∧
               k'.1 = k.1 ∧ (s, k') ≠ (t, k) ∧ ek'.2 = pt_dual ek.2).
  Context (Hmeet : ∀ t e s es k ek k' ek', q.2 !! t = Some e → q.2 !! s = Some es →
             offered_t (Θ t) e k → offered_t (Θ s) es k' →
             tenv_entry (Θ t) k = Some ek → tenv_entry (Θ s) k' = Some ek' →
             k'.1 = k.1 → (s, k') ≠ (t, k) → ek'.2 = pt_dual ek.2 →
             enabled q t ∨ enabled q s).
  Context (Hlink : ∀ t e, q.2 !! t = Some e → link_t e → enabled q t).

  Definition all_pts : gset point :=
    ⋃ ((λ te : nat * expr, tenv_pts (Θ te.1)) <$> map_to_list q.2).

  Lemma all_pts_entry t e k ek :
    q.2 !! t = Some e → tenv_entry (Θ t) k = Some ek → ek.2 ∈ all_pts.
  Proof.
    intros Ht Hk. apply elem_of_union_list. exists (tenv_pts (Θ t)). split.
    - apply list_elem_of_fmap. exists (t, e). split; [done|]. by apply elem_of_map_to_list.
    - by eapply tenv_pts_entry.
  Qed.

  (** A step of the chain from t to s, for s ≠ t. *)
  Lemma waits_of t e (k : ekey) (ek : sty * point) s es (k' : ekey) (ek' : sty * point) :
    q.2 !! t = Some e → offered_t (Θ t) e k → tenv_entry (Θ t) k = Some ek →
    q.2 !! s = Some es → k'.1 = k.1 → ek'.2 = pt_dual ek.2 →
    (k'.1, pt_pol ek'.2) ∈ fends es → s ≠ t → waits q t s.
  Proof.
    intros He Ho Hk Hes Hk1 Hd Hm Hst.
    destruct (offered_aends _ _ _ _ Ho Hk) as (a & S & Ha & HS & HkS).
    split; [done|]. exists e, a, S, (k.1, pt_pol ek.2), es. split_and!; try done.
    unfold cdual. simpl. rewrite Hk1, Hd in Hm. exact Hm.
  Qed.

  Lemma chain_from x :
    ∀ t e k ek, q.2 !! t = Some e → offered_t (Θ t) e k → tenv_entry (Θ t) k = Some ek →
      ek.2 = x → ∃ u, rtc (waits q) t u ∧ enabled q u.
  Proof.
    destruct HW as [HWwf Hirrefl].
    induction (strict_finite_acc (w_lt W) all_pts (wf_lt_trans W HWwf) Hirrefl x)
      as [x _ IH].
    intros t e k ek He Ho Hk Hx.
    destruct (Hpartner t e k ek He Hk) as (s & es & k' & ek' & Hes & Hk' & Hk1 & Hne & Hd).
    (* a step to s, or s is t itself *)
    assert (∀ u, rtc (waits q) s u → enabled q u → ∃ u, rtc (waits q) t u ∧ enabled q u)
      as Hvia.
    { intros u Hsu Hu. destruct (decide (s = t)) as [->|Hst]; [by exists u|].
      exists u. split; [|done]. eapply rtc_l; [|exact Hsu].
      eapply waits_of; [exact He|exact Ho|exact Hk|exact Hes|exact Hk1|exact Hd| |exact Hst].
      by eapply Hmention. }
    destruct (decide (offered_t (Θ s) es k')) as [Ho'|Hno'].
    { destruct (Hmeet t e s es k ek k' ek') as [Ht|Hs]; try done.
      - exists t. by split.
      - by apply (Hvia s). }
    destruct (act es) as [a|] eqn:Ha.
    - destruct (admin_or_sess a) as [Had|Hse].
      + apply (Hvia s); [done|]. destruct Had as [Had Hns].
        apply (admin_enabled q s es a Hes Ha Had). intros c d ->. exfalso. apply Hns.
        unfold is_sess. simpl. by eexists.
      + pose proof (Hirr s es k' ek' Hes Hk') as Hnirr.
        destruct (Hready s es Hes Hnirr (sess_stable es a Ha Hse)) as [_ [Hl|Hbr]].
        { apply (Hvia s); [done|]. by apply (Hlink s es). }
        destruct (offered_exists W (Θ s) (F s) es (Hready s es Hes Hnirr)
          (sess_stable es a Ha Hse) (λ Hv, Hnirr (val_irred es Hv))) as [k0 Ho0].
        destruct Ho0 as (σ0 & e0 & Hst0 & Hsel0) eqn:Ho0'.
        destruct (selects_entry _ _ _ Hsel0) as [ek0 Hek0].
        assert (w_lt W ek0.2 x) as Hlt.
        { destruct (Hbr k0 ek0 (ex_intro _ σ0 (ex_intro _ e0 (conj Hst0 Hsel0))) Hek0)
            as [Hb _].
          specialize (Hb k' ek' Hk' Hno'). unfold entry_head in Hb.
          by rewrite Hd, pt_dual_dual, Hx in Hb. }
        destruct (IH ek0.2 (conj (all_pts_entry s es k0 ek0 Hes Hek0) Hlt) s es k0 ek0 Hes
          (ex_intro _ σ0 (ex_intro _ e0 (conj Hst0 Hsel0))) Hek0 eq_refl) as (u & Hsu & Hu).
        by apply (Hvia u).
    - exfalso. apply (Hirr s es k' ek' Hes Hk'). by apply act_None_irred.
  Qed.

  Theorem local_progress_ready : local_progress q.
  Proof.
    intros t (e & a & He & Ha & Hse). simpl in He.
    assert (¬ irred e) as Hnirr.
    { intros Hirr'. destruct (sess_stable_step e a Ha Hse) as (σ & e' & Hst).
      by apply (Hirr' _ _ Hst). }
    destruct (Hready t e He Hnirr (sess_stable e a Ha Hse)) as [_ [Hl|_]].
    { exists t. split; [done|]. by apply (Hlink t e). }
    assert (¬ is_val e) as Hv by (intros Hv; rewrite act_val in Ha; done).
    destruct (offered_exists W (Θ t) (F t) e (Hready t e He Hnirr) (sess_stable e a Ha Hse) Hv)
      as [k Ho].
    destruct Ho as (σ & e' & Hst & Hsel) eqn:Ho'.
    destruct (selects_entry _ _ _ Hsel) as [ek Hek].
    exact (chain_from ek.2 t e k ek He Ho Hek eq_refl).
  Qed.
End local_progress.
