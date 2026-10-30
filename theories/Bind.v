(** * Evaluation contexts (the bind lemma for the term relation)

    Running K[e] runs e while e is not a value, with the context's
    environment Θ2 inert, and hands over to the continuation once e is a
    value. The frame of e must lie below the heads of Θ2 ([heads_above]),
    so that every entry of Θ2 sits above whatever e offers. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export PTerm.

Set Default Proof Using "All".

(** Every entry of Θ2 lies at or above some point of H. *)
Definition heads_above (W : world) (H : gset point) (Θ2 : tenv) : Prop :=
  ∀ k e, tenv_entry Θ2 k = Some e → ∃ h, h ∈ H ∧ w_le W h e.2.

Lemma heads_above_mono W W' H Θ2 : wext W W' → heads_above W H Θ2 → heads_above W' H Θ2.
Proof.
  intros (_ & Heq & Hlt & _) Hh k e He. destruct (Hh k e He) as (h & Hh1 & [Hq|Hq]).
  - exists h. split; [done|]. left. by apply Heq.
  - exists h. split; [done|]. right. by apply Hlt.
Qed.

(** ** Composition, pointwise *)

Lemma comp_lookup R Θ Θ1 Θ2 c :
  tenv_comp R Θ Θ1 Θ2 → Θ2 !! c = None → Θ !! c = Θ1 !! c.
Proof. intros [Hj _] H2. specialize (Hj c). rewrite H2 in Hj. by inversion Hj. Qed.

Lemma comp_set R Θ Θ1 Θ2 c o :
  tenv_comp R Θ Θ1 Θ2 → Θ2 !! c = None →
  tenv_comp R (partial_alter (λ _, o) c Θ) (partial_alter (λ _, o) c Θ1) Θ2.
Proof.
  intros [Hj Hd] H2. split.
  - intros x. destruct (decide (x = c)) as [->|Hx].
    + rewrite !lookup_partial_alter_eq, H2. destruct o; constructor.
    + rewrite !lookup_partial_alter_ne by done. apply Hj.
  - intros x e1 e2. destruct (decide (x = c)) as [->|Hx]; [by rewrite H2|].
    rewrite lookup_partial_alter_ne by done. apply Hd.
Qed.

Lemma comp_comm R Θ Θ1 Θ2 :
  (∀ x y, R x y → R y x) → tenv_comp R Θ Θ1 Θ2 → tenv_comp R Θ Θ2 Θ1.
Proof.
  intros Hs [Hj Hd]. split.
  - intros x. specialize (Hj x). inversion Hj; constructor.
  - intros x e1 e2 H1 H2. destruct (Hd x e2 e1 H2 H1). split; [auto|by apply sdual_sym].
Qed.

(** Reassociation: Θ = (Θc, Θd), Θb  gives  Θ = (Θc, Θb), Θd. *)
Definition tjoin (Θc Θb : tenv) : tenv :=
  merge (λ oc ob, match oc, ob with
                  | Some (One e1), Some (One e2) => Some (Both e1 e2)
                  | Some o, None => Some o
                  | None, Some o => Some o
                  | _, _ => None
                  end) Θc Θb.

(** The same, with the order of a both-ends entry taken from Θ. *)
Definition tjoin_as (Θ Θc Θb : tenv) : tenv :=
  merge (λ ox o, match ox, o with
                 | Some (Both _ _), Some (Both e1 e2) => Some (Both e1 e2)
                 | _, _ => ox
                 end) (tjoin Θc Θb) Θ.

Ltac jcases x Θs :=
  let rec go l :=
    lazymatch l with
    | (?M, ?r) => let E := fresh "E" in destruct (M !! x) as [[]|] eqn:E; go r
    | tt => idtac
    end in go Θs.

Lemma comp_assoc R Θ Θa Θb Θc Θd :
  (∀ x y, R x y → R y x) →
  tenv_comp R Θ Θa Θb → tenv_comp R Θa Θc Θd →
  tenv_comp R (tjoin_as Θ Θc Θb) Θc Θb ∧ tenv_comp R Θ (tjoin_as Θ Θc Θb) Θd.
Proof.
  intros Hs [Hj1 Hd1] [Hj2 Hd2].
  split; split.
  - intros x. unfold tjoin_as, tjoin. rewrite !lookup_merge. specialize (Hj1 x). specialize (Hj2 x).
    jcases x (Θc, (Θb, (Θd, (Θa, (Θ, tt))))); simpl; rewrite ?E, ?E0, ?E1, ?E2, ?E3 in *;
      inversion Hj1; inversion Hj2; subst; try constructor.
  - intros x e1 e2 Hc Hb. specialize (Hj1 x). specialize (Hj2 x).
    jcases x (Θd, (Θa, tt)); rewrite ?Hc, ?Hb, ?E, ?E0 in *;
      inversion Hj2; inversion Hj1; subst; eauto.
  - intros x. unfold tjoin_as, tjoin. rewrite !lookup_merge. specialize (Hj1 x). specialize (Hj2 x).
    jcases x (Θc, (Θb, (Θd, (Θa, (Θ, tt))))); simpl; rewrite ?E, ?E0, ?E1, ?E2, ?E3 in *;
      inversion Hj1; inversion Hj2; subst; constructor.
  - intros x e1 e2 HX Hdx. unfold tjoin_as, tjoin in HX. rewrite !lookup_merge in HX.
    specialize (Hj1 x). specialize (Hj2 x). specialize (Hd1 x). specialize (Hd2 x).
    jcases x (Θc, (Θb, (Θa, (Θ, tt)))); simpl in HX; rewrite ?Hdx, ?E, ?E0, ?E1, ?E2 in *;
      simplify_eq; inversion Hj2; inversion Hj1; subst; eauto.
all: destruct (Hd1 _ _ eq_refl eq_refl); split; [by apply Hs|by apply sdual_sym].
Qed.

(** ** The redex of e acts on no channel of the context *)

Lemma tenv_hd_one Θ c e1 u k Θr :
  Θ !! c = Some (One e1) → tenv_hd Θ c u k Θr → e1.2 = k ∧ unfoldS e1.1 = u.
Proof.
  intros Hc (s & [(_ & ->)|(e' & _ & [->| ->])] & Hu);
    rewrite lookup_insert_eq in Hc; by simplify_eq.
Qed.

Lemma sess_stable e σ e' : tstep e (LSess σ) e' → stable_t e.
Proof.
  intros Hst α f Hf. destruct (tstep_same_act _ _ _ _ _ Hst Hf) as (a & Ha & Ha').
  destruct a, α; simpl in *; done.
Qed.

Lemma subjs_free n W Θ Θ1 Θ2 Th F H e σ e' :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above W H Θ2 →
  Erel (S n) W Θ1 Th (F ∪ H) e → tstep e (LSess σ) e' → subjs σ ## dom Θ2.
Proof.
  intros [HWf Hirr] [Hj Hd] Hh HE Hst c Hc1 Hc2.
  pose proof (Erel_subjs _ _ _ _ _ _ _ _ HE Hst c Hc1) as Hc1'.
  pose proof (sess_stable _ _ _ Hst) as Hs.
  assert (¬ irred e) as Hni by (intros Hi; by apply (Hi _ _ Hst)).
  pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep.
  apply Erel_S_iff in HE as (_ & Hrdy & _). destruct (Hrdy Hni) as [_ Hfr].
  apply elem_of_dom in Hc1' as [o1 Ho1]. apply elem_of_dom in Hc2 as [o2 Ho2].
  pose proof (Hj c) as Jc. rewrite Ho1, Ho2 in Jc. inversion Jc as [| | |e1 e2|e1 e2]; subst.
  all: destruct (Hd c e1 e2 Ho1 Ho2) as [Hq _].
  all: assert (tenv_entry Θ1 (c, false) = Some e1) as Hen by (unfold tenv_entry; simpl; by rewrite Ho1).
  all: assert (offered_t Θ1 e (c, false)) as Hoff.
  all: try (exists σ, e'; split; [done|];
            destruct σ as [c0 w|c0 w|c0|cd]; simpl in Hc1, Hstep |- *;
            [apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θ1r & m & U & s & k & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & ? & ? & m & U & s & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & k & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|];
             exists e1; split_and!; [done|done|discriminate]
            |split; [done|by eexists]]).
  all: pose proof (Hfr Hs (c, false) e1 Hoff Hen) as Hlt.
  all: assert (tenv_entry Θ2 (c, false) = Some e2) as Hen2 by (unfold tenv_entry; simpl; by rewrite Ho2).
  all: destruct (Hh _ _ Hen2) as (h & HhH & Hle).
  all: pose proof (Hlt h ltac:(set_solver)) as Hlh; unfold entry_head in Hlh; simpl in Hlh.
  all: apply (Hirr e1.2); destruct Hle as [Heq|Hlt'].
  all: try (eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlh|];
            eapply (wf_eq_trans _ HWf); [exact Heq|by apply (wf_eq_sym _ HWf)]).
  all: eapply (wf_lt_eq _ HWf); [apply HWf|eapply (wf_lt_trans _ HWf); [exact Hlh|exact Hlt']|];
         by apply (wf_eq_sym _ HWf).
Qed.

(** ** Moving a head entry between Θ1 and Θ = Θ1, Θ2 *)

Lemma palter_eq (A B : tenv) c :
  (∀ y, y ≠ c → A !! y = B !! y) → partial_alter (λ _, B !! c) c A = B.
Proof.
  intros H. apply map_eq. intros y. destruct (decide (y = c)) as [->|Hy].
  - by rewrite lookup_partial_alter_eq.
  - rewrite lookup_partial_alter_ne by done. by apply H.
Qed.

Lemma ext_transfer A c e B A' B' :
  tenv_ext A c e B → A' !! c = A !! c → B' !! c = B !! c →
  (∀ y, y ≠ c → A' !! y = B' !! y) → tenv_ext A' c e B'.
Proof.
  intros Hx HA HB Hy.
  assert (∀ o, B !! c = Some o → B' = <[c := o]> A') as Hins.
  { intros o Ho. apply map_eq. intros z. destruct (decide (z = c)) as [->|Hz].
    - by rewrite lookup_insert_eq, HB.
    - rewrite lookup_insert_ne by done. symmetry. by apply Hy. }
  destruct Hx as [(H1 & ->)|(e' & H1 & [->| ->])].
  - left. split; [by rewrite HA|]. apply Hins. by rewrite lookup_insert_eq.
  - right. exists e'. split; [by rewrite HA|]. left. apply Hins. by rewrite lookup_insert_eq.
  - right. exists e'. split; [by rewrite HA|]. right. apply Hins. by rewrite lookup_insert_eq.
Qed.

Lemma ext_off A c e B y : tenv_ext A c e B → y ≠ c → A !! y = B !! y.
Proof. intros Hx Hy. by apply (proj2 (tenv_ext_inv _ _ _ _ Hx)). Qed.

(** The composite's head: Θ = Θ1, Θ2 with c ∉ dom Θ2. *)
Lemma comp_ext R Θ Θ1 Θ2 Θ1r c e :
  tenv_comp R Θ Θ1 Θ2 → Θ2 !! c = None → tenv_ext Θ1r c e Θ1 →
  tenv_comp R (partial_alter (λ _, Θ1r !! c) c Θ) Θ1r Θ2 ∧
  tenv_ext (partial_alter (λ _, Θ1r !! c) c Θ) c e Θ.
Proof.
  intros Hc H2 Hx. split.
  - pose proof (comp_set _ _ _ _ c (Θ1r !! c) Hc H2) as H.
    rewrite (palter_eq Θ1 Θ1r c) in H; [done|].
    intros y Hy. symmetry. by apply (ext_off _ _ _ _ _ Hx).
  - eapply ext_transfer; [exact Hx|by rewrite lookup_partial_alter_eq|by apply (comp_lookup R Θ Θ1 Θ2)|].
    intros y Hy. rewrite lookup_partial_alter_ne by done. done.
Qed.

(** The converse: extending the composite's remainder at c. *)
Lemma comp_ext_back R Θr Θ1r Θ2 Θrc c e :
  tenv_comp R Θr Θ1r Θ2 → Θ2 !! c = None → tenv_ext Θr c e Θrc →
  tenv_comp R Θrc (partial_alter (λ _, Θrc !! c) c Θ1r) Θ2 ∧
  tenv_ext Θ1r c e (partial_alter (λ _, Θrc !! c) c Θ1r).
Proof.
  intros Hc H2 Hx. split.
  - pose proof (comp_set _ _ _ _ c (Θrc !! c) Hc H2) as H.
    rewrite (palter_eq Θr Θrc c) in H; [done|].
    intros y Hy. by apply (ext_off _ _ _ _ _ Hx).
  - eapply ext_transfer; [exact Hx|symmetry; by apply (comp_lookup R Θr Θ1r Θ2)|by rewrite lookup_partial_alter_eq|].
    intros y Hy. rewrite lookup_partial_alter_ne by done. done.
Qed.

(** A term with a session step offers some entry. *)
Lemma offered_some n W Θ T F e σ e' :
  Erel (S n) W Θ T F e → tstep e (LSess σ) e' → ∃ k, offered_t Θ e k.
Proof.
  intros HE Hst. pose proof (Erel_subjs _ _ _ _ _ _ _ _ HE Hst) as Hsub.
  pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep.
  assert (∀ c u k Θr, tenv_hd Θ c u k Θr → ∃ b s, tenv_entry Θ (c, b) = Some (s, k) ∧ unfoldS s = u)
    as Hhd.
  { intros c u k Θr (s & [(_ & ->)|(e0 & _ & [->| ->])] & Hu).
    - exists false, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq.
    - exists false, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq.
    - exists true, s. unfold tenv_entry. simpl. by rewrite lookup_insert_eq. }
  destruct σ as [c w|c w|c|cd]; simpl in Hstep.
  - destruct Hstep as (Θ1 & m & U & s & k & Hh & _). destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    exists (c, b), (SRecv c w), e'. split; [done|]. split; [done|]. eauto 10.
  - destruct Hstep as (Θr & ? & ? & m & U & s & k & ? & Hh & _).
    destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    exists (c, b), (SSend c w), e'. split; [done|]. split; [done|]. eauto 10.
  - destruct Hstep as (Θ1 & k & Hh & _). destruct (Hhd _ _ _ _ Hh) as (b & s0 & He & Hu).
    destruct b.
    + destruct (tenv_entry Θ (c, false)) as [e0|] eqn:E0.
      * assert (unfoldS e0.1 = SEnd ∨ unfoldS e0.1 ≠ SEnd) as [Hu0|Hu0]
          by (destruct (unfoldS e0.1); first [by left|by right]).
        -- exists (c, false), (SClos c), e'. split; [done|]. split; [done|].
           exists e0. split_and!; [done|done|discriminate].
        -- exists (c, true), (SClos c), e'. split; [done|]. split; [done|].
           exists (s0, k). split_and!; [done|done|]. intros _ e1 He1. congruence.
      * exists (c, true), (SClos c), e'. split; [done|]. split; [done|].
        exists (s0, k). split_and!; [done|done|]. intros _ e1 He1. congruence.
    + exists (c, false), (SClos c), e'. split; [done|]. split; [done|].
      exists (s0, k). split_and!; [done|done|discriminate].
  - destruct (set_choose_or_empty cd) as [[c Hc]|Hcd].
    + assert (c ∈ dom Θ) as HcΘ by (apply Hsub; done). apply elem_of_dom in HcΘ as [o Ho].
      exists (c, false), (SLink cd), e'. split; [done|]. split; [done|].
      unfold tenv_entry. simpl. rewrite Ho. destruct o; by eexists.
    + exfalso. destruct Hstep as (c & d & ? & ? & ? & ? & ? & ? & -> & _). set_solver.
Qed.

(** ** Readiness of K[e] *)

Lemma lt_le_W W x y z : world_wf W → w_lt W x y → w_le W y z → w_lt W x z.
Proof.
  intros HW Hxy [Hyz|Hyz].
  - eapply (wf_lt_eq _ HW); [apply HW|exact Hxy|exact Hyz].
  - eapply (wf_lt_trans _ HW); eauto.
Qed.

Lemma eq_le_W W x y z : world_wf W → w_le W x y → w_eq W y z → w_le W x z.
Proof.
  intros HW [Hxy|Hxy] Hyz.
  - left. eapply (wf_eq_trans _ HW); eauto.
  - right. eapply (wf_lt_eq _ HW); [apply HW|exact Hxy|exact Hyz].
Qed.

Lemma entry_agree R Θ Θ1 Θ2 c b :
  tenv_comp R Θ Θ1 Θ2 → c ∉ dom Θ2 → tenv_entry Θ (c, b) = tenv_entry Θ1 (c, b).
Proof.
  intros Hc Hc2. unfold tenv_entry. simpl.
  rewrite (comp_lookup R Θ Θ1 Θ2); [done|done|by apply not_elem_of_dom].
Qed.

Section bind_ready.
  Context (n : nat) (W : world) (Θ Θ1 Θ2 : tenv) (Th : ty) (F H : gset point).
  Context (f : frame) (e : expr).
  Context (Hf : frame_val f) (Hv : ¬ is_val e) (HW : strict W).
  Context (Hc : tenv_comp (w_eq W) Θ Θ1 Θ2) (Hh : heads_above W H Θ2).
  Context (HE : Erel (S n) W Θ1 Th (F ∪ H) e).

  Lemma br_up k : offered_t Θ1 e k → offered_t Θ (fill_frame f e) k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & e' & Hst & Hsel).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (subjs_free _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hst (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, (fill_frame f e'). split; [by apply tstep_fill|].
    eapply selects_agree; [|exact Hsel]. intros y Hy.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (subjs_free _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hst y Hy).
  Qed.

  Lemma br_down k : offered_t Θ (fill_frame f e) k → offered_t Θ1 e k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & E' & Hst & Hsel).
    destruct (tstep_fill_inv _ _ _ _ Hf Hv Hst) as (e' & Hst' & ->).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (subjs_free _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hst' (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, e'. split; [done|].
    eapply selects_agree; [|exact Hsel]. intros y Hy. symmetry.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (subjs_free _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hst' y Hy).
  Qed.

  Lemma br_stable : stable_t (fill_frame f e) → stable_t e.
  Proof. intros Hs α e' Hst. exact (Hs _ _ (tstep_fill _ _ _ _ Hf Hst)). Qed.

  Lemma bind_ready : ready_t W Θ (fill_frame f e) ∧ frame_t W Θ (fill_frame f e) F.
  Proof.
    pose proof HE as HE0. apply Erel_S_iff in HE0 as (Hval & Hrdy & _).
    assert (¬ irred e) as Hni by (intros Hi; apply Hv; by eapply Vrel_val, Hval).
    destruct (Hrdy Hni) as [Hr Hfr].
    split.
    - intros Hs. pose proof (br_stable Hs) as Hse. destruct (Hr Hse) as [_ Hab].
      destruct (tstep_progress e) as [Hi|(α & e' & Hst)]; [by destruct Hni|].
      pose proof (Hse _ _ Hst) as Hα. destruct α as [|σ|c|w]; try done.
      destruct (offered_some _ _ _ _ _ _ _ _ HE Hst) as [k0 Hk0].
      destruct (br_up k0 Hk0) as [Hk0' Hk0f].
      split; [intros Hno; exfalso; exact (Hno k0 Hk0')|].
      intros [c b] ent Hent Hnot.
      destruct (decide (c ∈ dom Θ2)) as [Hin|Hnin].
      + assert (∃ ent0, tenv_entry Θ1 k0 = Some ent0) as [ent0 Hent0].
        { destruct Hk0 as (σ0 & e0 & Hst0 & Hsel0). by apply (selects_entry _ σ0). }
        assert (∃ h, h ∈ H ∧ w_le W h ent.2) as (h & HhH & Hle).
        { apply elem_of_dom in Hin as [o2 Ho2]. destruct Hc as [Hj Hd].
          pose proof (Hj c) as Jc. unfold tenv_entry in Hent. simpl in Hent. rewrite Ho2 in Jc.
          destruct (Θ1 !! c) as [o1|] eqn:Ho1, (Θ !! c) as [o|] eqn:Ho;
            inversion Jc; subst; try done.
          all: first [ (apply (Hh (c, b)); unfold tenv_entry; simpl; rewrite Ho2; done) | lazymatch type of Ho1 with _ = Some (One ?e1) => lazymatch type of Ho2 with _ = Some (One ?e2) =>
                     destruct (Hh (c, false) e2) as (h & Hh1 & Hh2);
                       [unfold tenv_entry; simpl; by rewrite Ho2|];
                     destruct (Hd c e1 e2 Ho1 Ho2) as [Hq _];
                     exists h; split; [done|];
                     destruct b; simplify_eq; first
                       [done|eapply eq_le_W; [apply HW|exact Hh2|by apply (wf_eq_sym _ (proj1 HW))]]
                 end end ]. }
        exists k0, ent0. split_and!; [done| |].
        * rewrite <-Hent0. destruct k0. by apply (entry_agree _ _ _ _ _ _ Hc).
        * eapply lt_le_W; [apply HW| |exact Hle].
          exact (Hfr Hse k0 ent0 Hk0 Hent0 h ltac:(set_solver)).
      + rewrite (entry_agree _ _ _ _ _ _ Hc) in Hent by done.
        destruct (Hab (c, b) ent Hent) as (k' & ent' & Ho' & He' & Hlt).
        { intros Ho. apply Hnot. exact (proj1 (br_up _ Ho)). }
        destruct (br_up k' Ho') as [Ho'' Hk'f].
        exists k', ent'. split_and!; [done| |done].
        rewrite <-He'. destruct k'. by apply (entry_agree _ _ _ _ _ _ Hc).
    - intros Hs k ent Ho Hent y Hy.
      destruct (br_down k Ho) as [Ho' Hkf].
      rewrite (surjective_pairing k), (entry_agree _ _ _ _ _ _ Hc) in Hent by done.
      rewrite <-surjective_pairing in Hent.
      exact (Hfr (br_stable Hs) k ent Ho' Hent y ltac:(set_solver)).
  Qed.
End bind_ready.
