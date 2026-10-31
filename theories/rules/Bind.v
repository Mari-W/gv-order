(** * Evaluation contexts (the bind lemma for the term relation)

    Running K[e] runs e while e is not a value, with the context's
    environment Θ2 inert, and hands over to the continuation once e is a
    value. The frame of e must lie below the heads of Θ2 ([heads_above]),
    so that every entry of Θ2 sits above whatever e offers. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export composition.PTerm.

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

(** With the comparisons of readiness in hand, the redex acts on no
    channel of the context. *)
Lemma subjs_free_br n W Θ Θ1 Θ2 Th F H e σ e' :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above W H Θ2 →
  Erel (S n) W Θ1 Th (F ∪ H) e → below_rest W Θ1 (offered_t Θ1 e) (F ∪ H) →
  tstep e (LSess σ) e' → subjs σ ## dom Θ2.
Proof.
  intros [HWf Hirr] [Hj Hd] Hh HE Hfr Hst c Hc1 Hc2.
  pose proof (Erel_subjs _ _ _ _ _ _ _ _ HE Hst c Hc1) as Hc1'.
  pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hstep.
  apply elem_of_dom in Hc1' as [o1 Ho1]. apply elem_of_dom in Hc2 as [o2 Ho2].
  pose proof (Hj c) as Jc. rewrite Ho1, Ho2 in Jc. inversion Jc as [| | |e1 e2|e1 e2]; subst.
  all: destruct (Hd c e1 e2 Ho1 Ho2) as [Hq _].
  all: assert (tenv_entry Θ1 (c, false) = Some e1) as Hen by (unfold tenv_entry; simpl; by rewrite Ho1).
  all: assert (offered_t Θ1 e (c, false)) as Hoff.
  all: try (exists σ, e'; split; [done|];
            destruct σ as [c0 w|c0 w|c0|cd|c0 i|c0 i]; simpl in Hc1, Hstep |- *;
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
            |split; [done|by eexists]
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & s1 & s2 & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10
            |apply elem_of_singleton in Hc1; subst c0;
             destruct Hstep as (Θr & s1 & s2 & k & ? & Hhd & _);
             destruct (tenv_hd_one _ _ _ _ _ _ Ho1 Hhd) as [_ Hu]; split; [done|]; eauto 10]).
  all: pose proof (proj2 (Hfr (c, false) e1 Hoff Hen)) as Hlt.
  all: assert (tenv_entry Θ2 (c, false) = Some e2) as Hen2 by (unfold tenv_entry; simpl; by rewrite Ho2).
  all: destruct (Hh _ _ Hen2) as (h & HhH & Hle).
  all: pose proof (Hlt h ltac:(set_solver)) as Hlh; unfold entry_head in Hlh; simpl in Hlh.
  all: apply (Hirr e1.2); destruct Hle as [Heq|Hlt'].
  all: try (eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlh|];
            eapply (wf_eq_trans _ HWf); [exact Heq|by apply (wf_eq_sym _ HWf)]).
  all: eapply (wf_lt_eq _ HWf); [apply HWf|eapply (wf_lt_trans _ HWf); [exact Hlh|exact Hlt']|];
         by apply (wf_eq_sym _ HWf).
Qed.

(** A redex other than a link acts on no channel of the context. A link
    may act on the other end of a channel the context holds, because a
    term at a link compares nothing (sharp edges 68). *)
Lemma subjs_free n W Θ Θ1 Θ2 Th F H e σ e' :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above W H Θ2 →
  Erel (S n) W Θ1 Th (F ∪ H) e → tstep e (LSess σ) e' → (∀ cd, σ ≠ SLink cd) →
  subjs σ ## dom Θ2.
Proof.
  intros HW Hc Hh HE Hst Hnl.
  pose proof (sess_stable _ _ _ Hst) as Hs.
  assert (¬ irred e) as Hni by (intros Hi; by apply (Hi _ _ Hst)).
  pose proof HE as HE0. apply Erel_S_iff in HE0 as (_ & Hrdy & _).
  destruct (Hrdy Hni Hs) as [_ [Hl|Hfr]].
  - destruct (link_t_only _ _ _ Hl Hst) as [cd ->]. by destruct (Hnl cd).
  - exact (subjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hfr Hst).
Qed.

(** ** Moving a head entry between Θ1 and Θ = Θ1, Θ2 *)

Lemma comp_entry_some R Θ Θ1 Θ2 k :
  tenv_comp R Θ Θ1 Θ2 → is_Some (tenv_entry Θ1 k) → is_Some (tenv_entry Θ k).
Proof.
  intros [Hj _] Hs. destruct k as [c b]. unfold tenv_entry in *. simpl in *.
  specialize (Hj c).
  destruct (Θ1 !! c) as [[]|], (Θ2 !! c) as [[]|], (Θ !! c) as [[]|];
    inversion Hj; subst; destruct b; simpl in *; try done; by eexists.
Qed.

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

(** The same when Θ2 may hold the other end of c. *)
Lemma comp_ext_gen R Θ Θ1 Θ2 Θ1r c e :
  tenv_comp R Θ Θ1 Θ2 → tenv_ext Θ1r c e Θ1 →
  ∃ Θr, tenv_comp R Θr Θ1r Θ2 ∧ tenv_ext Θr c e Θ.
Proof.
  intros Hc Hx. destruct (Θ2 !! c) as [o2|] eqn:H2.
  2: { exists (partial_alter (λ _, Θ1r !! c) c Θ). by eapply comp_ext. }
  destruct Hc as [Hj Hd]. pose proof (Hj c) as Jc. rewrite H2 in Jc.
  destruct (Θ !! c) as [oc|] eqn:Hoc.
  2: { destruct Hx as [(H1 & ->)|(e' & H1 & [-> | ->])]; rewrite lookup_insert_eq in Jc;
       inversion Jc. }
  destruct Hx as [(H1 & ->)|(e' & H1 & [-> | ->])]; rewrite lookup_insert_eq in Jc;
    inversion Jc as [| | |e1 e2|e1 e2]; subst.
  all: exists (<[c := One e2]> Θ); split; [split|].
  1,4: intros x; destruct (decide (x = c)) as [->|Hx];
       [rewrite lookup_insert_eq, H1, H2; constructor
       |rewrite lookup_insert_ne by done; specialize (Hj x);
        by rewrite lookup_insert_ne in Hj by done].
  1,3: intros x e1' e3 Hx1 Hx2; destruct (decide (x = c)) as [->|Hx];
       [by rewrite H1 in Hx1|apply (Hd x); [by rewrite lookup_insert_ne|done]].
  all: right; exists e2; split; [by rewrite lookup_insert_eq|].
  all: first [ left; apply map_eq; intros x; destruct (decide (x = c)) as [->|Hx];
                [by rewrite lookup_insert_eq, Hoc|by rewrite !lookup_insert_ne]
              | right; apply map_eq; intros x; destruct (decide (x = c)) as [->|Hx];
                [by rewrite lookup_insert_eq, Hoc|by rewrite !lookup_insert_ne] ].
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

  Section bind_ready_br.
  Context (Hbr : below_rest W Θ1 (offered_t Θ1 e) (F ∪ H)).

  Lemma br_up k : offered_t Θ1 e k → offered_t Θ (fill_frame f e) k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & e' & Hst & Hsel).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (subjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, (fill_frame f e'). split; [by apply tstep_fill|].
    eapply selects_agree; [|exact Hsel]. intros y Hy.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (subjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst y Hy).
  Qed.

  Lemma br_down k : offered_t Θ (fill_frame f e) k → offered_t Θ1 e k ∧ k.1 ∉ dom Θ2.
  Proof.
    intros (σ & E' & Hst & Hsel).
    destruct (tstep_fill_inv _ _ _ _ Hf Hv Hst) as (e' & Hst' & ->).
    assert (k.1 ∉ dom Θ2) as Hk.
    { intros Hin. apply (subjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst' (k.1)); [|done].
      by apply (selects_subj _ _ _ Hsel). }
    split; [|done]. exists σ, e'. split; [done|].
    eapply selects_agree; [|exact Hsel]. intros y Hy. symmetry.
    apply (comp_lookup _ _ _ _ _ Hc), not_elem_of_dom.
    exact (subjs_free_br _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hbr Hst' y Hy).
  Qed.
  End bind_ready_br.

  Lemma br_stable : stable_t (fill_frame f e) → stable_t e.
  Proof. intros Hs α e' Hst. exact (Hs _ _ (tstep_fill _ _ _ _ Hf Hst)). Qed.

  Lemma bind_ready : ready_t W Θ F (fill_frame f e).
  Proof.
    pose proof HE as HE0. apply Erel_S_iff in HE0 as (Hval & Hrdy & _).
    assert (¬ irred e) as Hni by (intros Hi; apply Hv; by eapply Vrel_val, Hval).
    intros Hs. pose proof (br_stable Hs) as Hse. destruct (Hrdy Hni Hse) as [_ Hab].
    destruct Hab as [(cd & e1 & Hl)|Hab].
    { (* a link redex: K[e] offers its entries and compares nothing *)
      split; [|left; exists cd, (fill_frame f e1); by apply tstep_fill].
      intros Hno. exfalso.
      destruct (offered_some _ _ _ _ _ _ _ _ HE Hl) as [k0 (σ & e' & Hst & Hsel)].
      destruct (link_t_only e σ e' (ex_intro _ cd (ex_intro _ e1 Hl)) Hst) as [cd' ->].
      apply (Hno k0). exists (SLink cd'), (fill_frame f e'). split; [by apply tstep_fill|].
      destruct Hsel as [Hk Hent]. split; [done|]. exact (comp_entry_some _ _ _ _ _ Hc Hent). }
    split.
    - destruct (tstep_progress e) as [Hi|(α & e' & Hst)]; [by destruct Hni|].
      pose proof (Hse _ _ Hst) as Hα. destruct α as [|σ|c|w]; try done.
      destruct (offered_some _ _ _ _ _ _ _ _ HE Hst) as [k0 Hk0].
      destruct (br_up Hab k0 Hk0) as [Hk0' _].
      intros Hno. exfalso. exact (Hno k0 Hk0').
    - right. intros k0 ent0 Hoff0 Hent0.
      destruct (br_down Hab k0 Hoff0) as [Hk0 Hk0f].
      rewrite (surjective_pairing k0), (entry_agree _ _ _ _ _ _ Hc) in Hent0 by done.
      rewrite <-surjective_pairing in Hent0.
      destruct (Hab k0 ent0 Hk0 Hent0) as [H1 H2]. split.
      + intros [c b] ent Hent Hnot.
        destruct (decide (c ∈ dom Θ2)) as [Hin|Hnin].
        * assert (∃ h, h ∈ H ∧ w_le W h ent.2) as (h & HhH & Hle).
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
          eapply lt_le_W; [apply HW| |exact Hle].
          apply H2. by apply elem_of_union_r.
        * rewrite (entry_agree _ _ _ _ _ _ Hc) in Hent by done.
          apply (H1 (c, b) ent Hent). intros Ho'. apply Hnot. exact (proj1 (br_up Hab _ Ho')).
      + intros y Hy. apply H2. by apply elem_of_union_l.
  Qed.
End bind_ready.

Lemma comp_insert R Θ Θ1 Θ2 c o :
  tenv_comp R Θ Θ1 Θ2 → Θ2 !! c = None → tenv_comp R (<[c := o]> Θ) (<[c := o]> Θ1) Θ2.
Proof.
  intros [Hj Hd] H2. split.
  - intros x. destruct (decide (x = c)) as [->|Hx].
    + rewrite !lookup_insert_eq, H2. constructor.
    + rewrite !lookup_insert_ne by done. apply Hj.
  - intros x e1 e2. destruct (decide (x = c)) as [->|Hx]; [by rewrite H2|].
    rewrite lookup_insert_ne by done. apply Hd.
Qed.

(** ** The bind lemma *)

Lemma Erel_bind n : ∀ f W Θ Θ1 Θ2 Th T F H e,
  frame_val f → strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → heads_above W H Θ2 →
  Erel n W Θ1 Th (F ∪ H) e →
  (∀ W' j Θ1' Θ' v, wext W W' → j ≤ n → tenv_comp (w_eq W') Θ' Θ1' Θ2 →
     Vrel j W' Θ1' Th v → Erel j W' Θ' T F (fill_frame f v)) →
  Erel n W Θ T F (fill_frame f e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros f W Θ Θ1 Θ2 Th T F H e Hf HW Hc Hh HE HK.
  destruct n as [|n']; [apply Erel_0|].
  remember (F ∪ H) as FH eqn:HFH.
  revert Θ Hc HK Hh HW HFH.
  induction HE as [W Θ1 Th FH e Hval Hrdy Hstep] using Erel_S_ind.
  intros Θ Hc HK Hh HW ->.
  assert (HE : Erel (S n') W Θ1 Th (F ∪ H) e).
  { apply Erel_S_iff. split_and!; [done|done|]. intros α e' Hst.
    eapply Ecase_gen_mono; [|exact (Hstep α e' Hst)]. by intros ? ? ? ? ? [? _]. }
  assert (∀ x y, w_eq W x y → w_eq W y x) as Hsym by apply (wf_eq_sym _ (proj1 HW)).
  destruct (is_val e) eqn:Hv.
  { apply (HK W (S n') Θ1 Θ e); [by apply wext_refl|lia|done|].
    apply Hval, val_irred. by rewrite Hv. }
  assert (¬ is_val e) as Hnv by (rewrite Hv; intros []).
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. apply Hnv. eapply Vrel_val, Hval.
    intros α e' Hst. by apply (Hirr α (fill_frame f e')), tstep_fill.
  - intros _. exact (bind_ready n' W Θ Θ1 Θ2 Th F H f e Hf Hnv HW Hc Hh HE).
  - intros α E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
    pose proof (Hstep α e' Hst') as Hcase.
    assert (∀ σ, α = LSess σ → (∀ cd, σ ≠ SLink cd) → subjs σ ## dom Θ2) as Hfree.
    { intros σ ->. exact (subjs_free _ _ _ _ _ _ _ _ _ _ _ HW Hc Hh HE Hst'). }
    assert (∀ W' j, wext W W' → j ≤ n' →
              ∀ W'' j' Θ1' Θ' v, wext W' W'' → j' ≤ j → tenv_comp (w_eq W'') Θ' Θ1' Θ2 →
                Vrel j' W'' Θ1' Th v → Erel j' W'' Θ' T F (fill_frame f v)) as HKd.
    { intros W' j HW' Hj W'' j' Θ1' Θ' v HW'' Hj' Hc' HV.
      apply (HK W'' j' Θ1' Θ' v); [by eapply wext_trans|lia|done|done]. }
    destruct α as [|[c w|c w|c|cd|c i|c i]|c|w]; simpl in Hcase |- *.
    + (* β *)
      eapply (IHn n'); [lia|done|done|done|done|exact Hcase|].
      apply (HKd W n'); [by apply wext_refl|done].
    + (* receive *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & m & U & s & k & (s0 & Hext & Hu) & Hcont).
      destruct (comp_ext _ _ _ _ _ c _ Hc H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), m, U, s, k. split; [by exists s0|].
      intros W' j Θp Θrc Θ' HW' Hj Hextc Hcomp' HV.
      pose proof (proj2 (proj2 (proj2 HW'))) as HWs'.
      assert (∀ x y, w_eq W' x y → w_eq W' y x) as Hsym' by apply (wf_eq_sym _ (proj1 HWs')).
      pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW')) Hcr) as Hcr'.
      destruct (comp_ext_back _ _ _ _ _ c _ Hcr' H2c Hextc) as [Hc1 Hext1].
      destruct (comp_assoc _ _ _ _ _ _ Hsym' Hcomp' Hc1) as [HX1 HX2].
      pose proof (Hcont W' j Θp _ _ HW' Hj Hext1 HX1 HV) as HEj.
      eapply (IHn j); [lia|done|done|exact HX2|by eapply heads_above_mono|exact HEj|].
      apply (HKd W' j); [done|done].
    + (* send *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & A & B & m & U & s & k & Θ1' & (s0 & Hext & Hu) & HcAB & HV & Hext' & HE' & HΦ).
      destruct (comp_ext _ _ _ _ _ c _ Hc H2c Hext) as [Hcr Hextr].
      destruct (comp_assoc _ _ _ _ _ _ Hsym Hcr HcAB) as [HX1 HX2].
      set (X := tjoin_as (partial_alter (λ _, Θ1r !! c) c Θ) A Θ2) in *.
      exists (partial_alter (λ _, Θ1r !! c) c Θ), X, B, m, U, s, k,
        (partial_alter (λ _, Θ1' !! c) c X).
      split_and!; [by exists s0|done|done| |].
      * eapply ext_transfer; [exact Hext'|by apply (comp_lookup _ _ _ _ _ HX1)|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite lookup_partial_alter_ne.
      * pose proof (comp_set _ _ _ _ c (Θ1' !! c) HX1 H2c) as Hcs.
        rewrite (palter_eq A Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
        exact (HΦ _ Hcs HK Hh HW eq_refl).
    + (* close *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1' & k & (s0 & Hext & Hu) & HE' & HΦ).
      destruct (comp_ext _ _ _ _ _ c _ Hc H2c Hext) as [Hcr Hextr].
      exists (partial_alter (λ _, Θ1' !! c) c Θ), k. split; [by exists s0|].
      exact (HΦ _ Hcr HK Hh HW eq_refl).
    + (* link *)
      (* the context may hold the other end of c or d (sharp edges 68) *)
      destruct Hcase as (c & d & Θ1' & Θm & sc & sd & kc & kd & -> & Hx1 & Hx2 & Hdu & Heq & HE' & HΦ).
      destruct (comp_ext_gen _ _ _ _ _ c _ Hc Hx2) as (Θm' & Hcm & Hextm).
      destruct (comp_ext_gen _ _ _ _ _ d _ Hcm Hx1) as (Θ1'' & Hc1 & Hext1).
      eexists c, d, _, _, sc, sd, kc, kd. split_and!; [done|exact Hext1|exact Hextm|done|done|].
      exact (HΦ _ Hc1 HK Hh HW eq_refl).
    + (* select *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE' & HΦ).
      destruct (comp_ext _ _ _ _ _ c _ Hc H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * exact (HΦ _ Hcs HK Hh HW eq_refl).
    + (* branch *)
      assert (Θ2 !! c = None) as H2c.
      { apply not_elem_of_dom. intros Hin. apply (Hfree _ eq_refl ltac:(done) c); [simpl; set_solver|done]. }
      destruct Hcase as (Θ1r & s1 & s2 & k & Θ1' & (s0 & Hext & Hu) & Hext' & HE').
      destruct (comp_ext _ _ _ _ _ c _ Hc H2c Hext) as [Hcr Hextr].
      pose proof (comp_set _ _ _ _ c (Θ1' !! c) Hcr H2c) as Hcs.
      rewrite (palter_eq Θ1r Θ1' c) in Hcs; [|intros y Hy; by apply (ext_off _ _ _ _ _ Hext')].
      exists (partial_alter (λ _, Θ1r !! c) c Θ), s1, s2, k,
        (partial_alter (λ _, Θ1' !! c) c (partial_alter (λ _, Θ1r !! c) c Θ)).
      split_and!; [by exists s0| |].
      * eapply ext_transfer; [exact Hext'|by rewrite lookup_partial_alter_eq|
          by rewrite lookup_partial_alter_eq|].
        intros y Hy. by rewrite !lookup_partial_alter_ne by congruence.
      * eapply (IHn n'); [lia|done|done|exact Hcs|done|exact HE'|].
        apply (HKd W n'); [by apply wext_refl|done].
    + (* new *)
      intros HcΘ.
      assert (Θ1 !! c = None ∧ Θ2 !! c = None) as [H1c H2c].
      { rewrite (tenv_join_dom _ _ _ (proj1 Hc)) in HcΘ.
        split; apply not_elem_of_dom; clear -HcΘ; set_solver. }
      destruct (Hcase ltac:(by apply not_elem_of_dom)) as (a0 & s & s' & W1 & Hfr0 & Hdd & Hwf & HE1).
      destruct (fresh_const (w_names W ∪ tenv_roots Θ ∪ ty_roots T ∪ frame_roots F ∪
                  tenv_roots Θ1 ∪ ty_roots Th ∪ frame_roots (F ∪ H))) as [a1 Ha1].
      destruct (Erel_new_rename n' W W1 Θ1 Th (F ∪ H) e' c s s' a0 a1 (proj1 HW) Hwf Hfr0
                  ltac:(clear -Ha1; set_solver) HE1) as (W1' & Hwf' & HE1').
      exists a1, (stysw a0 a1 s), (stysw a0 a1 s'), W1'. split_and!.
      * clear -Ha1. set_solver.
      * by apply sdual_sw.
      * done.
      * pose proof (proj1 Hwf') as HW1'.
        eapply (IHn n'); [lia|done|exact (proj2 (proj2 (proj2 HW1')))|
          |by eapply heads_above_mono|exact HE1'|].
        { apply comp_insert; [|done]. exact (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW1')) Hc). }
        apply (HKd W1' n'); [done|done].
    + (* spawn *)
      destruct Hcase as (Θa & Θb & ub & lb & HcAB & HV & HE').
      destruct (comp_assoc _ _ _ _ _ _ Hsym Hc (comp_comm _ _ _ _ Hsym HcAB)) as [HX1 HX2].
      exists Θa, (tjoin_as Θ Θb Θ2), ub, lb. split_and!.
      * by apply comp_comm.
      * done.
      * eapply (IHn n'); [lia|done|done|exact HX1|done|exact HE'|].
        apply (HKd W n'); [by apply wext_refl|done].
Qed.
