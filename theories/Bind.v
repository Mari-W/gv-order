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
