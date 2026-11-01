(** * A channel at a fresh point between known points (E-NewFresh)

    let (x, y) = new ∗ in e creates its channel at a fresh point (a, 0)
    and places it above the points of L and below the points of H.
    Every point of L lies below every point of H already
    (betweenness), so the facts L ≺ (a, 0) ≺ H relate no two old points
    anew. The world that adds them is a fresh extension W ⊑ₒ W′ placing
    a, the same extension O-New asks for ([wext_fresh_between]). The
    definition of ⊑ₒ is unchanged. It already lets the fresh name
    relate to old points and only forbids new facts among old points
    (docs/extensions/fresh-points.md, sharp edges 90). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.BoxRules.

Set Default Proof Using "All".

(** ** The world with a fresh point between L and H *)

Section between.
  Context (W : world) (a : nat) (L H : list point).
  Context (HW : strict W) (HL : Forall (pt_known W) L) (HH : Forall (pt_known W) H).
  Context (Hbt : ∀ l h, l ∈ L → h ∈ H → w_lt W l h) (Ha : NConst a ∉ w_names W).

  Definition bfacts (x y : point) : Prop :=
    w_lt W x y ∨ (x ∈ L ∧ y = pconst a) ∨ (x = pconst a ∧ y ∈ H).

  Definition Wb : world := wgen (w_names W ∪ {[NConst a]}) (w_eq W) bfacts.

  (** The order of Wb, in closed form. *)
  Definition blt (x y : point) : Prop :=
    w_lt W x y ∨
    ((∃ l, l ∈ L ∧ w_le W x l) ∧ pt_name y = NConst a) ∨
    (x = pconst a ∧ ∃ h, h ∈ H ∧ w_le W h y).

  Let Hwf : world_wf W := proj1 HW.

  Lemma wf_lt_irr h : ¬ w_lt W h h.
  Proof. apply HW. Qed.

  Lemma b_known_L l : l ∈ L → pt_known W l.
  Proof. intros Hl. rewrite Forall_forall in HL. by apply HL. Qed.

  Lemma b_known_H h : h ∈ H → pt_known W h.
  Proof. intros Hh. rewrite Forall_forall in HH. by apply HH. Qed.

  (** An a-rooted point is related in W only to itself and along
      program order. *)
  Lemma b_eq_a z u : pt_root z = NConst a → w_eq W z u → z = u.
  Proof.
    intros Hz He. destruct (wf_eq_supp _ Hwf _ _ He) as [->|[Hz' _]]; [done|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma b_eq_a' z u : pt_root z = NConst a → w_eq W u z → u = z.
  Proof. intros Hz He. symmetry. apply b_eq_a; [done|]. by apply (wf_eq_sym _ Hwf). Qed.

  Lemma b_lt_a_l z u : pt_root z = NConst a → w_lt W z u → pt_name z = pt_name u.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [[? _]|[Hz' _]]; [done|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma b_lt_a_r z u : pt_root z = NConst a → w_lt W u z →
    pt_name u = pt_name z ∧ pt_off u < pt_off z.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [?|[_ Hz']]; [done|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  (** A known point and an a-rooted point are unrelated in W. *)
  Lemma b_le_known_a x z : pt_known W x → pt_root z = NConst a → ¬ w_le W x z.
  Proof.
    intros Hx Hz [He|Hl].
    - apply b_eq_a' in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - destruct (b_lt_a_r _ _ Hz Hl) as [Hn _]. apply Ha. unfold pt_known, pt_root in *.
      rewrite Hn in Hx. congruence.
  Qed.

  Lemma b_le_a_known x z : pt_known W x → pt_root z = NConst a → ¬ w_le W z x.
  Proof.
    intros Hx Hz [He|Hl].
    - apply b_eq_a in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - pose proof (b_lt_a_l _ _ Hz Hl) as Hn. apply Ha. unfold pt_known, pt_root in *.
      rewrite <-Hn in Hx. congruence.
  Qed.

  Lemma b_le_lt x y z : w_le W x y → w_lt W y z → w_lt W x z.
  Proof.
    intros [He|Hl] H2.
    - eapply (wf_lt_eq _ Hwf); [exact He|exact H2|apply (wf_eq_refl _ Hwf)].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma b_lt_le x y z : w_lt W x y → w_le W y z → w_lt W x z.
  Proof.
    intros H1 [He|Hl].
    - eapply (wf_lt_eq _ Hwf); [apply (wf_eq_refl _ Hwf)|exact H1|exact He].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma b_le_le x y z : w_le W x y → w_le W y z → w_le W x z.
  Proof.
    intros [He|Hl] H2.
    - destruct H2 as [He'|Hl'].
      + left. by eapply (wf_eq_trans _ Hwf).
      + right. by eapply b_le_lt; [left|].
    - right. by eapply b_lt_le.
  Qed.

  Lemma pconst_root : pt_root (pconst a) = NConst a.
  Proof. done. Qed.

  Lemma geq_W x y : geq (w_eq W) x y → w_eq W x y.
  Proof.
    induction 1; eauto using wf_eq_refl, wf_eq_sym, wf_eq_trans, wf_eq_shift, wf_eq_slot.
  Qed.

  Lemma glt_blt x y : glt (w_eq W) bfacts x y → blt x y.
  Proof.
    induction 1 as [x y Hb|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - destruct Hb as [Hb|[[Hx ->]|[-> Hy]]].
      + by left.
      + right; left. split; [|done]. exists x. split; [done|left; apply (wf_eq_refl _ Hwf)].
      + right; right. split; [done|]. exists y. split; [done|left; apply (wf_eq_refl _ Hwf)].
    - left. apply (wf_lt_po _ Hwf).
    - apply geq_W in Hx, Hy.
      destruct IH as [IH|[[(l & Hl & Hle) Hn]|[-> (h & Hh & Hle)]]].
      + left. by eapply (wf_lt_eq _ Hwf).
      + right; left. split.
        * exists l. split; [done|]. eapply b_le_le; [left; exact Hx|exact Hle].
        * apply b_eq_a in Hy; [by subst|]. unfold pt_root. by rewrite Hn.
      + right; right. split.
        * by apply b_eq_a' in Hx.
        * exists h. split; [done|]. eapply b_le_le; [exact Hle|left; exact Hy].
    - destruct IH1 as [H1|[[(l & Hl & Hle) Hn]|[-> (h & Hh & Hle)]]];
      destruct IH2 as [H2|[[(l' & Hl' & Hle') Hn']|[-> (h' & Hh' & Hle')]]].
      + left. by eapply (wf_lt_trans _ Hwf).
      + right; left. split; [|done]. exists l'. split; [done|]. right. by eapply b_lt_le.
      + exfalso. destruct (b_lt_a_r (pconst a) x eq_refl H1) as [_ Ho]. simpl in Ho. lia.
      + right; left. split; [exists l; by split|].
        assert (pt_root y = NConst a) as Hy by (unfold pt_root; by rewrite Hn).
        by rewrite <-(b_lt_a_l _ _ Hy H2).
      + exfalso. apply (b_le_a_known l' y); [by apply b_known_L|unfold pt_root; by rewrite Hn|done].
      + left. eapply b_le_lt; [exact Hle|]. eapply b_lt_le; [|exact Hle']. by apply Hbt.
      + right; right. split; [done|]. exists h. split; [done|]. right. by eapply b_le_lt.
      + exfalso. apply (wf_lt_irr h).
        eapply b_le_lt; [exact (b_le_le _ _ _ Hle Hle')|]. by apply Hbt.
      + exfalso. by apply (b_le_known_a h (pconst a)); [apply b_known_H|..].
  Qed.

  Lemma Wb_wf : world_wf Wb.
  Proof.
    apply wgen_wf.
    - intros p [Hp|Hp%elem_of_singleton]%elem_of_union; [by apply (wf_names_const _ Hwf)|].
      by eexists.
    - intros x y Hxy. eapply eq_or_supp_mono; [|by apply (wf_eq_supp _ Hwf)]. set_solver.
    - intros x y [Hxy|[[Hx ->]|[-> Hy]]].
      + eapply po_or_supp_mono; [|by apply (wf_lt_supp _ Hwf)]. set_solver.
      + right. split; [|unfold pt_root; simpl; set_solver].
        apply elem_of_union_l. by apply b_known_L.
      + right. split; [unfold pt_root; simpl; set_solver|].
        apply elem_of_union_l. by apply b_known_H.
  Qed.

  Lemma Wb_strict : strict Wb.
  Proof.
    split; [apply Wb_wf|]. intros x Hx. apply glt_blt in Hx.
    destruct Hx as [Hx|[[(l & Hl & Hle) Hn]|[-> (h & Hh & Hle)]]].
    - by apply (wf_lt_irr x).
    - apply (b_le_a_known l x); [by apply b_known_L|unfold pt_root; by rewrite Hn|done].
    - by apply (b_le_known_a h (pconst a)); [apply b_known_H|..].
  Qed.

  Lemma Wb_fresh : wext_fresh W {[NConst a]} Wb.
  Proof.
    split_and!.
    - split_and!.
      + simpl. set_solver.
      + intros x y Hxy. by apply geq_base.
      + intros x y Hxy. apply glt_base. by left.
      + apply Wb_strict.
    - set_solver.
    - done.
    - intros x y Hx Hy. split.
      + simpl. apply geq_W.
      + intros Hxy. apply glt_blt in Hxy.
        destruct Hxy as [Hxy|[[_ Hn]|[-> _]]]; [done| |].
        * exfalso. apply Hy. apply elem_of_singleton. unfold pt_root. by rewrite Hn.
        * exfalso. apply Hx. by apply elem_of_singleton.
  Qed.
End between.

(** W ⊑ₒ W′ placing a, with L ≺ (a, 0) ≺ H in W′. *)
Lemma wext_fresh_between W a L H :
  strict W → Forall (pt_known W) L → Forall (pt_known W) H →
  (∀ l h, l ∈ L → h ∈ H → w_lt W l h) → NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧
    Forall (λ l, w_lt W' l (pconst a)) L ∧ Forall (λ h, w_lt W' (pconst a) h) H.
Proof.
  intros HW HL HH Hbt Ha. exists (Wb W a L H). split_and!.
  - by apply Wb_fresh.
  - apply Forall_forall. intros l Hl. apply glt_base. right. left. by split.
  - apply Forall_forall. intros h Hh. apply glt_base. right. right. by split.
Qed.

(** ** Environments of the created channel *)

Lemma comp_single_one R Θ c e :
  Θ !! c = None → tenv_comp R (<[c := One e]> Θ) {[c := One e]} Θ.
Proof.
  intros Hc. split.
  - intros c'. destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_insert_eq, lookup_singleton_eq, Hc. constructor.
    + rewrite lookup_insert_ne, lookup_singleton_ne by done.
      destruct (Θ !! c'); constructor.
  - intros c' e1 e2 H1 H2. destruct (decide (c' = c)) as [->|Hne].
    + by rewrite Hc in H2.
    + by rewrite lookup_singleton_ne in H1.
Qed.

Lemma comp_single_both R Θ c e1 e2 :
  Θ !! c = None → R e1.2 e2.2 → sdual e1.1 e2.1 →
  tenv_comp R (<[c := Both e2 e1]> Θ) {[c := One e1]} (<[c := One e2]> Θ).
Proof.
  intros Hc HR Hd. split.
  - intros c'. destruct (decide (c' = c)) as [->|Hne].
    + rewrite !lookup_insert_eq, lookup_singleton_eq. constructor.
    + rewrite !lookup_insert_ne, lookup_singleton_ne by done.
      destruct (Θ !! c'); constructor.
  - intros c' e1' e2' H1 H2. destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_singleton_eq in H1. rewrite lookup_insert_eq in H2. by simplify_eq.
    + by rewrite lookup_singleton_ne in H1.
Qed.

(** ** Facts on every instant and carried point of the fresh channel

    The facts of a general E-NewFresh relate points x known to W and
    points p of the fresh name a: (a, k), its carried points (a, k).i,
    their successors, and so on. [Lo x p] states x ≺ p and [Hi q y]
    states q ≺ y. A path through a enters at some p, moves along program
    order of one name of a to some q, and leaves. Betweenness asks
    x ≺ y in W for every such pair, that is, for every Lo x p and Hi q y
    with q on the name of p at an offset at least that of p
    (sharp edges 93). Program order is the only order between points of
    a, because C has no ≡ fact and W does not know a. *)

Definition ple (p v : point) : Prop := pt_name p = pt_name v ∧ pt_off p ≤ pt_off v.

Section between_gen.
  Context (W : world) (a : nat) (Lo Hi : point → point → Prop).
  Context (HW : strict W).
  Context (HLo : ∀ x p, Lo x p → pt_known W x ∧ pt_root p = NConst a).
  Context (HHi : ∀ q y, Hi q y → pt_root q = NConst a ∧ pt_known W y).
  Context (Hbt : ∀ x p q y, Lo x p → Hi q y → ple p q → w_lt W x y).
  Context (Ha : NConst a ∉ w_names W).

  Let Hwf : world_wf W := proj1 HW.

  Definition gfacts (x y : point) : Prop := w_lt W x y ∨ Lo x y ∨ Hi x y.

  Definition Wg : world := wgen (w_names W ∪ {[NConst a]}) (w_eq W) gfacts.

  Definition gblt (u v : point) : Prop :=
    w_lt W u v ∨
    (∃ x p, Lo x p ∧ w_le W u x ∧ ple p v) ∨
    (∃ q y, Hi q y ∧ ple u q ∧ w_le W y v) ∨
    (∃ q y x p, Hi q y ∧ Lo x p ∧ ple u q ∧ w_le W y x ∧ ple p v).

  Lemma ple_root p v : ple p v → pt_root p = pt_root v.
  Proof. intros [H _]. unfold pt_root. by rewrite H. Qed.

  Lemma ple_trans p q v : ple p q → ple q v → ple p v.
  Proof. intros [H1 H2] [H3 H4]. split; [congruence|lia]. Qed.

  Lemma g_eq_a z u : pt_root z = NConst a → w_eq W z u → z = u.
  Proof.
    intros Hz He. destruct (wf_eq_supp _ Hwf _ _ He) as [->|[Hz' _]]; [done|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_eq_a' z u : pt_root z = NConst a → w_eq W u z → u = z.
  Proof. intros Hz He. symmetry. apply g_eq_a; [done|]. by apply (wf_eq_sym _ Hwf). Qed.

  Lemma g_lt_a_l z u : pt_root z = NConst a → w_lt W z u → ple z u.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [[? ?]|[Hz' _]]; [split; [done|lia]|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_lt_a_r z u : pt_root z = NConst a → w_lt W u z → ple u z.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [[? ?]|[_ Hz']]; [split; [done|lia]|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_le_known_a x z : pt_known W x → pt_root z = NConst a → ¬ w_le W x z.
  Proof.
    intros Hx Hz [He|Hl].
    - apply g_eq_a' in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - apply (g_lt_a_r _ _ Hz), ple_root in Hl. apply Ha. unfold pt_known in Hx. congruence.
  Qed.

  Lemma g_le_a_known x z : pt_known W x → pt_root z = NConst a → ¬ w_le W z x.
  Proof.
    intros Hx Hz [He|Hl].
    - apply g_eq_a in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - apply (g_lt_a_l _ _ Hz), ple_root in Hl. apply Ha. unfold pt_known in Hx. congruence.
  Qed.

  Lemma g_le_lt x y z : w_le W x y → w_lt W y z → w_lt W x z.
  Proof.
    intros [He|Hl] H2.
    - eapply (wf_lt_eq _ Hwf); [exact He|exact H2|apply (wf_eq_refl _ Hwf)].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma g_lt_le x y z : w_lt W x y → w_le W y z → w_lt W x z.
  Proof.
    intros H1 [He|Hl].
    - eapply (wf_lt_eq _ Hwf); [apply (wf_eq_refl _ Hwf)|exact H1|exact He].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma g_le_le x y z : w_le W x y → w_le W y z → w_le W x z.
  Proof.
    intros [He|Hl] H2.
    - destruct H2 as [He'|Hl'].
      + left. by eapply (wf_eq_trans _ Hwf).
      + right. by eapply g_le_lt; [left|].
    - right. by eapply g_lt_le.
  Qed.

  Lemma g_le_refl x : w_le W x x.
  Proof. left. apply (wf_eq_refl _ Hwf). Qed.

  Lemma g_root_lo x p : Lo x p → pt_root p = NConst a.
  Proof. intros H. apply (HLo _ _ H). Qed.

  Lemma g_root_hi q y : Hi q y → pt_root q = NConst a.
  Proof. intros H. apply (HHi _ _ H). Qed.

  Lemma g_geq_W x y : geq (w_eq W) x y → w_eq W x y.
  Proof.
    induction 1; eauto using wf_eq_refl, wf_eq_sym, wf_eq_trans, wf_eq_shift, wf_eq_slot.
  Qed.

  Lemma g_lt_strict_ple u v w : pt_root w = NConst a → w_lt W u v → ple v w → ple u w.
  Proof.
    intros Hw H1 Hvw. eapply ple_trans; [|exact Hvw].
    apply g_lt_a_r in H1; [destruct H1; split; [done|lia]|].
    by rewrite (ple_root _ _ Hvw).
  Qed.

  Lemma g_ple_lt p v w : pt_root p = NConst a → ple p v → w_lt W v w → ple p w.
  Proof.
    intros Hp Hpv H2. eapply ple_trans; [exact Hpv|].
    apply g_lt_a_l in H2; [destruct H2; split; [done|lia]|].
    by rewrite <-(ple_root _ _ Hpv).
  Qed.

  Lemma glt_gblt u v : glt (w_eq W) gfacts u v → gblt u v.
  Proof.
    induction 1 as [u v Hb|u|u u' v v' Hu _ IH Hv|u v w _ IH1 _ IH2].
    - destruct Hb as [Hb|[Hb|Hb]].
      + by left.
      + right; left. exists u, v. split_and!; [done|apply g_le_refl|split; [done|lia]].
      + right; right; left. exists u, v. split_and!; [done|split; [done|lia]|apply g_le_refl].
    - left. apply (wf_lt_po _ Hwf).
    - apply g_geq_W in Hu, Hv.
      destruct IH as [IH|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                      (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]].
      + left. by eapply (wf_lt_eq _ Hwf).
      + right; left. exists x, p. split_and!; [done|eapply g_le_le; [left; exact Hu|exact Hle]|].
        assert (pt_root v' = NConst a) as Hr by (rewrite <-(ple_root _ _ Hp); by apply (g_root_lo x)).
        apply (g_eq_a _ _ Hr) in Hv. by subst.
      + right; right; left. exists q, y.
        assert (pt_root u' = NConst a) as Hr by (rewrite (ple_root _ _ Hq); by apply (g_root_hi _ y)).
        apply (g_eq_a' _ _ Hr) in Hu. subst. split_and!; [done|done|].
        eapply g_le_le; [exact Hle|left; exact Hv].
      + right; right; right. exists q, y, x, p.
        assert (pt_root u' = NConst a) as Hr by (rewrite (ple_root _ _ Hq); by apply (g_root_hi _ y)).
        apply (g_eq_a' _ _ Hr) in Hu. subst.
        assert (pt_root v' = NConst a) as Hr' by (rewrite <-(ple_root _ _ Hp); by apply (g_root_lo x)).
        apply (g_eq_a _ _ Hr') in Hv. by subst.
    - destruct IH1 as [H1|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                      (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]];
      destruct IH2 as [H2|[(x' & p' & Hl' & Hle' & Hp')|[(q' & y' & Hh' & Hq' & Hle')|
                      (q' & y' & x' & p' & Hh' & Hl' & Hq' & Hyx' & Hp')]]].
      (* B1 then _ *)
      + left. by eapply (wf_lt_trans _ Hwf).
      + right; left. exists x', p'. split_and!; [done|right; by eapply g_lt_le|done].
      + right; right; left. exists q', y'. split_and!; [done| |done].
        apply (g_lt_strict_ple u v); [by apply (g_root_hi _ y')|done|done].
      + right; right; right. exists q', y', x', p'. split_and!; [done|done| |done|done].
        apply (g_lt_strict_ple u v); [by apply (g_root_hi _ y')|done|done].
      (* B2 then _ *)
      + right; left. exists x, p. split_and!; [done|done|].
        apply (g_ple_lt p v); [by apply (g_root_lo x)|done|done].
      + exfalso. apply (g_le_a_known x' v); [by apply (HLo _ _ Hl')| |done].
        rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
      + left. eapply g_le_lt; [exact Hle|]. eapply g_lt_le; [|exact Hle'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      + right; left. exists x', p'. split_and!; [done| |done].
        right. eapply g_le_lt; [exact Hle|]. eapply g_lt_le; [|exact Hyx'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      (* B3 then _ *)
      + right; right; left. exists q, y. split_and!; [done|done|]. right. by eapply g_le_lt.
      + right; right; right. exists q, y, x', p'. split_and!; try done. by eapply g_le_le.
      + exfalso. apply (g_le_known_a y v); [by apply (HHi _ _ Hh)| |done].
        rewrite (ple_root _ _ Hq'). by apply (g_root_hi _ y').
      + exfalso. apply (g_le_known_a y v); [by apply (HHi _ _ Hh)| |done].
        rewrite (ple_root _ _ Hq'). by apply (g_root_hi _ y').
      (* B4 then _ *)
      + right; right; right. exists q, y, x, p. split_and!; [done|done|done|done|].
        apply (g_ple_lt p v); [by apply (g_root_lo x)|done|done].
      + exfalso. apply (g_le_a_known x' v); [by apply (HLo _ _ Hl')| |done].
        rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
      + right; right; left. exists q, y. split_and!; [done|done|].
        right. eapply g_le_lt; [exact Hyx|]. eapply g_lt_le; [|exact Hle'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      + right; right; right. exists q, y, x', p'. split_and!; [done|done|done| |done].
        right. eapply g_le_lt; [exact Hyx|]. eapply g_lt_le; [|exact Hyx'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
  Qed.

  Lemma Wg_wf : world_wf Wg.
  Proof.
    apply wgen_wf.
    - intros p [Hp|Hp%elem_of_singleton]%elem_of_union; [by apply (wf_names_const _ Hwf)|].
      by eexists.
    - intros x y Hxy. eapply eq_or_supp_mono; [|by apply (wf_eq_supp _ Hwf)]. set_solver.
    - intros x y [Hxy|[Hxy|Hxy]].
      + eapply po_or_supp_mono; [|by apply (wf_lt_supp _ Hwf)]. set_solver.
      + destruct (HLo _ _ Hxy) as [Hx Hy]. right. unfold pt_known in Hx. rewrite Hy. set_solver.
      + destruct (HHi _ _ Hxy) as [Hx Hy]. right. unfold pt_known in Hy. rewrite Hx. set_solver.
  Qed.

  Lemma Wg_strict : strict Wg.
  Proof.
    split; [apply Wg_wf|]. intros u Hu. apply glt_gblt in Hu.
    destruct Hu as [Hu|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                    (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]].
    - by apply (proj2 HW u).
    - apply (g_le_a_known x u); [by apply (HLo _ _ Hl)| |done].
      rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
    - apply (g_le_known_a y u); [by apply (HHi _ _ Hh)| |done].
      rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y).
    - apply (proj2 HW x). eapply g_lt_le; [|exact Hyx].
      apply (Hbt x p q y); [done|done|]. by eapply ple_trans.
  Qed.

  Lemma Wg_fresh : wext_fresh W {[NConst a]} Wg.
  Proof.
    split_and!.
    - split_and!.
      + simpl. set_solver.
      + intros x y Hxy. by apply geq_base.
      + intros x y Hxy. apply glt_base. by left.
      + apply Wg_strict.
    - set_solver.
    - done.
    - intros x y Hx Hy. split.
      + simpl. apply g_geq_W.
      + intros Hxy. apply glt_gblt in Hxy.
        destruct Hxy as [Hxy|[(x' & p & Hl & _ & Hp)|[(q & y' & Hh & Hq & _)|
                        (q & y' & x' & p & Hh & _ & Hq & _ & _)]]]; [done|..]; exfalso.
        * apply Hy. apply elem_of_singleton. rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x').
        * apply Hx. apply elem_of_singleton. rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y').
        * apply Hx. apply elem_of_singleton. rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y').
  Qed.
End between_gen.

Lemma wext_fresh_between_gen W a (Lo Hi : point → point → Prop) :
  strict W →
  (∀ x p, Lo x p → pt_known W x ∧ pt_root p = NConst a) →
  (∀ q y, Hi q y → pt_root q = NConst a ∧ pt_known W y) →
  (∀ x p q y, Lo x p → Hi q y → ple p q → w_lt W x y) →
  NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧
    (∀ x p, Lo x p → w_lt W' x p) ∧ (∀ q y, Hi q y → w_lt W' q y).
Proof.
  intros HW HL HH Hbt Ha. exists (Wg W a Lo Hi). split_and!.
  - by apply Wg_fresh.
  - intros x p H. apply glt_base. right. by left.
  - intros q y H. apply glt_base. by right; right.
Qed.

(** ** Points of the fresh name

    A fact of E-NewFresh names a point of the fresh channel by a point
    whose root is the variable 0. [pfresh a p] puts the constant a
    there. It keeps the offset and the shape of carried points, so it
    is injective on such points and keeps program order both ways. *)

Definition pfresh (a : nat) (p : point) : point := pt_inst (λ _, pconst a) p.

Fixpoint rn (a : nat) (n : pname) : pname :=
  match n with
  | NVar _ => NConst a
  | NConst c => NConst c
  | NSlot q b i => NSlot (rn a q) b i
  end.

Lemma pn_inst_fresh a n : pn_inst (λ _, pconst a) n = Pt (rn a n) 0.
Proof. induction n as [c|v|q IH b i]; simpl; [done|done|]. by rewrite IH. Qed.

Lemma pfresh_name a p : pt_name (pfresh a p) = rn a (pt_name p).
Proof. destruct p as [n o]. unfold pfresh, pt_inst. simpl. by rewrite pn_inst_fresh. Qed.

Lemma pfresh_off a p : pt_off (pfresh a p) = pt_off p.
Proof. destruct p as [n o]. unfold pfresh, pt_inst. simpl. rewrite pn_inst_fresh. simpl. lia. Qed.

Lemma rn_root a n v : pn_root n = NVar v → pn_root (rn a n) = NConst a.
Proof. induction n as [c|w|q IH b i]; simpl; [done|done|exact IH]. Qed.

Lemma pfresh_root a p v : pt_root p = NVar v → pt_root (pfresh a p) = NConst a.
Proof. intros H. unfold pt_root. rewrite pfresh_name. by apply (rn_root _ _ v). Qed.

Lemma rn_inj a n m : pn_root n = NVar 0 → pn_root m = NVar 0 → rn a n = rn a m → n = m.
Proof.
  revert m. induction n as [c|v|q IH b i]; intros [c'|v'|q' b' i'];
    simpl; intros Hn Hm E; try congruence.
  injection E as E -> ->. f_equal. by apply IH.
Qed.

Lemma pfresh_ple a p q :
  pt_root p = NVar 0 → pt_root q = NVar 0 → ple (pfresh a p) (pfresh a q) → ple p q.
Proof.
  intros Hp Hq [Hn Ho]. rewrite !pfresh_name in Hn. rewrite !pfresh_off in Ho.
  split; [|done]. by apply (rn_inj a).
Qed.

(** ** E-NewFresh, semantically

    The continuation is good in every later world that places some a
    above L and below H. At the step of new the world is W′ ⊒ W, and
    the fresh extension of W′ by L ≺ (a, 0) ≺ H is such a world. *)

Lemma sem_typed_newfresh W Θ Δ F e T S (Lo Hi : point → point → Prop) :
  (∀ x p, Lo x p → pt_known W x ∧ pt_root p = NVar 0) →
  (∀ q y, Hi q y → pt_root q = NVar 0 ∧ pt_known W y) →
  (∀ x p q y, Lo x p → Hi q y → ple p q → w_lt W x y) →
  (∀ W1 a, wext W W1 → (∀ x p, Lo x p → w_lt W1 x (pfresh a p)) →
     (∀ q y, Hi q y → w_lt W1 (pfresh a q) y) → pt_known W1 (pconst a) →
     sem_typed W1 Θ (Some (TSess (dual S) (pconst a)) :: Some (TSess S (pconst a)) :: Δ) F e T) →
  sem_typed W Θ Δ F (LetP (App ENew EUnit) e) T.
Proof.
  intros HL HH Hbt Hb n W' Θ' Θ'' γ HW Hc Hg. simpl.
  set (e' := subst (up (up γ)) e).
  destruct n as [|n']; [apply Erel_0|].
  pose proof (proj2 (proj2 (proj2 HW))) as HWs.
  pose proof (proj1 HWs) as HWf.
  assert (tstep (LetP (App ENew EUnit) e') (LNew "c") (LetP (Pair (Chan "c") (Chan "c")) e'))
    as Hst0 by (apply TStepLetP, TStepHead, HeadNew).
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst0).
  - intros α e'' Hst.
    apply tstep_letp_inv in Hst as [(e1' & Hst & ->)|(u & w & Heq & _)]; [|discriminate].
    apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | |c| | | | | | | |]; subst. simpl. intros HcΘ.
    assert (Θ !! c = None ∧ Θ' !! c = None) as [H1c H2c].
    { rewrite (tenv_join_dom _ _ _ (proj1 Hc)) in HcΘ.
      split; apply not_elem_of_dom; clear -HcΘ; set_solver. }
    destruct (fresh_const (w_names W' ∪ tenv_roots Θ'' ∪ ty_roots T ∪ frame_roots F)) as [a Ha].
    destruct HW as (HN & HEq & HLt & _).
    destruct (wext_fresh_between_gen W' a (λ x p', ∃ p, Lo x p ∧ p' = pfresh a p)
                (λ q' y, ∃ q, Hi q y ∧ q' = pfresh a q) HWs) as (W1 & Hfr & HL1 & HH1).
    { intros x p' (p & Hp & ->). destruct (HL _ _ Hp) as [Hx Hr]. split.
      - unfold pt_known in *. by apply HN.
      - by apply (pfresh_root _ _ 0). }
    { intros q' y (q & Hq & ->). destruct (HH _ _ Hq) as [Hr Hy]. split.
      - by apply (pfresh_root _ _ 0).
      - unfold pt_known in *. by apply HN. }
    { intros x p' q' y (p & Hp & ->) (q & Hq & ->) Hpq. apply HLt.
      apply (Hbt x p q y Hp Hq). apply (pfresh_ple a); [apply (HL _ _ Hp)|apply (HH _ _ Hq)|done]. }
    { clear -Ha. set_solver. }
    exists a, S, (dual S), W1. split_and!.
    + clear -Ha. set_solver.
    + apply sdual_dual.
    + done.
    + destruct Hfr as [HWW1 [_ [Hnames _]]].
      pose proof (proj2 (proj2 (proj2 HWW1))) as HW1s. pose proof (proj1 HW1s) as HW1f.
      assert (∀ x y, w_eq W1 x y → w_eq W1 y x) as Hsym by apply (wf_eq_sym _ HW1f).
      apply (Erel_det_beta _ _ _ _ _ _ (subst2 (Chan c) (Chan c) e')).
      * by apply TStepHead, HeadLetP.
      * intros α e'' Hst'. apply tstep_letp_inv in Hst'
          as [(e1' & Hst' & _)|(u & w & Heq & _ & _ & -> & ->)].
        -- exfalso. eapply val_no_tstep; [exact Hst'|done].
        -- by injection Heq as -> ->.
      * unfold e'. rewrite subst2_subst.
        apply (Hb W1 a (wext_trans _ _ _ (conj HN (conj HEq (conj HLt HWs))) HWW1)
                 (λ x p Hp, HL1 x _ (ex_intro _ p (conj Hp eq_refl)))
                 (λ q y Hq, HH1 _ y (ex_intro _ q (conj Hq eq_refl)))
                 ltac:(unfold pt_known; simpl; rewrite Hnames; set_solver)
                 n' W1 (<[c := Both (S, pconst a) (dual S, pconst a)]> Θ') _ _ (wext_refl _ HW1s)).
        -- apply comp_comm; [done|]. apply comp_insert; [|done].
           apply comp_comm; [done|]. eapply tenv_comp_mono; [|exact Hc]. apply HWW1.
        -- simpl. exists {[c := One (dual S, pconst a)]}, (<[c := One (S, pconst a)]> Θ').
           split_and!.
           ++ apply comp_single_both; [done|apply (wf_eq_refl _ HW1f)|].
              apply sdual_sym, sdual_dual.
           ++ apply Vrel_sess_iff. exists c, (dual S), (pconst a).
              split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW1f)].
           ++ exists {[c := One (S, pconst a)]}, Θ'. split_and!.
              ** by apply comp_single_one.
              ** apply Vrel_sess_iff. exists c, S, (pconst a).
                 split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW1f)].
              ** eapply grounding_down; [|eapply grounding_mono; [exact HWf|exact HWW1|exact Hg]].
                 lia.
Qed.
