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

(** The worlds with facts on every point of the fresh channel, [Wg],
    [wext_fresh_between_gen] and [pfresh] live in rules/FreshWorlds.v, because
    the existential signature of new uses them in rules/TermRules.v. *)

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
