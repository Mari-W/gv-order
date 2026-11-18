(** * P-Term (stage S4)

    A single thread in E at the empty future, over the interface Σ and the
    ends Θ_B of the restricted channels C, both ends of each held as dual
    pairs at dual points, with Σ partner-free, is in P:

      sem_p_term : prim T → sth Θ Σ Θ_B C → t ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^∅ →
                   (C, {t}) ∈ P[κ]^W _ n⟦Σ ⊢ T⟧

    [sth] packs the conditions on the environments: Θ = Σ ∪ Θ_B, the ends
    of Θ_B are those of C, Σ holds no end of C, Σ is partner-free
    ([pfree]), and the ends of Θ_B are dual pairs at dual points
    ([dpairs]).

    The proof is a strong induction on the level and, inside it, an
    induction over the steps of cost 0 whose predicate is closed under
    renaming ([Erel_S_ind_ren]). The clause (fuse) of P reads a fusion of
    the thread as the renamed thread over a fused interface ([sth_fuse]).
    A spawn splits the environment of the thread by O-Spawn: the channels
    with one end on each side become the cut of P-Connect, which composes
    the parent and the child ([spawn_split], [conn_all]). *)

From GV Require Export compat.ConnectP compat.RenameInd.
From GV Require Import fuel.FuelMono.

(** ** The environments of a single thread *)

Inductive sth (Θ Σ ΘB : senv) (C : gset chan) : Prop :=
  | Sth (st_env : Θ = Σ ∪ ΘB) (st_dom : ∀ o, o ∈ dom ΘB ↔ ech o ∈ C)
      (st_disj : chans_of Σ ## C) (st_free : pfree Σ) (st_pairs : dpairs C ΘB).

Section sth_proj.
  Context Θ Σ ΘB C (H : sth Θ Σ ΘB C).
  Lemma st_env : Θ = Σ ∪ ΘB. Proof. by destruct H. Qed.
  Lemma st_dom : ∀ o, o ∈ dom ΘB ↔ ech o ∈ C. Proof. by destruct H. Qed.
  Lemma st_disj : chans_of Σ ## C. Proof. by destruct H. Qed.
  Lemma st_free : pfree Σ. Proof. by destruct H. Qed.
  Lemma st_pairs : dpairs C ΘB. Proof. by destruct H. Qed.
End sth_proj.

Lemma ech_inj_dual o o' : ech o = ech o' → o = o' ∨ o = edual o'.
Proof. destruct o, o'; simpl; intros ->; auto. Qed.

Lemma pfree_sub' (Σ Σ' : senv) : dom Σ' ⊆ dom Σ → pfree Σ → pfree Σ'.
Proof. intros Hs H o Ho Hd. apply (H o); set_solver. Qed.

Section sth.
  Implicit Types (Θ Σ ΘB : senv) (C : gset chan).

  Lemma sth_disj Θ Σ ΘB C : sth Θ Σ ΘB C → Σ ##ₘ ΘB.
  Proof.
    intros [_ Hd Hc _ _]. apply map_disjoint_spec. intros o v1 v2 H1 H2.
    apply (Hc (ech o)); [apply elem_of_chans_of; by eapply elem_of_dom_2|].
    apply Hd. by eapply elem_of_dom_2.
  Qed.

  Lemma sth_lookup_B Θ Σ ΘB C o v : sth Θ Σ ΘB C → ΘB !! o = Some v → Θ !! o = Some v.
  Proof.
    intros Hs H. rewrite (st_env _ _ _ _ Hs). apply lookup_union_Some_r; [|done].
    by apply (sth_disj _ _ _ _ Hs).
  Qed.

  Lemma sth_lookup_S Θ Σ ΘB C o v : sth Θ Σ ΘB C → Σ !! o = Some v → Θ !! o = Some v.
  Proof. intros Hs H. rewrite (st_env _ _ _ _ Hs). by apply lookup_union_Some_l. Qed.

  (** An end of Θ on a restricted channel is an end of Θ_B. *)
  Lemma sth_lookup_C Θ Σ ΘB C o v : sth Θ Σ ΘB C → ech o ∈ C → Θ !! o = Some v → ΘB !! o = Some v.
  Proof.
    intros Hs Hc H. rewrite (st_env _ _ _ _ Hs) in H. apply lookup_union_Some_raw in H as [H|[_ H]]; [|done].
    exfalso. apply (st_disj _ _ _ _ Hs (ech o)); [apply elem_of_chans_of; by eapply elem_of_dom_2|done].
  Qed.

  Lemma sth_lookup_nC Θ Σ ΘB C o v : sth Θ Σ ΘB C → ech o ∉ C → Θ !! o = Some v → Σ !! o = Some v.
  Proof.
    intros Hs Hc H. rewrite (st_env _ _ _ _ Hs) in H. apply lookup_union_Some_raw in H as [H|[_ H]]; [done|].
    exfalso. apply Hc, (st_dom _ _ _ _ Hs). by eapply elem_of_dom_2.
  Qed.

  (** Both ends of a restricted channel are held. *)
  Lemma sth_both Θ Σ ΘB C o : sth Θ Σ ΘB C → ech o ∈ C → o ∈ dom Θ ∧ edual o ∈ dom Θ.
  Proof.
    intros Hs Hc. destruct (st_pairs _ _ _ _ Hs o Hc) as (S & x & S' & H1 & H2 & _).
    split; eapply elem_of_dom_2; eapply sth_lookup_B; eauto.
  Qed.

  (** The thread holds the partner of an end only on a restricted channel. *)
  Lemma sth_partner Θ Σ ΘB C o : sth Θ Σ ΘB C → o ∈ dom Θ → edual o ∈ dom Θ → ech o ∈ C.
  Proof.
    intros Hs H1 H2. destruct (decide (ech o ∈ C)) as [|Hn]; [done|exfalso].
    apply elem_of_dom in H1 as [v1 H1], H2 as [v2 H2].
    apply (sth_lookup_nC _ _ _ _ _ _ Hs Hn) in H1.
    assert (ech (edual o) ∉ C) as Hn' by by rewrite ech_edual.
    apply (sth_lookup_nC _ _ _ _ _ _ Hs Hn') in H2.
    apply (st_free _ _ _ _ Hs o); by eapply elem_of_dom_2.
  Qed.
End sth.

(** ** Steps of a single thread *)

Lemma soup_single M e i e0 : soup M = {[+ e +]} → M !! i = Some e0 → e0 = e ∧ delete i M = ∅.
Proof.
  intros H Hi. rewrite (soup_delete M i e0 Hi) in H.
  assert (e0 ∈ ({[+ e +]} : gmultiset expr)) as He0 by (rewrite <-H; multiset_solver).
  apply gmultiset_elem_of_singleton in He0 as ->. split; [done|].
  assert (soup (delete i M) = ∅) as H0 by multiset_solver.
  apply map_empty. intros j. destruct (delete i M !! j) as [x|] eqn:Hj; [|done].
  assert (x ∈ soup (delete i M)) as Hx by (apply elem_of_soup; eauto).
  rewrite H0 in Hx. multiset_solver.
Qed.

Lemma soup_single_two M e i j e1 e2 : soup M = {[+ e +]} → i ≠ j → M !! i = Some e1 → M !! j = Some e2 → False.
Proof.
  intros H Hij Hi Hj. destruct (soup_single M e i e1 H Hi) as [_ Hd].
  assert (delete i M !! j = Some e2) as Hj' by (by rewrite lookup_delete_ne).
  by rewrite Hd, lookup_empty in Hj'.
Qed.

Lemma soup_single_upd M e i e0 e' : soup M = {[+ e +]} → M !! i = Some e0 → soup (<[i := e']> M) = {[+ e' +]}.
Proof.
  intros H Hi. destruct (soup_single M e i e0 H Hi) as [_ Hd].
  rewrite (soup_update M i e0 e' Hi), Hd, soup_empty. multiset_solver.
Qed.

(** The steps of (C, {e}): an administrative step, a link of a
    restricted channel, or an offer on free channels. *)
Lemma istep_single q ev q' C e :
  erase q = (C, {[+ e +]}) → istep q ev q' →
  (∃ i e', ev = EvBeta i ∧ tstep e LBeta e' ∧ erase q' = (C, {[+ e' +]})) ∨
  (∃ i ℓ c e', ev = EvNew i ℓ c ∧ tstep e (LNew ℓ c) e' ∧ c ∉ C ∧ c ∉ fchans e ∧
     erase q' = (C ∪ {[c]}, {[+ e' +]})) ∨
  (∃ i κf o c e', ev = EvNewAt i κf o c ∧ tstep e (LNewAt κf o c) e' ∧ c ∉ C ∧ c ∉ fchans e ∧
     erase q' = (C ∪ {[c]}, {[+ e' +]})) ∨
  (∃ i j v e', ev = EvSpawn i j v ∧ tstep e (LSpawn v) e' ∧
     erase q' = (C, {[+ e' +]} ⊎ {[+ App v EUnit +]})) ∨
  (∃ i o1 o2 e', ev = EvLink i o1 o2 ∧ tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' ∧ ech o1 ∈ C ∧
     erase q' = (C ∖ {[ech o1]}, {[+ emap (csub o1 o2) e' +]})) ∨
  (∃ i σ e', ev = EvSess i σ ∧ tstep e (LSess σ) e' ∧ subjs σ ## C ∧
     erase q' = (C ∖ sentc σ, {[+ e' +]})).
Proof.
  intros Hq Hst. destruct q as [C' M]. unfold erase in Hq. simpl in Hq. injection Hq as -> HM.
  inversion Hst; subst;
    try (exfalso; match goal with
      | H1 : M !! ?i = Some _, H2 : M !! ?j = Some _, Hn : ?i ≠ ?j |- _ =>
          exact (soup_single_two _ _ _ _ _ _ HM Hn H1 H2) end);
    match goal with H : M !! ?i = Some _ |- _ => pose proof H as Hi; destruct (soup_single _ _ _ _ HM H) as [-> _] end;
    try match goal with H : _ ∉ echans _ |- _ => rewrite HM, echans_singleton in H end;
    unfold erase; simpl.
  - left. eexists _, _. split_and!; [done|done|]. by erewrite soup_single_upd.
  - right; left. eexists _, _, _, _. split_and!; [done|done|done|done|]. by erewrite soup_single_upd.
  - do 2 right; left. eexists _, _, _, _, _. split_and!; [done|done|done|done|]. by erewrite soup_single_upd.
  - do 3 right; left. eexists _, _, _, _. split_and!; [done|done|].
    match goal with H : M !! ?j = None |- _ => rename H into Hj end.
    rewrite soup_insert; [by erewrite soup_single_upd|].
    rewrite lookup_insert_ne; [done|]. intros ->. congruence.
  - do 4 right; left. eexists _, _, _, _. split_and!; [done|done|done|].
    rewrite soup_fmap. erewrite soup_single_upd by done. by rewrite gmultiset_map_singleton.
  - do 5 right. eexists _, _, _. split_and!; [done|done|done|]. by erewrite soup_single_upd.
Qed.

(** ** Splitting the environment at a spawn *)

Ltac mcrush := apply map_eq; intros ?o; rewrite ?lookup_union, ?map_lookup_filter;
  repeat match goal with |- context [?m !! ?o] => destruct (m !! o) eqn:?; simpl end;
  repeat (case_guard; simpl); try done.

Lemma elem_of_dom_filter (P : cend * (sty * point) → Prop) `{!∀ x, Decision (P x)} (m : senv) o :
  o ∈ dom (filter P m) ↔ ∃ v, m !! o = Some v ∧ P (o, v).
Proof. rewrite elem_of_dom. split; [intros [v Hv]; apply map_lookup_filter_Some in Hv; eauto|].
  intros (v & H1 & H2). exists v. by apply map_lookup_filter_Some. Qed.

Lemma elem_of_chans_of_iff c (Σ : senv) : c ∈ chans_of Σ ↔ ∃ o, c = ech o ∧ o ∈ dom Σ.
Proof. unfold chans_of. apply elem_of_map. Qed.

Lemma both_ends (P : cend → Prop) o : P (EPos (ech o)) ∧ P (ENeg (ech o)) ↔ P o ∧ P (edual o).
Proof. destruct o; simpl; tauto. Qed.

Section split.
  Context (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C).

  (** The part Θs of Θ, its interface, its cut ends (partner outside Θs),
      its restricted ends and channels. *)
  Context (Θs : senv) (Hsub : Θs ⊆ Θ).
  Definition s_if : senv := filter (λ oe : cend * (sty * point), ech oe.1 ∉ C) Θs.
  Definition s_cut : senv := filter (λ oe : cend * (sty * point), ech oe.1 ∈ C ∧ edual oe.1 ∉ dom Θs) Θs.
  Definition s_res : senv := filter (λ oe : cend * (sty * point), ech oe.1 ∈ C ∧ edual oe.1 ∈ dom Θs) Θs.
  Definition s_ch : gset chan := filter (λ c, EPos c ∈ dom Θs ∧ ENeg c ∈ dom Θs) C.

  Lemma sub_lookup o v : Θs !! o = Some v → Θ !! o = Some v.
  Proof. intros H. by eapply lookup_weaken. Qed.

  Lemma side_sth : sth Θs (s_if ∪ s_cut) s_res s_ch.
  Proof.
    constructor.
    - unfold s_if, s_cut, s_res. mcrush. all: exfalso; tauto.
    - intros o. unfold s_res, s_ch. rewrite elem_of_dom_filter, elem_of_filter.
      rewrite (both_ends (λ o, o ∈ dom Θs)). split.
      + intros (v & Hv & Hc & Hd). simpl in *. split_and!; [by eapply elem_of_dom_2|done|done].
      + intros [[H1 H2] Hc]. apply elem_of_dom in H1 as [v Hv]. eauto.
    - intros c Hc1 Hc2. apply elem_of_chans_of_iff in Hc1 as (o & -> & Ho).
      rewrite dom_union_L in Ho. apply elem_of_filter in Hc2 as [Hb Hc].
      apply (both_ends (λ o, o ∈ dom Θs) o) in Hb as [_ Hb]; cbv beta in Hb.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_dom_filter in Ho as (v & _ & Hp); simpl in Hp;
        [exact (Hp Hc)|exact (proj2 Hp Hb)].
    - intros o Ho Hd. rewrite dom_union_L in Ho, Hd.
      assert (o ∈ dom Θs ∧ edual o ∈ dom Θs) as [H1 H2].
      { unfold s_if, s_cut in Ho, Hd. rewrite !elem_of_union, !elem_of_dom_filter in Ho, Hd.
        split; [destruct Ho as [(v & Hv & _)|(v & Hv & _)]|destruct Hd as [(v & Hv & _)|(v & Hv & _)]];
          by eapply elem_of_dom_2. }
      assert (ech o ∈ C) as Hc.
      { apply elem_of_dom in H1 as [v1 V1], H2 as [v2 V2].
        apply (sth_partner _ _ _ _ _ Hs); [exact (elem_of_dom_2 _ _ _ (sub_lookup _ _ V1))
          |exact (elem_of_dom_2 _ _ _ (sub_lookup _ _ V2))]. }
      unfold s_if, s_cut in Ho. rewrite !elem_of_union, !elem_of_dom_filter in Ho.
      destruct Ho as [(v & _ & Hp)|(v & _ & _ & Hp)]; simpl in Hp; tauto.
    - intros o Hc. apply elem_of_filter in Hc as [Hb Hc].
      apply (both_ends (λ o, o ∈ dom Θs) o) in Hb as [Hb1 Hb2]; cbv beta in Hb1, Hb2.
      destruct (st_pairs _ _ _ _ Hs o Hc) as (S & x & S' & H1 & H2 & Hd).
      apply elem_of_dom in Hb1 as [v1 V1], Hb2 as [v2 V2].
      pose proof (sth_lookup_B _ _ _ _ _ _ Hs H1) as T1. pose proof (sth_lookup_B _ _ _ _ _ _ Hs H2) as T2.
      rewrite (sub_lookup _ _ V1) in T1. rewrite (sub_lookup _ _ V2) in T2. simplify_eq.
      exists S, x, S'. unfold s_res. rewrite !map_lookup_filter_Some. simpl. rewrite ech_edual, edual_edual.
      split_and!; try done; by eapply elem_of_dom_2.
  Qed.
End split.

Lemma sth_if Θ Σ ΘB C : sth Θ Σ ΘB C → Σ = filter (λ oe : cend * (sty * point), ech oe.1 ∉ C) Θ.
Proof.
  intros Hs. apply map_eq. intros o. rewrite map_lookup_filter. destruct (Θ !! o) as [v|] eqn:E; simpl.
  - case_guard as Hc; simpl.
    + symmetry. by apply (sth_lookup_nC _ _ _ _ _ _ Hs Hc) in E.
    + destruct (Σ !! o) eqn:E'; [|done]. exfalso.
      apply (st_disj _ _ _ _ Hs (ech o)); [apply elem_of_chans_of; by eapply elem_of_dom_2|done].
  - destruct (Σ !! o) eqn:E'; [|done]. by rewrite (sth_lookup_S _ _ _ _ _ _ Hs E') in E.
Qed.

(** O-Spawn splits Θ into ΘM ∪ Θr. The channels with one end on each side
    become the cut of P-Connect. *)
Lemma spawn_split Θ Σ ΘB C ΘM Θr :
  sth Θ Σ ΘB C → ΘM ##ₘ Θr → Θ = ΘM ∪ Θr →
  sth Θr (s_if C Θr ∪ s_cut C Θr) (s_res C Θr) (s_ch C Θr) ∧
  sth ΘM (s_if C ΘM ∪ s_cut C ΘM) (s_res C ΘM) (s_ch C ΘM) ∧
  conn (s_if C Θr) (s_cut C Θr) (s_ch C Θr) (s_if C ΘM) (s_cut C ΘM) (s_ch C ΘM) ∧
  Σ = s_if C Θr ∪ s_if C ΘM ∧ C = s_ch C Θr ∪ s_ch C ΘM ∪ chans_of (s_cut C Θr).
Proof.
  intros Hs Hd ->.
  assert (Θr ⊆ ΘM ∪ Θr) as Sr by (by apply map_union_subseteq_r).
  assert (ΘM ⊆ ΘM ∪ Θr) as SM by (apply map_union_subseteq_l).
  pose proof (side_sth _ _ _ _ Hs Θr Sr) as Hr. pose proof (side_sth _ _ _ _ Hs ΘM SM) as HM.
  assert (∀ o, o ∈ dom ΘM → o ∉ dom Θr) as Hx.
  { intros o H1 H2. apply elem_of_dom in H1 as [? H1], H2 as [? H2]. by eapply (map_disjoint_spec ΘM Θr). }
  (** A restricted end lies on exactly one side. *)
  assert (∀ o, ech o ∈ C → o ∈ dom ΘM ∨ o ∈ dom Θr) as Hone.
  { intros o Hc. destruct (sth_both _ _ _ _ o Hs Hc) as [H _]. by rewrite dom_union_L, elem_of_union in H. }
  split_and!; [done|done| |..].
  - constructor.
    + apply map_disjoint_spec. intros o v1 v2 V1 V2. unfold s_if, s_cut in *.
      apply map_lookup_filter_Some in V1 as [_ P1], V2 as [_ P2]. simpl in *. tauto.
    + apply map_disjoint_spec. intros o v1 v2 V1 V2. unfold s_if, s_cut in *.
      apply map_lookup_filter_Some in V1 as [_ P1], V2 as [_ P2]. simpl in *. tauto.
    + split.
      * intros o. unfold s_cut. rewrite !elem_of_dom_filter. simpl. rewrite ech_edual, edual_edual. split.
        -- intros (v & Hv & Hc & Hn). destruct (Hone (edual o)) as [H|H]; [by rewrite ech_edual|done|].
           apply elem_of_dom in H as [w Hw]. exists w. split_and!; [done|done|].
           intros Hn'. apply (Hx o); [by eapply elem_of_dom_2|done].
        -- intros (v & Hv & Hc & Hn). destruct (Hone o Hc) as [H|H]; [|done].
           apply elem_of_dom in H as [w Hw]. exists w. split_and!; [done|done|].
           intros Hn'. apply (Hx (edual o)); [done|by eapply elem_of_dom_2].
      * intros o S x Ho. unfold s_cut in Ho. apply map_lookup_filter_Some in Ho as (Ho & Hc & Hn). simpl in *.
        destruct (st_pairs _ _ _ _ Hs o Hc) as (S1 & x1 & S' & H1 & H2 & Hdu).
        pose proof (sth_lookup_B _ _ _ _ _ _ Hs H1) as T1. pose proof (sth_lookup_B _ _ _ _ _ _ Hs H2) as T2.
        rewrite (lookup_union_r ΘM Θr o) in T1 by (apply not_elem_of_dom; intros Hm; apply (Hx o Hm); by eapply elem_of_dom_2).
        rewrite Ho in T1. simplify_eq.
        assert (edual o ∈ dom ΘM) as HdM.
        { destruct (Hone (edual o)) as [H|H]; [by rewrite ech_edual|done|done]. }
        rewrite lookup_union_l' in T2 by (by apply elem_of_dom).
        exists S'. split; [|done]. unfold s_cut. apply map_lookup_filter_Some. simpl.
        rewrite ech_edual, edual_edual. split_and!; [done|done|]. intros Hm. apply (Hx o Hm). by eapply elem_of_dom_2.
    + eapply pfree_sub'; [|exact (st_free _ _ _ _ Hr)]. rewrite dom_union_L. set_solver.
    + eapply pfree_sub'; [|exact (st_free _ _ _ _ HM)]. rewrite dom_union_L. set_solver.
    + eapply pfree_sub'; [|exact (st_free _ _ _ _ Hr)]. rewrite dom_union_L. set_solver.
    + intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o1 & -> & H1), H2 as (o2 & Heq & H2).
      unfold s_if in H1, H2. apply elem_of_dom_filter in H1 as (v1 & V1 & C1), H2 as (v2 & V2 & C2). simpl in *.
      destruct (ech_inj_dual o2 o1 (eq_sym Heq)) as [-> | ->].
      * apply (Hx o1); by eapply elem_of_dom_2.
      * apply C1. apply (sth_partner _ _ _ _ _ Hs); rewrite dom_union_L; apply elem_of_union;
          [right|left]; by eapply elem_of_dom_2.
    + intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o1 & -> & H1), H2 as (o2 & Heq & H2).
      unfold s_if, s_cut in H1, H2. apply elem_of_dom_filter in H1 as (v1 & V1 & C1), H2 as (v2 & V2 & C2 & _).
      simpl in *. by rewrite <-Heq in C2.
    + intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o1 & -> & H1), H2 as (o2 & Heq & H2).
      unfold s_if, s_cut in H1, H2. apply elem_of_dom_filter in H1 as (v1 & V1 & C1), H2 as (v2 & V2 & C2 & _).
      simpl in *. by rewrite <-Heq in C2.
    + intros c H1 H2. unfold s_ch in H1, H2. apply elem_of_filter in H1 as [[H1 _] _], H2 as [[H2 _] _].
      by apply (Hx (EPos c)).
    + intros c H1 H2. unfold s_ch in H1. apply elem_of_filter in H1 as [Hb Hc].
      apply elem_of_union in H2 as [H2|H2]; [apply elem_of_union in H2 as [H2|H2]|];
        apply elem_of_chans_of_iff in H2 as (o & -> & Ho); unfold s_if, s_cut in Ho.
      * apply elem_of_dom_filter in Ho as (v & _ & Hp). simpl in Hp. tauto.
      * apply elem_of_dom_filter in Ho as (v & _ & Hp). simpl in Hp. tauto.
      * apply elem_of_dom_filter in Ho as (v & _ & _ & Hp). simpl in Hp.
        apply (both_ends (λ o, o ∈ dom Θr) o) in Hb. cbv beta in Hb. tauto.
    + intros c H1 H2. unfold s_ch in H1. apply elem_of_filter in H1 as [Hb Hc].
      apply (both_ends (λ o, o ∈ dom ΘM) (EPos c)) in Hb as [Hb1 Hb2]. cbv beta in Hb1, Hb2. simpl in Hb2.
      apply elem_of_union in H2 as [H2|H2]; [apply elem_of_union in H2 as [H2|H2]|];
        apply elem_of_chans_of_iff in H2 as (o & -> & Ho); unfold s_if, s_cut in Ho.
      * apply elem_of_dom_filter in Ho as (v & _ & Hp). simpl in Hp. tauto.
      * apply elem_of_dom_filter in Ho as (v & _ & Hp). simpl in Hp. tauto.
      * apply elem_of_dom_filter in Ho as (v & Hv & _ & Hp). simpl in Hp.
        destruct o; simpl in *; [apply (Hx _ Hb1)|apply (Hx _ Hb2)]; by eapply elem_of_dom_2.
  - rewrite (sth_if _ _ _ _ Hs), map_filter_union by done. unfold s_if. by apply map_union_comm, map_disjoint_filter.
  - apply set_eq. intros c. rewrite !elem_of_union. unfold s_ch. rewrite !elem_of_filter. split.
    + intros Hc. destruct (Hone (EPos c) Hc) as [P1|P1]; destruct (Hone (ENeg c) Hc) as [N1|N1].
      * left; right. auto.
      * right. apply elem_of_chans_of_iff. exists (ENeg c). split; [done|]. unfold s_cut. apply elem_of_dom_filter.
        apply elem_of_dom in N1 as [v Hv]. exists v. simpl. split_and!; [done|done|]. by apply Hx.
      * right. apply elem_of_chans_of_iff. exists (EPos c). split; [done|]. unfold s_cut. apply elem_of_dom_filter.
        apply elem_of_dom in P1 as [v Hv]. exists v. simpl. split_and!; [done|done|]. by apply Hx.
      * left; left. auto.
    + intros [[[_ Hc]|[_ Hc]]|Hc]; [done|done|]. apply elem_of_chans_of_iff in Hc as (o & -> & Ho).
      unfold s_cut in Ho. apply elem_of_dom_filter in Ho as (v & _ & Hc & _). done.
Qed.

(** ** A fusion of a single thread *)

Section fuse.
  Context (Θ Σ ΘB : senv) (C : gset chan) (e : expr) (Hs : sth Θ Σ ΘB C).
  Context (h : cend → cend) (D : gset chan) (Hf : fuse_ok h D Σ (C, {[+ e +]})).

  Lemma fs_held o : o ∈ dom Θ → pheld Σ (C, {[+ e +]}) o.
  Proof.
    intros Ho. rewrite (st_env _ _ _ _ Hs), dom_union_L in Ho. unfold pheld. simpl.
    apply elem_of_union in Ho as [Ho|Ho]; [by left|right]. by apply (st_dom _ _ _ _ Hs).
  Qed.

  Lemma fs_kinj : kinj h Θ.
  Proof.
    destruct Hf as (_ & Hi & _). intros o1 o2 v1 v2 H1 H2 Heq.
    apply Hi; [apply fs_held|apply fs_held|done]; by eapply elem_of_dom_2.
  Qed.

  Definition fs_res : senv := kren h ΘB ∪ filter (λ oe : cend * (sty * point), ech oe.1 ∈ D) (kren h Σ).

  Lemma pfuse_single : pfuse h D (C, {[+ e +]}) = (set_map (gch h) C ∪ D, {[+ emap h e +]}).
  Proof. unfold pfuse. cbn [fst snd]. by rewrite emapE_singleton. Qed.

  Lemma sth_fuse : sth (kren h Θ) (sdrop D (kren h Σ)) fs_res (set_map (gch h) C ∪ D).
  Proof.
    destruct Hf as (Hdc & Hi & Hp & HD & HDp).
    pose proof fs_kinj as Hk.
    assert (kinj h Σ) as KΣ by (eapply kinj_sub; [|exact Hk]; rewrite (st_env _ _ _ _ Hs), dom_union_L; set_solver).
    assert (kinj h ΘB) as KB by (eapply kinj_sub; [|exact Hk]; rewrite (st_env _ _ _ _ Hs), dom_union_L; set_solver).
    assert (kren h Σ ##ₘ kren h ΘB) as Hdisj.
    { apply kren_disjoint; [by rewrite <-(st_env _ _ _ _ Hs)|exact (sth_disj _ _ _ _ Hs)]. }
    (** The image of an end of a restricted channel. *)
    simpl in HD.
    assert (∀ o', ech o' ∈ (set_map (gch h) C : gset chan) → ∃ o0, ech o0 ∈ C ∧ h o0 = o') as Himg.
    { intros o' Ho'. apply elem_of_map in Ho' as (c & Hc & HcC). unfold gch in Hc.
      destruct (ech_inj_dual o' (h (EPos c)) Hc) as [-> | ->]; [exists (EPos c); done|].
      exists (ENeg c). split; [done|]. change (ENeg c) with (edual (EPos c)). by rewrite Hdc. }
    constructor.
    - rewrite (st_env _ _ _ _ Hs), kren_union by (by rewrite <-(st_env _ _ _ _ Hs)).
      unfold fs_res, sdrop. apply map_eq. intros o. rewrite !lookup_union, !map_lookup_filter.
      destruct (kren h Σ !! o) eqn:E1, (kren h ΘB !! o) eqn:E2; simpl; repeat (case_guard; simpl); try done.
      all: exfalso; by apply (proj1 (map_disjoint_spec _ _) Hdisj o _ _ E1 E2).
    - intros o. unfold fs_res. rewrite dom_union_L, elem_of_union, elem_of_dom_filter, elem_of_union. split.
      + intros [Ho|(v & Hv & Hc)]; [left|right; done].
        rewrite kren_dom in Ho by done. apply elem_of_map in Ho as (o0 & -> & Ho0).
        rewrite ech_gch by done. apply elem_of_map. exists (ech o0). split; [done|]. by apply (st_dom _ _ _ _ Hs).
      + intros [Ho|Ho].
        * left. destruct (Himg o Ho) as (o0 & Hc & <-). rewrite kren_dom by done. apply elem_of_map.
          exists o0. split; [done|]. by apply (st_dom _ _ _ _ Hs).
        * right. destruct (HDp o Ho) as (S & x & S' & H1 & _). eauto.
    - intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o & -> & Ho). unfold sdrop in Ho.
      apply elem_of_dom_filter in Ho as (v & Hv & HnD). simpl in HnD.
      apply elem_of_union in H2 as [H2|H2]; [|done].
      destruct (Himg o H2) as (o0 & Hc & Heq). destruct (kren_lookup_inv _ _ _ _ Hv) as (o1 & -> & Ho1).
      assert (o1 = o0) as ->.
      { apply Hi; [left; by eapply elem_of_dom_2|right; simpl; done|done]. }
      apply (st_disj _ _ _ _ Hs (ech o0)); [apply elem_of_chans_of; by eapply elem_of_dom_2|done].
    - intros o Ho Hd. unfold sdrop in Ho, Hd. apply elem_of_dom_filter in Ho as (v1 & V1 & N1), Hd as (v2 & V2 & N2).
      simpl in N1, N2. destruct (kren_lookup_inv _ _ _ _ V1) as (o1 & -> & O1).
      destruct (kren_lookup_inv _ _ _ _ V2) as (o2 & Heq & O2).
      destruct (Hp o1 o2) as [->|HD']; [left; by eapply elem_of_dom_2|left; by eapply elem_of_dom_2|done| |done].
      apply (st_free _ _ _ _ Hs o1); by eapply elem_of_dom_2.
    - intros o Ho. apply elem_of_union in Ho as [Ho|Ho].
      + destruct (Himg o Ho) as (o0 & Hc & <-).
        destruct (st_pairs _ _ _ _ Hs o0 Hc) as (S & x & S' & H1 & H2 & Hdu).
        exists S, x, S'. unfold fs_res. rewrite <-Hdc. split_and!; [| |done]; apply lookup_union_Some_l; by apply kren_lookup.
      + destruct (HDp o Ho) as (S & x & S' & H1 & H2 & Hdu). exists S, x, S'.
        assert (∀ o', ech o' ∈ D → kren h ΘB !! o' = None) as HN.
        { intros o' Hd'. destruct (kren h ΘB !! o') eqn:E; [|done]. exfalso.
          destruct (kren_lookup_inv _ _ _ _ E) as (o0 & -> & O0). apply (HD (ech (h o0))); [done|].
          rewrite ech_gch by done. apply elem_of_map. exists (ech o0). split; [done|].
          apply (st_dom _ _ _ _ Hs). by eapply elem_of_dom_2. }
        unfold fs_res. split_and!; [| |done]; rewrite lookup_union_r by (apply HN; by rewrite ?ech_edual);
          apply map_lookup_filter_Some; split; [done| |done|]; simpl; by rewrite ?ech_edual.
  Qed.
End fuse.

(** ** The environments after a step *)

Section steps_env.
  Context (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C).

  Lemma sth_cfresh c : c ∉ C → c ∉ chans_of Σ → cfresh c Θ.
  Proof.
    intros H1 H2. rewrite (st_env _ _ _ _ Hs). unfold cfresh. rewrite !dom_union_L, !elem_of_union.
    assert (∀ o, ech o = c → o ∉ dom Σ ∧ o ∉ dom ΘB) as Hn.
    { intros o <-. split; [intros Ho; apply H2; by apply elem_of_chans_of|rewrite (st_dom _ _ _ _ Hs); done]. }
    destruct (Hn (EPos c) eq_refl), (Hn (ENeg c) eq_refl). tauto.
  Qed.

  Lemma sth_new c S x : c ∉ C → c ∉ chans_of Σ →
    sth (new_env c S x Θ) Σ (new_env c S x ΘB) (C ∪ {[c]}).
  Proof.
    intros H1 H2. pose proof (sth_disj _ _ _ _ Hs) as Hd. constructor.
    - rewrite (st_env _ _ _ _ Hs). unfold new_env. rewrite !insert_union_r; [done|..];
        apply not_elem_of_dom; intros Ho; apply H2;
        first [change c with (ech (ENeg c)); by apply elem_of_chans_of
              |change c with (ech (EPos c)); by apply elem_of_chans_of].
    - intros o. unfold new_env. rewrite !dom_insert_L, !elem_of_union, !elem_of_singleton, (st_dom _ _ _ _ Hs).
      destruct o; simpl; naive_solver.
    - intros c' Hc1 Hc2. apply elem_of_union in Hc2 as [Hc2| ->%elem_of_singleton]; [|done].
      by apply (st_disj _ _ _ _ Hs c').
    - exact (st_free _ _ _ _ Hs).
    - intros o Ho. apply elem_of_union in Ho as [Ho|Ho].
      + destruct (st_pairs _ _ _ _ Hs o Ho) as (S1 & x1 & S1' & L1 & L2 & Hdu). exists S1, x1, S1'.
        unfold new_env. assert (ech o ≠ c) by (intros <-; done).
        rewrite !lookup_insert_ne; [done|..]; try (intros <-; simpl in *; by rewrite ?ech_edual in *).
        all: destruct o; simpl in *; congruence.
      + apply elem_of_singleton in Ho. unfold new_env. destruct o as [c0|c0]; simpl in Ho; subst c0; simpl.
        * exists S, x, (dual S). rewrite lookup_insert_eq, lookup_insert_ne, lookup_insert_eq by done.
          split_and!; [done|done|]. apply seqv_refl.
        * exists (dual S), x‾, S. rewrite lookup_insert_ne, lookup_insert_eq, lookup_insert_eq by done.
          rewrite pt_dual_dual. split_and!; [done|done|]. unfold sdual. rewrite dual_involutive. apply seqv_refl.
  Qed.

  Lemma sth_upd o v : ech o ∉ C → o ∈ dom Θ → sth (<[o := v]> Θ) (<[o := v]> Σ) ΘB C.
  Proof.
    intros Hc Ho. assert (o ∈ dom Σ) as HoΣ.
    { apply elem_of_dom in Ho as [w Hw]. eapply elem_of_dom_2. by apply (sth_lookup_nC _ _ _ _ _ _ Hs Hc). }
    constructor.
    - by rewrite (st_env _ _ _ _ Hs), insert_union_l.
    - exact (st_dom _ _ _ _ Hs).
    - unfold chans_of. rewrite dom_insert_L. assert ({[o]} ∪ dom Σ = dom Σ) as -> by set_solver.
      exact (st_disj _ _ _ _ Hs).
    - intros o'. rewrite dom_insert_L. assert ({[o]} ∪ dom Σ = dom Σ) as -> by set_solver.
      exact (st_free _ _ _ _ Hs o').
    - exact (st_pairs _ _ _ _ Hs).
  Qed.

  Lemma sth_del o : ech o ∉ C → sth (delete o Θ) (delete o Σ) ΘB C.
  Proof.
    intros Hc. constructor.
    - rewrite (st_env _ _ _ _ Hs), delete_union. f_equal. apply delete_id.
      apply not_elem_of_dom. rewrite (st_dom _ _ _ _ Hs). done.
    - exact (st_dom _ _ _ _ Hs).
    - intros c H1 H2. apply (st_disj _ _ _ _ Hs c); [|done]. unfold chans_of in *. set_solver.
    - eapply pfree_sub'; [|exact (st_free _ _ _ _ Hs)]. set_solver.
    - exact (st_pairs _ _ _ _ Hs).
  Qed.
End steps_env.

(** ** Offers and readiness of a single thread *)

Lemma offers_sends a σ σ' : offers a (LSess σ) → offers a (LSess σ') → sends σ = sends σ'.
Proof. destruct a, σ, σ'; simpl; intros; destruct_and?; subst; done. Qed.

Lemma subjs_sends σ : subjs σ = set_map ech (sends σ).
Proof. destruct σ; simpl; by rewrite ?set_map_singleton_L. Qed.

(** A thread that offers no link offers one end. *)
Lemma offered_one Θ e o o' : offered_t Θ e o → offered_t Θ e o' → ¬ link_t e → o = o'.
Proof.
  intros [_ (σ & e1 & H1 & Ho)] [_ (σ' & e2 & H2 & Ho')] Hl.
  destruct (act_step _ _ _ H1) as (a & Ha & Hoff). destruct (act_step _ _ _ H2) as (a' & Ha' & Hoff').
  rewrite Ha in Ha'. injection Ha' as <-. rewrite <-(offers_sends a σ σ' Hoff Hoff') in Ho'.
  destruct σ; simpl in Ho, Ho'; [set_solver..|exfalso; apply Hl; by exists os, e1].
Qed.

Definition q1 (C : gset chan) (e : expr) : config := (C, {[0 := e]}).

Lemma soup_q1 e : soup {[0 := e]} = {[+ e +]}.
Proof. rewrite <-insert_empty, (soup_insert ∅ 0 e) by apply lookup_empty. by rewrite soup_empty, (left_id_L ∅ (⊎)). Qed.

Lemma erase_q1 C e : erase (q1 C e) = (C, {[+ e +]}).
Proof.
  unfold erase, q1. cbn [fst snd]. by rewrite soup_q1.
Qed.

Lemma single_sess C e σ e' : tstep e (LSess σ) e' → subjs σ ## C →
  pstep (C, {[+ e +]}) (PSess σ) (C ∖ sentc σ, {[+ e' +]}).
Proof.
  intros Hs Hc. exists (q1 C e), (EvSess 0 σ), (C ∖ sentc σ, <[0 := e']> {[0 := e]}).
  split_and!; [apply erase_q1|by eapply p_act_session; [rewrite lookup_singleton_eq| |]|  |done].
  unfold erase. simpl. rewrite insert_singleton. by rewrite <-(erase_q1 _ e').
Qed.

(** A non-session step of the thread is a τ step of (C, {e}). *)
Lemma single_tau C e α e' : tstep e α e' → (∀ σ, α ≠ LSess σ) → ∃ p', preduction (C, {[+ e +]}) p'.
Proof.
  intros Hs Hα. destruct α as [|ℓ c|κf o c|v|σ].
  - eexists. exists (q1 C e), (EvBeta 0), (C, <[0 := e']> {[0 := e]}). split_and!; [apply erase_q1| |done|done].
    eapply p_act_beta; [by rewrite lookup_singleton_eq|done].
  - set (c' := fresh (C ∪ fchans e)). pose proof (is_fresh (C ∪ fchans e)) as Hf. fold c' in Hf.
    destruct (new_retarget e ℓ c e' c' Hs) as [e'' He''].
    eexists. exists (q1 C e), (EvNew 0 ℓ c'), (C ∪ {[c']}, <[0 := e'']> {[0 := e]}). split_and!; [apply erase_q1| |done|done].
    eapply p_act_new; [by rewrite lookup_singleton_eq|done|set_solver|].
    rewrite soup_q1, echans_singleton. set_solver.
  - set (c' := fresh (C ∪ fchans e)). pose proof (is_fresh (C ∪ fchans e)) as Hf. fold c' in Hf.
    destruct (new_at_retarget e κf o c e' c' Hs) as [e'' He''].
    eexists. exists (q1 C e), (EvNewAt 0 κf o c'), (C ∪ {[c']}, <[0 := e'']> {[0 := e]}). split_and!; [apply erase_q1| |done|done].
    eapply p_act_new_at; [by rewrite lookup_singleton_eq|done|set_solver|].
    rewrite soup_q1, echans_singleton. set_solver.
  - eexists. exists (q1 C e), (EvSpawn 0 1 v), (C, <[1 := App v EUnit]> (<[0 := e']> {[0 := e]})).
    split_and!; [apply erase_q1| |done|done].
    eapply p_act_spawn; [by rewrite lookup_singleton_eq|done|by rewrite lookup_singleton_ne].
  - by destruct (Hα σ).
Qed.

(** A link of a restricted channel is a τ step. *)
Lemma single_link_tau C e os e' o : tstep e (LSess (SLink os)) e' → o ∈ os → ech o ∈ C →
  ∃ p', preduction (C, {[+ e +]}) p'.
Proof.
  intros Hs Ho Hc. destruct (act_step _ _ _ Hs) as (a & Ha & Hoff).
  destruct a as [| | | | | | |o1 o2| |]; simpl in Hoff; try contradiction. subst os.
  assert (∃ o', tstep e (LSess (SLink ({[o]} ∪ {[o']}))) e') as [o' Hs'].
  { apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho.
    - exists o2. by rewrite Ho.
    - exists o1. by rewrite Ho, (union_comm_L {[o2]}). }
  eexists. exists (q1 C e), (EvLink 0 o o'), (C ∖ {[ech o]}, emap (csub o o') <$> (<[0 := e']> {[0 := e]})).
  split_and!; [apply erase_q1| |done|done].
  eapply p_act_link; [by rewrite lookup_singleton_eq|done|done].
Qed.

Global Instance link_t_dec e : Decision (link_t e).
Proof.
  destruct (act e) as [a|] eqn:Ha.
  - destruct a as [| | | | | | |o1 o2| |];
      try (right; intros (os & e' & Hs); destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoff);
           rewrite Ha in Ha'; injection Ha' as <-; simpl in Hoff; done).
    left. destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e' He']. by eexists _, _.
  - right. intros (os & e' & Hs). destruct (act_step _ _ _ Hs) as (a' & Ha' & _). by rewrite Ha in Ha'.
Qed.

Section single_ready.
  Context (W1 : world) (HS : strict W1) (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C) (e : expr).

  (** A stable (C, {e}) gives a stable e, and a link offer of e is one of
      (C, {e}). *)
  Lemma single_stable : stable_p (C, {[+ e +]}) → stable_t e ∧ (link_t e → link_p (C, {[+ e +]})).
  Proof.
    intros Hst. split.
    - intros α e' Hs'. destruct α as [| | | |σ]; [..|by eauto];
        (destruct (single_tau C e _ e' Hs') as [p' Hp']; [done|]; by destruct (Hst p')).
    - intros (os & e' & Hl). destruct (decide (subjs (SLink os) ## C)) as [Hd|Hd].
      + exists os, (C ∖ sentc (SLink os), {[+ e' +]}). by apply single_sess.
      + exfalso. rewrite subjs_sends in Hd. simpl in Hd.
        destruct (decide (∃ o, o ∈ os ∧ ech o ∈ C)) as [(o & Ho & Hc)|Hn].
        * destruct (single_link_tau C e os e' o Hl Ho Hc) as [p' Hp']. by destruct (Hst p').
        * apply Hd. intros c H1 H2. apply elem_of_map in H1 as (o & -> & Ho). eauto.
  Qed.

  (** Below the rest at the empty future, an offered end is free. *)
  Lemma offered_free o : below_rest W1 Θ (offered_t Θ e) ∅ → ¬ link_t e → offered_t Θ e o → ech o ∉ C.
  Proof.
    intros Hb Hl Ho Hc. destruct (st_pairs _ _ _ _ Hs o Hc) as (S & x & S' & H1 & H2 & _).
    apply (sth_lookup_B _ _ _ _ _ _ Hs) in H1, H2.
    destruct (Hb o S x Ho H1) as [B _].
    assert (¬ offered_t Θ e (edual o)) as Hn.
    { intros Ho'. pose proof (offered_one _ _ _ _ Ho Ho' Hl) as Heq. destruct o; discriminate. }
    pose proof (B _ _ _ H2 Hn) as Hlt. rewrite pt_dual_dual in Hlt. by apply (proj2 HS x).
  Qed.

  Lemma offered_sess o : offered_t Θ e o → ¬ link_t e → ech o ∉ C →
    o ∈ dom Σ ∧ offered_p Σ (C, {[+ e +]}) o.
  Proof.
    intros Ho Hl Hc. destruct Ho as [Hd (σ & e' & Hs' & Hσ)].
    assert (o ∈ dom Σ) as HoΣ.
    { apply elem_of_dom in Hd as [v Hv]. eapply elem_of_dom_2. by apply (sth_lookup_nC _ _ _ _ _ _ Hs Hc). }
    split; [done|]. split; [done|]. exists σ, (C ∖ sentc σ, {[+ e' +]}). split; [|done].
    apply single_sess; [done|]. rewrite subjs_sends.
    destruct σ; simpl in Hσ |- *; try (exfalso; apply Hl; by eexists _, _).
    all: apply elem_of_singleton in Hσ as ->; rewrite set_map_singleton_L; set_solver.
  Qed.
End single_ready.

(** ** The environments of Q-Send *)

Definition rpart (C : gset chan) (ΘM Θr : senv) : senv :=
  filter (λ oe : cend * (sty * point), ech oe.1 ∈ C ∧ edual oe.1 ∈ dom ΘM) Θr.
Definition rkeep (C : gset chan) (ΘM Θr : senv) : senv :=
  filter (λ oe : cend * (sty * point), ech oe.1 ∈ C ∧ edual oe.1 ∉ dom ΘM) Θr.
Definition rin (C : gset chan) (Θ : senv) : senv := filter (λ oe : cend * (sty * point), ech oe.1 ∈ C) Θ.
Definition rout (C : gset chan) (Θ : senv) : senv := filter (λ oe : cend * (sty * point), ech oe.1 ∉ C) Θ.

Section send.
  Context (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C).
  Context (o : cend) (S0 : sty) (x : point) (Ho : Θ !! o = Some (S0, x)) (Hc : ech o ∉ C).
  Context (ΘM Θr : senv) (Hd : ΘM ##ₘ Θr) (HΘ : delete o Θ = ΘM ∪ Θr).

  Lemma snd_x o' : o' ∈ dom ΘM → o' ∉ dom Θr.
  Proof. intros H1 H2. apply elem_of_dom in H1 as [? H1], H2 as [? H2]. by apply (proj1 (map_disjoint_spec _ _) Hd o' _ _ H1 H2). Qed.

  Lemma snd_lookup o' w : (ΘM ∪ Θr) !! o' = Some w → Θ !! o' = Some w ∧ o' ≠ o.
  Proof. rewrite <-HΘ. intros H. apply lookup_delete_Some in H as [Hne H]. split; [done|]. intros ->. done. Qed.

  Lemma snd_M o' w : ΘM !! o' = Some w → Θ !! o' = Some w ∧ o' ≠ o.
  Proof. intros H. apply snd_lookup. by apply lookup_union_Some_l. Qed.

  Lemma snd_r o' w : Θr !! o' = Some w → Θ !! o' = Some w ∧ o' ≠ o.
  Proof. intros H. apply snd_lookup. by apply lookup_union_Some_r. Qed.

  Lemma snd_held o' : ech o' ∈ C → o' ∈ dom ΘM ∨ o' ∈ dom Θr.
  Proof.
    intros Hc'. destruct (sth_both _ _ _ _ o' Hs Hc') as [H _].
    assert (o' ≠ o) by (intros ->; done).
    assert (o' ∈ dom (delete o Θ)) as H' by (rewrite dom_delete_L; set_solver).
    by rewrite HΘ, dom_union_L, elem_of_union in H'.
  Qed.

  Lemma snd_Σo : Σ !! o = Some (S0, x).
  Proof. by apply (sth_lookup_nC _ _ _ _ _ _ Hs Hc). Qed.

  Lemma snd_split : rout C ΘM ##ₘ rout C Θr ∧ delete o Σ = rout C ΘM ∪ rout C Θr.
  Proof.
    split; [by apply map_disjoint_filter|].
    rewrite (sth_if _ _ _ _ Hs), <-map_filter_delete, HΘ. by apply map_filter_union.
  Qed.

  Lemma snd_ΘM : rout C ΘM ∪ rin C ΘM = ΘM.
  Proof. unfold rout, rin. mcrush. Qed.

  Lemma snd_send_split : send_split Σ (rpart C ΘM Θr) (rin C ΘM).
  Proof.
    split_and!.
    - intros o' Ho'. apply elem_of_dom_filter in Ho' as (w & _ & Hc'). simpl in Hc'.
      split; intros Hin; apply (st_disj _ _ _ _ Hs (ech o')); [by apply elem_of_chans_of|done| |done].
      rewrite <-ech_edual. by apply elem_of_chans_of.
    - intros o'. unfold rpart, rin. rewrite !elem_of_dom_filter. simpl. rewrite ech_edual. split.
      + intros (w & Hw & Hc' & HM). apply elem_of_dom in HM as [w' Hw']. split; [eauto|].
        intros (w'' & Hw'' & _). apply (snd_x o'); by eapply elem_of_dom_2.
      + intros [(w & Hw & Hc') Hn]. destruct (snd_held o' Hc') as [H|H].
        * exfalso. apply Hn. apply elem_of_dom in H as [w' Hw']. eauto.
        * apply elem_of_dom in H as [w' Hw']. exists w'. split_and!; [done|done|by eapply elem_of_dom_2].
    - intros o' S y Ho'. unfold rin in Ho'. apply map_lookup_filter_Some in Ho' as [Ho' Hc']. simpl in Hc'.
      destruct (st_pairs _ _ _ _ Hs o' Hc') as (S1 & y1 & S' & H1 & H2 & Hdu).
      apply (sth_lookup_B _ _ _ _ _ _ Hs) in H1, H2. rewrite (proj1 (snd_M _ _ Ho')) in H1. simplify_eq.
      exists S'. split; [|done].
      assert (ech (edual o') ∈ C) as Hc'' by by rewrite ech_edual.
      destruct (snd_held (edual o') Hc'') as [HM|Hr].
      + apply elem_of_dom in HM as [w Hw]. rewrite (proj1 (snd_M _ _ Hw)) in H2. simplify_eq.
        apply lookup_union_Some_r; [apply map_disjoint_spec; intros ? ? ? A B;
          apply map_lookup_filter_Some in A as [A _], B as [B _]; apply (snd_x _ (elem_of_dom_2 _ _ _ B)); by eapply elem_of_dom_2|].
        apply map_lookup_filter_Some. split; [done|]. simpl. by rewrite ech_edual.
      + apply elem_of_dom in Hr as [w Hw]. rewrite (proj1 (snd_r _ _ Hw)) in H2. simplify_eq.
        apply lookup_union_Some_l. apply map_lookup_filter_Some. split; [done|]. simpl.
        rewrite ech_edual, edual_edual. split; [done|by eapply elem_of_dom_2].
  Qed.

  Lemma snd_sth v : sth (<[o := v]> Θr) (<[o := v]> (rout C Θr ∪ rpart C ΘM Θr)) (rkeep C ΘM Θr)
                        (C ∖ set_map ech (dom ΘM)).
  Proof.
    assert (Θr = rout C Θr ∪ rpart C ΘM Θr ∪ rkeep C ΘM Θr) as Er.
    { unfold rout, rpart, rkeep. mcrush. all: exfalso; tauto. }
    assert (∀ o', o' ∈ dom (rout C Θr ∪ rpart C ΘM Θr) → (ech o' ∉ C ∨ edual o' ∈ dom ΘM) ∧ o' ∈ dom Θr) as Hif.
    { intros o'. rewrite dom_union_L, elem_of_union. unfold rout, rpart. rewrite !elem_of_dom_filter.
      intros [(w & Hw & Hp)|(w & Hw & Hp & Hq)]; simpl in *; (split; [tauto|by eapply elem_of_dom_2]). }
    constructor.
    - by rewrite <-insert_union_l, <-Er.
    - intros o'. unfold rkeep. rewrite elem_of_dom_filter, elem_of_difference. simpl. split.
      + intros (w & Hw & Hc' & Hn). split; [done|]. intros (o'' & Heq & Ho'')%elem_of_map.
        destruct (ech_inj_dual o' o'' Heq) as [<- | ->]; [apply (snd_x o' Ho''); by eapply elem_of_dom_2|].
        by rewrite edual_edual in Hn.
      + intros [Hc' Hn]. destruct (snd_held o' Hc') as [H|H].
        * exfalso. apply Hn. apply elem_of_map. by exists o'.
        * apply elem_of_dom in H as [w Hw]. exists w. split_and!; [done|done|].
          intros H. apply Hn. apply elem_of_map. exists (edual o'). by rewrite ech_edual.
    - intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o' & -> & Ho'). apply elem_of_difference in H2 as [H2 H3].
      rewrite dom_insert_L, elem_of_union in Ho'. destruct Ho' as [->%elem_of_singleton|Ho']; [done|].
      destruct (Hif o' Ho') as [[Hn|HM] _]; [done|]. apply H3. apply elem_of_map. exists (edual o'). by rewrite ech_edual.
    - intros o' H1 H2. rewrite dom_insert_L, elem_of_union in H1, H2.
      assert (∀ o'', o'' ∈ dom (rout C Θr ∪ rpart C ΘM Θr) → o'' ∈ dom Θ ∧ o'' ≠ o) as HΘd.
      { intros o'' H. destruct (Hif o'' H) as [_ Hr]. apply elem_of_dom in Hr as [w Hw].
        destruct (snd_r _ _ Hw) as [A B]. split; [by eapply elem_of_dom_2|done]. }
      assert (o ∈ dom Θ) as HoΘ by (by eapply elem_of_dom_2).
      destruct H1 as [->%elem_of_singleton|H1], H2 as [H2%elem_of_singleton|H2].
      + by destruct o.
      + apply Hc. apply (sth_partner _ _ _ _ _ Hs); [done|apply HΘd, H2].
      + apply Hc. apply (sth_partner _ _ _ _ _ Hs); [done|]. rewrite <-H2, edual_edual. apply HΘd, H1.
      + destruct (Hif o' H1) as [P1 R1], (Hif (edual o') H2) as [P2 R2].
        assert (ech o' ∈ C) as Hc' by (apply (sth_partner _ _ _ _ _ Hs); [apply HΘd, H1|apply HΘd, H2]).
        rewrite ech_edual, edual_edual in P2. destruct P1 as [?|P1]; [done|]. destruct P2 as [?|P2]; [done|].
        by apply (snd_x o').
    - intros o' Ho'. apply elem_of_difference in Ho' as [Hc' Hn].
      destruct (st_pairs _ _ _ _ Hs o' Hc') as (S & y & S' & H1 & H2 & Hdu).
      apply (sth_lookup_B _ _ _ _ _ _ Hs) in H1, H2. exists S, y, S'.
      assert (∀ o'', ech o'' = ech o' → o'' ∉ dom ΘM) as HnM.
      { intros o'' Heq H. apply Hn. apply elem_of_map. by exists o''. }
      assert (∀ o'' w, ech o'' = ech o' → Θ !! o'' = Some w → Θr !! o'' = Some w) as Hr.
      { intros o'' w Heq Hw. assert (ech o'' ∈ C) as Hc'' by by rewrite Heq.
        destruct (snd_held o'' Hc'') as [H|H]; [by destruct (HnM o'' Heq)|].
        apply elem_of_dom in H as [w' Hw']. rewrite (proj1 (snd_r _ _ Hw')) in Hw. by simplify_eq. }
      unfold rkeep. rewrite !map_lookup_filter_Some. simpl. rewrite ech_edual, edual_edual.
      split_and!; [by apply Hr| | |by apply Hr; rewrite ?ech_edual| | |done]; try done.
      + apply HnM. by rewrite ech_edual.
      + by apply HnM.
  Qed.
End send.

(** ** The environments of Q-Recv *)

Definition rback (Σ Θ2 : senv) : senv :=
  filter (λ oe : cend * (sty * point), ech oe.1 ∈ recv_back Σ Θ2) (Σ ∪ Θ2).

Section recv.
  Context (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C).
  Context (Θ2 : senv) (HC2 : set_map ech (dom Θ2) ## C) (Hok : recv_ok Σ Θ2).

  Lemma rcv_Σ2 o : o ∈ dom Θ2 → o ∉ dom Σ.
  Proof. apply Hok. Qed.

  Lemma rcv_C2 o : o ∈ dom Θ2 → ech o ∉ C.
  Proof. intros Ho Hc. apply (HC2 (ech o)); [apply elem_of_map; by exists o|done]. Qed.

  Lemma rcv_disj : Θ ##ₘ Θ2.
  Proof.
    apply map_disjoint_spec. intros o v1 v2 H1 H2. rewrite (st_env _ _ _ _ Hs) in H1.
    apply lookup_union_Some_raw in H1 as [H1|[_ H1]].
    - apply (rcv_Σ2 o); by eapply elem_of_dom_2.
    - apply (rcv_C2 o); [by eapply elem_of_dom_2|]. apply (st_dom _ _ _ _ Hs). by eapply elem_of_dom_2.
  Qed.

  (** The channel of an end of Σ ∪ Θ2 is brought back iff its partner is
      held as well. *)
  Lemma rcv_back o : o ∈ dom Σ ∪ dom Θ2 → ech o ∈ recv_back Σ Θ2 ↔ edual o ∈ dom Σ ∪ dom Θ2 ∧ (o ∈ dom Θ2 ∨ edual o ∈ dom Θ2).
  Proof.
    intros Ho. unfold recv_back. rewrite elem_of_map. split.
    - intros (o' & Heq & Ho'). apply elem_of_filter in Ho' as [Hp Ho'].
      destruct (ech_inj_dual o o' Heq) as [-> | ->]; [set_solver|]. rewrite edual_edual. set_solver.
    - intros [Hd [H2|H2]].
      + exists o. split; [done|]. apply elem_of_filter. set_solver.
      + exists (edual o). rewrite ech_edual. split; [done|]. apply elem_of_filter. split; [rewrite edual_edual|]; set_solver.
  Qed.

  Lemma rcv_pfree : pfree Σ.
  Proof. exact (st_free _ _ _ _ Hs). Qed.

  Lemma rcv_sth : sth (Θ ∪ Θ2) (recv_env Σ Θ2) (ΘB ∪ rback Σ Θ2) (C ∪ recv_back Σ Θ2).
  Proof.
    pose proof (sth_disj _ _ _ _ Hs) as HdB.
    assert (recv_back Σ Θ2 ## C) as HRC.
    { intros c H1 H2. unfold recv_back in H1. apply elem_of_map in H1 as (o & -> & Ho).
      apply elem_of_filter in Ho as [_ Ho]. by apply (rcv_C2 o). }
    assert (∀ o, ech o ∈ C → Σ !! o = None ∧ Θ2 !! o = None) as HnC.
    { intros o Hc. split; apply not_elem_of_dom; intros Ho.
      - apply (st_disj _ _ _ _ Hs (ech o)); [by apply elem_of_chans_of|done].
      - by apply (rcv_C2 o). }
    assert (∀ o, ΘB !! o ≠ None → ech o ∈ C) as HBC.
    { intros o Ho. apply (st_dom _ _ _ _ Hs). apply elem_of_dom. destruct (ΘB !! o); [by eexists|done]. }
    constructor.
    - rewrite (st_env _ _ _ _ Hs). apply map_eq. intros o. unfold recv_env, rback.
      rewrite !lookup_union, !map_lookup_filter, !lookup_union.
      destruct (ΘB !! o) eqn:EB.
      { assert (ech o ∈ C) as Hc by (apply HBC; by rewrite EB). destruct (HnC o Hc) as [-> ->]. simpl.
        by rewrite ?(left_id_L None union), ?(right_id_L None union). }
      destruct (Σ !! o) eqn:E1, (Θ2 !! o) eqn:E2; simpl.
      + exfalso. apply (rcv_Σ2 o); by eapply elem_of_dom_2.
      + assert (o ∈ dom Σ ∪ dom Θ2) as Hd by (apply elem_of_union; left; by eapply elem_of_dom_2).
        pose proof (rcv_back o Hd) as Hb.
        assert (o ∉ dom Θ2) by (by apply not_elem_of_dom).
        repeat (case_guard; simpl); try done; exfalso;
        clear Hs HC2 Hok HdB HRC HnC HBC EB E1 E2; set_solver.
      + assert (o ∈ dom Σ ∪ dom Θ2) as Hd by (apply elem_of_union; right; by eapply elem_of_dom_2).
        pose proof (rcv_back o Hd) as Hb.
        assert (o ∈ dom Θ2) by (by eapply elem_of_dom_2).
        repeat (case_guard; simpl); try done; exfalso;
        clear Hs HC2 Hok HdB HRC HnC HBC EB E1 E2; set_solver.
      + done.
    - intros o. rewrite dom_union_L, elem_of_union, (st_dom _ _ _ _ Hs), elem_of_union. unfold rback.
      rewrite elem_of_dom_filter. split; [intros [?|(w & _ & ?)]; auto|].
      intros [?|Hb]; [by left|right].
      assert (o ∈ dom Σ ∪ dom Θ2) as Hd.
      { unfold recv_back in Hb. apply elem_of_map in Hb as (o' & Heq & Ho'). apply elem_of_filter in Ho' as [Hp Ho'].
        destruct (ech_inj_dual o o' Heq) as [-> | ->]; set_solver. }
      rewrite <-dom_union_L in Hd. apply elem_of_dom in Hd as [w Hw]. eauto.
    - intros c H1 H2. apply elem_of_chans_of_iff in H1 as (o & -> & Ho). unfold recv_env in Ho.
      rewrite dom_union_L, elem_of_union, !elem_of_dom_filter in Ho.
      assert (o ∈ dom Σ ∪ dom Θ2) as Hd.
      { destruct Ho as [(w & Hw & _)|(w & Hw & _)]; apply elem_of_union; [left|right]; by eapply elem_of_dom_2. }
      apply elem_of_union in H2 as [H2|H2].
      + destruct Ho as [(w & Hw & _)|(w & Hw & _)].
        * apply (st_disj _ _ _ _ Hs (ech o)); [apply elem_of_chans_of; by eapply elem_of_dom_2|done].
        * apply (rcv_C2 o); [by eapply elem_of_dom_2|done].
      + apply (rcv_back o Hd) in H2. simpl in Ho. destruct Ho as [(w & Hw & P)|(w & Hw & P)].
        * assert (o ∉ dom Θ2) by (intros H; apply (rcv_Σ2 o H); by eapply elem_of_dom_2). set_solver.
        * set_solver.
    - intros o H1 H2. unfold recv_env in H1, H2. rewrite dom_union_L, elem_of_union, !elem_of_dom_filter in H1, H2.
      simpl in H1, H2. rewrite edual_edual in H2.
      destruct H1 as [(w & Hw & P)|(w & Hw & P)]; destruct H2 as [(w' & Hw' & P')|(w' & Hw' & P')].
      + apply (st_free _ _ _ _ Hs o); by eapply elem_of_dom_2.
      + apply P. by eapply elem_of_dom_2.
      + apply (proj1 P). by eapply elem_of_dom_2.
      + apply (proj2 P). by eapply elem_of_dom_2.
    - intros o Ho. apply elem_of_union in Ho as [Hc|Hb].
      + destruct (st_pairs _ _ _ _ Hs o Hc) as (S & y & S' & H1 & H2 & Hdu). exists S, y, S'.
        split_and!; [by apply lookup_union_Some_l..|done].
      + assert (ech o ∉ C) as Hc by set_solver.
        assert (∀ o', ech o' = ech o → ΘB !! o' = None) as HN.
        { intros o' Heq. destruct (ΘB !! o') eqn:E; [|done]. exfalso. apply Hc. rewrite <-Heq. apply HBC. by rewrite E. }
        assert (o ∈ dom Σ ∪ dom Θ2) as Hd.
        { unfold recv_back in Hb. apply elem_of_map in Hb as (o' & Heq & Ho'). apply elem_of_filter in Ho' as [Hp Ho'].
          destruct (ech_inj_dual o o' Heq) as [-> | ->]; set_solver. }
        pose proof (proj1 (rcv_back o Hd) Hb) as [Hd' H2].
        assert (∀ o' w, ech o' = ech o → (Σ ∪ Θ2) !! o' = Some w → (ΘB ∪ rback Σ Θ2) !! o' = Some w) as Hl.
        { intros o' w Heq Hw. rewrite lookup_union_r by (by apply HN). unfold rback.
          apply map_lookup_filter_Some. split; [done|]. simpl. by rewrite Heq. }
        destruct H2 as [H2|H2].
        * apply elem_of_dom in H2 as [[S y] Hy].
          rewrite <-dom_union_L in Hd'. apply elem_of_dom in Hd' as [[S' y'] Hy'].
          assert ((Σ ∪ Θ2) !! o = Some (S, y)) as Hy2 by (rewrite lookup_union_r; [done|]; apply not_elem_of_dom, rcv_Σ2; by eapply elem_of_dom_2).
          destruct (proj2 Hok o S y S' y' Hy Hy') as [-> Hdu].
          exists S, y, S'. split_and!; [apply Hl; done|apply Hl; [by rewrite ech_edual|done]|done].
        * apply elem_of_dom in H2 as [[S y] Hy].
          assert (o ∈ dom (Σ ∪ Θ2)) as Hd2 by (by rewrite dom_union_L).
          apply elem_of_dom in Hd2 as [[S' y'] Hy'].
          rewrite <-(edual_edual o) in Hy' at 1.
          destruct (proj2 Hok (edual o) S y S' y' Hy Hy') as [-> Hdu].
          assert ((Σ ∪ Θ2) !! edual o = Some (S, y)) as Hy2.
          { rewrite lookup_union_r; [done|]. apply not_elem_of_dom, rcv_Σ2. by eapply elem_of_dom_2. }
          exists S', y‾, S. rewrite pt_dual_dual. split_and!; [apply Hl; [done|by rewrite edual_edual in Hy']|apply Hl; [by rewrite ech_edual|done]|].
          by apply sdual_sym.
  Qed.
End recv.

(** ** A link of a restricted channel *)

Lemma kren_csub (Θ0 : senv) o1 o2 v1 :
  Θ0 !! edual o1 = Some v1 → o1 ∉ dom Θ0 → o2 ∉ dom Θ0 → ech o2 ≠ ech o1 →
  kinj (csub o1 o2) Θ0 ∧ kren (csub o1 o2) Θ0 = <[o2 := v1]> (delete (edual o1) Θ0).
Proof.
  intros H1 N1 N2 Hne.
  assert (∀ o, o ∈ dom Θ0 → o ≠ edual o1 → csub o1 o2 o = o) as Hfix.
  { intros o Ho Hn. unfold csub. rewrite decide_False by done. rewrite decide_False; [done|]. by intros ->. }
  assert (csub o1 o2 (edual o1) = o2) as Hc by (unfold csub; by rewrite decide_True).
  assert (kinj (csub o1 o2) Θ0) as Hk.
  { intros a b va vb Ha Hb Heq. apply elem_of_dom_2 in Ha, Hb.
    destruct (decide (a = edual o1)) as [->|Na], (decide (b = edual o1)) as [->|Nb]; [done| | |].
    - rewrite Hc, (Hfix b Hb Nb) in Heq. subst. done.
    - rewrite Hc, (Hfix a Ha Na) in Heq. subst. done.
    - by rewrite (Hfix a Ha Na), (Hfix b Hb Nb) in Heq. }
  split; [done|].
  rewrite <-(insert_delete_id Θ0 (edual o1) v1 H1) at 1. rewrite kren_insert by (by rewrite insert_delete_id).
  rewrite Hc, kren_id; [done|]. intros o Ho. rewrite dom_delete_L in Ho. apply Hfix; set_solver.
Qed.

Section link.
  Context (Θ Σ ΘB : senv) (C : gset chan) (Hs : sth Θ Σ ΘB C).
  Context (o1 o2 : cend) (A1 A2 : sty) (y : point) (H1 : Θ !! o1 = Some (A1, y)) (H2 : Θ !! o2 = Some (A2, y‾)).
  Context (Hdu : sdual A1 A2) (Hne : o1 ≠ o2) (Hc : ech o1 ∈ C).

  Lemma lk_res : kinj (csub o1 o2) (delete o1 (delete o2 Θ)) ∧
    ∃ Σ'' ΘB'', sth (kren (csub o1 o2) (delete o1 (delete o2 Θ))) Σ'' ΘB'' (C ∖ {[ech o1]}) ∧ senv_eqv Σ'' Σ.
  Proof.
    pose proof (sth_disj _ _ _ _ Hs) as HdB.
    destruct (st_pairs _ _ _ _ Hs o1 Hc) as (A1x & yx & A1' & B1 & B1' & Hd1).
    rewrite (sth_lookup_B _ _ _ _ _ _ Hs B1) in H1. simplify_eq.
    assert (Σ !! o1 = None) as S1 by (apply not_elem_of_dom; intros Ho; apply (st_disj _ _ _ _ Hs (ech o1)); [by apply elem_of_chans_of|done]).
    assert (Σ !! edual o1 = None) as S1'.
    { apply not_elem_of_dom; intros Ho; apply (st_disj _ _ _ _ Hs (ech o1)); [rewrite <-ech_edual; by apply elem_of_chans_of|done]. }
    assert (∀ c, c ≠ ech o1 → c ∈ C → c ∈ C ∖ {[ech o1]}) as HCd by set_solver.
    destruct (decide (o2 = edual o1)) as [->|N2].
    { (* a link of the two ends of one channel *)
      assert (∀ o, csub o1 (edual o1) o = o) as Hid.
      { intros o. unfold csub. case_decide; [done|]. case_decide; [subst; by rewrite edual_edual|done]. }
      assert (kinj (csub o1 (edual o1)) (delete o1 (delete (edual o1) Θ))) as Hk.
      { intros a b va vb _ _. by rewrite !Hid. }
      split; [done|]. rewrite kren_id by (intros; apply Hid).
      exists Σ, (delete o1 (delete (edual o1) ΘB)). split; [|apply senv_eqv_refl]. constructor.
      - rewrite (st_env _ _ _ _ Hs), !delete_union, (delete_id Σ (edual o1)), (delete_id Σ o1) by done. done.
      - intros o. rewrite !dom_delete_L, elem_of_difference, elem_of_difference, (st_dom _ _ _ _ Hs), elem_of_difference, !elem_of_singleton.
        split; [intros [[Hc' N1] N1']; split; [done|]; intros Heq; destruct (ech_inj_dual o o1 Heq) as [-> | ->]; done|].
        intros [Hc' Hn]. split_and!; [done|intros ->; by rewrite ech_edual in Hn|intros ->; done].
      - intros c Hc1 Hc2. apply (st_disj _ _ _ _ Hs c); set_solver.
      - exact (st_free _ _ _ _ Hs).
      - intros o Ho. apply elem_of_difference in Ho as [Ho Hn].
        destruct (st_pairs _ _ _ _ Hs o Ho) as (S & x & S' & L1 & L2 & D). exists S, x, S'.
        assert (o ≠ o1 ∧ o ≠ edual o1 ∧ edual o ≠ o1 ∧ edual o ≠ edual o1) as (? & ? & ? & ?).
        { split_and!; intros Heq; apply Hn, elem_of_singleton; apply (f_equal ech) in Heq; rewrite ?ech_edual in Heq; done. }
        rewrite !lookup_delete_ne by done. done. }
    assert (ech o2 ≠ ech o1) as Nc.
    { intros Heq. destruct (ech_inj_dual o2 o1 Heq) as [-> | ->]; done. }
    assert (edual o1 ≠ o2) as N2' by (intros <-; done).
    assert (edual o1 ≠ o1) as N11 by (destruct o1; discriminate).
    destruct (kren_csub (delete o1 (delete o2 Θ)) o1 o2 (A1', y‾)) as [Hk Hren].
    { rewrite !lookup_delete_ne by done. exact (sth_lookup_B _ _ _ _ _ _ Hs B1'). }
    { rewrite !dom_delete_L. set_solver. }
    { rewrite !dom_delete_L. set_solver. }
    { done. }
    split; [done|]. rewrite Hren.
    destruct (decide (ech o2 ∈ C)) as [Hc2|Hc2].
    - (* the other channel is restricted as well *)
      destruct (st_pairs _ _ _ _ Hs o2 Hc2) as (A2x & yy & A2' & B2 & B2' & Hd2).
      rewrite (sth_lookup_B _ _ _ _ _ _ Hs B2) in H2. simplify_eq. rewrite pt_dual_dual in B2'.
      assert (Σ !! o2 = None) as S2 by (apply not_elem_of_dom; intros Ho; apply (st_disj _ _ _ _ Hs (ech o2)); [by apply elem_of_chans_of|done]).
      exists Σ, (<[o2 := (A1', y‾)]> (delete (edual o1) (delete o1 (delete o2 ΘB)))). split; [|apply senv_eqv_refl].
      constructor.
      + rewrite (st_env _ _ _ _ Hs), !delete_union, (delete_id Σ o2), (delete_id Σ o1), (delete_id Σ (edual o1)) by done.
        rewrite insert_union_r by done. done.
      + intros o. rewrite dom_insert_L, !dom_delete_L, elem_of_union, !elem_of_difference, !elem_of_singleton, (st_dom _ _ _ _ Hs).
        split.
        * intros [->|[[[Ho N1] N2''] N3]]; [split; [done|done]|].
          split; [done|]. intros Heq. destruct (ech_inj_dual o o1 Heq) as [-> | ->]; done.
        * intros [Ho Hn]. destruct (decide (o = o2)) as [->|No2]; [by left|right].
          split_and!; [done|..]; intros ->; [done|apply Hn; set_solver|apply Hn; rewrite ech_edual; set_solver].
      + intros c Hc1 Hc2'. apply (st_disj _ _ _ _ Hs c); set_solver.
      + exact (st_free _ _ _ _ Hs).
      + intros o Ho. apply elem_of_difference in Ho as [Ho Hn].
        assert (ech o ≠ ech o1) as Neo by set_solver.
        destruct (decide (ech o = ech o2)) as [Heq|Neq].
        * destruct (ech_inj_dual o o2 Heq) as [-> | ->].
          -- exists A1', y‾, A2'. rewrite lookup_insert_eq, lookup_insert_ne by (destruct o2; discriminate).
             rewrite !lookup_delete_ne by (intros Heq'; apply Nc; apply (f_equal ech) in Heq'; rewrite ?ech_edual in Heq'; congruence).
             rewrite ?lookup_delete_ne by (destruct o2; discriminate).
             rewrite pt_dual_dual. split_and!; [done|done|]. by eapply sdual_dual_dual.
          -- exists A2', y, A1'. rewrite edual_edual, lookup_insert_eq, lookup_insert_ne by (destruct o2; discriminate).
             rewrite !lookup_delete_ne by (intros Heq'; apply Nc; apply (f_equal ech) in Heq'; rewrite ?ech_edual in Heq'; congruence).
             rewrite ?lookup_delete_ne by (destruct o2; discriminate).
             split_and!; [done|done|]. apply sdual_sym. by eapply sdual_dual_dual.
        * destruct (st_pairs _ _ _ _ Hs o Ho) as (S & x & S' & L1 & L2 & D). exists S, x, S'.
          assert (∀ o', ech o' = ech o → o' ≠ o2 ∧ o' ≠ o1 ∧ o' ≠ edual o1) as Hn'.
          { intros o' Heq. split_and!; intros ->; [done|done|by rewrite ech_edual in Heq]. }
          destruct (Hn' o eq_refl) as (? & ? & ?). destruct (Hn' (edual o) (ech_edual o)) as (? & ? & ?).
          rewrite !lookup_insert_ne, !lookup_delete_ne by done. done.
    - (* the other end is free: the holder of o1‾ now holds o2 *)
      assert (Σ !! o2 = Some (A2, y‾)) as S2 by (by apply (sth_lookup_nC _ _ _ _ _ _ Hs Hc2)).
      exists (<[o2 := (A1', y‾)]> Σ), (delete (edual o1) (delete o1 ΘB)). split.
      + constructor.
        * assert (ΘB !! o2 = None) as B2 by (apply not_elem_of_dom; rewrite (st_dom _ _ _ _ Hs); done).
          rewrite (st_env _ _ _ _ Hs). apply map_eq. intros o.
          destruct (decide (o = o2)) as [->|No].
          { rewrite lookup_insert_eq, lookup_union, lookup_insert_eq, !lookup_delete_ne, B2 by done. done. }
          rewrite lookup_insert_ne, lookup_union, lookup_insert_ne by done.
          destruct (decide (o = o1)) as [->|N1].
          { rewrite lookup_delete_ne, lookup_delete_eq, S1, lookup_delete_ne, lookup_delete_eq by done. done. }
          destruct (decide (o = edual o1)) as [->|N1'].
          { rewrite !lookup_delete_eq, S1'. done. }
          rewrite !lookup_delete_ne by done. by rewrite lookup_union.
        * intros o. rewrite !dom_delete_L, !elem_of_difference, !elem_of_singleton, (st_dom _ _ _ _ Hs).
          split.
          -- intros [[Ho N1] N2'']. split; [done|]. intros Heq.
             destruct (ech_inj_dual o o1 Heq) as [-> | ->]; done.
          -- intros [Ho Hn]. split_and!; [done|..]; intros ->; apply Hn; rewrite ?ech_edual; set_solver.
        * intros c H1' H2'. apply elem_of_chans_of_iff in H1' as (o & -> & Ho). rewrite dom_insert_L in Ho.
          apply elem_of_difference in H2' as [H2' _]. apply elem_of_union in Ho as [->%elem_of_singleton|Ho]; [done|].
          apply (st_disj _ _ _ _ Hs (ech o)); [by apply elem_of_chans_of|done].
        * intros o. rewrite !dom_insert_L. assert ({[o2]} ∪ dom Σ = dom Σ) as -> by (apply elem_of_dom_2 in S2; set_solver).
          apply (st_free _ _ _ _ Hs).
        * intros o Ho. apply elem_of_difference in Ho as [Ho Hn].
          destruct (st_pairs _ _ _ _ Hs o Ho) as (S & x & S' & L1 & L2 & D). exists S, x, S'.
          assert (∀ o', ech o' = ech o → o' ≠ o1 ∧ o' ≠ edual o1) as Hn'.
          { intros o' Heq. split; intros ->; apply Hn; rewrite <-Heq, ?ech_edual; set_solver. }
          destruct (Hn' o eq_refl) as (? & ?). destruct (Hn' (edual o) (ech_edual o)) as (? & ?).
          rewrite !lookup_delete_ne by done. done.
      + intros o. destruct (decide (o = o2)) as [->|No].
        * rewrite lookup_insert_eq, S2. constructor. split; [done|]. by eapply sdual_trans_l.
        * rewrite lookup_insert_ne by done. destruct (Σ !! o) as [[S x]|]; constructor. split; [done|apply seqv_refl].
  Qed.
End link.

(** ** The clauses of a single thread *)

Definition PTermL (κ : ctable) (m : nat) : Prop :=
  ∀ W Θ T t Σ ΘB C, prim T → sth Θ Σ ΘB C → t ∈ E[κ]^W _ m⟦Θ ⊢ T⟧^∅ →
    (C, {[+ t +]}) ∈ P[κ]^W _ m⟦Σ ⊢ T⟧.

Lemma istep_single_sess q i σ q' C e : erase q = (C, {[+ e +]}) → istep q (EvSess i σ) q' →
  ∃ e', tstep e (LSess σ) e' ∧ subjs σ ## C ∧ erase q' = (C ∖ sentc σ, {[+ e' +]}).
Proof.
  intros Hq Hst.
  destruct (istep_single _ _ _ _ _ Hq Hst) as [(?&?&Heq&_)|[(?&?&?&?&Heq&_)|[(?&?&?&?&?&Heq&_)|
    [(?&?&?&?&Heq&_)|[(?&?&?&?&Heq&_)|(?&?&?&Heq&?&?&?)]]]]]; try discriminate.
  injection Heq as <- <-. eauto.
Qed.

Lemma gfresh_exists' ℓ (Θ : senv) : ∃ g, gfresh ℓ g Θ.
Proof.
  set (G := list_to_set (omap (λ p : cend * (sty * point),
    match pt_root p.2.2 with NGen ℓ' g => if decide (ℓ' = ℓ) then Some g else None | _ => None end)
    (map_to_list Θ)) : gset nat).
  exists (fresh G). intros o S x Ho Hr. apply (is_fresh G). apply elem_of_list_to_set, list_elem_of_omap.
  exists (o, (S, x)). split; [by apply elem_of_map_to_list|]. simpl. rewrite Hr. by rewrite decide_True.
Qed.

(** A link label read with the removed channel first. *)
Lemma link_norm (Θ : senv) o1 o2 p1 p2 S1 S2 x :
  ({[o1]} ∪ {[o2]}) = ({[p1]} ∪ {[p2]} : gset cend) → p1 ≠ p2 →
  Θ !! p1 = Some (S1, x) → Θ !! p2 = Some (S2, x‾) → sdual S1 S2 →
  ∃ A1 A2 y, o1 ≠ o2 ∧ Θ !! o1 = Some (A1, y) ∧ Θ !! o2 = Some (A2, y‾) ∧ sdual A1 A2 ∧
    delete o1 (delete o2 Θ) = delete p1 (delete p2 Θ).
Proof.
  intros Hos Hne H1 H2 Hd.
  assert (o1 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as E1 by (rewrite <-Hos; set_solver).
  assert (o2 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as E2 by (rewrite <-Hos; set_solver).
  assert (p1 ∈ (({[o1]} ∪ {[o2]}) : gset cend)) as F1 by (rewrite Hos; set_solver).
  assert (p2 ∈ (({[o1]} ∪ {[o2]}) : gset cend)) as F2 by (rewrite Hos; set_solver).
  apply elem_of_union in E1 as [E1|E1], E2 as [E2|E2]; apply elem_of_singleton in E1, E2; subst.
  - exfalso. apply Hne. set_solver.
  - exists S1, S2, x. split_and!; done.
  - exists S2, S1, x‾. rewrite pt_dual_dual. split_and!; [done|done|done|by apply sdual_sym|apply delete_delete].
  - exfalso. apply Hne. set_solver.
Qed.

Section core.
  Context (κ : ctable) (n : nat) (IH : ∀ j, j < S n → PTermL κ j).
  Context (X : erel) (HXr : erel_ren X).
  Context (HX : ∀ W Θ T e Σ ΘB C, prim T → sth Θ Σ ΘB C → X W Θ T ∅ e →
                 Prel κ (S n) W Σ T (C, {[+ e +]})).

  Lemma ac_EP W Θ T e Σ ΘB C c : prim T → sth Θ Σ ΘB C →
    at_cost_E (S n) c (Erel κ) X W Θ T ∅ e →
    at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W Σ T (C, {[+ e +]}).
  Proof.
    intros HT Hs [A1 A2]. split.
    - intros Hc. exact (HX _ _ _ _ _ _ _ HT Hs (A1 Hc)).
    - intros Hc. refine (IH (S n - c) _ W Θ T e Σ ΘB C HT Hs (A2 Hc)). lia.
  Qed.

  Lemma core W Θ T e Σ ΘB C : prim T → sth Θ Σ ΘB C → Erel κ (S n) W Θ T ∅ e →
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) X W Θ T ∅ e →
    (∀ W1, W ⊑ W1 → ∀ v e', tstep e (LSpawn v) e' →
       at_cost_P (S n) (c_spawn κ) (Prel κ) (Prel κ (S n)) W1 Σ T (C, {[+ e' +]} ⊎ {[+ App v EUnit +]})) →
    ∀ W1, W ⊑ W1 → strict W1 →
    Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W1 Σ T (C, {[+ e +]}).
  Proof.
    intros HT Hs HE Hb Hsp W1 HW1 HS1.
    pose proof (Erel_mono κ _ _ _ _ _ _ _ HW1 HE) as HE1.
    destruct (Hb W1 HW1) as (Hstop & Hready & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    (** An offer of a stable thread without a link offer. *)
    assert (∀ a, act e = Some a → stable_t e → ¬ link_t e →
              ∃ o, o ∈ dom Σ ∧ offered_p Σ (C, {[+ e +]}) o ∧ offered_t Θ e o ∧
                   below_rest W1 Θ (offered_t Θ e) ∅) as Hoff.
    { intros a Ha Hst Hl. destruct (act_offer _ _ (alabel a) Ha (offers_alabel a)) as [e' He'].
      assert (¬ irred e) as Hni by (intros Hi; exact (Hi _ _ He')).
      destruct (Hready Hni Hst) as [_ [Hl'|Hbr]]; [done|].
      destruct (Hst _ _ He') as [σ Hσ]. rewrite Hσ in He'.
      assert (∃ o, sends σ = {[o]}) as [o Ho].
      { destruct σ; simpl; eauto. exfalso. apply Hl. by eexists _, _. }
      assert (offered_t Θ e o) as Hot.
      { split; [|exists σ, e'; split; [done|rewrite Ho; by apply elem_of_singleton]].
        pose proof (Erel_sends κ n W1 Θ T ∅ e σ e' HE1 He') as Hsub. apply Hsub. rewrite Ho. by apply elem_of_singleton. }
      pose proof (offered_free W1 HS1 Θ Σ ΘB C Hs e o Hbr Hl Hot) as Hc.
      destruct (offered_sess W1 HS1 Θ Σ ΘB C Hs e o Hot Hl Hc) as [HoΣ Hop]. eauto. }
    (** A pstep of (C, {e}) is a step of e. *)
    assert (∀ π p', pstep (C, {[+ e +]}) π p' → ¬ irred e) as Hps.
    { intros π p' (q & ev & q' & Hq & Hst & _) Hi.
      destruct (istep_single _ _ _ _ _ Hq Hst) as [(?&?&_&Hs'&_)|[(?&?&?&?&_&Hs'&_)|[(?&?&?&?&?&_&Hs'&_)|
        [(?&?&?&?&_&Hs'&_)|[(?&?&?&?&_&Hs'&_)|(?&?&?&_&Hs'&_)]]]]]; by eapply Hi. }
    split; [|split; [|unfold Psteps; split_and!]].
    - (* P-Stop *)
      intros Hpi. destruct (act e) as [a|] eqn:Ha.
      + exfalso. assert (stable_p (C, {[+ e +]})) as Hsp' by (intros p' Hp'; by apply (Hpi PTau p')).
        destruct (single_stable C e Hsp') as [Hst Hlk].
        destruct (decide (link_t e)) as [Hl|Hl].
        * destruct (Hlk Hl) as (os & p' & Hp'). exact (Hpi _ p' Hp').
        * destruct (Hoff a ltac:(first [exact Ha|reflexivity]) Hst Hl) as (o & _ & (_ & σ & p' & Hp' & _) & _). exact (Hpi _ p' Hp').
      + apply irred_act in Ha. pose proof (Hstop Ha) as Hv.
        pose proof (Vrel_prim_empty κ _ _ _ _ _ HT Hv) as HΘ.
        rewrite (st_env _ _ _ _ Hs) in HΘ. apply map_positive_l in HΘ as HΣ.
        rewrite HΣ, (left_id_L ∅ (∪)) in HΘ.
        assert (C = ∅) as HC.
        { apply set_eq. intros c. split; [|intros Hc; by apply elem_of_empty in Hc]. intros Hc.
          assert (EPos c ∈ dom ΘB) as Hd by (by apply (st_dom _ _ _ _ Hs)). by rewrite HΘ, dom_empty_L in Hd. }
        exists e, ∅. split_and!.
        * rewrite HC. f_equal. by rewrite (right_id_L ∅ (⊎)).
        * rewrite HΣ. rewrite (st_env _ _ _ _ Hs), HΣ, HΘ, (left_id_L ∅ (∪)) in Hv. exact Hv.
        * intros e0 He0. clear -He0. multiset_solver.
    - (* P-Ready *)
      intros Hni Hstab. destruct (single_stable C e Hstab) as [Hst Hlk].
      destruct (decide (link_t e)) as [Hl|Hl]; [left; by apply Hlk|right].
      destruct (act e) as [a|] eqn:Ha.
      2: { exfalso. apply Hni. intros π p' Hp'. apply (Hps π p' Hp'). by apply irred_act. }
      destruct (Hoff a ltac:(first [exact Ha|reflexivity]) Hst Hl) as (o & HoΣ & Hop & Hot & Hbr). split.
      + intros Hno. by destruct (Hno o).
      + intros o' S' x' Ho' Hno'. apply elem_of_dom in HoΣ as [[S0 x0] HoS].
        exists o, S0, x0. split_and!; [done|done|].
        apply (proj1 (Hbr o S0 x0 Hot (sth_lookup_S _ _ _ _ _ _ Hs HoS)) o' S' x' (sth_lookup_S _ _ _ _ _ _ Hs Ho')).
        intros Hot'. apply Hno'. by rewrite <-(offered_one _ _ _ _ Hot Hot' Hl).
    - (* Q-Admin and Q-Comm *)
      intros q ev q' Hq Hst Hτ.
      destruct (istep_single _ _ _ _ _ Hq Hst) as [(i & e' & -> & Hs' & ->)|[(i & ℓ & c & e' & -> & Hs' & HcC & Hce & ->)|
        [(i & κf & o & c & e' & -> & Hs' & HcC & Hce & ->)|[(i & j & v & e' & -> & Hs' & ->)|
        [(i & o1 & o2 & e' & -> & Hs' & Hc1 & ->)|(i & σ & e' & -> & _)]]]]]; cbn [fst ev_cost]; intros Hdisj.
      + eapply ac_EP; [done|exact Hs|]. by apply H1.
      + cbn [fst] in Hdisj. assert (c ∉ chans_of Σ) as HcΣ by (clear -Hdisj; set_solver).
        destruct (gfresh_exists' ℓ Θ) as [g Hg].
        destruct (H2 ℓ c e' Hs' (sth_cfresh _ _ _ _ Hs c HcC HcΣ) g Hg) as [S HS].
        eapply ac_EP; [done|by apply sth_new|exact HS].
      + cbn [fst] in Hdisj. assert (c ∉ chans_of Σ) as HcΣ by (clear -Hdisj; set_solver).
        destruct (H3 κf o c e' Hs' (sth_cfresh _ _ _ _ Hs c HcC HcΣ)) as (S0 & x & _ & S & HS).
        eapply ac_EP; [done|by apply sth_new|exact HS].
      + by apply (Hsp W1 HW1 v e').
      + destruct (H10 _ _ Hs') as (p1 & p2 & S1 & S2 & x & Hos & Hne & L1 & L2 & Hd & HA).
        destruct (link_norm Θ o1 o2 p1 p2 S1 S2 x Hos Hne L1 L2 Hd) as (A1 & A2 & y & Hne' & K1 & K2 & Hd' & Edel).
        rewrite <-Edel in HA.
        destruct (lk_res Θ Σ ΘB C Hs o1 o2 A1 A2 y K1 K2 Hd' Hne' Hc1) as [Hk (Σ'' & ΘB'' & Hs'' & Heqv)].
        assert (at_cost_E (S n) (c_link κ) (Erel κ) X W1 (kren (csub o1 o2) (delete o1 (delete o2 Θ))) T ∅
                  (emap (csub o1 o2) e')) as HA'.
        { destruct HA as [A1' A2']. split; intros Hc; [apply HXr; [done|by apply A1']|].
          apply Erel_rename; [done|by apply A2']. }
        destruct (ac_EP _ _ _ _ _ _ _ _ HT Hs'' HA') as [B1 B2]. split.
        * intros Hc. eapply Prel_conv; [exact Heqv|by apply B1].
        * intros Hc. eapply Prel_conv; [exact Heqv|by apply B2].
      + exfalso. unfold ev_tau in Hτ. simpl in Hτ. discriminate.
    - (* Q-Send *)
      intros q i o w q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H5 _ _ _ Hs') as (S0 & x & m & U & b & S & ΘM & Θr & Ho & Hu & Hd & HΘ & HV & HA).
      assert (HM : dom ΘM = fends w).
      { destruct (decide (c_give κ = 0)) as [Hc0|Hc0];
          [exact (Vrel_exact _ _ _ _ _ _ (proj1 HV Hc0))|exact (Vrel_exact _ _ _ _ _ _ (proj2 HV Hc0))]. }
      assert (ech o ∉ C) as Hc by (simpl in Hsub; intros Hc'; apply (Hsub (ech o)); [by apply elem_of_singleton|done]).
      destruct (snd_split Θ Σ ΘB C Hs o ΘM Θr Hd HΘ) as [Hd' HΣ].
      exists S0, x, m, U, b, S, (rout C ΘM), (rout C Θr), (rin C ΘM), (rpart C ΘM Θr). split_and!.
      + exact (snd_Σo Θ Σ ΘB C Hs o S0 x Ho Hc).
      + done.
      + done.
      + done.
      + intros o'. unfold rin. rewrite elem_of_dom_filter, <-HM. simpl. split.
        * intros (v & Hv & Hc'). split; [by eapply elem_of_dom_2|done].
        * intros [Hv Hc']. apply elem_of_dom in Hv as [v Hv]. eauto.
      + by rewrite <-dom_union_L, (snd_ΘM C ΘM).
      + exact (snd_send_split Θ Σ ΘB C Hs o S0 x Ho Hc ΘM Θr Hd HΘ).
      + by rewrite (snd_ΘM C ΘM).
      + simpl. unfold fchans. rewrite <-HM. eapply ac_EP; [done|exact (snd_sth Θ Σ ΘB C Hs o S0 x Ho Hc ΘM Θr Hd HΘ _)|exact HA].
    - (* Q-Recv *)
      intros q i o w q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H6 _ _ _ Hs') as (S0 & x & m & U & b & S & Ho & Hu & HR).
      assert (ech o ∉ C) as Hc by (simpl in Hsub; intros Hc'; apply (Hsub (ech o)); [by apply elem_of_singleton|done]).
      exists S0, x, m, U, b, S. split_and!; [exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc Ho)|done|].
      intros j Θ2 Hj HC2 Hok Hw. simpl in *. pose proof (c_take_pos κ).
      pose proof (sth_upd Θ Σ ΘB C Hs o (S, x⁺) Hc (elem_of_dom_2 _ _ _ Ho)) as Hs1.
      pose proof (rcv_disj _ _ _ _ Hs1 Θ2 HC2 Hok) as Hd1.
      assert (Θ ##ₘ Θ2) as Hd.
      { apply map_disjoint_spec. intros o' v1 v2 V1 V2. destruct (decide (o' = o)) as [->|Ne].
        - apply (proj1 (map_disjoint_spec _ _) Hd1 o (S, x⁺) v2); [by rewrite lookup_insert_eq|done].
        - apply (proj1 (map_disjoint_spec _ _) Hd1 o' v1 v2); [by rewrite lookup_insert_ne|done]. }
      rewrite difference_empty_L.
      refine (IH j _ W1 _ T e' _ _ _ HT (rcv_sth _ _ _ _ Hs1 Θ2 HC2 Hok) _); [lia|]. apply HR; [lia|done|done].
    - (* Q-Close *)
      intros q i o q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H7 _ _ Hs') as (S0 & x & Ho & Hu & HA).
      assert (ech o ∉ C) as Hc by (simpl in Hsub; intros Hc'; apply (Hsub (ech o)); [by apply elem_of_singleton|done]).
      exists S0, x. split_and!; [exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc Ho)|done|].
      simpl. rewrite difference_empty_L. eapply ac_EP; [done|by apply sth_del|exact HA].
    - (* Q-Select *)
      intros q i o bb q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H8 _ _ _ Hs') as (S0 & x & S1 & S2 & Ho & Hu & HA).
      assert (ech o ∉ C) as Hc by (simpl in Hsub; intros Hc'; apply (Hsub (ech o)); [by apply elem_of_singleton|done]).
      exists S0, x, S1, S2. split_and!; [exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc Ho)|done|].
      simpl. rewrite difference_empty_L. eapply ac_EP; [done|apply sth_upd; [done|done|by eapply elem_of_dom_2]|exact HA].
    - (* Q-Branch *)
      intros q i o bb q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H9 _ _ _ Hs') as (S0 & x & S1 & S2 & Ho & Hu & HA).
      assert (ech o ∉ C) as Hc by (simpl in Hsub; intros Hc'; apply (Hsub (ech o)); [by apply elem_of_singleton|done]).
      exists S0, x, S1, S2. split_and!; [exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc Ho)|done|].
      simpl. rewrite difference_empty_L. eapply ac_EP; [done|apply sth_upd; [done|done|by eapply elem_of_dom_2]|exact HA].
    - (* Q-Link *)
      intros q i os q' Hq Hst. destruct (istep_single_sess _ _ _ _ _ _ Hq Hst) as (e' & Hs' & Hsub & ->).
      destruct (H10 _ _ Hs') as (p1 & p2 & S1 & S2 & x & Hos & Hne & L1 & L2 & Hd & HA).
      cbn [subjs] in Hsub. subst os.
      assert (ech p1 ∉ C ∧ ech p2 ∉ C) as [Hc1 Hc2] by (clear -Hsub; set_solver).
      exists p1, p2, S1, S2, x. split_and!; [done|done|exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc1 L1)
        |exact (sth_lookup_nC _ _ _ _ _ _ Hs Hc2 L2)|done|].
      simpl. rewrite difference_empty_L. eapply ac_EP; [done|apply sth_del; [by apply sth_del|done]|exact HA].
  Qed.
End core.

(** ** The induction over the steps of cost 0 *)

Lemma app_thunk_step e1 α e' : tstep (App (Lam e1) EUnit) α e' → α = LBeta ∧ e' = subst1 EUnit e1.
Proof.
  intros Hs. assert (tstep (App (Lam e1) EUnit) LBeta (subst1 EUnit e1)) as Hb by (by apply tstep_head, t_act_app).
  destruct (act_step _ _ _ Hs) as (a & Ha & Hoff). simpl in Ha. injection Ha as <-.
  destruct α; simpl in Hoff; try contradiction. split; [done|]. by eapply tstep_det.
Qed.

Section node.
  Context (κ : ctable) (n : nat) (IH : ∀ j, j < S n → PTermL κ j).

  Definition Φt : erel := λ W Θ T F e, F = ∅ → prim T → ∀ Σ ΘB C, sth Θ Σ ΘB C →
    Prel κ (S n) W Σ T (C, {[+ e +]}).
  Definition Xt : erel := λ W Θ T F e, Erel κ (S n) W Θ T F e ∧ Φren Φt W Θ T F e.

  Lemma Xt_ren : erel_ren Xt.
  Proof.
    intros W Θ T F e h Hk [H1 H2]. split; [by apply Erel_rename|].
    intros g Hg. rewrite kren_kren by done. rewrite emap_emap. apply H2. by apply kinj_kren.
  Qed.

  Lemma Xt_P W Θ T e Σ ΘB C : prim T → sth Θ Σ ΘB C → Xt W Θ T ∅ e → Prel κ (S n) W Σ T (C, {[+ e +]}).
  Proof.
    intros HT Hs [_ H]. pose proof (H id (kinj_id Θ)) as H'. rewrite kren_id_map, emap_id in H'. exact (H' eq_refl HT Σ ΘB C Hs).
  Qed.

  Lemma Xt_E W Θ T F e : Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) Xt W Θ T F e → Erel κ (S n) W Θ T F e.
  Proof. intros Hb. apply Erel_S_iff. revert Hb. apply Ebody_mapX. by intros ? ? ? ? ? [? _]. Qed.

  (** The fusions of a single thread, given its spawns. *)
  Lemma node_gen W Θ T e :
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) Xt W Θ T ∅ e →
    (∀ h Σ ΘB C, kinj h Θ → prim T → sth (kren h Θ) Σ ΘB C → ∀ W1, W ⊑ W1 → ∀ v e', tstep (emap h e) (LSpawn v) e' →
       at_cost_P (S n) (c_spawn κ) (Prel κ) (Prel κ (S n)) W1 Σ T (C, {[+ e' +]} ⊎ {[+ App v EUnit +]})) →
    Φt W Θ T ∅ e.
  Proof.
    intros Hb Hsp _ HT Σ ΘB C Hs. apply Prel_S_iff. intros W1 HW1 HS1 h D Hf. rewrite pfuse_single.
    pose proof (Xt_E _ _ _ _ _ Hb) as HE. pose proof (fs_kinj Θ Σ ΘB C e Hs h D Hf) as Hk.
    pose proof (sth_fuse Θ Σ ΘB C e Hs h D Hf) as Hs'.
    refine (core κ n IH Xt Xt_ren Xt_P W (kren h Θ) T (emap h e) _ _ _ HT Hs' _ _ _ W1 HW1 HS1).
    - by apply Erel_rename.
    - by apply Ebody_rename; [apply Xt_ren| | |].
    - intros W2 HW2. exact (Hsp h _ _ _ Hk HT Hs' W2 HW2).
  Qed.

  (** A thread whose redex is a β-redex spawns nothing. *)
  Lemma node_beta W Θ T e : act e = Some ABeta →
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) Xt W Θ T ∅ e → Φt W Θ T ∅ e.
  Proof.
    intros Ha Hb. apply node_gen; [done|]. intros h Σ ΘB C _ _ _ W1 _ v e' Hs. exfalso.
    destruct (act_step _ _ _ Hs) as (a & Ha' & Hoff). rewrite act_emap, Ha in Ha'. simpl in Ha'.
    injection Ha' as <-. done.
  Qed.

  (** The spawned thread. *)
  Lemma child W ΘM v ΣM ΘBM CM :
    Vthunk κ (S n) (Vrel κ) (Erel κ) (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit) (λ W' Θ' F' e0, Xt W' Θ' TUnit F' e0) W ΘM v →
    sth ΘM ΣM ΘBM CM → ∀ m, m ≤ S n → Prel κ m W ΣM TUnit (CM, {[+ App v EUnit +]}).
  Proof.
    intros (e1 & -> & _ & Hv) Hs m Hm.
    assert (tstep (App (Lam e1) EUnit) LBeta (subst1 EUnit e1)) as Hβ by (by apply tstep_head, t_act_app).
    assert (∀ j W', j + c_beta κ ≤ S n → j < S n → W ⊑ W' → Erel κ j W' ΘM TUnit ∅ (subst1 EUnit e1)) as Hlow.
    { intros j W' Hj Hj' HW. destruct (Hv W' j ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [B _].
      rewrite map_union_empty in B. apply B; [done|]. by apply Vrel_unit_iff. }
    assert (∀ j W', j ≤ S n → j - c_beta κ < S n → W ⊑ W' → Erel κ (j - c_beta κ) W' ΘM TUnit ∅ (subst1 EUnit e1)) as Hlow'.
    { intros j W' Hj Hj' HW. destruct (decide (c_beta κ ≤ j)); [apply Hlow; [lia|lia|done]|].
      replace (j - c_beta κ) with 0 by lia. apply Erel_0. }
    assert (∀ W', W ⊑ W' → ¬ irred (App (Lam e1) EUnit) ∧ ready _ W'(ΘM ∣ ∅, App (Lam e1) EUnit)) as Hrd.
    { intros W' _. split; [intros Hi; exact (Hi _ _ Hβ)|]. intros Hst. destruct (Hst _ _ Hβ) as [σ Hσ]. discriminate. }
    destruct (decide (m = S n)) as [->|Hmn].
    - refine (node_beta W ΘM TUnit (App (Lam e1) EUnit) eq_refl _ eq_refl prim_unit ΣM ΘBM CM Hs).
      intros W' HW'. destruct (Hrd W' HW') as [Hni Hr].
      split; [intros Hi; by destruct Hni|split; [by intros _|unfold Esteps; split_and!]].
      all: intros; match goal with H : tstep _ _ _ |- _ => apply app_thunk_step in H as [Hα ->] end; try discriminate.
      split.
      + intros Hc. destruct (Hv W' (S n) ∅ EUnit HW' ltac:(lia) (map_disjoint_empty_r _)) as [_ B].
        rewrite map_union_empty in B. by apply B.
      + intros Hc. apply Hlow'; [lia|lia|done].
    - refine (IH m ltac:(lia) W ΘM TUnit _ ΣM ΘBM CM prim_unit Hs _).
      destruct m as [|m]; [apply Erel_0|]. apply Erel_S_iff. intros W' HW'.
      destruct (Hrd W' HW') as [Hni Hr].
      split; [intros Hi; by destruct Hni|split; [by intros _|unfold Esteps; split_and!]].
      all: intros; match goal with H : tstep _ _ _ |- _ => apply app_thunk_step in H as [Hα ->] end; try discriminate.
      split.
      + intros Hc. apply Hlow; [lia|lia|done].
      + intros Hc. apply Hlow'; [lia|lia|done].
  Qed.

  (** A spawn: the parent and the child compose over the cut of the
      channels with one end on each side (P-Connect). *)
  Lemma spawn_case W Θ T e Σ ΘB C : prim T → sth Θ Σ ΘB C →
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) Xt W Θ T ∅ e →
    ∀ W1, W ⊑ W1 → ∀ v e', tstep e (LSpawn v) e' →
      at_cost_P (S n) (c_spawn κ) (Prel κ) (Prel κ (S n)) W1 Σ T (C, {[+ e' +]} ⊎ {[+ App v EUnit +]}).
  Proof.
    intros HT Hs Hb W1 HW1 v e' Hst.
    destruct (Hb W1 HW1) as (_ & _ & _ & _ & _ & H4 & _).
    destruct (H4 _ _ Hst) as (ΘM & Θr & Hd & HΘ & Hth & HA).
    destruct (spawn_split Θ Σ ΘB C ΘM Θr Hs Hd HΘ) as (Hr & HM & Hc & HΣ & HC).
    pose proof (ac_EP κ n IH Xt Xt_P W1 Θr T e' _ _ _ _ HT Hr HA) as [P1 P2].
    assert (∀ m, m ≤ S n → Prel κ m W1 (s_if C Θr ∪ s_cut C Θr) T (s_ch C Θr, {[+ e' +]}) →
              Prel κ m W1 Σ T (C, {[+ e' +]} ⊎ {[+ App v EUnit +]})) as Hcomp.
    { intros m Hm H1. pose proof (child W1 ΘM v _ _ _ Hth HM m Hm) as H2.
      pose proof (conn_all κ T HT m W1 _ _ _ _ _ _ H1 H2 Hc) as H. unfold pconn in H. simpl in H.
      assert (((C, {[+ e' +]} ⊎ {[+ App v EUnit +]}) : proc) =
              (s_ch C Θr ∪ s_ch C ΘM ∪ chans_of (s_cut C Θr), {[+ e' +]} ⊎ {[+ App v EUnit +]})) as Ep
        by (by rewrite <-HC).
      rewrite Ep, HΣ. exact H. }
    split.
    - intros Hc0. apply Hcomp; [lia|]. by apply P1.
    - intros Hc0. apply Hcomp; [lia|]. by apply P2.
  Qed.

  Lemma node W Θ T e : Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) Xt W Θ T ∅ e → Φt W Θ T ∅ e.
  Proof.
    intros Hb. apply node_gen; [done|]. intros h Σ ΘB C Hk HT Hs W1 HW1 v e' Hst.
    pose proof (Xt_E _ _ _ _ _ Hb) as HE.
    refine (spawn_case W (kren h Θ) T (emap h e) Σ ΘB C HT Hs _ W1 HW1 v e' Hst). by apply Ebody_rename; [apply Xt_ren| | |].
  Qed.
End node.

(** ** P-Term *)

Lemma pterm_level κ n : (∀ j, j < S n → PTermL κ j) → PTermL κ (S n).
Proof.
  intros IH W Θ T t Σ ΘB C HT Hs Ht.
  assert (∀ W Θ T F e, Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n))
            (λ W Θ T F e, Erel κ (S n) W Θ T F e ∧ Φren (Φt κ n) W Θ T F e) W Θ T F e →
            Φt κ n W Θ T F e) as Hnode.
  { intros W' Θ' T' F e Hb ->. by apply (node κ n IH). }
  pose proof (Erel_S_ind_ren κ n (Φt κ n) Hnode W Θ T ∅ t Ht id (kinj_id Θ)) as H.
  rewrite kren_id_map, emap_id in H. exact (H eq_refl HT Σ ΘB C Hs).
Qed.

Theorem pterm_all κ m : PTermL κ m.
Proof.
  induction (lt_wf m) as [m _ IH]. destruct m as [|n].
  - intros ? ? ? ? ? ? ? _ _ _. apply Prel_0.
  - apply pterm_level. intros j Hj. by apply IH.
Qed.

(** P-Term: a single thread in E at the empty future, over Σ partner-free
    and the dual pairs Θ_B of its restricted channels, is in P. *)
Theorem sem_p_term κ n W Θ Σ ΘB C t T :
  prim T → sth Θ Σ ΘB C → t ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^∅ → (C, {[+ t +]}) ∈ P[κ]^W _ n⟦Σ ⊢ T⟧.
Proof. intros HT Hs Ht. exact (pterm_all κ n W Θ T t Σ ΘB C HT Hs Ht). Qed.
