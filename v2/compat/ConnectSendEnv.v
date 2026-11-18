(** * P-Connect, environments of an external send of the composite (stage S4)

    p1 sends on its interface end o. It moves the ends Σv1 of its
    environment and Θe1 of its restricted channels, and the partners Σe1
    of those of Θe1 whose partner stays join its interface. In the
    composite the moved cut ends are restricted, so they move with Θe,
    and their partners in p2 join the interface of the composite. The
    environments read here are those of the composite's Q-Send, and the
    cut after the send is re-split by the composite's new interface
    ([conn_filter]). *)

From GV Require Export compat.ConnectMsg.

Section send_env.
  #[local] Set Default Proof Using "All".
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).
  Context (o : cend) (Do : o ∈ dom Σ1).
  Context (Σv1 Σr1 Θe1 Σe1 : senv) (Dvr : Σv1 ##ₘ Σr1) (Edel : delete o (Σ1 ∪ ΣC) = Σv1 ∪ Σr1).
  Context (HΘe : ∀ o', o' ∈ dom Θe1 → ech o' ∈ C1) (Hss : send_split (Σ1 ∪ ΣC) Σe1 Θe1).
  Context (vo : sty * point).

  Local Abbreviation Σ := (Σ1 ∪ Σ2).
  Local Abbreviation Σv := (fin Σ Σv1).
  Local Abbreviation Θe := (fout Σ Σv1 ∪ Θe1).
  Local Abbreviation Σr := (fin Σ Σr1 ∪ Σ2).
  Local Abbreviation ΣDm := (filter (λ kv : cend * (sty * point), edual kv.1 ∈ dom Σv1) ΣD).
  Local Abbreviation Σe := (Σe1 ∪ ΣDm).
  Local Abbreviation E1 := (<[o := vo]> (Σr1 ∪ Σe1)).
  Local Abbreviation E2 := (Σ2 ∪ ΣD).
  Local Abbreviation Σ' := (<[o := vo]> (Σr ∪ Σe)).

  Local Lemma Co : o ∉ dom ΣC ∧ o ∉ dom Σ2 ∧ o ∉ dom ΣD ∧ ech o ∉ C1 ∧ ech o ∉ C2 ∧
    edual o ∉ dom Σ1 ∧ edual o ∉ dom ΣC ∧ edual o ∉ dom Σ2 ∧ edual o ∉ dom ΣD.
  Proof. apply (cls_1 _ _ _ _ _ _ Hc o Do). Qed.

  Local Lemma Lvr o' v : (Σv1 ∪ Σr1) !! o' = Some v ↔ (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. rewrite <-Edel, lookup_delete_Some. naive_solver. Qed.

  Local Lemma Lv o' v : Σv1 !! o' = Some v → (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. intros H. apply Lvr. by apply lookup_union_Some_l. Qed.

  Local Lemma Lr o' v : Σr1 !! o' = Some v → (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. intros H. apply Lvr. by apply lookup_union_Some_r. Qed.

  Local Lemma Dv o' : o' ∈ dom Σv1 → (o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ o' ≠ o.
  Proof.
    intros [v Hv]%elem_of_dom. destruct (Lv _ _ Hv) as [H Hne]. split; [|done].
    destruct (lookup_1C _ _ _ _ H) as [[_ ?]|[_ ?]]; auto.
  Qed.

  Local Lemma Dr o' : o' ∈ dom Σr1 → (o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ o' ≠ o.
  Proof.
    intros [v Hv]%elem_of_dom. destruct (Lr _ _ Hv) as [H Hne]. split; [|done].
    destruct (lookup_1C _ _ _ _ H) as [[_ ?]|[_ ?]]; auto.
  Qed.

  Local Lemma Dvr' o' : o' ∈ dom Σv1 → o' ∉ dom Σr1.
  Proof. intros H1 H2. apply map_disjoint_dom in Dvr. by apply (Dvr o'). Qed.

  Local Lemma Dcov o' : o' ∈ dom Σ1 ∨ o' ∈ dom ΣC → o' ≠ o → o' ∈ dom Σv1 ∨ o' ∈ dom Σr1.
  Proof.
    intros H Hne. rewrite <-elem_of_union, <-dom_union_L, <-Edel, dom_delete_L, dom_union_L.
    clear -H Hne. set_solver.
  Qed.

  Local Lemma De o' : o' ∈ dom Σe1 → ech o' ∈ C1 ∧ edual o' ∈ dom Θe1 ∧ o' ∉ dom Θe1.
  Proof.
    intros H. destruct Hss as (_ & Hs2 & _). apply Hs2 in H as [A B]. split; [|done].
    rewrite <-ech_edual. by apply HΘe.
  Qed.

  Local Lemma LDm o' v : ΣDm !! o' = Some v ↔ ΣD !! o' = Some v ∧ edual o' ∈ dom Σv1.
  Proof. by rewrite map_lookup_filter_Some. Qed.

  Local Lemma DDm o' : o' ∈ dom ΣDm ↔ o' ∈ dom ΣD ∧ edual o' ∈ dom Σv1.
  Proof.
    split.
    - intros [v Hv]%elem_of_dom. apply LDm in Hv as [A B]. split; [by eapply elem_of_dom_2|done].
    - intros [[v Hv]%elem_of_dom B]. apply elem_of_dom. exists v. by apply LDm.
  Qed.

  (** The classes of the ends that a send touches. *)
  Local Lemma Kv o' : o' ∈ dom Σv1 → o' ∉ dom Σ → o' ∈ dom ΣC.
  Proof. intros H HΣ. destruct (Dv _ H) as [[D|D] _]; [|done]. rewrite dom_union_L in HΣ. set_solver. Qed.

  Local Lemma Kv' o' : o' ∈ dom Σv1 → o' ∈ dom Σ → o' ∈ dom Σ1.
  Proof.
    intros H HΣ. destruct (Dv _ H) as [[D|D] _]; [done|]. exfalso. rewrite dom_union_L, elem_of_union in HΣ.
    destruct HΣ; contra_with (cls_C _ _ _ _ _ _ Hc o' D).
  Qed.

  Local Lemma Kr' o' : o' ∈ dom Σr1 → o' ∈ dom Σ → o' ∈ dom Σ1.
  Proof.
    intros H HΣ. destruct (Dr _ H) as [[D|D] _]; [done|]. exfalso. rewrite dom_union_L, elem_of_union in HΣ.
    destruct HΣ; contra_with (cls_C _ _ _ _ _ _ Hc o' D).
  Qed.

  Local Lemma Kr o' : o' ∈ dom Σr1 → o' ∉ dom Σ → o' ∈ dom ΣC.
  Proof. intros H HΣ. destruct (Dr _ H) as [[D|D] _]; [|done]. rewrite dom_union_L in HΣ. set_solver. Qed.

  (** ** The environments of the composite's Q-Send *)

  Lemma snd_vr : Σv ##ₘ Σr.
  Proof.
    apply map_disjoint_dom. intros o' H1 H2. apply fin_dom in H1 as [A HA].
    rewrite dom_union_L, elem_of_union in H2. destruct H2 as [H2|H2].
    - apply fin_dom in H2 as [B _]. by apply (Dvr' o').
    - destruct (Dv _ A) as [[D|D] _]; [contra_with (cls_1 _ _ _ _ _ _ Hc o' D)|contra_with (cls_C _ _ _ _ _ _ Hc o' D)].
  Qed.

  Local Lemma fin_1C : fin Σ (Σ1 ∪ ΣC) = Σ1.
  Proof.
    destruct Hc as [Hd1 _ _ _ _ _ _ _ _ _ _ _]. unfold fin. rewrite map_filter_union by done.
    rewrite (map_filter_id _ Σ1); [|intros i x Hi; simpl; rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2].
    match goal with |- _ ∪ ?F = _ => assert (F = ∅) as -> end; [|by rewrite (right_id_L ∅ (∪))].
    apply map_empty. intros i. apply map_lookup_filter_None. right.
    intros x Hi. simpl. assert (i ∈ dom ΣC) as D by (by eapply elem_of_dom_2).
    rewrite dom_union_L, elem_of_union. pose proof (cls_C _ _ _ _ _ _ Hc i D). tauto.
  Qed.

  Lemma snd_del : delete o Σ = Σv ∪ Σr.
  Proof.
    rewrite delete_union, (delete_id Σ2 o) by (apply not_elem_of_dom; apply Co).
    rewrite (assoc_L (∪)). f_equal. unfold fin. rewrite <-map_filter_union by done.
    rewrite <-Edel, map_filter_delete. fold (fin Σ (Σ1 ∪ ΣC)). by rewrite fin_1C.
  Qed.

  Lemma snd_payload : Σv ∪ Θe = Σv1 ∪ Θe1.
  Proof. by rewrite (assoc_L (∪)), fin_fout. Qed.

  Local Lemma DΘe o' : o' ∈ dom Θe ↔ (o' ∈ dom Σv1 ∧ o' ∈ dom ΣC) ∨ o' ∈ dom Θe1.
  Proof.
    rewrite dom_union_L, elem_of_union, fout_dom. split.
    - intros [[A B]|A]; [left; split; [done|by apply Kv]|by right].
    - intros [[A B]|A]; [left|by right]. split; [done|]. pose proof (cls_C _ _ _ _ _ _ Hc o' B).
      rewrite dom_union_L, elem_of_union. tauto.
  Qed.

  Lemma snd_moved (M : gset cend) :
    (∀ o', o' ∈ dom Θe1 ↔ o' ∈ M ∧ ech o' ∈ C1) → M = dom Σv1 ∪ dom Θe1 →
    (∀ o', o' ∈ dom Θe ↔ o' ∈ M ∧ ech o' ∈ C1 ∪ C2 ∪ chans_of ΣC) ∧ M = dom Σv ∪ dom Θe.
  Proof.
    intros HM1 HM. split; [|by rewrite <-dom_union_L, snd_payload, dom_union_L].
    intros o'. rewrite DΘe. split.
    - intros [[A B]|A].
      + split; [rewrite HM; clear -A; set_solver|]. apply elem_of_union_r. by apply elem_of_chans_of.
      + apply HM1 in A as [A B]. split; [done|clear -B; set_solver].
    - intros [A B]. rewrite HM, elem_of_union in A. destruct A as [A|A]; [|by right].
      left. split; [done|]. destruct (Dv _ A) as [[D|D] _]; [|done]. exfalso.
      pose proof (cls_1 _ _ _ _ _ _ Hc o' D) as P. destruct Hc as [_ _ _ _ _ _ _ H1C _ _ HC1 HC2].
      pose proof (elem_of_chans_of _ _ D) as Hch. rewrite !elem_of_union in B.
      destruct B as [[B|B]|B]; [tauto|tauto|clear -B Hch H1C; set_solver].
  Qed.

  Lemma snd_split : send_split Σ Σe Θe.
  Proof.
    destruct Hss as (Hs1 & Hs2 & Hs3). split_and!.
    - intros o' H. rewrite dom_union_L, !not_elem_of_union. apply DΘe in H as [[A B]|A].
      + pose proof (cls_C _ _ _ _ _ _ Hc o' B). tauto.
      + pose proof (cls_c1 _ _ _ _ _ _ Hc o' (HΘe _ A)) as P1.
        pose proof (cls_c1 _ _ _ _ _ _ Hc (edual o') ltac:(rewrite ech_edual; by apply HΘe)) as P2. tauto.
    - intros o'. rewrite dom_union_L, elem_of_union, DDm, !DΘe. split.
      + intros [H|[A B]].
        * destruct (De _ H) as (Hc1 & B & B'). split; [by right|].
          intros [[_ D]|D]; [contra_with (cls_c1 _ _ _ _ _ _ Hc o' Hc1)|done].
        * pose proof (cls_D _ _ _ _ _ _ o' Hc A) as P. split; [left; tauto|].
          intros [[D _]|D].
          { destruct (Dv _ D) as [[?|?] _]; tauto. }
          { pose proof (cls_c1 _ _ _ _ _ _ Hc o' (HΘe _ D)). tauto. }
      + intros [[[A B]|A] N].
        * right. split; [|done]. destruct Hc as [_ _ [Hcd _] _ _ _ _ _ _ _ _ _]. by apply Hcd.
        * left. apply Hs2. split; [done|]. intros D. apply N. by right.
    - intros o' S y H. apply lookup_union_Some_raw in H as [H|[N H]].
      + apply fout_lookup in H as [H HΣ]. destruct (Lv _ _ H) as [L _].
        assert (o' ∈ dom ΣC) as D by (apply Kv; [by eapply elem_of_dom_2|done]).
        apply lookup_union_Some_raw in L as [L|[_ L]]; [exfalso; contra_with (cls_C _ _ _ _ _ _ Hc o' D)|].
        destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ L) as (S' & L' & Hs).
        exists S'. split; [|done]. apply lookup_union_Some_l. apply lookup_union_Some_raw. right. split.
        * apply not_elem_of_dom. intros D'. destruct (De _ D') as (Hc1 & _). rewrite ech_edual in Hc1.
          contra_with (cls_C _ _ _ _ _ _ Hc o' D).
        * apply LDm. rewrite edual_edual. split; [done|by eapply elem_of_dom_2].
      + destruct (Hs3 _ _ _ H) as (S' & L & Hs). exists S'. split; [|done].
        assert (ech (edual o') ∈ C1) as Hc1 by (rewrite ech_edual; apply HΘe; by eapply elem_of_dom_2).
        pose proof (cls_c1 _ _ _ _ _ _ Hc _ Hc1) as P.
        assert (ΣDm !! edual o' = None) as N1 by (apply not_elem_of_dom; rewrite DDm; tauto).
        assert (fout Σ Σv1 !! edual o' = None) as N2.
        { apply not_elem_of_dom. rewrite fout_dom. intros [D _]. destruct (Dv _ D) as [[?|?] _]; tauto. }
        rewrite !lookup_union in L |- *. rewrite ?N1, ?N2. revert L; rewrite ?lookup_union; rewrite ?N1, ?N2; destruct (Σe1 !! edual o'), (Θe1 !! edual o'); done.
  Qed.

  (** ** The cut after the send *)

  Local Lemma DE1 o' : o' ∈ dom E1 ↔ o' = o ∨ o' ∈ dom Σr1 ∨ o' ∈ dom Σe1.
  Proof. rewrite dom_insert_L, dom_union_L. set_solver. Qed.

  Local Lemma DΣ' o' : o' ∈ dom Σ' ↔
    o' = o ∨ (o' ∈ dom Σr1 ∧ o' ∈ dom Σ1) ∨ o' ∈ dom Σ2 ∨ o' ∈ dom Σe1 ∨ (o' ∈ dom ΣD ∧ edual o' ∈ dom Σv1).
  Proof.
    rewrite dom_insert_L, !dom_union_L, !elem_of_union, elem_of_singleton, fin_dom, DDm.
    assert (o' ∈ dom Σr1 → o' ∈ dom Σ → o' ∈ dom Σ1) by apply Kr'.
    assert (o' ∈ dom Σ1 → o' ∈ dom Σ) by (rewrite dom_union_L; set_solver).
    tauto.
  Qed.

  Local Lemma DE2 o' : o' ∈ dom E2 ↔ o' ∈ dom Σ2 ∨ o' ∈ dom ΣD.
  Proof. rewrite dom_union_L. set_solver. Qed.

  Local Lemma snd_disj : dom E1 ## dom E2.
  Proof.
    intros o' H1 H2. apply DE1 in H1. apply DE2 in H2. pose proof Co.
    destruct H1 as [->|[H1|H1]]; [tauto|..].
    - destruct (Dr _ H1) as [[D|D] _]; [pose proof (cls_1 _ _ _ _ _ _ Hc o' D)|pose proof (cls_C _ _ _ _ _ _ Hc o' D)]; tauto.
    - destruct (De _ H1) as (Hc1 & _). pose proof (cls_c1 _ _ _ _ _ _ Hc o' Hc1). tauto.
  Qed.

  Local Lemma snd_pfree1 : pfree E1.
  Proof.
    intros o' H1 H2. apply DE1 in H1, H2. pose proof Co as Co'.
    destruct H1 as [->|[H1|H1]].
    - destruct H2 as [E|[H2|H2]]; [by apply (edual_ne o)|..].
      + destruct (Dr _ H2) as [[?|?] _]; tauto.
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1. tauto.
    - destruct (Dr _ H1) as [D1 Hne].
      destruct H2 as [E|[H2|H2]].
      + subst o. rewrite edual_edual in Co'. destruct D1; tauto.
      + destruct (Dr _ H2) as [D2 _]. apply (pfree_1C _ _ _ _ _ _ Hc o'); rewrite dom_union_L; clear -D1 D2; set_solver.
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1.
        destruct D1 as [D|D]; [contra_with (cls_1 _ _ _ _ _ _ Hc o' D)|contra_with (cls_C _ _ _ _ _ _ Hc o' D)].
    - destruct (De _ H1) as (Hc1 & A & B). destruct H2 as [E|[H2|H2]].
      + subst o. rewrite ech_edual in Co'. tauto.
      + destruct (Dr _ H2) as [D _]. rewrite <-(ech_edual o') in Hc1.
        destruct D as [D|D]; [contra_with (cls_1 _ _ _ _ _ _ Hc _ D)|contra_with (cls_C _ _ _ _ _ _ Hc _ D)].
      + destruct (De _ H2) as (_ & A' & _). rewrite edual_edual in A'. done.
  Qed.

  Local Lemma snd_pfreeΣ' : pfree Σ'.
  Proof.
    intros o' H1 H2. apply DΣ' in H1, H2. pose proof Co as Co'.
    assert (pfree Σ) as Hf by (destruct Hc; by apply pfree_union).
    assert (∀ a, a ∈ dom Σ1 ∨ a ∈ dom Σ2 → a ∈ dom Σ) as HΣ by (intros a Ha; rewrite dom_union_L; set_solver).
    destruct H1 as [->|[[_ H1]|[H1|[H1|[H1 B1]]]]].
    - destruct H2 as [E|[[_ H2]|[H2|[H2|[H2 B2]]]]]; [by apply (edual_ne o)|tauto|tauto|..].
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1. tauto.
      + tauto.
    - destruct H2 as [E|[[_ H2]|[H2|[H2|[H2 B2]]]]].
      + subst o. rewrite edual_edual in Co'. tauto.
      + by apply (Hf o'); apply HΣ; left.
      + by apply (Hf o'); apply HΣ; [left|right].
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1. contra_with (cls_1 _ _ _ _ _ _ Hc o' H1).
      + contra_with (cls_1 _ _ _ _ _ _ Hc o' H1).
    - destruct H2 as [E|[[_ H2]|[H2|[H2|[H2 B2]]]]].
      + subst o. rewrite edual_edual in Co'. tauto.
      + by apply (Hf o'); apply HΣ; [right|left].
      + by apply (Hf o'); apply HΣ; right.
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1. contra_with (cls_2 _ _ _ _ _ _ o' Hc H1).
      + contra_with (cls_2 _ _ _ _ _ _ o' Hc H1).
    - destruct (De _ H1) as (Hc1 & A & B). pose proof (cls_c1 _ _ _ _ _ _ Hc o' Hc1) as P.
      pose proof (cls_c1 _ _ _ _ _ _ Hc (edual o') ltac:(by rewrite ech_edual)) as P'.
      destruct H2 as [E|[[_ H2]|[H2|[H2|[H2 B2]]]]]; [subst o; tauto|tauto|tauto| |tauto].
      destruct (De _ H2) as (_ & A' & _). rewrite edual_edual in A'. done.
    - pose proof (cls_D _ _ _ _ _ _ o' Hc H1) as P.
      destruct H2 as [E|[[_ H2]|[H2|[H2|[H2 B2]]]]]; [subst o; tauto|tauto|tauto| |].
      + destruct (De _ H2) as (Hc1 & _). rewrite ech_edual in Hc1. tauto.
      + rewrite edual_edual in B2. destruct (Dv _ B2) as [[?|?] _]; tauto.
  Qed.

  Local Lemma snd_out1 o' : o' ∈ dom E1 → o' ∉ dom Σ' → edual o' ∈ dom E2 ∧ edual o' ∉ dom Σ'.
  Proof.
    intros H1 HΣ. rewrite DΣ' in HΣ. rewrite DE2, DΣ', edual_edual.
    apply DE1 in H1 as [->|[H1|H1]]; [tauto| |tauto].
    destruct (Dr _ H1) as [[D|D] Hne]; [tauto|]. pose proof (cls_C _ _ _ _ _ _ Hc o' D) as P.
    split; [tauto|]. pose proof (Dvr' o') as Nr. intros [E|[[? ?]|[?|[He|[? ?]]]]];
      [rewrite <-E in Do; tauto|tauto|tauto|destruct (De _ He) as (Hc1 & _); rewrite ech_edual in Hc1; tauto|tauto].
  Qed.

  Local Lemma snd_out2 o' : o' ∈ dom E2 → o' ∉ dom Σ' → edual o' ∈ dom E1 ∧ edual o' ∉ dom Σ'.
  Proof.
    intros H2 HΣ. rewrite DΣ' in HΣ. rewrite DE1, DΣ'.
    apply DE2 in H2 as [H2|H2]; [tauto|]. pose proof (cls_D _ _ _ _ _ _ o' Hc H2) as P.
    assert (edual o' ∉ dom Σv1) as Nv by tauto.
    assert (edual o' ∈ dom Σr1) as R.
    { destruct (Dcov (edual o')) as [?|?]; [tauto| |done|done]. intros E. rewrite <-E in Do. tauto. }
    split; [tauto|]. intros [E|[[? ?]|[?|[He|[? ?]]]]];
      [rewrite <-E in Do; tauto|tauto|tauto|destruct (De _ He) as (Hc1 & _); rewrite ech_edual in Hc1; tauto|tauto].
  Qed.

  Local Lemma snd_types o' S1 y1 : E1 !! o' = Some (S1, y1) → o' ∉ dom Σ' →
    ∃ S2, E2 !! edual o' = Some (S2, y1‾) ∧ sdual S1 S2.
  Proof.
    intros H1 HΣ. assert (o' ∈ dom E1) as D1 by (by eapply elem_of_dom_2).
    rewrite DΣ' in HΣ. apply lookup_insert_Some in H1 as [[<- _]|[Hne H1]]; [tauto|].
    apply lookup_union_Some_raw in H1 as [H1|[_ H1]].
    - destruct (Lr _ _ H1) as [L _]. assert (o' ∈ dom Σr1) as R by (by eapply elem_of_dom_2).
      destruct (Dr _ R) as [[D|D] _]; [tauto|].
      apply lookup_union_Some_raw in L as [L|[_ L]]; [exfalso; contra_with (cls_C _ _ _ _ _ _ Hc o' D)|].
      destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ L) as (S' & L' & Hs).
      exists S'. split; [|done]. by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD C1 C2).
    - exfalso. apply HΣ. right. right. right. left. by eapply elem_of_dom_2.
  Qed.

  Local Lemma chans_E1 c : c ∈ chans_of E1 → c ∈ chans_of Σ1 ∪ chans_of ΣC ∨ c ∈ (set_map ech (dom Θe1) : gset chan).
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply DE1 in H as [->|[H|H]].
    - left. apply elem_of_union_l, elem_of_chans_of, Do.
    - left. destruct (Dr _ H) as [[D|D] _]; [apply elem_of_union_l|apply elem_of_union_r]; by apply elem_of_chans_of.
    - right. destruct (De _ H) as (_ & D & _). rewrite <-ech_edual. by apply elem_of_map_2.
  Qed.

  Local Lemma chans_E2 c : c ∈ chans_of E2 → c ∈ chans_of Σ2 ∪ chans_of ΣC.
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply DE2 in H as [H|H].
    - apply elem_of_union_l. by apply elem_of_chans_of.
    - apply elem_of_union_r. destruct (cls_D _ _ _ _ _ _ o' Hc H) as (_ & _ & _ & _ & _ & _ & _ & _ & Dc).
      rewrite <-ech_edual. by apply elem_of_chans_of.
  Qed.

  Local Abbreviation C1' := (C1 ∖ set_map ech (dom Σv1 ∪ dom Θe1)).

  Lemma snd_conn : conn (fin Σ' E1) (fout Σ' E1) C1' (fin Σ' E2) (fout Σ' E2) C2.
  Proof.
    pose proof Hc as Hc0. destruct Hc0 as [_ _ _ _ _ _ _ _ _ HCC HC1 HC2].
    apply conn_filter.
    - apply snd_disj.
    - apply snd_pfree1.
    - apply (pfree_1C Σ2 ΣD Σ1 ΣC C2 C1). by apply conn_sym.
    - apply snd_pfreeΣ'.
    - apply snd_out1.
    - apply snd_out2.
    - apply snd_types.
    - clear -HCC. set_solver.
    - intros c Hc1 Hc2. apply elem_of_difference in Hc1 as [Hc1 Hn].
      apply elem_of_union in Hc2 as [H|H].
      + destruct (chans_E1 c H) as [H'|H'].
        * clear -HC1 Hc1 H'. set_solver.
        * apply Hn. rewrite set_map_union_L. clear -H'. set_solver.
      + apply chans_E2 in H. clear -HC1 Hc1 H. set_solver.
    - intros c Hc2 Hcc. apply elem_of_union in Hcc as [H|H].
      + destruct (chans_E1 c H) as [H'|H'].
        * clear -HC2 Hc2 H'. set_solver.
        * apply elem_of_map in H' as (o' & -> & H'). pose proof (HΘe _ H'). clear -HCC Hc2 H0. set_solver.
      + apply chans_E2 in H. clear -HC2 Hc2 H. set_solver.
  Qed.

  Local Lemma snd_cover o' v : Σ' !! o' = Some v → E1 !! o' = Some v ∨ E2 !! o' = Some v.
  Proof.
    intros H. apply lookup_insert_Some in H as [[<- <-]|[Hne H]]; [left; by rewrite lookup_insert_eq|].
    rewrite lookup_insert_ne by done.
    apply lookup_union_Some_raw in H as [H|[N H]]; [apply lookup_union_Some_raw in H as [H|[N' H]]|].
    - apply fin_lookup in H as [H _]. left. by apply lookup_union_Some_l.
    - right. by apply lookup_union_Some_l.
    - apply lookup_union_Some_raw in H as [H|[N' H]].
      + left. apply lookup_union_Some_raw. right. split; [|done].
        apply not_elem_of_dom. intros R. destruct (De o') as (Hc1 & _); [by eapply elem_of_dom_2|].
        destruct (Dr _ R) as [[D|D] _]; [contra_with (cls_1 _ _ _ _ _ _ Hc o' D)|contra_with (cls_C _ _ _ _ _ _ Hc o' D)].
      + apply LDm in H as [H _]. right. by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD C1 C2).
  Qed.

  Lemma snd_iface : fin Σ' E1 ∪ fin Σ' E2 = Σ'.
  Proof. apply fin_union; [apply snd_disj|apply snd_cover]. Qed.

  Lemma snd_chans : (C1 ∪ C2 ∪ chans_of ΣC) ∖ set_map ech (dom Σv1 ∪ dom Θe1) = C1' ∪ C2 ∪ chans_of (fout Σ' E1).
  Proof.
    pose proof Hc as Hc0. destruct Hc0 as [_ _ _ _ _ _ _ H1C H2C HCC HC1 HC2].
    apply set_eq. intros c. rewrite !elem_of_difference, !elem_of_union. split.
    - intros [[[Hc1|Hc2]|HK] Hn]; [left; left; apply elem_of_difference; tauto| |].
      + left. right. done.
      + right. apply elem_of_chans_of_iff in HK as (o' & HK & <-). apply elem_of_chans_of, fout_dom.
        pose proof (cls_C _ _ _ _ _ _ Hc o' HK) as P.
        assert (o' ∉ dom Σv1) as Nv by (intros D; apply Hn; apply elem_of_map_2; clear -D; set_solver).
        assert (o' ≠ o) as Hne. { intros E. rewrite <-E in Do. tauto. }
        destruct (Dcov o') as [R|R]; [by right|done|done|]. split; [apply DE1; tauto|].
        rewrite DΣ'. pose proof (Dvr' o') as Nr. intros [E|[[? ?]|[?|[He|[? ?]]]]]; try tauto.
        destruct (De _ He) as (Hc1 & _). tauto.
    - intros [[Hc1|Hc2]|Hf].
      + apply elem_of_difference in Hc1 as [Hc1 Hn]. split; [tauto|done].
      + split; [tauto|]. intros (o' & -> & Hm)%elem_of_map. apply elem_of_union in Hm as [Hm|Hm].
        * destruct (Dv _ Hm) as [[D|D] _]; [contra_with (cls_1 _ _ _ _ _ _ Hc o' D)|contra_with (cls_C _ _ _ _ _ _ Hc o' D)].
        * pose proof (HΘe _ Hm). clear -HCC Hc2 H. set_solver.
      + apply elem_of_chans_of_iff in Hf as (o' & Hf & <-). apply fout_dom in Hf as [H HΣ].
        rewrite DΣ' in HΣ. apply DE1 in H as [->|[H|H]]; [tauto| |tauto].
        destruct (Dr _ H) as [[D|D] Hne]; [tauto|]. split; [right; by apply elem_of_chans_of|].
        pose proof (cls_C _ _ _ _ _ _ Hc o' D) as P.
        intros (m & E & Hm)%elem_of_map. apply ech_eq in E as [E|E]; subst.
        * apply elem_of_union in Hm as [Hm|Hm]; [eapply Dvr'; eassumption|].
          pose proof (cls_c1 _ _ _ _ _ _ Hc _ (HΘe _ Hm)). tauto.
        * apply elem_of_union in Hm as [Hm|Hm].
          { destruct (Dv _ Hm) as [[?|?] _]; tauto. }
          { pose proof (cls_c1 _ _ _ _ _ _ Hc _ (HΘe _ Hm)) as P'. rewrite ech_edual in P'. tauto. }
  Qed.
End send_env.

(** ** Environments of an external receive of the composite

    p1 receives Θ2 on an interface end (already retyped in Σ1). An end of
    Θ2 whose partner lies in Σ2 stays in the interface of p1 and becomes
    a cut end, its partner the matching end of p2. *)
Section recv_env.
  #[local] Set Default Proof Using "All".
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).
  Context (Θ2 : senv) (HΘ : set_map ech (dom Θ2) ## C1 ∪ C2 ∪ chans_of ΣC).
  Context (Hok : recv_ok (Σ1 ∪ Σ2) Θ2).

  Local Abbreviation Σ := (Σ1 ∪ Σ2).
  Local Abbreviation E1 := (recv_env (Σ1 ∪ ΣC) Θ2).
  Local Abbreviation E2 := (Σ2 ∪ ΣD).
  Local Abbreviation Σ' := (recv_env Σ Θ2).

  (** The class of an end of Θ2. *)
  Local Lemma CΘ o' : o' ∈ dom Θ2 →
    o' ∉ dom Σ1 ∧ o' ∉ dom Σ2 ∧ o' ∉ dom ΣC ∧ o' ∉ dom ΣD ∧ edual o' ∉ dom ΣC ∧ edual o' ∉ dom ΣD ∧
    ech o' ∉ C1 ∧ ech o' ∉ C2.
  Proof.
    intros H. pose proof Hc as Hc0. destruct Hc0 as [_ _ Hcut _ _ _ _ _ _ _ _ _].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    assert (ech o' ∈ (set_map ech (dom Θ2) : gset chan)) as Hm by (by apply elem_of_map_2).
    assert (o' ∉ dom Σ) as HnΣ by (by apply Hok). rewrite dom_union_L, not_elem_of_union in HnΣ.
    assert (∀ a (X : senv), a ∈ dom X → ech a ∈ chans_of X) as Hx by (intros; by apply elem_of_chans_of).
    split_and!; try tauto.
    - intros D. apply Hx in D. clear -D Hm HΘ. set_solver.
    - intros D. apply Hx in D. rewrite HKD in D. clear -D Hm HΘ. set_solver.
    - intros D. apply Hx in D. rewrite ech_edual in D. clear -D Hm HΘ. set_solver.
    - intros D. apply Hx in D. rewrite ech_edual, HKD in D. clear -D Hm HΘ. set_solver.
    - clear -Hm HΘ. set_solver.
    - clear -Hm HΘ. set_solver.
  Qed.

  Lemma rcv_ok1 : recv_ok (Σ1 ∪ ΣC) Θ2.
  Proof.
    destruct Hok as [Hok1 Hok2]. split.
    - intros o' H. pose proof (CΘ o' H). rewrite dom_union_L, not_elem_of_union. tauto.
    - intros o' S y S' y' H1 H2. apply (Hok2 o' S y S' y' H1).
      assert (o' ∈ dom Θ2) as D by (by eapply elem_of_dom_2). pose proof (CΘ o' D) as P.
      apply lookup_union_Some_raw in H2 as [H2|[N H2]].
      + apply lookup_union_Some_raw in H2 as [H2|[N' H2]]; [by do 2 apply lookup_union_Some_l|].
        exfalso. apply (proj1 (proj2 (proj2 (proj2 (proj2 P))))). by eapply elem_of_dom_2.
      + apply lookup_union_Some_raw. right. split; [|done]. apply not_elem_of_dom.
        rewrite dom_union_L, not_elem_of_union. apply not_elem_of_dom in N.
        rewrite dom_union_L, not_elem_of_union in N. split; [tauto|].
        intros D2. apply (Hok1 (edual o')); [by eapply elem_of_dom_2|]. rewrite dom_union_L. set_solver.
  Qed.

  Local Lemma RE1 o' : o' ∈ dom E1 ↔
    ((o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ edual o' ∉ dom Θ2) ∨
    (o' ∈ dom Θ2 ∧ edual o' ∉ dom Σ1 ∧ edual o' ∉ dom ΣC ∧ edual o' ∉ dom Θ2).
  Proof. rewrite (recv_env_dom _ _ _ rcv_ok1), !dom_union_L, elem_of_union, not_elem_of_union. tauto. Qed.

  Local Lemma RΣ' o' : o' ∈ dom Σ' ↔
    ((o' ∈ dom Σ1 ∨ o' ∈ dom Σ2) ∧ edual o' ∉ dom Θ2) ∨
    (o' ∈ dom Θ2 ∧ edual o' ∉ dom Σ1 ∧ edual o' ∉ dom Σ2 ∧ edual o' ∉ dom Θ2).
  Proof. rewrite (recv_env_dom _ _ _ Hok), !dom_union_L, elem_of_union, not_elem_of_union. tauto. Qed.

  Local Lemma RE2 o' : o' ∈ dom E2 ↔ o' ∈ dom Σ2 ∨ o' ∈ dom ΣD.
  Proof. rewrite dom_union_L. set_solver. Qed.

  Local Lemma rcv_disj : dom E1 ## dom E2.
  Proof.
    intros o' H1 H2. apply RE1 in H1. apply RE2 in H2.
    destruct H1 as [[[D|D] _]|[D _]].
    - pose proof (cls_1 _ _ _ _ _ _ Hc o' D). tauto.
    - pose proof (cls_C _ _ _ _ _ _ Hc o' D). tauto.
    - pose proof (CΘ o' D). tauto.
  Qed.

  Local Lemma rcv_out1 o' : o' ∈ dom E1 → o' ∉ dom Σ' → edual o' ∈ dom E2 ∧ edual o' ∉ dom Σ'.
  Proof.
    intros H1 HΣ. rewrite RΣ' in HΣ. rewrite RE2, RΣ', edual_edual.
    apply RE1 in H1 as [[[D|D] N]|[D N]].
    - tauto.
    - pose proof (cls_C _ _ _ _ _ _ Hc o' D) as P.
      assert (edual o' ∉ dom Θ2) as N' by (intros D'; pose proof (CΘ _ D') as P'; rewrite edual_edual in P'; tauto).
      tauto.
    - pose proof (CΘ o' D) as P. assert (edual o' ∈ dom Σ2) as D2 by (destruct (decide (edual o' ∈ dom Σ2)); tauto).
      pose proof (cls_2 _ _ _ _ _ _ _ Hc D2) as P2. rewrite edual_edual in P2. tauto.
  Qed.

  Local Lemma rcv_out2 o' : o' ∈ dom E2 → o' ∉ dom Σ' → edual o' ∈ dom E1 ∧ edual o' ∉ dom Σ'.
  Proof.
    intros H2 HΣ. rewrite RΣ' in HΣ. rewrite RE1, RΣ', edual_edual.
    apply RE2 in H2 as [D|D].
    - pose proof (cls_2 _ _ _ _ _ _ _ Hc D) as P.
      assert (edual o' ∈ dom Θ2) as D' by (destruct (decide (edual o' ∈ dom Θ2)); tauto). pose proof (CΘ _ D') as P'.
      assert (o' ∉ dom Θ2) as N by (intros D3; pose proof (CΘ _ D3) as P3; tauto). tauto.
    - pose proof (cls_D _ _ _ _ _ _ _ Hc D) as P.
      assert (o' ∉ dom Θ2) as N by (intros D3; pose proof (CΘ _ D3) as P3; tauto).
      assert (edual o' ∉ dom Θ2) as N' by (intros D'; pose proof (CΘ _ D') as P'; rewrite edual_edual in P'; tauto).
      tauto.
  Qed.

  Local Lemma rcv_types o' S1 y1 : E1 !! o' = Some (S1, y1) → o' ∉ dom Σ' →
    ∃ S2, E2 !! edual o' = Some (S2, y1‾) ∧ sdual S1 S2.
  Proof.
    intros H1 HΣ. assert (o' ∈ dom E1) as D1 by (by eapply elem_of_dom_2). rewrite RΣ' in HΣ.
    apply (recv_env_lookup _ _ _ _ rcv_ok1) in H1 as [[H1 N]|[H1 N]].
    - apply lookup_union_Some_raw in H1 as [H1|[_ H1]].
      + exfalso. apply HΣ. left. split; [left; by eapply elem_of_dom_2|done].
      + destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ H1) as (S' & L' & Hs).
        exists S'. split; [|done]. by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD C1 C2).
    - assert (o' ∈ dom Θ2) as D by (by eapply elem_of_dom_2).
      assert (edual o' ∈ dom Σ2) as D2 by (rewrite dom_union_L, not_elem_of_union in N; destruct (decide (edual o' ∈ dom Σ2)); tauto).
      apply elem_of_dom in D2 as [[S2 y2] L2]. exists S2.
      destruct Hok as [_ Hok2]. destruct (Hok2 o' S1 y1 S2 y2 H1) as [-> Hs].
      { apply lookup_union_Some_l. apply lookup_union_Some_raw. right. split; [|done].
        apply not_elem_of_dom. intros D'. pose proof (cls_2 _ _ _ _ _ _ (edual o') Hc ltac:(by eapply elem_of_dom_2)) as P4. tauto. }
      split; [by apply lookup_union_Some_l|done].
  Qed.

  Local Lemma rchans_E1 c : c ∈ chans_of E1 → c ∈ chans_of Σ1 ∪ chans_of ΣC ∨ c ∈ (set_map ech (dom Θ2) : gset chan).
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply RE1 in H as [[[D|D] _]|[D _]].
    - left. apply elem_of_union_l. by apply elem_of_chans_of.
    - left. apply elem_of_union_r. by apply elem_of_chans_of.
    - right. by apply elem_of_map_2.
  Qed.

  Local Lemma rchans_E2 c : c ∈ chans_of E2 → c ∈ chans_of Σ2 ∪ chans_of ΣC.
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply RE2 in H as [H|H].
    - apply elem_of_union_l. by apply elem_of_chans_of.
    - apply elem_of_union_r. destruct (cls_D _ _ _ _ _ _ o' Hc H) as (_ & _ & _ & _ & _ & _ & _ & _ & Dc).
      rewrite <-ech_edual. by apply elem_of_chans_of.
  Qed.

  Local Abbreviation C1' := (C1 ∪ recv_back (Σ1 ∪ ΣC) Θ2).

  Lemma rcv_conn : conn (fin Σ' E1) (fout Σ' E1) C1' (fin Σ' E2) (fout Σ' E2) C2.
  Proof.
    pose proof Hc as Hc0. destruct Hc0 as [_ _ _ _ _ _ H12 H1C H2C HCC HC1 HC2].
    pose proof (recv_back_sub (Σ1 ∪ ΣC) Θ2) as Hb.
    apply conn_filter.
    - apply rcv_disj.
    - apply pfree_recv_env; [apply rcv_ok1|apply (pfree_1C _ _ _ _ _ _ Hc)].
    - apply (pfree_1C Σ2 ΣD Σ1 ΣC C2 C1). by apply conn_sym.
    - apply pfree_recv_env; [done|]. destruct Hc. by apply pfree_union.
    - apply rcv_out1.
    - apply rcv_out2.
    - apply rcv_types.
    - clear -HCC Hb HΘ. set_solver.
    - intros c Hc1 Hc2. apply elem_of_union in Hc1 as [Hc1|Hc1].
      + apply elem_of_union in Hc2 as [H|H].
        * destruct (rchans_E1 c H) as [H'|H']; [clear -HC1 Hc1 H'; set_solver|clear -HΘ Hc1 H'; set_solver].
        * apply rchans_E2 in H. clear -HC1 Hc1 H. set_solver.
      + apply elem_of_union in Hc2 as [H|H].
        * by apply (recv_back_env_disj _ _ rcv_ok1 c).
        * apply recv_back_elem in Hc1 as (o' & Ho' & <- & Hp). pose proof (CΘ o' Ho') as P.
          apply elem_of_chans_of_iff in H as (o'' & H & E). apply RE2 in H.
          apply ech_eq in E as [E|E]; subst; [tauto|]. rewrite edual_edual in *.
          rewrite dom_union_L, elem_of_union in Hp.
          destruct H as [H|H]; [|tauto]. pose proof (cls_2 _ _ _ _ _ _ _ Hc H) as P2.
          destruct Hp as [[Hp|Hp]|Hp]; [tauto|tauto|]. pose proof (CΘ _ Hp). tauto.
    - intros c Hc2 Hcc. apply elem_of_union in Hcc as [H|H].
      + destruct (rchans_E1 c H) as [H'|H']; [clear -HC2 Hc2 H'; set_solver|clear -HΘ Hc2 H'; set_solver].
      + apply rchans_E2 in H. clear -HC2 Hc2 H. set_solver.
  Qed.

  Local Lemma rcv_cover o' v : Σ' !! o' = Some v → E1 !! o' = Some v ∨ E2 !! o' = Some v.
  Proof.
    intros H. apply (recv_env_lookup _ _ _ _ Hok) in H as [[H N]|[H N]].
    - apply lookup_union_Some_raw in H as [H|[N' H]].
      + left. apply (recv_env_lookup _ _ _ _ rcv_ok1). left. split; [by apply lookup_union_Some_l|done].
      + right. by apply lookup_union_Some_l.
    - left. apply (recv_env_lookup _ _ _ _ rcv_ok1). right. split; [done|].
      assert (o' ∈ dom Θ2) as D by (by eapply elem_of_dom_2). pose proof (CΘ o' D).
      rewrite !dom_union_L, !not_elem_of_union in N |- *. tauto.
  Qed.

  Lemma rcv_iface : fin Σ' E1 ∪ fin Σ' E2 = Σ'.
  Proof. apply fin_union; [apply rcv_disj|apply rcv_cover]. Qed.

  Lemma rcv_chans : C1 ∪ C2 ∪ chans_of ΣC ∪ recv_back Σ Θ2 = C1' ∪ C2 ∪ chans_of (fout Σ' E1).
  Proof.
    apply set_eq. intros c. rewrite !elem_of_union. split.
    - intros [[[Hc1|Hc2]|HK]|Hb]; [tauto|tauto| |].
      + right. apply elem_of_chans_of_iff in HK as (o' & HK & <-). apply elem_of_chans_of, fout_dom.
        pose proof (cls_C _ _ _ _ _ _ Hc o' HK) as P.
        assert (o' ∉ dom Θ2 ∧ edual o' ∉ dom Θ2) as [N N'].
        { split; intros D; pose proof (CΘ _ D) as P'; rewrite ?edual_edual in P'; tauto. }
        rewrite RE1, RΣ'. tauto.
      + apply recv_back_elem in Hb as (o' & Ho' & <- & Hp). pose proof (CΘ o' Ho') as P.
        rewrite dom_union_L, elem_of_union in Hp. destruct Hp as [[Hp|Hp]|Hp].
        * left. left. right. apply recv_back_elem. exists o'. split_and!; [done|done|]. left.
          rewrite dom_union_L. set_solver.
        * right. apply elem_of_chans_of, fout_dom. pose proof (cls_2 _ _ _ _ _ _ _ Hc Hp) as P2.
          assert (edual o' ∉ dom Θ2) as N by (intros D; by apply (proj1 Hok (edual o')); [|rewrite dom_union_L; set_solver]).
          rewrite RE1, RΣ'. tauto.
        * left. left. right. apply recv_back_elem. exists o'. split_and!; [done|done|by right].
    - intros [[[Hc1|Hb]|Hc2]|Hf]; [tauto| |tauto|].
      + apply recv_back_elem in Hb as (o' & Ho' & <- & Hp). pose proof (CΘ o' Ho') as P. right.
        apply recv_back_elem. exists o'. split_and!; [done|done|].
        rewrite !dom_union_L, !elem_of_union in Hp |- *. tauto.
      + apply elem_of_chans_of_iff in Hf as (o' & Hf & <-). apply fout_dom in Hf as [H HΣ].
        rewrite RE1 in H. rewrite RΣ' in HΣ. destruct H as [[[D|D] N]|[D N]].
        * tauto.
        * left. right. by apply elem_of_chans_of.
        * right. apply recv_back_elem. exists o'. split_and!; [done|done|]. left.
          rewrite dom_union_L, elem_of_union. destruct (decide (edual o' ∈ dom Σ2)); tauto.
  Qed.
End recv_env.
