(** * P-Connect, renaming a composite (stage S4)

    A renaming of the held ends of a composite that fixes its interface
    keeps the side conditions of P-Connect ([conn_rename]). Links of
    restricted and cut channels rename the composite this way. *)

From GV Require Export compat.ConnectSplit.
From GV Require Import fuel.FuelMono.

(** A renaming identifies the channels of two held ends only if they
    share a channel. *)
Lemma ren_ech h Σ p a b : pren_ok h Σ p → pheld Σ p a → pheld Σ p b → ech (h a) = ech (h b) → ech a = ech b.
Proof.
  intros (_ & Hi & Hp) Ha Hb E. apply ech_eq in E as [E|E].
  - by rewrite (Hi _ _ Hb Ha E).
  - rewrite (Hp _ _ Ha Hb E). by rewrite ech_edual.
Qed.

Lemma img_disj h Σ p (N1 N2 O1 O2 : gset chan) :
  pren_ok h Σ p →
  (∀ c, c ∈ N1 → ∃ a, pheld Σ p a ∧ ech a ∈ O1 ∧ c = ech (h a)) →
  (∀ c, c ∈ N2 → ∃ a, pheld Σ p a ∧ ech a ∈ O2 ∧ c = ech (h a)) →
  O1 ## O2 → N1 ## N2.
Proof.
  intros Hok H1 H2 HO c Hc1 Hc2. destruct (H1 c Hc1) as (a & Ha & Oa & ->).
  destruct (H2 _ Hc2) as (b & Hb & Ob & E). apply (ren_ech h Σ p a b Hok Ha Hb) in E as E'.
  apply (HO (ech a)); [done|by rewrite E'].
Qed.

Lemma img_union h Σ p (N1 N2 O1 O2 : gset chan) :
  (∀ c, c ∈ N1 → ∃ a, pheld Σ p a ∧ ech a ∈ O1 ∧ c = ech (h a)) →
  (∀ c, c ∈ N2 → ∃ a, pheld Σ p a ∧ ech a ∈ O2 ∧ c = ech (h a)) →
  ∀ c, c ∈ N1 ∪ N2 → ∃ a, pheld Σ p a ∧ ech a ∈ O1 ∪ O2 ∧ c = ech (h a).
Proof.
  intros H1 H2 c [Hc|Hc]%elem_of_union.
  - destruct (H1 c Hc) as (a & ? & ? & ?). exists a. split_and!; [done|set_solver|done].
  - destruct (H2 c Hc) as (a & ? & ? & ?). exists a. split_and!; [done|set_solver|done].
Qed.

Section conn_rename.
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).
  Context (h : cend → cend) (E : gmultiset expr).
  Context (Hok : pren_ok h (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E)).
  Context (Hfix : ∀ o, o ∈ dom (Σ1 ∪ Σ2) → h o = o).
  #[local] Set Default Proof Using "All".

  Local Abbreviation Hd := (pheld (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E)).

  Local Lemma KD : chans_of ΣD = chans_of ΣC.
  Proof. destruct Hc as [_ _ Hcut _ _ _ _ _ _ _ _ _]. by apply cut_dual_chans. Qed.

  Local Lemma H_1 o : o ∈ dom Σ1 → Hd o.
  Proof. intros H. left. rewrite dom_union_L. set_solver. Qed.
  Local Lemma H_2 o : o ∈ dom Σ2 → Hd o.
  Proof. intros H. left. rewrite dom_union_L. set_solver. Qed.
  Local Lemma H_C o : o ∈ dom ΣC → Hd o.
  Proof. intros H. right. simpl. apply elem_of_union_r. by apply elem_of_chans_of. Qed.
  Local Lemma H_D o : o ∈ dom ΣD → Hd o.
  Proof. intros H. right. simpl. apply elem_of_union_r. rewrite <-KD. by apply elem_of_chans_of. Qed.
  Local Lemma H_c1 c : c ∈ C1 → Hd (EPos c).
  Proof. intros H. right. simpl. set_solver. Qed.
  Local Lemma H_c2 c : c ∈ C2 → Hd (EPos c).
  Proof. intros H. right. simpl. set_solver. Qed.

  Local Lemma kinjC : kinj h ΣC.
  Proof. intros a b va vb Ha Hb. apply Hok; apply H_C; by eapply elem_of_dom_2. Qed.
  Local Lemma kinjD : kinj h ΣD.
  Proof. intros a b va vb Ha Hb. apply Hok; apply H_D; by eapply elem_of_dom_2. Qed.

  Local Lemma img_fix (X : senv) : (∀ o, o ∈ dom X → Hd o) → (∀ o, o ∈ dom X → h o = o) →
    ∀ c, c ∈ chans_of X → ∃ a, Hd a ∧ ech a ∈ chans_of X ∧ c = ech (h a).
  Proof.
    intros HX Hf c (o & Ho & <-)%elem_of_chans_of_iff. exists o. split_and!; [by apply HX|by apply elem_of_chans_of|by rewrite Hf].
  Qed.

  Local Lemma img_kren (X : senv) : kinj h X → (∀ o, o ∈ dom X → Hd o) →
    ∀ c, c ∈ chans_of (kren h X) → ∃ a, Hd a ∧ ech a ∈ chans_of X ∧ c = ech (h a).
  Proof.
    intros Hk HX c (o & Ho & <-)%elem_of_chans_of_iff. rewrite kren_dom in Ho by done.
    apply elem_of_map in Ho as (a & -> & Ha). exists a. split_and!; [by apply HX|by apply elem_of_chans_of|done].
  Qed.

  Local Lemma img_set (C : gset chan) : (∀ c, c ∈ C → Hd (EPos c)) →
    ∀ c, c ∈ (set_map (gch h) C : gset chan) → ∃ a, Hd a ∧ ech a ∈ C ∧ c = ech (h a).
  Proof. intros HC c (c0 & -> & Hc0)%elem_of_map. exists (EPos c0). split_and!; [by apply HC|done|done]. Qed.

  Local Lemma fix1 o : o ∈ dom Σ1 → h o = o.
  Proof. intros H. apply Hfix. rewrite dom_union_L. set_solver. Qed.
  Local Lemma fix2 o : o ∈ dom Σ2 → h o = o.
  Proof. intros H. apply Hfix. rewrite dom_union_L. set_solver. Qed.

  Local Definition iC := img_kren ΣC kinjC H_C.
  Local Definition iD := img_kren ΣD kinjD H_D.
  Local Definition i1 := img_fix Σ1 H_1 fix1.
  Local Definition i2 := img_fix Σ2 H_2 fix2.
  Local Definition ic1 := img_set C1 H_c1.
  Local Definition ic2 := img_set C2 H_c2.

  Local Lemma disj_ren (X Y : senv) : (∀ o, o ∈ dom X → Hd o) → (∀ o, o ∈ dom Y → Hd o) → X ##ₘ Y →
    kinj h X → (∀ o, o ∈ dom Y → h o = o) → Y ##ₘ kren h X.
  Proof.
    intros HX HY Hxy Hk Hf. apply map_disjoint_dom. intros o Hy Hx. rewrite kren_dom in Hx by done.
    apply elem_of_map in Hx as (a & -> & Ha). destruct Hok as (_ & Hi & _).
    assert (a = h a) as Ea by (apply Hi; [by apply HX|by apply HY|by rewrite (Hf (h a) Hy)]).
    assert (a ∈ dom Y) as Ha' by (by rewrite Ea).
    apply map_disjoint_dom in Hxy. by apply (Hxy a).
  Qed.

  Lemma conn_rename : conn Σ1 (kren h ΣC) (set_map (gch h) C1) Σ2 (kren h ΣD) (set_map (gch h) C2).
  Proof.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 [Hcd Hct] Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof Hok as (Hdc & Hi & Hp).
    constructor.
    - apply disj_ren; [apply H_C|apply H_1|by apply map_disjoint_sym|apply kinjC|apply fix1].
    - apply disj_ren; [apply H_D|apply H_2|by apply map_disjoint_sym|apply kinjD|apply fix2].
    - split.
      + intros o. rewrite !kren_dom by first [apply kinjC|apply kinjD]. rewrite !elem_of_map. split.
        * intros (a & -> & Ha). exists (edual a). rewrite Hdc. split; [done|]. by apply Hcd.
        * intros (a & Ea & Ha). exists (edual a). split; [rewrite Hdc, <-Ea; by rewrite edual_edual|]. apply Hcd. by rewrite edual_edual.
      + intros o S x Ho. apply kren_lookup_inv in Ho as (a & -> & Ha). destruct (Hct _ _ _ Ha) as (S' & Hb & Hs).
        exists S'. split; [|done]. rewrite <-Hdc. by apply kren_lookup; [apply kinjD|].
    - done.
    - done.
    - intros o Ho Ho'. rewrite kren_dom in Ho, Ho' by apply kinjC. apply elem_of_map in Ho as (a & -> & Ha), Ho' as (b & Eb & Hb).
      apply (HfC a Ha). rewrite <-(Hp a b); [done|by apply H_C|by apply H_C|done].
    - done.
    - eapply img_disj; [exact Hok|apply i1|apply iC|done].
    - eapply img_disj; [exact Hok|apply i2|apply iC|done].
    - eapply img_disj; [exact Hok|apply ic1|apply ic2|done].
    - eapply img_disj; [exact Hok|apply ic1| |exact HC1]. apply img_union; [apply img_union|]; [apply i1|apply i2|apply iC].
    - eapply img_disj; [exact Hok|apply ic2| |exact HC2]. apply img_union; [apply img_union|]; [apply i1|apply i2|apply iC].
  Qed.
End conn_rename.

(** The held ends of a component are held ends of the composite. *)
Lemma pheld_pconn_1 Σ1 ΣC Σ2 (p1 p2 : proc) o :
  pheld (Σ1 ∪ ΣC) p1 o → pheld (Σ1 ∪ Σ2) (pconn p1 p2 (chans_of ΣC)) o.
Proof.
  intros [Ho|Ho]; [rewrite dom_union_L in Ho; apply elem_of_union in Ho as [Ho|Ho]|].
  - left. rewrite dom_union_L. set_solver.
  - right. simpl. apply elem_of_union_r. by apply elem_of_chans_of.
  - right. simpl. set_solver.
Qed.

Lemma pheld_pconn_2 Σ1 ΣC Σ2 ΣD (p1 p2 : proc) o : chans_of ΣD = chans_of ΣC →
  pheld (Σ2 ∪ ΣD) p2 o → pheld (Σ1 ∪ Σ2) (pconn p1 p2 (chans_of ΣC)) o.
Proof.
  intros HK [Ho|Ho]; [rewrite dom_union_L in Ho; apply elem_of_union in Ho as [Ho|Ho]|].
  - left. rewrite dom_union_L. set_solver.
  - right. simpl. apply elem_of_union_r. rewrite <-HK. by apply elem_of_chans_of.
  - right. simpl. set_solver.
Qed.

Lemma pren_ok_sub h Σ p Σ' p' : pren_ok h Σ p → (∀ o, pheld Σ' p' o → pheld Σ p o) → pren_ok h Σ' p'.
Proof. intros (Hd & Hi & Hp) Hs. split_and!; [done| |]; intros a b Ha Hb; [apply Hi|apply Hp]; auto. Qed.

Lemma csub_cases o1 o2 o : (o = edual o1 ∧ csub o1 o2 o = o2) ∨ (o = o1 ∧ csub o1 o2 o = edual o2) ∨
  (o ≠ edual o1 ∧ o ≠ o1 ∧ csub o1 o2 o = o).
Proof.
  unfold csub. destruct (decide (o = edual o1)) as [A|A]; [by left|].
  destruct (decide (o = o1)) as [B|B]; [by right; left|by right; right].
Qed.

(** csub o1 o2 is a renaming whenever o2 and its partner are not held,
    whatever happens to o1. *)
Lemma pren_ok_csub_r o1 o2 Σ p :
  ech o2 ≠ ech o1 → ¬ pheld Σ p o2 → ¬ pheld Σ p (edual o2) → pren_ok (csub o1 o2) Σ p.
Proof.
  intros Hne H2 H3. split; [by apply csub_dcomm|].
  split; intros a b Ha Hb E;
    destruct (csub_cases o1 o2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases o1 o2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; rewrite ?Ea, ?Eb; rewrite ?edual_edual in *;
    first [ done | tauto | (exfalso; by apply (edual_ne o2)) | (exfalso; apply (edual_ne o2); by symmetry)
          | (apply edual_inj in E; subst; rewrite ?edual_edual in *; tauto)
          | (subst; rewrite ?edual_edual in *; tauto) ].
Qed.

(** csub o1 o2 after csub o2 o1 is csub o1 o2. *)
Lemma csub_csub o1 o2 o : ech o1 ≠ ech o2 → csub o1 o2 (csub o2 o1 o) = csub o1 o2 o.
Proof.
  intros Hne. destruct (csub_cases o2 o1 o) as [(-> & ->)|[(-> & ->)|(_ & _ & ->)]]; [| |done];
    unfold csub; repeat case_decide; try done; exfalso;
    match goal with
    | H : ?a = edual ?a |- _ => by destruct (edual_ne a)
    | H : edual ?a = ?a |- _ => by destruct (edual_ne a)
    | H : ?a = ?b |- _ => apply (f_equal ech) in H; rewrite ?ech_edual in H; congruence
    end.
Qed.

(** ** Environments after a link of a cut end *)

Lemma kren_csub_eq o1 o2 (Θ : senv) v :
  Θ !! edual o1 = Some v → o1 ∉ dom Θ → o2 ∉ dom Θ → ech o2 ≠ ech o1 →
  kren (csub o1 o2) Θ = <[o2 := v]> (delete (edual o1) Θ).
Proof.
  intros Hv H1 H2 Hne.
  assert (kinj (csub o1 o2) Θ) as Hk.
  { intros a b va vb Ha Hb E.
    destruct (csub_cases o1 o2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases o1 o2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; subst; try done;
    first [ by destruct (edual_ne o2) | (exfalso; apply (edual_ne o2); by symmetry)
          | (exfalso; apply H1; by eapply elem_of_dom_2)
          | (exfalso; apply H2; by eapply elem_of_dom_2) ]. }
  rewrite <-(insert_delete_id Θ (edual o1) v) at 1 by done.
  rewrite kren_insert by (by rewrite insert_delete_id).
  unfold csub at 1. rewrite decide_True by done. f_equal. apply kren_id.
  intros o Ho. apply elem_of_dom in Ho as [w Hw]. apply lookup_delete_Some in Hw as [Hne' Hw].
  destruct (csub_cases o1 o2 o) as [(Eo & _)|[(Eo & _)|(_ & _ & ->)]]; [done| |done].
  exfalso. subst. apply H1. by eapply elem_of_dom_2.
Qed.

Lemma conn_del Σ1 ΣC C1 Σ2 ΣD C2 o :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → o ∈ dom ΣC →
  conn Σ1 (delete o ΣC) C1 Σ2 (delete (edual o) ΣD) C2 ∧ chans_of (delete o ΣC) = chans_of ΣC ∖ {[ech o]}.
Proof.
  intros Hc Ho. destruct Hc as [Hd1 Hd2 [Hcd Hct] Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
  assert (chans_of (delete o ΣC) = chans_of ΣC ∖ {[ech o]}) as HK.
  { unfold chans_of. rewrite dom_delete_L. apply set_eq. intros c. rewrite elem_of_difference, !elem_of_map.
    split.
    - intros (o' & -> & Ho'). apply elem_of_difference in Ho' as [Ho1 Ho2]. split; [eauto|].
      intros He%elem_of_singleton. apply ech_eq in He as [->| ->]; [set_solver|]. apply (HfC _ Ho). by rewrite edual_edual.
    - intros [(o' & -> & Ho') Hn]. exists o'. split; [done|]. apply elem_of_difference. split; [done|].
      intros ->%elem_of_singleton. by apply Hn, elem_of_singleton. }
  split; [|done]. constructor.
  - by apply map_disjoint_delete_r.
  - by apply map_disjoint_delete_r.
  - split.
    + intros o'. rewrite !dom_delete_L, !elem_of_difference, Hcd, !elem_of_singleton.
      split; intros [? Hn]; split; try done; intros E; apply Hn; [by rewrite <-E, edual_edual|by rewrite E, edual_edual].
    + intros o' S x Hl. apply lookup_delete_Some in Hl as [Hne Hl]. destruct (Hct _ _ _ Hl) as (S' & ? & ?).
      exists S'. split; [|done]. rewrite lookup_delete_ne; [done|]. intros E. by apply Hne, edual_inj.
  - done.
  - done.
  - intros o' Ho'. rewrite !dom_delete_L in Ho' |- *. set_solver.
  - done.
  - rewrite HK. clear -H1C. set_solver.
  - rewrite HK. clear -H2C. set_solver.
  - done.
  - rewrite HK. clear -HC1. set_solver.
  - rewrite HK. clear -HC2. set_solver.
Qed.

(** A link of a cut end o1 with an interface end o2 of the same side. *)
Lemma conn_link_iface Σ1 ΣC C1 Σ2 ΣD C2 o1 o2 S2 y :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → o1 ∈ dom ΣC → Σ1 !! o2 = Some (S2, y) →
  conn (delete o2 Σ1) (delete o1 ΣC) C1 (<[o2 := (S2, y)]> Σ2) (delete (edual o1) ΣD) C2.
Proof.
  intros Hc Ho1 Ho2. assert (o2 ∈ dom Σ1) as D2 by (by eapply elem_of_dom_2).
  pose proof (cls_1 _ _ _ _ _ _ Hc o2 D2) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct (conn_del _ _ _ _ _ _ o1 Hc Ho1) as [Hc' HK].
  destruct Hc' as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
  assert (ech o2 ∈ chans_of Σ1) as Ec by (by apply elem_of_chans_of).
  assert (chans_of (delete o2 Σ1) ⊆ chans_of Σ1) as S1 by (apply chans_of_mono; rewrite dom_delete_L; set_solver).
  assert (chans_of (<[o2 := (S2, y)]> Σ2) = {[ech o2]} ∪ chans_of Σ2) as E2.
  { unfold chans_of. rewrite dom_insert_L, set_map_union_L, set_map_singleton_L. done. }
  assert (ech o2 ∉ chans_of (delete o2 Σ1)) as Nd.
  { intros (o' & Ho' & E)%elem_of_chans_of_iff. rewrite dom_delete_L in Ho'. apply elem_of_difference in Ho' as [Ho' Hn].
    apply ech_eq in E as [->| ->]; [set_solver|]. rewrite edual_edual in N6. done. }
  assert (ech o2 ∉ chans_of (delete o1 ΣC)) as Nc.
  { rewrite HK. intros [Hin _]%elem_of_difference. destruct Hc as [_ _ _ _ _ _ _ H1C' _ _ _ _]. by apply (H1C' (ech o2)). }
  constructor.
  - apply map_disjoint_delete_l. apply map_disjoint_delete_r. by destruct Hc.
  - apply map_disjoint_insert_l. split; [|done]. apply not_elem_of_dom. rewrite dom_delete_L. set_solver.
  - done.
  - apply (pfree_sub _ Σ1); [rewrite dom_delete_L; set_solver|by destruct Hc].
  - intros o Ho Ho'. rewrite dom_insert_L in Ho, Ho'. apply elem_of_union in Ho as [Ho|Ho], Ho' as [Ho'|Ho'].
    + apply elem_of_singleton in Ho, Ho'. subst. by destruct (edual_ne o2).
    + apply elem_of_singleton in Ho. subst. done.
    + apply elem_of_singleton in Ho'. rewrite <-Ho', edual_edual in N8. done.
    + by apply (Hf2 o).
  - done.
  - rewrite E2. clear -H12 S1 Nd. set_solver.
  - clear -H1C S1. set_solver.
  - rewrite E2. clear -H2C Nc. set_solver.
  - done.
  - rewrite E2. clear -HC1 S1 Ec. set_solver.
  - rewrite E2. clear -HC2 S1 Ec. set_solver.
Qed.

(** A link of two cut ends of one side fuses the other side on the
    channel of the kept end. *)
Lemma fuse_ok_csub_cut o1 o2 Σ p :
  ech o2 ≠ ech o1 → ¬ pheld Σ p o1 → ¬ pheld Σ p o2 → dpairs {[ech o2]} (kren (csub o1 o2) Σ) →
  fuse_ok (csub o1 o2) {[ech o2]} Σ p.
Proof.
  intros Hne H1 H2 Hdp. split_and!; [by apply csub_dcomm| | | |done].
  - intros a b Ha Hb E;
    destruct (csub_cases o1 o2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases o1 o2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; subst; try done;
    first [ by destruct (edual_ne o2) | (exfalso; apply (edual_ne o2); by symmetry) | tauto ].
  - intros a b Ha Hb E;
    destruct (csub_cases o1 o2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases o1 o2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; rewrite ?Ra; subst; rewrite ?edual_edual in *; try tauto;
    first [ (right; apply elem_of_singleton; first [done | by rewrite ech_edual | (rewrite E; by rewrite ?ech_edual)
                                                  | (rewrite <-E; by rewrite ?ech_edual)])
          | (left; first [done | by rewrite E, ?edual_edual | by rewrite <-E, ?edual_edual]) ].
  - intros c Hc (c0 & -> & Hc0)%elem_of_map. apply elem_of_singleton in Hc. revert Hc.
    unfold gch. destruct (csub_cases o1 o2 (EPos c0)) as [(E & ->)|[(E & ->)|(_ & _ & ->)]]; intros Hc.
    + apply H1. right. rewrite <-(ech_edual o1), <-E. done.
    + apply H1. right. rewrite <-E. done.
    + apply H2. right. simpl in Hc. by rewrite <-Hc.
Qed.

(** The type of an interface end does not matter to [conn]. *)
Lemma conn_retype1 Σ1 ΣC C1 Σ2 ΣD C2 o v :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → o ∈ dom Σ1 → conn (<[o := v]> Σ1) ΣC C1 Σ2 ΣD C2.
Proof.
  intros [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2] Ho.
  assert (dom (<[o := v]> Σ1) = dom Σ1) as Ed by (rewrite dom_insert_L; set_solver).
  assert (chans_of (<[o := v]> Σ1) = chans_of Σ1) as Ec by (unfold chans_of; by rewrite Ed).
  constructor; rewrite ?Ec; try done.
  - apply map_disjoint_dom. rewrite Ed. by apply map_disjoint_dom.
  - intros o' Ho'. rewrite Ed in Ho' |- *. by apply Hf1.
Qed.
