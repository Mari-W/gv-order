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
