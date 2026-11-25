(** * P-Connect, a fusion of the composite (stage S4)

    A fusion (h, D) of the composite is a composite of fusions of the
    components over a larger cut. A channel of D whose two ends come
    from Σ1 is fused by p1 (D1), one whose two ends come from Σ2 by p2
    (D2), and one with an end on each side becomes a cut channel. The
    new cut is re-split by the fused interface ([conn_filter]). The
    lemmas read environments and channel sets only. *)

From GV Require Export compat.ConnectSplit.
From GV Require Import fuel.FuelMono.

Lemma fuse_ok_proc h D Σ (p p' : proc) : p.1 = p'.1 → fuse_ok h D Σ p → fuse_ok h D Σ p'.
Proof. intros E. unfold fuse_ok, pheld. by rewrite E. Qed.

Lemma sdrop_dom D (Σ : senv) o : o ∈ dom (sdrop D Σ) ↔ o ∈ dom Σ ∧ ech o ∉ D.
Proof.
  split.
  - intros [v Hv]%elem_of_dom. apply sdrop_lookup in Hv as [A B]. split; [by eapply elem_of_dom_2|done].
  - intros [[v Hv]%elem_of_dom B]. apply elem_of_dom. exists v. by apply sdrop_lookup.
Qed.

(** The channels a fusion leaves to one side: both ends come from Σ. *)
Definition dside (h : cend → cend) (Σ : senv) (D : gset chan) : gset chan :=
  filter (λ c, EPos c ∈ dom (kren h Σ) ∧ ENeg c ∈ dom (kren h Σ)) D.

Lemma dside_iff h Σ D o : ech o ∈ dside h Σ D ↔ ech o ∈ D ∧ o ∈ dom (kren h Σ) ∧ edual o ∈ dom (kren h Σ).
Proof. unfold dside. rewrite elem_of_filter. destruct o; simpl; tauto. Qed.

Section fuse_side.
  #[local] Set Default Proof Using "All".
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).
  Context (h : cend → cend) (D : gset chan) (Ep : gmultiset expr).
  Context (Hh : fuse_ok h D (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, Ep)).

  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation D1 := (dside h Σ1 D).
  Local Abbreviation D2 := (dside h Σ2 D).
  Local Abbreviation E1 := (sdrop D1 (kren h (Σ1 ∪ ΣC))).
  Local Abbreviation E2 := (sdrop D2 (kren h (Σ2 ∪ ΣD))).
  Local Abbreviation Σf := (sdrop D (kren h (Σ1 ∪ Σ2))).

  Local Definition held (a : cend) : Prop :=
    a ∈ dom Σ1 ∨ a ∈ dom ΣC ∨ a ∈ dom Σ2 ∨ a ∈ dom ΣD ∨ ech a ∈ C1 ∨ ech a ∈ C2.

  Local Lemma HKD : chans_of ΣD = K.
  Proof. apply cut_dual_chans. by destruct Hc. Qed.

  Local Lemma held_p a : held a → pheld (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ K, Ep) a.
  Proof.
    unfold pheld. simpl. rewrite dom_union_L, !elem_of_union. intros [H|[H|[H|[H|[H|H]]]]]; try tauto.
    - right. right. by apply elem_of_chans_of.
    - right. right. rewrite <-HKD. by apply elem_of_chans_of.
  Qed.

  Local Lemma Hd : dcomm h.
  Proof. by destruct Hh. Qed.

  Local Lemma hinj a b : held a → held b → h a = h b → a = b.
  Proof. intros Ha Hb E. destruct Hh as (_ & Hi & _). apply Hi; [by apply held_p|by apply held_p|done]. Qed.

  Local Lemma hpart a b : held a → held b → h b = edual (h a) → b = edual a ∨ ech (h a) ∈ D.
  Proof. intros Ha Hb E. destruct Hh as (_ & _ & Hp & _). apply Hp; [by apply held_p|by apply held_p|done]. Qed.

  Local Lemma notD a : ech a ∈ C1 ∪ C2 ∪ K → ech (h a) ∉ D.
  Proof.
    intros Ha HD. destruct Hh as (Hd' & _ & _ & Hg & _). rewrite (ech_gch h a Hd') in HD.
    apply (Hg (gch h (ech a))); [done|]. by apply elem_of_map_2.
  Qed.

  Local Lemma chinj a b : held a → held b → ech (h a) = ech (h b) → ech a = ech b ∨ ech (h a) ∈ D.
  Proof.
    intros Ha Hb E. apply ech_eq in E as [E|E].
    - left. by rewrite (hinj b a Hb Ha E).
    - destruct (hpart a b Ha Hb E) as [->|?]; [left; by rewrite ech_edual|by right].
  Qed.

  Local Lemma kinj_h (Θ : senv) : (∀ a, a ∈ dom Θ → held a) → kinj h Θ.
  Proof. intros H o1 o2 v1 v2 H1 H2 E. apply hinj; [apply H; by eapply elem_of_dom_2|apply H; by eapply elem_of_dom_2|done]. Qed.

  Local Lemma KD (Θ : senv) o' : (∀ a, a ∈ dom Θ → held a) → o' ∈ dom (kren h Θ) ↔ ∃ a, o' = h a ∧ a ∈ dom Θ.
  Proof. intros H. rewrite (kren_dom h Θ (kinj_h Θ H)), elem_of_map. done. Qed.

  Local Lemma H1C a : a ∈ dom (Σ1 ∪ ΣC) → held a.
  Proof. rewrite dom_union_L, elem_of_union. unfold held. tauto. Qed.
  Local Lemma H2D a : a ∈ dom (Σ2 ∪ ΣD) → held a.
  Proof. rewrite dom_union_L, elem_of_union. unfold held. tauto. Qed.
  Local Lemma H12 a : a ∈ dom (Σ1 ∪ Σ2) → held a.
  Proof. rewrite dom_union_L, elem_of_union. unfold held. tauto. Qed.
  Local Lemma H1 a : a ∈ dom Σ1 → held a.
  Proof. unfold held. tauto. Qed.
  Local Lemma H2 a : a ∈ dom Σ2 → held a.
  Proof. unfold held. tauto. Qed.

  Local Lemma DE1 o' : o' ∈ dom E1 ↔ (∃ a, o' = h a ∧ (a ∈ dom Σ1 ∨ a ∈ dom ΣC)) ∧ ech o' ∉ D1.
  Proof. rewrite sdrop_dom, (KD _ _ H1C). setoid_rewrite dom_union_L. setoid_rewrite elem_of_union. done. Qed.
  Local Lemma DE2 o' : o' ∈ dom E2 ↔ (∃ a, o' = h a ∧ (a ∈ dom Σ2 ∨ a ∈ dom ΣD)) ∧ ech o' ∉ D2.
  Proof. rewrite sdrop_dom, (KD _ _ H2D). setoid_rewrite dom_union_L. setoid_rewrite elem_of_union. done. Qed.
  Local Lemma DΣf o' : o' ∈ dom Σf ↔ (∃ a, o' = h a ∧ (a ∈ dom Σ1 ∨ a ∈ dom Σ2)) ∧ ech o' ∉ D.
  Proof. rewrite sdrop_dom, (KD _ _ H12). setoid_rewrite dom_union_L. setoid_rewrite elem_of_union. done. Qed.
  Local Lemma DD1 o' : ech o' ∈ D1 ↔ ech o' ∈ D ∧ (∃ a, o' = h a ∧ a ∈ dom Σ1) ∧ (∃ b, edual o' = h b ∧ b ∈ dom Σ1).
  Proof. rewrite dside_iff, !(KD _ _ H1). done. Qed.
  Local Lemma DD2 o' : ech o' ∈ D2 ↔ ech o' ∈ D ∧ (∃ a, o' = h a ∧ a ∈ dom Σ2) ∧ (∃ b, edual o' = h b ∧ b ∈ dom Σ2).
  Proof. rewrite dside_iff, !(KD _ _ H2). done. Qed.

  (** Both ends of a channel of D are images of the interface. *)
  Local Lemma DD o' : ech o' ∈ D → ∃ b S x S', edual o' = h b ∧ (b ∈ dom Σ1 ∨ b ∈ dom Σ2) ∧
      kren h (Σ1 ∪ Σ2) !! o' = Some (S, x) ∧ kren h (Σ1 ∪ Σ2) !! edual o' = Some (S', x‾) ∧ sdual S S'.
  Proof.
    intros HD. destruct Hh as (_ & _ & _ & _ & Hdp). destruct (Hdp o' HD) as (S & x & S' & L & L' & Hs).
    destruct (kren_lookup_inv _ _ _ _ L') as (b & Eb & Lb).
    exists b, S, x, S'. split_and!; [done| |done|done|done].
    apply elem_of_dom_2 in Lb. rewrite dom_union_L, elem_of_union in Lb. done.
  Qed.

  (** The classes of a held end. *)
  Local Ltac cls a :=
    first [ let H := fresh in assert (a ∈ dom Σ1) as H by assumption; pose proof (cls_1 _ _ _ _ _ _ Hc a H)
          | let H := fresh in assert (a ∈ dom ΣC) as H by assumption; pose proof (cls_C _ _ _ _ _ _ Hc a H)
          | let H := fresh in assert (a ∈ dom Σ2) as H by assumption; pose proof (cls_2 _ _ _ _ _ _ a Hc H)
          | let H := fresh in assert (a ∈ dom ΣD) as H by assumption; pose proof (cls_D _ _ _ _ _ _ a Hc H) ].

  (** A held end whose image lies in D comes from the interface. *)
  Local Lemma inD_iface a : held a → ech (h a) ∈ D → a ∈ dom Σ1 ∨ a ∈ dom Σ2.
  Proof.
    intros Ha HD. destruct Ha as [?|[Ha|[?|[Ha|[Ha|Ha]]]]]; try tauto; exfalso; (apply (notD a); [|exact HD]).
    - apply elem_of_union_r. by apply elem_of_chans_of.
    - apply elem_of_union_r. rewrite <-HKD. by apply elem_of_chans_of.
    - set_solver.
    - set_solver.
  Qed.

  (** ** Side conditions for one side; the other side is the mirror *)

  Lemma fs_ok1 (p1 : proc) : p1.1 = C1 → fuse_ok h D1 (Σ1 ∪ ΣC) p1.
  Proof.
    intros Ep1. destruct Hh as (Hd' & Hi & Hp & Hg & Hdp).
    assert (∀ a, pheld (Σ1 ∪ ΣC) p1 a → held a) as Hhe.
    { intros a [Ha|Ha]; [by apply H1C|]. rewrite Ep1 in Ha. unfold held. tauto. }
    split_and!.
    - done.
    - intros a b Ha Hb E. apply hinj; [by apply Hhe|by apply Hhe|done].
    - intros a b Ha Hb E. destruct (hpart a b (Hhe a Ha) (Hhe b Hb) E) as [?|HD]; [by left|right].
      apply DD1. split; [done|]. pose proof (Hhe a Ha) as Ha'. pose proof (Hhe b Hb) as Hb'.
      destruct (inD_iface a Ha' HD) as [A|A]; [|exfalso].
      + split; [by exists a|]. exists b. split; [done|].
        rewrite <-ech_edual, <-E in HD. destruct (inD_iface b Hb' HD) as [B|B]; [done|].
        destruct Ha as [Ha|Ha]; rewrite ?Ep1 in Ha.
        * rewrite dom_union_L, elem_of_union in Ha. destruct Ha as [Ha|Ha]; [|cls a; cls b; tauto].
          (* a ∈ Σ1, b held by p1 and in Σ2 *)
          destruct Hb as [Hb|Hb]; rewrite ?Ep1 in Hb.
          { rewrite dom_union_L, elem_of_union in Hb. cls b. destruct Hb; tauto. }
          { cls b. tauto. }
        * cls a. tauto.
      + destruct Ha as [Ha|Ha]; rewrite ?Ep1 in Ha.
        * rewrite dom_union_L, elem_of_union in Ha. cls a. destruct Ha; tauto.
        * cls a. tauto.
    - intros c Hc1 Hc2. apply elem_of_filter in Hc1 as [_ Hc1]. apply (Hg c); [done|].
      rewrite Ep1 in Hc2. revert Hc2. apply set_map_mono; [done|]. clear. set_solver.
    - intros o' Ho'. apply DD1 in Ho' as (HD & (a & -> & A) & (b & Eb & B)).
      destruct (DD (h a) HD) as (b' & S & x & S' & Eb' & B' & L & L' & Hs).
      exists S, x, S'. split_and!; [|rewrite Eb in L' |- *|done].
      + destruct (kren_lookup_inv _ _ _ _ L) as (a' & Ea & La).
        assert (a' = a) as -> by (apply hinj; [apply H12; by eapply elem_of_dom_2|by apply H1|done]).
        apply kren_lookup; [apply kinj_h, H1C|]. apply lookup_union_Some_raw in La as [La|[_ La]]; [by apply lookup_union_Some_l|].
        exfalso. cls a. apply elem_of_dom_2 in La. tauto.
      + destruct (kren_lookup_inv _ _ _ _ L') as (b2 & E2 & Lb2).
        assert (b2 = b) as -> by (apply hinj; [apply H12; by eapply elem_of_dom_2|by apply H1|done]).
        apply kren_lookup; [apply kinj_h, H1C|]. apply lookup_union_Some_raw in Lb2 as [Lb2|[_ Lb2]]; [by apply lookup_union_Some_l|].
        exfalso. cls b. apply elem_of_dom_2 in Lb2. tauto.
  Qed.

  Lemma fs_pfree1 : pfree E1.
  Proof.
    intros o' H H'. apply DE1 in H as ((a & -> & A) & N). apply DE1 in H' as ((b & Eb & B) & N').
    assert (held a) as Ha by (unfold held; tauto). assert (held b) as Hb by (unfold held; tauto).
    destruct (hpart a b Ha Hb (eq_sym Eb)) as [->|HD].
    - apply (pfree_1C _ _ _ _ _ _ Hc a); rewrite dom_union_L, elem_of_union; tauto.
    - destruct (inD_iface a Ha HD) as [A'|A'].
      + destruct (inD_iface b Hb ltac:(by rewrite <-Eb, ech_edual)) as [B'|B'].
        * apply N. apply DD1. split; [done|]. split; [by exists a|by exists b].
        * cls b. destruct B; tauto.
      + cls a. destruct A; tauto.
  Qed.

  Lemma fs_out1 o' : o' ∈ dom E1 → o' ∉ dom Σf → edual o' ∈ dom E2 ∧ edual o' ∉ dom Σf.
  Proof.
    intros H HΣ. apply DE1 in H as ((a & -> & A) & N). rewrite DΣf in HΣ. rewrite DE2, DΣf.
    assert (held a) as Ha by (unfold held; tauto).
    destruct A as [A|A].
    - assert (ech (h a) ∈ D) as HD.
      { destruct (decide (ech (h a) ∈ D)) as [?|ND]; [done|]. exfalso. apply HΣ. split; [|done]. exists a. tauto. }
      destruct (DD (h a) HD) as (b & S & x & S' & Eb & B & _).
      assert (held b) as Hb by (unfold held; tauto).
      destruct B as [B|B].
      + exfalso. apply N. apply DD1. split; [done|]. split; [by exists a|by exists b].
      + split; [split; [exists b; tauto|]|].
        * rewrite DD2, ech_edual. intros (_ & _ & (a' & Ea & A')). rewrite edual_edual in Ea. assert (held a') as Ha' by (unfold held; tauto).
          rewrite (hinj a a' Ha Ha' Ea) in A. cls a'. tauto.
        * rewrite ech_edual. tauto.
    - cls a. assert (edual a ∈ dom ΣD) as Bd by tauto.
      assert (held (edual a)) as Hb by (unfold held; tauto).
      assert (ech (h (edual a)) ∉ D) as ND.
      { apply notD. apply elem_of_union_r. rewrite ech_edual. by apply elem_of_chans_of. }
      rewrite <-Hd. split; [split; [exists (edual a); tauto|]|].
      + intros HD2. apply DD2 in HD2 as [? _]. tauto.
      + intros [(b & Eb & B) _]. assert (held b) as Hb' by (unfold held; tauto).
        rewrite <-(hinj _ _ Hb Hb' Eb) in B. tauto.
  Qed.

  Lemma fs_types1 o' S1 y1 : E1 !! o' = Some (S1, y1) → o' ∉ dom Σf →
    ∃ S2, E2 !! edual o' = Some (S2, y1‾) ∧ sdual S1 S2.
  Proof.
    intros L HΣ. assert (o' ∈ dom E1) as D1' by (by eapply elem_of_dom_2).
    destruct (fs_out1 o' D1' HΣ) as [DE _]. apply sdrop_lookup in L as [L N].
    destruct (kren_lookup_inv _ _ _ _ L) as (a & -> & La).
    assert (a ∈ dom (Σ1 ∪ ΣC)) as A by (by eapply elem_of_dom_2).
    assert (held a) as Ha by (by apply H1C).
    apply DE2 in DE as [(b & Eb & B) ND2].
    assert (held b) as Hb by (rewrite <-elem_of_union, <-dom_union_L in B; by apply H2D).
    apply lookup_union_Some_raw in La as [La|[Na La]].
    - (* an interface end fused across the cut *)
      assert (ech (h a) ∈ D) as HD.
      { destruct (hpart a b Ha Hb (eq_sym Eb)) as [->|?]; [|done]. exfalso. pose proof (elem_of_dom_2 _ _ _ La) as Da. cls a.
        destruct B; tauto. }
      destruct (DD (h a) HD) as (b' & S & x & S' & _ & _ & L1 & L2 & Hs).
      assert (kren h (Σ1 ∪ Σ2) !! h a = Some (S1, y1)) as L1'.
      { apply kren_lookup; [apply kinj_h, H12|by apply lookup_union_Some_l]. }
      rewrite L1' in L1. injection L1 as <- <-. exists S'. split; [|done].
      apply sdrop_lookup. split; [|done]. rewrite Eb in L2 |- *.
      destruct (kren_lookup_inv _ _ _ _ L2) as (b2 & Eb2 & Lb2).
      assert (b2 = b) as -> by (apply hinj; [apply H12; by eapply elem_of_dom_2|done|done]).
      apply kren_lookup; [apply kinj_h, H2D|]. apply lookup_union_Some_raw in Lb2 as [Lb2|[_ Lb2]].
      + exfalso. apply elem_of_dom_2 in La, Lb2. cls a. cls b. tauto.
      + by apply lookup_union_Some_l.
    - (* a cut end *)
      assert (a ∈ dom ΣC) as AC by (by eapply elem_of_dom_2).
      destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ La) as (S' & L' & Hs).
      exists S'. split; [|done]. rewrite <-Hd. apply sdrop_lookup. split.
      + apply kren_lookup; [apply kinj_h, H2D|]. by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD C1 C2).
      + intros HD2. apply DD2 in HD2 as [HD _]. rewrite Hd, ech_edual in HD. apply (notD a); [|done].
        apply elem_of_union_r. by apply elem_of_chans_of.
  Qed.

  Lemma fs_C1 : set_map (gch h) C1 ∪ D1 ## chans_of E1 ∪ chans_of E2.
  Proof.
    intros c Hc1 Hc2. apply elem_of_union in Hc2.
    destruct Hc2 as [(o' & H & <-)%elem_of_chans_of_iff|(o' & H & <-)%elem_of_chans_of_iff].
    - apply DE1 in H as ((a & -> & A) & N). assert (held a) as Ha by (unfold held; tauto).
      apply elem_of_union in Hc1 as [Hc1|Hc1]; [|done].
      apply elem_of_map in Hc1 as (c0 & E & Hc0). unfold gch in E.
      assert (held (EPos c0)) as Hc0' by (unfold held; simpl; tauto).
      destruct (chinj a (EPos c0) Ha Hc0' E) as [E'|HD].
      + simpl in E'. rewrite <-E' in Hc0. destruct A as [A|A]; cls a; tauto.
      + apply (notD (EPos c0)); [simpl; clear -Hc0; set_solver|by rewrite <-E].
    - apply DE2 in H as ((a & -> & A) & N). assert (held a) as Ha by (unfold held; tauto).
      apply elem_of_union in Hc1 as [Hc1|Hc1].
      + apply elem_of_map in Hc1 as (c0 & E & Hc0). unfold gch in E.
        assert (held (EPos c0)) as Hc0' by (unfold held; simpl; tauto).
        destruct (chinj a (EPos c0) Ha Hc0' E) as [E'|HD].
        * simpl in E'. rewrite <-E' in Hc0. destruct A as [A|A]; cls a; tauto.
        * apply (notD (EPos c0)); [simpl; clear -Hc0; set_solver|by rewrite <-E].
      + apply DD1 in Hc1 as (_ & (b & Eb & B) & _).
        assert (held b) as Hb by (unfold held; tauto).
        rewrite <-(hinj _ _ Hb Ha (eq_sym Eb)) in A. cls b. destruct A; tauto.
  Qed.

  (** ** Side conditions for both sides at once *)

  Lemma fs_disj : dom E1 ## dom E2.
  Proof.
    intros o' H H'. apply DE1 in H as ((a & -> & A) & _). apply DE2 in H' as ((b & Eb & B) & _).
    assert (held a) as Ha by (unfold held; tauto). assert (held b) as Hb by (unfold held; tauto).
    rewrite <-(hinj _ _ Ha Hb Eb) in B. destruct A as [A|A]; cls a; tauto.
  Qed.

  Lemma fs_pfreeΣ : pfree Σf.
  Proof.
    intros o' H H'. apply DΣf in H as ((a & -> & A) & N). apply DΣf in H' as ((b & Eb & B) & _).
    assert (held a) as Ha by (unfold held; tauto). assert (held b) as Hb by (unfold held; tauto).
    destruct (hpart a b Ha Hb (eq_sym Eb)) as [->|HD]; [|done].
    assert (pfree (Σ1 ∪ Σ2)) as Hf by (destruct Hc; by apply pfree_union).
    apply (Hf a); rewrite dom_union_L, elem_of_union; tauto.
  Qed.

  Lemma fs_cover o' v : Σf !! o' = Some v → E1 !! o' = Some v ∨ E2 !! o' = Some v.
  Proof.
    intros H. apply sdrop_lookup in H as [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (a & -> & La).
    apply lookup_union_Some_raw in La as [La|[Na La]].
    - left. apply sdrop_lookup. split.
      + apply kren_lookup; [apply kinj_h, H1C|by apply lookup_union_Some_l].
      + intros HD. apply dside_iff in HD as [? _]. done.
    - right. apply sdrop_lookup. split.
      + apply kren_lookup; [apply kinj_h, H2D|by apply lookup_union_Some_l].
      + intros HD. apply dside_iff in HD as [? _]. done.
  Qed.

  Lemma fs_iface : ConnectSplit.fin Σf E1 ∪ ConnectSplit.fin Σf E2 = Σf.
  Proof. apply fin_union; [apply fs_disj|apply fs_cover]. Qed.

  Lemma fs_CC : set_map (gch h) C1 ∪ D1 ## set_map (gch h) C2 ∪ D2.
  Proof.
    pose proof Hc as Hc0. destruct Hc0 as [_ _ _ _ _ _ _ _ _ HCC _ _].
    assert (∀ c0, c0 ∈ C1 ∪ C2 → gch h c0 ∉ D) as ND.
    { intros c0 Hc0. unfold gch. apply (notD (EPos c0)). simpl. clear -Hc0. set_solver. }
    intros c Hc1 Hc2. apply elem_of_union in Hc1 as [Hc1|Hc1]; apply elem_of_union in Hc2 as [Hc2|Hc2].
    - apply elem_of_map in Hc1 as (c1 & -> & Hc1). apply elem_of_map in Hc2 as (c2 & E & Hc2).
      unfold gch in E. destruct (chinj (EPos c1) (EPos c2)) as [E'|HD]; [unfold held; simpl; tauto|unfold held; simpl; tauto|done| |].
      + simpl in E'. subst. clear -HCC Hc1 Hc2. set_solver.
      + apply (ND c1); [clear -Hc1; set_solver|done].
    - apply elem_of_map in Hc1 as (c1 & -> & Hc1). apply elem_of_filter in Hc2 as [_ Hc2].
      apply (ND c1); [clear -Hc1; set_solver|done].
    - apply elem_of_map in Hc2 as (c2 & -> & Hc2). apply elem_of_filter in Hc1 as [_ Hc1].
      apply (ND c2); [clear -Hc2; set_solver|done].
    - assert (ech (EPos c) ∈ D1) as A by exact Hc1. assert (ech (EPos c) ∈ D2) as B by exact Hc2.
      apply DD1 in A as (_ & (a & Ea & A) & _). apply DD2 in B as (_ & (b & Eb & B) & _).
      rewrite Ea in Eb. rewrite (hinj a b (H1 a A) (H2 b B) Eb) in A. cls b. tauto.
  Qed.

  Lemma fs_chans : set_map (gch h) (C1 ∪ C2 ∪ K) ∪ D =
      (set_map (gch h) C1 ∪ D1) ∪ (set_map (gch h) C2 ∪ D2) ∪ chans_of (fout Σf E1).
  Proof.
    apply set_eq. intros c. split.
    - intros Hc'. apply elem_of_union in Hc' as [Hm|HD].
      + rewrite !set_map_union_L, !elem_of_union in Hm. destruct Hm as [[Hm|Hm]|Hm].
        * clear -Hm. set_solver.
        * clear -Hm. set_solver.
        * apply elem_of_union_r. apply elem_of_map in Hm as (k & -> & Hk).
          apply elem_of_chans_of_iff in Hk as (a & A & <-). rewrite <-(ech_gch h a Hd).
          apply elem_of_chans_of, fout_dom. assert (held a) as Ha by (unfold held; tauto).
          assert (ech (h a) ∉ D) as ND by (apply notD; apply elem_of_union_r; by apply elem_of_chans_of).
          rewrite DE1, DΣf. split.
          { split; [exists a; tauto|]. intros HD1. apply DD1 in HD1 as [? _]. done. }
          intros [(b & Eb & B) _]. assert (held b) as Hb by (unfold held; tauto).
          rewrite <-(hinj _ _ Ha Hb Eb) in B. cls a. tauto.
      + assert (ech (EPos c) ∈ D) as HD' by exact HD.
        destruct (DD (EPos c) HD') as (b & S & x & S' & Eb & B & L & _ & _).
        destruct (kren_lookup_inv _ _ _ _ L) as (a & Ea & La). apply elem_of_dom_2 in La.
        rewrite dom_union_L, elem_of_union in La.
        assert (held a) as Ha by (unfold held; tauto). assert (held b) as Hb by (unfold held; tauto).
        destruct La as [A|A], B as [B|B].
        * do 2 apply elem_of_union_l. apply elem_of_union_r. apply (DD1 (EPos c)). split; [done|]. split; [by exists a|by exists b].
        * apply elem_of_union_r. change c with (ech (EPos c)). apply elem_of_chans_of, fout_dom.
          rewrite DE1, DΣf. split; [split; [exists a; tauto|]|tauto].
          intros HD1. apply DD1 in HD1 as (_ & _ & (b' & Eb' & B')). rewrite Eb in Eb'.
          rewrite (hinj _ _ Hb (H1 b' B') Eb') in B. cls b'. tauto.
        * apply elem_of_union_r. change c with (ech (ENeg c)). apply elem_of_chans_of, fout_dom.
          change (ENeg c) with (edual (EPos c)). rewrite DE1, DΣf, ech_edual. split; [split; [exists b; tauto|]|tauto].
          intros HD1. apply DD1 in HD1 as (_ & (b' & Eb' & B') & _). rewrite Ea in Eb'.
          rewrite (hinj _ _ Ha (H1 b' B') Eb') in A. cls b'. tauto.
        * apply elem_of_union_l, elem_of_union_r, elem_of_union_r. apply (DD2 (EPos c)). split; [done|]. split; [by exists a|by exists b].
    - intros Hc'. rewrite !elem_of_union in Hc'. destruct Hc' as [[[Hm|Hm]|[Hm|Hm]]|Hf].
      + apply elem_of_union_l. rewrite !set_map_union_L. clear -Hm. set_solver.
      + apply elem_of_union_r. by apply elem_of_filter in Hm as [_ ?].
      + apply elem_of_union_l. rewrite !set_map_union_L. clear -Hm. set_solver.
      + apply elem_of_union_r. by apply elem_of_filter in Hm as [_ ?].
      + apply elem_of_chans_of_iff in Hf as (o' & Hf & <-). apply fout_dom in Hf as [H HΣ].
        apply DE1 in H as ((a & -> & A) & N). rewrite DΣf in HΣ.
        destruct (decide (ech (h a) ∈ D)) as [?|ND]; [by apply elem_of_union_r|].
        destruct A as [A|A]; [exfalso; apply HΣ; split; [exists a; tauto|done]|].
        apply elem_of_union_l. rewrite (ech_gch h a Hd). apply elem_of_map_2.
        apply elem_of_union_r. by apply elem_of_chans_of.
  Qed.
End fuse_side.

(** The cut after a fusion of the composite. *)
Lemma fs_sym Σ1 ΣC Σ2 ΣD C1 C2 h D Ep : conn Σ1 ΣC C1 Σ2 ΣD C2 →
  fuse_ok h D (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, Ep) → fuse_ok h D (Σ2 ∪ Σ1) (C2 ∪ C1 ∪ chans_of ΣD, Ep).
Proof.
  intros Hc Hh. pose proof Hc as Hc0. destruct Hc0 as [_ _ Hcut _ _ _ H12 _ _ _ _ _].
  rewrite <-(map_union_comm Σ1 Σ2) by (apply chans_disj_map; done).
  eapply fuse_ok_proc; [|exact Hh]. simpl. rewrite (cut_dual_chans _ _ Hcut). clear. set_solver.
Qed.

Lemma fs_conn Σ1 ΣC Σ2 ΣD C1 C2 h D Ep (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2)
    (Hh : fuse_ok h D (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, Ep)) :
  let Σf := sdrop D (kren h (Σ1 ∪ Σ2)) in
  let E1 := sdrop (dside h Σ1 D) (kren h (Σ1 ∪ ΣC)) in
  let E2 := sdrop (dside h Σ2 D) (kren h (Σ2 ∪ ΣD)) in
  conn (ConnectSplit.fin Σf E1) (fout Σf E1) (set_map (gch h) C1 ∪ dside h Σ1 D)
       (ConnectSplit.fin Σf E2) (fout Σf E2) (set_map (gch h) C2 ∪ dside h Σ2 D).
Proof.
  intros Σf E1 E2. pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs. pose proof (fs_sym _ _ _ _ _ _ _ _ _ Hc Hh) as Hhs.
  assert (Σ1 ∪ Σ2 = Σ2 ∪ Σ1) as E12 by (apply map_union_comm, chans_disj_map; by destruct Hc).
  apply conn_filter.
  - apply (fs_disj _ _ _ _ _ _ Hc h D Ep Hh).
  - apply (fs_pfree1 _ _ _ _ _ _ Hc h D Ep Hh).
  - apply (fs_pfree1 _ _ _ _ _ _ Hcs h D Ep Hhs).
  - apply (fs_pfreeΣ _ _ _ _ _ _ Hc h D Ep Hh).
  - apply (fs_out1 _ _ _ _ _ _ Hc h D Ep Hh).
  - intros o' H HΣ. unfold Σf in *. rewrite E12 in HΣ |- *. by apply (fs_out1 _ _ _ _ _ _ Hcs h D Ep Hhs).
  - apply (fs_types1 _ _ _ _ _ _ Hc h D Ep Hh).
  - apply (fs_CC _ _ _ _ _ _ Hc h D Ep Hh).
  - apply (fs_C1 _ _ _ _ _ _ Hc h D Ep Hh).
  - pose proof (fs_C1 _ _ _ _ _ _ Hcs h D Ep Hhs) as H. unfold E1, E2. clear -H. set_solver.
Qed.
