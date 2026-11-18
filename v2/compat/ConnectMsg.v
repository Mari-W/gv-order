(** * P-Connect, a message across the cut (stage S4)

    The sender holds the cut end o, the receiver its partner. The sender
    moves the ends Σv of its environment and Θe of its restricted
    channels, the receiver receives Θ2 = Σv ∪ Θe. Afterwards the sender
    holds E1, the receiver E2, and the cut is re-split by the interface
    Σ1 ∪ Σ2 ([conn_filter]). The lemmas of [msg_env] read environments
    and channel sets only, so they serve both directions. *)

From GV Require Export compat.ConnectSplit.

Lemma recv_back_sub (Σ Θ2 : senv) : recv_back Σ Θ2 ⊆ set_map ech (dom Θ2).
Proof. intros c (o & Ho & <- & _)%recv_back_elem. by apply elem_of_map_2. Qed.

Lemma recv_env_dom (Σ Θ2 : senv) o : recv_ok Σ Θ2 →
  o ∈ dom (recv_env Σ Θ2) ↔ (o ∈ dom Σ ∧ edual o ∉ dom Θ2) ∨ (o ∈ dom Θ2 ∧ edual o ∉ dom Σ ∧ edual o ∉ dom Θ2).
Proof.
  intros Hok. split.
  - intros [v Hv]%elem_of_dom. apply (recv_env_lookup _ _ _ _ Hok) in Hv as [[A B]|[A B]].
    + left. split; [by eapply elem_of_dom_2|done].
    + right. split; [by eapply elem_of_dom_2|done].
  - intros [[[v A]%elem_of_dom B]|[[v A]%elem_of_dom B]]; apply elem_of_dom; exists v;
      apply (recv_env_lookup _ _ _ _ Hok); auto.
Qed.

(** A channel that a receive restricts is no channel of the environment
    after it. *)
Lemma recv_back_env_disj (Σ Θ2 : senv) : recv_ok Σ Θ2 →
  recv_back Σ Θ2 ## chans_of (recv_env Σ Θ2).
Proof.
  intros Hok c (o & Ho & <- & Hb)%recv_back_elem (o' & Ho' & E)%elem_of_chans_of_iff.
  apply (recv_env_dom _ _ _ Hok) in Ho'. apply ech_eq in E as [->| ->].
  - destruct Ho' as [[A _]|[_ [B C]]]; [|tauto]. by apply ((proj1 Hok) o').
  - rewrite ?edual_edual in *. destruct Ho' as [[_ B]|[_ [_ C]]]; done.
Qed.

Ltac lk_dom := repeat match goal with Hl : lookup _ _ = Some _ |- _ => apply elem_of_dom_2 in Hl end.
Ltac contra_with H := exfalso; generalize H; intro; lk_dom; rewrite ?ech_edual, ?edual_edual in *; naive_solver.

Section msg_env.
  #[local] Set Default Proof Using "All".
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).
  Context (o : cend) (S0 : sty) (x : point) (Lo : ΣC !! o = Some (S0, x)).
  Context (Σv Σr Θe Σe : senv) (Dvr : Σv ##ₘ Σr) (Edel : delete o (Σ1 ∪ ΣC) = Σv ∪ Σr).
  Context (HΘe : ∀ o', o' ∈ dom Θe → ech o' ∈ C1) (Hss : send_split (Σ1 ∪ ΣC) Σe Θe).
  Context (S S' : sty) (y : point) (HSS : sdual S S').

  Local Abbreviation E1 := (<[o := (S, y)]> (Σr ∪ Σe)).
  Local Abbreviation E2' := (<[edual o := (S', y‾)]> (Σ2 ∪ ΣD)).
  Local Abbreviation Θ2 := (Σv ∪ Θe).
  Local Abbreviation E2 := (recv_env E2' Θ2).
  Local Abbreviation Σ := (Σ1 ∪ Σ2).

  Local Lemma HoC : o ∈ dom ΣC.
  Proof. by eapply elem_of_dom_2. Qed.

  Local Lemma Lvr o' v : (Σv ∪ Σr) !! o' = Some v ↔ (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. rewrite <-Edel, lookup_delete_Some. naive_solver. Qed.

  Local Lemma Lv o' v : Σv !! o' = Some v → (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. intros H. apply Lvr. by apply lookup_union_Some_l. Qed.

  Local Lemma Lr o' v : Σr !! o' = Some v → (Σ1 ∪ ΣC) !! o' = Some v ∧ o' ≠ o.
  Proof. intros H. apply Lvr. by apply lookup_union_Some_r. Qed.

  Local Lemma Dv o' : o' ∈ dom Σv → (o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ o' ≠ o.
  Proof.
    intros [v Hv]%elem_of_dom. destruct (Lv _ _ Hv) as [H Hne]. split; [|done].
    destruct (lookup_1C _ _ _ _ H) as [[_ ?]|[_ ?]]; auto.
  Qed.

  Local Lemma Dr o' : o' ∈ dom Σr → (o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ o' ≠ o.
  Proof.
    intros [v Hv]%elem_of_dom. destruct (Lr _ _ Hv) as [H Hne]. split; [|done].
    destruct (lookup_1C _ _ _ _ H) as [[_ ?]|[_ ?]]; auto.
  Qed.

  Local Lemma Ldel o' v : (Σ1 ∪ ΣC) !! o' = Some v → o' ≠ o → Σv !! o' = Some v ∨ (Σv !! o' = None ∧ Σr !! o' = Some v).
  Proof. intros H Hne. apply lookup_union_Some_raw. by apply Lvr. Qed.

  Local Lemma De o' : o' ∈ dom Σe → ech o' ∈ C1 ∧ edual o' ∈ dom Θe ∧ o' ∉ dom Θe.
  Proof.
    intros H. destruct Hss as (_ & Hs2 & _). apply Hs2 in H as [A B]. split; [|done].
    rewrite <-ech_edual. by apply HΘe.
  Qed.

  (** The class of an end of Θ2. *)
  Local Lemma DΘ o' : o' ∈ dom Θ2 → ((o' ∈ dom Σ1 ∨ o' ∈ dom ΣC) ∧ o' ≠ o ∧ o' ∈ dom Σv) ∨ (ech o' ∈ C1 ∧ o' ∈ dom Θe).
  Proof. rewrite dom_union_L, elem_of_union. intros [H|H]; [left; by pose proof (Dv _ H) as [? ?]|right; auto]. Qed.

  Local Lemma LΘ o' v : Θ2 !! o' = Some v → (Σv !! o' = Some v) ∨ (Σv !! o' = None ∧ Θe !! o' = Some v).
  Proof. apply lookup_union_Some_raw. Qed.

  Local Lemma DE2' o' : o' ∈ dom E2' ↔ o' = edual o ∨ o' ∈ dom Σ2 ∨ o' ∈ dom ΣD.
  Proof. rewrite dom_insert_L, dom_union_L. set_solver. Qed.

  Local Lemma not_E2'_c1 o' : ech o' ∈ C1 → o' ∉ dom E2'.
  Proof.
    intros H. rewrite DE2'. destruct (cls_c1 _ _ _ _ _ _ Hc o' H) as (? & ? & ? & ? & ?).
    intros [->|[?|?]]; try done. rewrite ech_edual in H.
    by destruct (cls_C _ _ _ _ _ _ Hc o HoC) as (_ & _ & _ & ? & _).
  Qed.

  Local Lemma not_E2'_1 o' : o' ∈ dom Σ1 → o' ∉ dom E2'.
  Proof.
    intros H. rewrite DE2'. destruct (cls_1 _ _ _ _ _ _ Hc o' H) as (? & ? & ? & _).
    intros [->|[?|?]]; try done. by destruct (cls_C _ _ _ _ _ _ Hc o HoC) as (_ & _ & _ & _ & _ & ? & _).
  Qed.

  Local Lemma not_E2'_C o' : o' ∈ dom ΣC → o' ∉ dom E2'.
  Proof.
    intros H. rewrite DE2'. destruct (cls_C _ _ _ _ _ _ Hc o' H) as (? & ? & ? & _).
    intros [->|[?|?]]; try done. by destruct (cls_C _ _ _ _ _ _ Hc o HoC) as (_ & _ & _ & _ & _ & _ & ? & _).
  Qed.

  Lemma msg_recv_ok : recv_ok E2' Θ2.
  Proof.
    split.
    - intros o' Ho'. destruct (DΘ o' Ho') as [[[H|H] _]|[H _]].
      + by apply not_E2'_1. + by apply not_E2'_C. + by apply not_E2'_c1.
    - intros o' S1 y1 S2' y2 H1 H2. apply LΘ in H1 as [H1|[N1 H1]].
      + destruct (Lv _ _ H1) as [L Hne].
        apply lookup_union_Some_raw in H2 as [H2|[N2 H2]].
        * apply lookup_insert_Some in H2 as [[E _]|[Hne' H2]]; [by apply edual_inj in E|].
          apply lookup_union_Some_raw in H2 as [H2|[_ H2]].
          { exfalso. destruct (lookup_1C _ _ _ _ L) as [[_ D]|[_ D]].
            - contra_with (cls_1 _ _ _ _ _ _ Hc o' D).
            - contra_with (cls_C _ _ _ _ _ _ Hc o' D). }
          destruct (lookup_1C _ _ _ _ L) as [[_ D]|[L' D]].
          { exfalso. contra_with (cls_1 _ _ _ _ _ _ Hc o' D). }
          destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ L') as (S3 & L3 & Hs3).
          rewrite H2 in L3. by injection L3 as -> ->.
        * exfalso. assert (edual o' ∈ dom Θ2) as D' by (by eapply elem_of_dom_2).
          destruct (DΘ _ D') as [[[D|D] _]|[D _]].
          { apply (pfree_1C _ _ _ _ _ _ Hc o'); [by eapply elem_of_dom_2|rewrite dom_union_L; clear -D; set_solver]. }
          { apply (pfree_1C _ _ _ _ _ _ Hc o'); [by eapply elem_of_dom_2|rewrite dom_union_L; clear -D; set_solver]. }
          { rewrite ech_edual in D. destruct (lookup_1C _ _ _ _ L) as [[_ D1]|[_ D1]].
            - contra_with (cls_1 _ _ _ _ _ _ Hc o' D1).
            - contra_with (cls_C _ _ _ _ _ _ Hc o' D1). }
      + assert (ech o' ∈ C1) as Hc1 by (apply HΘe; by eapply elem_of_dom_2).
        destruct Hss as (_ & Hs2 & Hs3). destruct (Hs3 _ _ _ H1) as (S3 & L3 & Hs).
        apply lookup_union_Some_raw in H2 as [H2|[N2 H2]].
        { exfalso. apply (not_E2'_c1 (edual o')); [by rewrite ech_edual|by eapply elem_of_dom_2]. }
        apply lookup_union_Some_raw in H2 as [H2|[N3 H2]].
        { exfalso. assert (edual o' ∈ dom Σv) as D by (by eapply elem_of_dom_2).
          destruct (Dv _ D) as [[D'|D'] _]; rewrite <-ech_edual in Hc1.
          - contra_with (cls_1 _ _ _ _ _ _ Hc _ D').
          - contra_with (cls_C _ _ _ _ _ _ Hc _ D'). }
        apply lookup_union_Some_raw in L3 as [L3|[_ L3]].
        { exfalso. assert (edual o' ∈ dom Σe) as D by (by eapply elem_of_dom_2).
          apply Hs2 in D as [_ D]. apply D. by eapply elem_of_dom_2. }
        rewrite H2 in L3. by injection L3 as -> ->.
  Qed.

  Lemma msg_recv_disj : set_map ech (dom Θ2) ## C2.
  Proof.
    intros c (o' & -> & Ho')%elem_of_map Hc2. destruct (DΘ o' Ho') as [[[H|H] _]|[H _]].
    - contra_with (cls_1 _ _ _ _ _ _ Hc o' H).
    - contra_with (cls_C _ _ _ _ _ _ Hc o' H).
    - contra_with (cls_c1 _ _ _ _ _ _ Hc o' H).
  Qed.
  Local Lemma DE1 o' : o' ∈ dom E1 ↔ o' = o ∨ o' ∈ dom Σr ∨ o' ∈ dom Σe.
  Proof. rewrite dom_insert_L, dom_union_L. set_solver. Qed.

  Local Lemma DE2 o' : o' ∈ dom E2 ↔ (o' ∈ dom E2' ∧ edual o' ∉ dom Θ2) ∨
    (o' ∈ dom Θ2 ∧ edual o' ∉ dom E2' ∧ edual o' ∉ dom Θ2).
  Proof. apply recv_env_dom, msg_recv_ok. Qed.

  Local Lemma Dvr' o' : o' ∈ dom Σv → o' ∉ dom Σr.
  Proof. intros H1 H2. apply map_disjoint_dom in Dvr. by apply (Dvr o'). Qed.

  (** The ends the sender keeps are neither received nor the receiver's. *)
  Local Lemma E1_out o' : o' ∈ dom E1 → o' ∉ dom Θ2 ∧ o' ∉ dom E2'.
  Proof.
    rewrite DE1. intros [->|[H|H]].
    - split.
      + intros D. destruct (DΘ _ D) as [[_ [? _]]|[D' _]]; [done|].
        contra_with (cls_C _ _ _ _ _ _ Hc o HoC).
      + apply not_E2'_C, HoC.
    - destruct (Dr _ H) as [[D|D] Hne]; split.
      + intros D'. destruct (DΘ _ D') as [[_ [_ D'']]|[D'' _]]; [by apply (Dvr' o')|contra_with (cls_1 _ _ _ _ _ _ Hc o' D)].
      + by apply not_E2'_1.
      + intros D'. destruct (DΘ _ D') as [[_ [_ D'']]|[D'' _]]; [by apply (Dvr' o')|contra_with (cls_C _ _ _ _ _ _ Hc o' D)].
      + by apply not_E2'_C.
    - destruct (De _ H) as (H1 & H2 & H3). split.
      + intros D'. destruct (DΘ _ D') as [[[D|D] _]|[_ D]]; [contra_with (cls_1 _ _ _ _ _ _ Hc o' D)|contra_with (cls_C _ _ _ _ _ _ Hc o' D)|done].
      + by apply not_E2'_c1.
  Qed.

  Local Lemma not_Θ2_C o' : o' ∈ dom ΣC → o' ∉ dom Σv → o' ∉ dom Θ2.
  Proof.
    intros H Hv D. destruct (DΘ _ D) as [[_ [_ ?]]|[D' _]]; [done|]. contra_with (cls_C _ _ _ _ _ _ Hc o' H).
  Qed.

  Lemma msg_disj : dom E1 ## dom E2.
  Proof.
    intros o' H1 H2. destruct (E1_out o' H1) as [A B]. apply DE2 in H2 as [[? _]|[? _]]; done.
  Qed.

  Lemma msg_pfree1 : pfree E1.
  Proof.
    intros o' H1 H2. apply DE1 in H1, H2.
    destruct H1 as [->|[H1|H1]].
    - destruct H2 as [E|[H2|H2]]; [by apply (edual_ne o)|..].
      + destruct (Dr _ H2) as [[D|D] _]; contra_with (cls_C _ _ _ _ _ _ Hc o HoC).
      + destruct (De _ H2) as (D & _). contra_with (cls_C _ _ _ _ _ _ Hc o HoC).
    - destruct H2 as [E|[H2|H2]].
      + apply (f_equal edual) in E. rewrite edual_edual in E. subst o'. destruct (Dr _ H1) as [[D|D] _]; contra_with (cls_C _ _ _ _ _ _ Hc o HoC).
      + destruct (Dr _ H1) as [D1 _]. destruct (Dr _ H2) as [D2 _].
        apply (pfree_1C _ _ _ _ _ _ Hc o'); rewrite dom_union_L; clear -D1 D2; set_solver.
      + destruct (De _ H2) as (D & _). destruct (Dr _ H1) as [[D1|D1] _].
        * contra_with (cls_1 _ _ _ _ _ _ Hc o' D1).
        * contra_with (cls_C _ _ _ _ _ _ Hc o' D1).
    - destruct (De _ H1) as (D & D' & D''). destruct H2 as [E|[H2|H2]].
      + rewrite <-ech_edual, E in D. contra_with (cls_C _ _ _ _ _ _ Hc o HoC).
      + rewrite <-ech_edual in D. destruct (Dr _ H2) as [[D1|D1] _].
        * contra_with (cls_1 _ _ _ _ _ _ Hc _ D1).
        * contra_with (cls_C _ _ _ _ _ _ Hc _ D1).
      + destruct (De _ H2) as (_ & E & _). rewrite edual_edual in E. done.
  Qed.

  Lemma msg_pfree2' : pfree E2'.
  Proof.
    intros o' H1 H2. apply DE2' in H1, H2. pose proof (cls_C _ _ _ _ _ _ Hc o HoC) as Co.
    assert (pfree (Σ2 ∪ ΣD)) as Hf by (apply (pfree_1C Σ2 ΣD Σ1 ΣC C2 C1); by apply conn_sym).
    destruct H1 as [->|H1], H2 as [E|H2].
    - by apply (edual_ne (edual o)).
    - rewrite edual_edual in H2. destruct H2; tauto.
    - apply edual_inj in E as ->. destruct H1; tauto.
    - apply (Hf o'); rewrite dom_union_L; clear -H1 H2; set_solver.
  Qed.

  Lemma msg_pfree2 : pfree E2.
  Proof. apply pfree_recv_env; [apply msg_recv_ok|apply msg_pfree2']. Qed.

  Lemma msg_out1 o' : o' ∈ dom E1 → o' ∉ dom Σ → edual o' ∈ dom E2 ∧ edual o' ∉ dom Σ.
  Proof.
    intros H1 HΣ. rewrite dom_union_L, not_elem_of_union in HΣ. destruct HΣ as [N1 N2].
    rewrite dom_union_L, not_elem_of_union, DE2, edual_edual.
    pose proof (E1_out o' H1) as [A B]. apply DE1 in H1 as [->|[H1|H1]].
    - pose proof (cls_C _ _ _ _ _ _ Hc o HoC) as Co. split; [left; split; [apply DE2'; by left|done]|tauto].
    - destruct (Dr _ H1) as [[D|D] _]; [done|]. pose proof (cls_C _ _ _ _ _ _ Hc o' D) as Co.
      split; [left; split; [apply DE2'; tauto|done]|tauto].
    - destruct (De _ H1) as (D & D' & D''). rewrite <-ech_edual in D.
      pose proof (cls_c1 _ _ _ _ _ _ Hc _ D) as Co. split; [|tauto].
      right. split; [rewrite dom_union_L; clear -D'; set_solver|done].
  Qed.

  Lemma msg_out2 o' : o' ∈ dom E2 → o' ∉ dom Σ → edual o' ∈ dom E1 ∧ edual o' ∉ dom Σ.
  Proof.
    intros H2 HΣ. rewrite dom_union_L, not_elem_of_union in HΣ. destruct HΣ as [N1 N2].
    rewrite dom_union_L, not_elem_of_union, DE1. apply DE2 in H2 as [[H2 B]|[H2 [B B']]].
    - apply DE2' in H2 as [->|[H2|H2]]; [|done|].
      + rewrite edual_edual. pose proof (cls_C _ _ _ _ _ _ Hc o HoC) as Co. tauto.
      + pose proof (cls_D _ _ _ _ _ _ o' Hc H2) as Co. destruct Co as (_ & _ & _ & _ & _ & _ & _ & _ & Dc).
        pose proof (cls_C _ _ _ _ _ _ Hc _ Dc) as Co. split; [|tauto].
        destruct (decide (edual o' = o)) as [E|Hne]; [by left|right; left].
        apply elem_of_dom in Dc as [v Hv]. apply lookup_1C_C with (Σ1 := Σ1) (Σ2 := Σ2) (ΣD := ΣD) (C1 := C1) (C2 := C2) in Hv; [|done].
        destruct (Ldel _ _ Hv Hne) as [Lv'|[_ Lr']]; [exfalso; apply B; rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|].
        by eapply elem_of_dom_2.
    - destruct (DΘ _ H2) as [[[D|D] _]|[D D']]; [done| |].
      + exfalso. apply B. apply DE2'. right; right. by destruct (cls_C _ _ _ _ _ _ Hc o' D) as (_ & _ & _ & _ & _ & _ & _ & _ & ?).
      + destruct Hss as (_ & Hs2 & Hs3). apply elem_of_dom in D' as [[S3 y3] L3].
        destruct (Hs3 _ _ _ L3) as (S4 & L4 & _). apply lookup_union_Some_raw in L4 as [L4|[_ L4]].
        * pose proof (cls_c1 _ _ _ _ _ _ Hc _ (eq_ind_r (λ c, c ∈ C1) D (ech_edual o'))) as Co.
          split; [right; right; by eapply elem_of_dom_2|tauto].
        * exfalso. apply B'. rewrite dom_union_L. apply elem_of_union_r. by eapply elem_of_dom_2.
  Qed.
  Local Lemma not_Θ2_of_1C o' : o' ∈ dom ΣC → o' ∉ dom Σv → edual (edual o') ∉ dom Θ2.
  Proof. rewrite edual_edual. apply not_Θ2_C. Qed.

  Lemma msg_types o' S1 y1 : E1 !! o' = Some (S1, y1) → o' ∉ dom Σ →
    ∃ S2, E2 !! edual o' = Some (S2, y1‾) ∧ sdual S1 S2.
  Proof.
    intros H1 HΣ. rewrite dom_union_L, not_elem_of_union in HΣ. destruct HΣ as [N1 N2].
    assert (o' ∈ dom E1) as D1 by (by eapply elem_of_dom_2). destruct (E1_out o' D1) as [A B].
    pose proof msg_recv_ok as Hok.
    apply lookup_insert_Some in H1 as [[<- E]|[Hne H1]].
    - injection E as <- <-. exists S'. split; [|done]. apply (recv_env_lookup _ _ _ _ Hok). left.
      rewrite lookup_insert_eq, edual_edual. done.
    - apply lookup_union_Some_raw in H1 as [H1|[N3 H1]].
      + destruct (Lr _ _ H1) as [L _]. destruct (lookup_1C _ _ _ _ L) as [[_ D]|[L' D]]; [done|].
        destruct Hc as [_ _ [_ Hct] _ _ _ _ _ _ _ _ _]. destruct (Hct _ _ _ L') as (S2 & L2 & Hs).
        exists S2. split; [|done]. apply (recv_env_lookup _ _ _ _ Hok). left. rewrite edual_edual. split; [|done].
        rewrite lookup_insert_ne by (intros E; by apply Hne, edual_inj).
        by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD C1 C2).
      + assert (o' ∈ dom Σe) as De' by (by eapply elem_of_dom_2). destruct (De _ De') as (Dc & D3 & D4).
        apply elem_of_dom in D3 as [[S3 y3] L3]. destruct Hss as (_ & _ & Hs3).
        destruct (Hs3 _ _ _ L3) as (S4 & L4 & Hs). rewrite edual_edual in L4.
        rewrite (lookup_union_Some_l _ _ _ _ H1) in L4. injection L4 as -> ->.
        exists S3. split; [|by apply sdual_sym]. rewrite pt_dual_dual.
        apply (recv_env_lookup _ _ _ _ Hok). right. rewrite edual_edual. split_and!; [|done|done].
        apply lookup_union_Some_raw. right. split; [|done].
        apply not_elem_of_dom. intros D5. rewrite <-ech_edual in Dc.
        destruct (Dv _ D5) as [[D6|D6] _]; [contra_with (cls_1 _ _ _ _ _ _ Hc _ D6)|contra_with (cls_C _ _ _ _ _ _ Hc _ D6)].
  Qed.

  Lemma msg_cover o' v : Σ !! o' = Some v → E1 !! o' = Some v ∨ E2 !! o' = Some v.
  Proof.
    intros H. pose proof msg_recv_ok as Hok. pose proof (cls_C _ _ _ _ _ _ Hc o HoC) as Co.
    apply lookup_union_Some_raw in H as [H|[N H]].
    - assert (o' ∈ dom Σ1) as D by (by eapply elem_of_dom_2). pose proof (cls_1 _ _ _ _ _ _ Hc o' D) as C1'.
      assert (o' ≠ o) as Hne by (intros ->; tauto).
      destruct (Ldel o' v (lookup_union_Some_l _ _ _ _ H) Hne) as [Lv'|[Nv Lr']].
      + right. apply (recv_env_lookup _ _ _ _ Hok). right. split_and!.
        * by apply lookup_union_Some_l.
        * rewrite DE2'. intros [E|[?|?]]; [apply edual_inj in E; done|tauto|tauto].
        * intros D'. destruct (DΘ _ D') as [[[D''|D''] _]|[D'' _]]; [tauto|tauto|rewrite ech_edual in D''; tauto].
      + left. rewrite lookup_insert_ne by done. by apply lookup_union_Some_l.
    - assert (o' ∈ dom Σ2) as D by (by eapply elem_of_dom_2). pose proof (cls_2 _ _ _ _ _ _ o' Hc D) as C2'.
      right. apply (recv_env_lookup _ _ _ _ Hok). left. split.
      + rewrite lookup_insert_ne by (intros <-; tauto). by apply lookup_union_Some_l.
      + intros D'. destruct (DΘ _ D') as [[[D''|D''] _]|[D'' _]]; [tauto|tauto|rewrite ech_edual in D''; tauto].
  Qed.

  Local Abbreviation C1' := (C1 ∖ set_map ech (dom Σv ∪ dom Θe)).
  Local Abbreviation C2' := (C2 ∪ recv_back E2' Θ2).

  Local Lemma chans_E1 c : c ∈ chans_of E1 → c ∈ chans_of ΣC ∪ chans_of Σ1 ∨ c ∈ (set_map ech (dom Θe) : gset chan).
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply DE1 in H as [->|[H|H]].
    - left. apply elem_of_union_l, elem_of_chans_of, HoC.
    - left. destruct (Dr _ H) as [[D|D] _]; [apply elem_of_union_r|apply elem_of_union_l]; by apply elem_of_chans_of.
    - right. destruct (De _ H) as (_ & D & _). rewrite <-ech_edual. by apply elem_of_map_2.
  Qed.

  Local Lemma chans_E2 c : c ∈ chans_of E2 → c ∈ chans_of ΣC ∪ chans_of Σ2 ∨ c ∈ (set_map ech (dom Θ2) : gset chan).
  Proof.
    intros (o' & H & <-)%elem_of_chans_of_iff. apply DE2 in H as [[H _]|[H _]].
    - left. apply DE2' in H as [->|[H|H]].
      + rewrite ech_edual. apply elem_of_union_l, elem_of_chans_of, HoC.
      + apply elem_of_union_r. by apply elem_of_chans_of.
      + apply elem_of_union_l. destruct (cls_D _ _ _ _ _ _ o' Hc H) as (_ & _ & _ & _ & _ & _ & _ & _ & Dc).
        rewrite <-ech_edual. by apply elem_of_chans_of.
    - right. by apply elem_of_map_2.
  Qed.

  Local Lemma chans_Θ2 c : c ∈ (set_map ech (dom Θ2) : gset chan) → c ∈ chans_of ΣC ∪ chans_of Σ1 ∨ c ∈ (set_map ech (dom Θe) : gset chan).
  Proof.
    intros (o' & -> & H)%elem_of_map. destruct (DΘ _ H) as [[[D|D] _]|[_ D]].
    - left. apply elem_of_union_r. by apply elem_of_chans_of.
    - left. apply elem_of_union_l. by apply elem_of_chans_of.
    - right. by apply elem_of_map_2.
  Qed.

  Local Lemma C1_disj c : c ∈ C1 → c ∉ chans_of ΣC ∪ chans_of Σ1 ∪ chans_of Σ2.
  Proof. destruct Hc as [_ _ _ _ _ _ _ _ _ _ HC1 _]. clear -HC1. set_solver. Qed.

  Local Lemma C2_disj c : c ∈ C2 → c ∉ chans_of ΣC ∪ chans_of Σ1 ∪ chans_of Σ2 ∪ C1.
  Proof. destruct Hc as [_ _ _ _ _ _ _ _ _ HCC _ HC2]. clear -HC2 HCC. set_solver. Qed.

  Local Lemma Θe_C1 : (set_map ech (dom Θe) : gset chan) ⊆ C1.
  Proof. intros c (o' & -> & H)%elem_of_map. by apply HΘe. Qed.

  Lemma msg_CC : C1' ## C2'.
  Proof.
    pose proof (recv_back_sub E2' Θ2) as Hb. rewrite dom_union_L, set_map_union_L in Hb.
    destruct Hc as [_ _ _ _ _ _ _ _ _ HCC _ _]. clear -Hb HCC. set_solver.
  Qed.

  Lemma msg_C1 : C1' ## chans_of E1 ∪ chans_of E2.
  Proof.
    intros c Hc1 Hc2. apply elem_of_difference in Hc1 as [Hc1 Hn]. pose proof (C1_disj c Hc1) as N.
    rewrite set_map_union_L in Hn. apply elem_of_union in Hc2 as [H|H].
    - destruct (chans_E1 c H); clear -N Hn H0; set_solver.
    - destruct (chans_E2 c H) as [H'|H']; [clear -N H'; set_solver|].
      rewrite dom_union_L, set_map_union_L in H'. clear -Hn H'. set_solver.
  Qed.

  Lemma msg_C2 : C2' ## chans_of E1 ∪ chans_of E2.
  Proof.
    pose proof msg_recv_ok as Hok. intros c Hc2 Hcc. apply elem_of_union in Hc2 as [Hc2|Hb].
    - pose proof (C2_disj c Hc2) as N. pose proof Θe_C1 as HΘ. apply elem_of_union in Hcc as [H|H].
      + destruct (chans_E1 c H); clear -N H0 HΘ; set_solver.
      + destruct (chans_E2 c H) as [H'|H']; [clear -N H'; set_solver|].
        destruct (chans_Θ2 c H'); clear -N H0 HΘ; set_solver.
    - apply elem_of_union in Hcc as [H|H].
      + apply recv_back_elem in Hb as (o' & Ho' & <- & Hp).
        apply elem_of_chans_of_iff in H as (o'' & H & E). apply ech_eq in E as [->| ->].
        * destruct (E1_out o'' H) as [A _]. done.
        * rewrite edual_edual in Hp. destruct (E1_out o'' H) as [A B]. destruct Hp; done.
      + by apply (recv_back_env_disj E2' Θ2 Hok c).
  Qed.

  Lemma msg_chans : C1 ∪ C2 ∪ chans_of ΣC = C1' ∪ C2' ∪ chans_of (fout Σ E1).
  Proof.
    pose proof (cls_C _ _ _ _ _ _ Hc o HoC) as Co.
    apply set_eq. intros c. split.
    - intros Hc'. apply elem_of_union in Hc' as [Hc'|HK]; [apply elem_of_union in Hc' as [Hc1|Hc2]|].
      + destruct (decide (c ∈ (set_map ech (dom Σv ∪ dom Θe) : gset chan))) as [Hm|Hm]; [|clear -Hc1 Hm; set_solver].
        apply elem_of_map in Hm as (o' & -> & Hm). apply elem_of_union in Hm as [Hm|Hm].
        { exfalso. destruct (Dv _ Hm) as [[D|D] _]; [contra_with (cls_1 _ _ _ _ _ _ Hc _ D)|contra_with (cls_C _ _ _ _ _ _ Hc _ D)]. }
        destruct (decide (edual o' ∈ dom Θe)) as [Hp|Hp].
        * apply elem_of_union_l, elem_of_union_r, elem_of_union_r. apply recv_back_elem.
          exists o'. split_and!; [rewrite dom_union_L; clear -Hm; set_solver|done|right; rewrite dom_union_L; clear -Hp; set_solver].
        * apply elem_of_union_r. destruct Hss as (_ & Hs2 & _).
          assert (edual o' ∈ dom Σe) as De' by (apply Hs2; by rewrite edual_edual).
          rewrite <-ech_edual. apply elem_of_chans_of, fout_dom. split; [apply DE1; by right; right|].
          destruct (De _ De') as (Dc & _). pose proof (cls_c1 _ _ _ _ _ _ Hc _ Dc) as Cc.
          rewrite dom_union_L, not_elem_of_union. tauto.
      + clear -Hc2. set_solver.
      + apply elem_of_chans_of_iff in HK as (o' & HK & <-). destruct (decide (o' = o)) as [->|Hne].
        * apply elem_of_union_r, elem_of_chans_of, fout_dom. split; [apply DE1; by left|].
          rewrite dom_union_L, not_elem_of_union. tauto.
        * pose proof (cls_C _ _ _ _ _ _ Hc o' HK) as Co'. apply elem_of_dom in HK as [v Hv].
          apply (lookup_1C_C Σ1 ΣC Σ2 ΣD C1 C2 Hc) in Hv. destruct (Ldel _ _ Hv Hne) as [Lv'|[_ Lr']].
          { apply elem_of_union_l, elem_of_union_r, elem_of_union_r. apply recv_back_elem.
            exists o'. split_and!; [rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|done|left].
            apply DE2'. tauto. }
          apply elem_of_union_r, elem_of_chans_of, fout_dom. split; [apply DE1; right; left; by eapply elem_of_dom_2|].
          rewrite dom_union_L, not_elem_of_union. tauto.
    - pose proof Θe_C1 as HΘ. intros Hc'. apply elem_of_union in Hc' as [Hc'|Hf]; [apply elem_of_union in Hc' as [Hc1|Hc2]|].
      + clear -Hc1. set_solver.
      + apply elem_of_union in Hc2 as [Hc2|Hb]; [clear -Hc2; set_solver|].
        apply recv_back_elem in Hb as (o' & Ho' & <- & Hp). destruct (DΘ _ Ho') as [[[D|D] _]|[D _]].
        * exfalso. pose proof (cls_1 _ _ _ _ _ _ Hc _ D) as C1'. destruct Hp as [Hp|Hp].
          { apply DE2' in Hp as [E|[?|?]]; [apply edual_inj in E as ->|tauto|tauto]. tauto. }
          { destruct (DΘ _ Hp) as [[[?|?] _]|[D' _]]; [tauto|tauto|rewrite ech_edual in D'; tauto]. }
        * apply elem_of_union_r. by apply elem_of_chans_of.
        * clear -D. set_solver.
      + apply elem_of_chans_of_iff in Hf as (o' & Hf & <-). apply fout_dom in Hf as [H HΣ].
        rewrite dom_union_L, not_elem_of_union in HΣ. destruct HΣ as [N1 _].
        apply DE1 in H as [->|[H|H]].
        * apply elem_of_union_r, elem_of_chans_of, HoC.
        * destruct (Dr _ H) as [[D|D] _]; [done|]. apply elem_of_union_r. by apply elem_of_chans_of.
        * destruct (De _ H) as (D & _). clear -D. set_solver.
  Qed.

  (** The side conditions of P-Connect after the message. *)
  Lemma msg_conn : conn (fin Σ E1) (fout Σ E1) C1' (fin Σ E2) (fout Σ E2) C2'.
  Proof.
    apply conn_filter.
    - apply msg_disj.
    - apply msg_pfree1.
    - apply msg_pfree2.
    - destruct Hc. by apply pfree_union.
    - apply msg_out1.
    - apply msg_out2.
    - apply msg_types.
    - apply msg_CC.
    - apply msg_C1.
    - apply msg_C2.
  Qed.

  Lemma msg_iface : fin Σ E1 ∪ fin Σ E2 = Σ.
  Proof. apply fin_union; [apply msg_disj|apply msg_cover]. Qed.
End msg_env.
