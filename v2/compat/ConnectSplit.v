(** * P-Connect, re-splitting a cut (stage S4)

    After a step of the composite the two components hold new
    environments E1 and E2. The composite keeps an interface Σ, and the
    rest of E1 and E2 is the new cut. [conn_filter] gives the side
    conditions of P-Connect for the split by Σ from conditions on E1, E2
    and Σ alone. *)

From GV Require Export compat.Connect.

(** The ends of E in the interface Σ, and the rest. *)
Definition fin (Σ E : senv) : senv := filter (λ kv : cend * (sty * point), kv.1 ∈ dom Σ) E.
Definition fout (Σ E : senv) : senv := filter (λ kv : cend * (sty * point), kv.1 ∉ dom Σ) E.

Lemma fin_fout (Σ E : senv) : fin Σ E ∪ fout Σ E = E.
Proof. apply map_filter_union_complement. Qed.

Lemma fin_fout_disj (Σ E : senv) : fin Σ E ##ₘ fout Σ E.
Proof. apply map_disjoint_filter_complement. Qed.

Lemma fin_lookup (Σ E : senv) o v : fin Σ E !! o = Some v ↔ E !! o = Some v ∧ o ∈ dom Σ.
Proof. unfold fin. by rewrite map_lookup_filter_Some. Qed.

Lemma fout_lookup (Σ E : senv) o v : fout Σ E !! o = Some v ↔ E !! o = Some v ∧ o ∉ dom Σ.
Proof. unfold fout. by rewrite map_lookup_filter_Some. Qed.

Lemma fin_dom (Σ E : senv) o : o ∈ dom (fin Σ E) ↔ o ∈ dom E ∧ o ∈ dom Σ.
Proof.
  split.
  - intros [w Hw]%elem_of_dom. apply fin_lookup in Hw as [? ?]. split; [by eapply elem_of_dom_2|done].
  - intros [[w Hw]%elem_of_dom Ho]. apply elem_of_dom. exists w. by apply fin_lookup.
Qed.

Lemma fout_dom (Σ E : senv) o : o ∈ dom (fout Σ E) ↔ o ∈ dom E ∧ o ∉ dom Σ.
Proof.
  split.
  - intros [w Hw]%elem_of_dom. apply fout_lookup in Hw as [? ?]. split; [by eapply elem_of_dom_2|done].
  - intros [[w Hw]%elem_of_dom Ho]. apply elem_of_dom. exists w. by apply fout_lookup.
Qed.

Lemma elem_of_chans_of_iff c (Σ : senv) : c ∈ chans_of Σ ↔ ∃ o, o ∈ dom Σ ∧ ech o = c.
Proof. unfold chans_of. rewrite elem_of_map. split; intros (o & ? & ?); eauto. Qed.

(** The interface is the union of the two parts in it. *)
Lemma fin_union (Σ E1 E2 : senv) :
  dom E1 ## dom E2 → (∀ o v, Σ !! o = Some v → E1 !! o = Some v ∨ E2 !! o = Some v) →
  fin Σ E1 ∪ fin Σ E2 = Σ.
Proof.
  intros Hd HΣ. apply map_eq. intros o. rewrite lookup_union.
  destruct (Σ !! o) as [v|] eqn:Ho.
  - destruct (HΣ o v Ho) as [H|H].
    + assert (fin Σ E1 !! o = Some v) as -> by (apply fin_lookup; split; [done|by eapply elem_of_dom_2]).
      by destruct (fin Σ E2 !! o).
    + assert (fin Σ E2 !! o = Some v) as -> by (apply fin_lookup; split; [done|by eapply elem_of_dom_2]).
      destruct (fin Σ E1 !! o) as [v'|] eqn:H1; [|done].
      exfalso. apply fin_lookup in H1 as [H1 _]. apply (Hd o); by eapply elem_of_dom_2.
  - assert (o ∉ dom Σ) as Hn by (by apply not_elem_of_dom).
    assert (fin Σ E1 !! o = None) as -> by (apply eq_None_not_Some; intros [? (_ & ?)%fin_lookup]; done).
    assert (fin Σ E2 !! o = None) as -> by (apply eq_None_not_Some; intros [? (_ & ?)%fin_lookup]; done).
    done.
Qed.

Lemma chans_of_mono (Σ Σ' : senv) : dom Σ ⊆ dom Σ' → chans_of Σ ⊆ chans_of Σ'.
Proof. intros H c. rewrite !elem_of_chans_of_iff. intros (o & ? & ?). exists o. split; [set_solver|done]. Qed.

Lemma chans_of_fin (Σ E : senv) : chans_of (fin Σ E) ⊆ chans_of E.
Proof. apply chans_of_mono. intros o Ho. by apply fin_dom in Ho as [? _]. Qed.

Lemma chans_of_fout (Σ E : senv) : chans_of (fout Σ E) ⊆ chans_of E.
Proof. apply chans_of_mono. intros o Ho. by apply fout_dom in Ho as [? _]. Qed.

Lemma pfree_sub (Σ Σ' : senv) : dom Σ ⊆ dom Σ' → pfree Σ' → pfree Σ.
Proof. intros H Hf o Ho Ho'. apply (Hf o); set_solver. Qed.

(** The side conditions of P-Connect for the split by Σ. *)
Lemma conn_filter (Σ E1 E2 : senv) (C1 C2 : gset chan) :
  dom E1 ## dom E2 → pfree E1 → pfree E2 → pfree Σ →
  (∀ o, o ∈ dom E1 → o ∉ dom Σ → edual o ∈ dom E2 ∧ edual o ∉ dom Σ) →
  (∀ o, o ∈ dom E2 → o ∉ dom Σ → edual o ∈ dom E1 ∧ edual o ∉ dom Σ) →
  (∀ o S y, E1 !! o = Some (S, y) → o ∉ dom Σ → ∃ S', E2 !! edual o = Some (S', y‾) ∧ sdual S S') →
  C1 ## C2 → C1 ## chans_of E1 ∪ chans_of E2 → C2 ## chans_of E1 ∪ chans_of E2 →
  conn (fin Σ E1) (fout Σ E1) C1 (fin Σ E2) (fout Σ E2) C2.
Proof.
  intros Hd Hf1 Hf2 HfΣ H12 H21 Ht HCC HC1 HC2.
  pose proof (chans_of_fin Σ E1) as Hs1. pose proof (chans_of_fin Σ E2) as Hs2.
  pose proof (chans_of_fout Σ E1) as Hs3. pose proof (chans_of_fout Σ E2) as Hs4.
  constructor.
  - apply fin_fout_disj.
  - apply fin_fout_disj.
  - split.
    + intros o. rewrite !fout_dom. split.
      * intros [Ho Hn]. by apply H21.
      * intros [Ho Hn]. destruct (H12 _ Ho Hn) as [A B]. rewrite edual_edual in A, B. done.
    + intros o S y (Hl & Hn)%fout_lookup. destruct (Ht _ _ _ Hl Hn) as (S' & A & B).
      exists S'. split; [|done]. apply fout_lookup. split; [done|].
      apply (H12 o); [by eapply elem_of_dom_2|done].
  - apply (pfree_sub _ Σ); [intros o Ho; by apply fin_dom in Ho as [_ ?]|done].
  - apply (pfree_sub _ Σ); [intros o Ho; by apply fin_dom in Ho as [_ ?]|done].
  - apply (pfree_sub _ E1); [intros o Ho; by apply fout_dom in Ho as [? _]|done].
  - intros c. rewrite !elem_of_chans_of_iff. intros (o1 & H1 & <-) (o2 & H2 & E).
    apply fin_dom in H1 as [A1 B1]. apply fin_dom in H2 as [A2 B2].
    symmetry in E. apply ech_eq in E as [->| ->]; [by apply (Hd o1)|by apply (HfΣ o1)].
  - intros c. rewrite !elem_of_chans_of_iff. intros (o1 & H1 & <-) (o2 & H2 & E).
    apply fin_dom in H1 as [A1 B1]. apply fout_dom in H2 as [A2 B2].
    symmetry in E. apply ech_eq in E as [->| ->]; [done|by apply (Hf1 o1)].
  - intros c. rewrite !elem_of_chans_of_iff. intros (o1 & H1 & <-) (o2 & H2 & E).
    apply fin_dom in H1 as [A1 B1]. apply fout_dom in H2 as [A2 B2].
    symmetry in E. apply ech_eq in E as [->| ->]; [by apply (Hd o1)|].
    destruct (H12 _ A2 B2) as [_ B]. rewrite edual_edual in B. done.
  - done.
  - clear -Hs1 Hs2 Hs3 HC1. set_solver.
  - clear -Hs1 Hs2 Hs3 HC2. set_solver.
Qed.

(** ** Lookups in the environment after a receive *)

Lemma recv_env_lookup (Σ Θ2 : senv) o v :
  recv_ok Σ Θ2 →
  recv_env Σ Θ2 !! o = Some v ↔
    (Σ !! o = Some v ∧ edual o ∉ dom Θ2) ∨
    (Θ2 !! o = Some v ∧ edual o ∉ dom Σ ∧ edual o ∉ dom Θ2).
Proof.
  intros [Hok _]. unfold recv_env. rewrite lookup_union_Some_raw, !map_lookup_filter_Some, map_lookup_filter_None.
  simpl. split.
  - intros [[A B]|[_ C]]; [by left|by right].
  - intros [[A B]|[A B]].
    + by left.
    + right. split; [|done]. left.
      apply not_elem_of_dom. apply Hok. by eapply elem_of_dom_2.
Qed.

Lemma recv_back_elem (Σ Θ2 : senv) c :
  c ∈ recv_back Σ Θ2 ↔ ∃ o, o ∈ dom Θ2 ∧ ech o = c ∧ (edual o ∈ dom Σ ∨ edual o ∈ dom Θ2).
Proof.
  unfold recv_back. rewrite elem_of_map. split.
  - intros (o & -> & Ho). apply elem_of_filter in Ho as [A B]. eauto.
  - intros (o & A & <- & B). exists o. split; [done|]. by apply elem_of_filter.
Qed.

Lemma pfree_union (Σ1 Σ2 : senv) : pfree Σ1 → pfree Σ2 → chans_of Σ1 ## chans_of Σ2 → pfree (Σ1 ∪ Σ2).
Proof.
  intros H1 H2 H12 o. rewrite !dom_union_L, !elem_of_union. intros Ho Ho'.
  destruct Ho as [Ho|Ho], Ho' as [Ho'|Ho'].
  - by apply (H1 o).
  - apply (H12 (ech o)); [by apply elem_of_chans_of|]. rewrite <-ech_edual. by apply elem_of_chans_of.
  - apply (H12 (ech o)); [|by apply elem_of_chans_of]. rewrite <-ech_edual. by apply elem_of_chans_of.
  - by apply (H2 o).
Qed.

(** ** The classes of an end under a cut

    An end lies in at most one of Σ1, ΣC, Σ2, ΣD, the channels C1 and
    C2, and its partner lies only where the cut puts it. *)
Section classes.
  Context (Σ1 ΣC Σ2 ΣD : senv) (C1 C2 : gset chan) (Hc : conn Σ1 ΣC C1 Σ2 ΣD C2).

  Lemma cls_1 o : o ∈ dom Σ1 →
    o ∉ dom ΣC ∧ o ∉ dom Σ2 ∧ o ∉ dom ΣD ∧ ech o ∉ C1 ∧ ech o ∉ C2 ∧
    edual o ∉ dom Σ1 ∧ edual o ∉ dom ΣC ∧ edual o ∉ dom Σ2 ∧ edual o ∉ dom ΣD.
  Proof.
    intros Ho. destruct Hc as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    assert (ech o ∈ chans_of Σ1) as Hch by (by apply elem_of_chans_of).
    assert (∀ o' (X : senv), o' ∈ dom X → ech o' ∈ chans_of X) as Hx by (intros; by apply elem_of_chans_of).
    split_and!.
    - intros H. apply Hx in H. clear -H Hch H1C. set_solver.
    - intros H. apply Hx in H. clear -H Hch H12. set_solver.
    - intros H. apply Hx in H. rewrite HKD in H. clear -H Hch H1C. set_solver.
    - intros H. clear -H Hch HC1. set_solver.
    - intros H. clear -H Hch HC2. set_solver.
    - by apply Hf1.
    - intros H. apply Hx in H. rewrite ech_edual in H. clear -H Hch H1C. set_solver.
    - intros H. apply Hx in H. rewrite ech_edual in H. clear -H Hch H12. set_solver.
    - intros H. apply Hx in H. rewrite ech_edual, HKD in H. clear -H Hch H1C. set_solver.
  Qed.

  Lemma cls_C o : o ∈ dom ΣC →
    o ∉ dom Σ1 ∧ o ∉ dom Σ2 ∧ o ∉ dom ΣD ∧ ech o ∉ C1 ∧ ech o ∉ C2 ∧
    edual o ∉ dom Σ1 ∧ edual o ∉ dom ΣC ∧ edual o ∉ dom Σ2 ∧ edual o ∈ dom ΣD.
  Proof.
    intros Ho. destruct Hc as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    assert (ech o ∈ chans_of ΣC) as Hch by (by apply elem_of_chans_of).
    assert (∀ o' (X : senv), o' ∈ dom X → ech o' ∈ chans_of X) as Hx by (intros; by apply elem_of_chans_of).
    split_and!.
    - intros H. apply Hx in H. clear -H Hch H1C. set_solver.
    - intros H. apply Hx in H. clear -H Hch H2C. set_solver.
    - intros H. apply (proj1 Hcut) in H. by apply (HfC o).
    - intros H. clear -H Hch HC1. set_solver.
    - intros H. clear -H Hch HC2. set_solver.
    - intros H. apply Hx in H. rewrite ech_edual in H. clear -H Hch H1C. set_solver.
    - by apply HfC.
    - intros H. apply Hx in H. rewrite ech_edual in H. clear -H Hch H2C. set_solver.
    - apply (proj1 Hcut). by rewrite edual_edual.
  Qed.

  Lemma cls_c1 o : ech o ∈ C1 →
    o ∉ dom Σ1 ∧ o ∉ dom ΣC ∧ o ∉ dom Σ2 ∧ o ∉ dom ΣD ∧ ech o ∉ C2.
  Proof.
    intros Ho. destruct Hc as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof (cut_dual_chans _ _ Hcut) as HKD.
    assert (∀ o' (X : senv), o' ∈ dom X → ech o' ∈ chans_of X) as Hx by (intros; by apply elem_of_chans_of).
    split_and!; intros H; try apply Hx in H; rewrite ?HKD in H; clear -H Ho HC1 HCC; set_solver.
  Qed.

  Lemma lookup_1C o v : (Σ1 ∪ ΣC) !! o = Some v → (Σ1 !! o = Some v ∧ o ∈ dom Σ1) ∨ (ΣC !! o = Some v ∧ o ∈ dom ΣC).
  Proof.
    intros H. apply lookup_union_Some_raw in H as [H|[_ H]]; [left|right]; split; try done; by eapply elem_of_dom_2.
  Qed.

  Lemma lookup_1C_C o v : ΣC !! o = Some v → (Σ1 ∪ ΣC) !! o = Some v.
  Proof.
    intros H. apply lookup_union_Some_raw. right. split; [|done].
    apply not_elem_of_dom. apply (cls_C o). by eapply elem_of_dom_2.
  Qed.

  Lemma lookup_2D_D o v : ΣD !! o = Some v → (Σ2 ∪ ΣD) !! o = Some v.
  Proof.
    intros H. apply lookup_union_Some_raw. right. split; [|done].
    apply not_elem_of_dom. intros H2. destruct Hc as [_ _ Hcut _ _ _ _ _ H2C _ _ _].
    apply (H2C (ech o)); [by apply elem_of_chans_of|]. rewrite <-(cut_dual_chans _ _ Hcut).
    apply elem_of_chans_of. by eapply elem_of_dom_2.
  Qed.

  Lemma pfree_1C : pfree (Σ1 ∪ ΣC).
  Proof. destruct Hc. by apply pfree_union. Qed.
End classes.

Lemma cls_2 Σ1 ΣC Σ2 ΣD C1 C2 o : conn Σ1 ΣC C1 Σ2 ΣD C2 → o ∈ dom Σ2 →
  o ∉ dom ΣD ∧ o ∉ dom Σ1 ∧ o ∉ dom ΣC ∧ ech o ∉ C2 ∧ ech o ∉ C1 ∧
  edual o ∉ dom Σ2 ∧ edual o ∉ dom ΣD ∧ edual o ∉ dom Σ1 ∧ edual o ∉ dom ΣC.
Proof. intros Hc. apply (cls_1 Σ2 ΣD Σ1 ΣC C2 C1). by apply conn_sym. Qed.

Lemma cls_D Σ1 ΣC Σ2 ΣD C1 C2 o : conn Σ1 ΣC C1 Σ2 ΣD C2 → o ∈ dom ΣD →
  o ∉ dom Σ2 ∧ o ∉ dom Σ1 ∧ o ∉ dom ΣC ∧ ech o ∉ C2 ∧ ech o ∉ C1 ∧
  edual o ∉ dom Σ2 ∧ edual o ∉ dom ΣD ∧ edual o ∉ dom Σ1 ∧ edual o ∈ dom ΣC.
Proof. intros Hc. apply (cls_C Σ2 ΣD Σ1 ΣC C2 C1). by apply conn_sym. Qed.

(** A pair of partners in the environment after a receive is a pair
    before it. *)
Lemma pfree_recv_env (Σ Θ2 : senv) : recv_ok Σ Θ2 → pfree Σ → pfree (recv_env Σ Θ2).
Proof.
  intros Hok Hf o Ho Ho'. apply elem_of_dom in Ho as [v Hv], Ho' as [v' Hv'].
  apply (recv_env_lookup _ _ _ _ Hok) in Hv, Hv'. rewrite edual_edual in Hv'.
  destruct Hv as [[A B]|[A B]], Hv' as [[A' B']|[A' B']].
  - apply (Hf o); by eapply elem_of_dom_2.
  - apply B. by eapply elem_of_dom_2.
  - apply B'. by eapply elem_of_dom_2.
  - apply (proj2 B). by eapply elem_of_dom_2.
Qed.
