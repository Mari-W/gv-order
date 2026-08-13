(** * Compositionality for terms (Theorem 3.11) and the fundamental
      property, term half (Theorem 3.13)

    One lemma per term rule of Fig. 4: each shows that the semantic
    judgment is closed under the rule, so that the syntactic type
    system is validated rule by rule. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Relation.

(** ** Compositionality for terms (Theorem 3.11)

    One lemma per rule of Fig. 4, with ⊢ replaced by ⊨. The
    structural rules (unit, constants, variables, channels) are proved
    here; the binder/splitting rules are stated and admitted. *)

Lemma grounding_lenv_empty n Σ Δ γ :
  grounding n Σ Δ γ → lenv_empty Δ → Σ = ∅.
Proof.
  induction Δ as [|o Δ' IH] in Σ, γ |- *; simpl; intros Hg HΔ; [done|].
  destruct o as [T|].
  - assert (Some T = None) by (apply HΔ; constructor). done.
  - apply (IH _ (γ ∘ S)); [done|].
    intros o Ho. apply HΔ. rewrite elem_of_cons. auto.
Qed.

Lemma grounding_only n Σ Δ γ x T :
  grounding n Σ Δ γ → lenv_only Δ x T → Vrel n Σ T (γ x).
Proof.
  induction Δ as [|o Δ' IH] in Σ, γ, x |- *; intros Hg [Hlk Huniq]; [done|].
  destruct o as [T0|]; destruct x as [|x']; simpl in *; simplify_eq.
  - (* head available, x = 0 *)
    destruct Hg as (Σ1 & Σ2 & [-> Hdisj] & HV & Hg').
    assert (Σ2 = ∅) as ->.
    { eapply grounding_lenv_empty; [done|]. intros o Ho.
      destruct o as [T'|]; [exfalso|done].
      apply list_elem_of_lookup in Ho as [y Hy].
      by destruct (Huniq (S y) T'). }
    rewrite (right_id ∅ (∪)). exact HV.
  - (* head available, x = S x': contradicts uniqueness *)
    exfalso. by destruct (Huniq 0 T0).
  - (* head absent, x = S x' *)
    apply (IH _ (γ ∘ S) x'); [done|]. split; [done|].
    intros y T' Hy. destruct (Huniq (S y) T') as [Hxy ->]; [done|].
    split; [lia|done].
Qed.

(** Grounding substitutions are downward closed, split along splits of
    Δ, and assign channel-bounded values to available variables. *)
Lemma grounding_down m n Σ Δ γ :
  m ≤ n → grounding n Σ Δ γ → grounding m Σ Δ γ.
Proof.
  intros Hm. induction Δ as [|[T|] Δ' IH] in Σ, γ |- *; simpl; [done| |].
  - intros (Σ1 & Σ2 & Hsp & HV & Hg).
    exists Σ1, Σ2. eauto using Vrel_down.
  - apply IH.
Qed.

Lemma grounding_split n Σ Δ Δ1 Δ2 γ :
  lenv_split Δ Δ1 Δ2 → grounding n Σ Δ γ →
  ∃ Σ1 Σ2, senv_split Σ Σ1 Σ2 ∧ grounding n Σ1 Δ1 γ ∧ grounding n Σ2 Δ2 γ.
Proof.
  intros Hs. revert Σ γ. induction Hs; intros Σ γ Hg; simpl in *.
  - exists ∅, ∅. subst. split_and!; try done.
  - destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & ? & ? & ?). eauto 6.
  - destruct Hg as (Σa & Σb & [-> Hd] & HV & Hg).
    destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & [-> Hd2] & Hg1 & Hg2).
    exists (Σa ∪ Σ1), Σ2. split_and!; [| |done].
    + split; [by senv_perm|senv_disj].
    + exists Σa, Σ1. split_and!; try done. split; [done|senv_disj].
  - destruct Hg as (Σa & Σb & [-> Hd] & HV & Hg).
    destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & [-> Hd2] & Hg1 & Hg2).
    exists Σ1, (Σa ∪ Σ2). split_and!; [|done|].
    + split; [by senv_perm|senv_disj].
    + exists Σa, Σ2. split_and!; try done. split; [done|senv_disj].
  - (* lsplit_unl: the (channel-free) entry goes to both sides *)
    destruct Hg as (Σa & Σb & [-> Hd] & HV & Hg).
    pose proof (Vrel_unl_empty _ _ _ _ ltac:(eassumption) HV) as ->.
    destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & [-> Hd2] & Hg1 & Hg2).
    replace (∅ ∪ (Σ1 ∪ Σ2)) with (Σ1 ∪ Σ2)
      by (by rewrite (left_id (∅ : senv) (∪))).
    exists Σ1, Σ2. split_and!; [by split| |].
    + exists ∅, Σ1. split_and!; try done. apply senv_split_empty_l.
    + exists ∅, Σ2. split_and!; try done. apply senv_split_empty_l.
Qed.

Lemma grounding_fchans n Σ Δ γ x T :
  grounding n Σ Δ γ → Δ !! x = Some (Some T) → fchans (γ x) ⊆ dom Σ.
Proof.
  induction Δ as [|[T0|] Δ' IH] in Σ, γ, x |- *; intros Hg Hx;
    simpl in *; simplify_eq.
  - destruct x as [|x']; simpl in Hx; simplify_eq.
    + destruct Hg as (Σ1 & Σ2 & [-> _] & HV & _).
      pose proof (Vrel_fchans _ _ _ _ HV). senv_dom.
    + destruct Hg as (Σ1 & Σ2 & [-> _] & _ & Hg).
      specialize (IH _ _ _ Hg Hx). senv_dom.
  - destruct x as [|x']; simpl in Hx; simplify_eq.
    exact (IH _ _ _ Hg Hx).
Qed.

(** Closing a tight open term stays within the combined interface
    (grounding values are channel-tight, [grounding_fchans]). *)
Lemma grounding_subst_fchans n Σ Σ' Δ γ e :
  fchans e ⊆ dom Σ → allfv (lenv_avail Δ) e → grounding n Σ' Δ γ →
  fchans (subst γ e) ⊆ dom (Σ ∪ Σ').
Proof.
  intros He Hfv Hg. rewrite dom_union_L.
  etransitivity.
  { apply (fchans_subst e γ (dom Σ')).
    eapply allfv_mono; [|exact Hfv]. intros x (T' & Hx).
    by eapply grounding_fchans. }
  set_solver.
Qed.

(** Variants under one and two binders (the substitution is lifted,
    the new indices contribute no channels). *)
Lemma grounding_subst_fchans_up n Σ Σ' Δ γ e :
  fchans e ⊆ dom Σ → allfv (upP (lenv_avail Δ)) e → grounding n Σ' Δ γ →
  fchans (subst (up γ) e) ⊆ dom (Σ ∪ Σ').
Proof.
  intros He Hfv Hg. rewrite dom_union_L. etransitivity.
  { apply (fchans_subst e (up γ) (dom Σ')).
    eapply allfv_mono; [|exact Hfv].
    intros [|x]; simpl.
    - intros _. set_solver.
    - intros (T' & Hx). unfold compose. rewrite fchans_rename.
      by eapply grounding_fchans. }
  set_solver.
Qed.

Lemma grounding_subst_fchans_up2 n Σ Σ' Δ γ e :
  fchans e ⊆ dom Σ → allfv (upP (upP (lenv_avail Δ))) e →
  grounding n Σ' Δ γ →
  fchans (subst (up (up γ)) e) ⊆ dom (Σ ∪ Σ').
Proof.
  intros He Hfv Hg. rewrite dom_union_L. etransitivity.
  { apply (fchans_subst e (up (up γ)) (dom Σ')).
    eapply allfv_mono; [|exact Hfv].
    intros [|[|x]]; simpl.
    - intros _. set_solver.
    - intros _. unfold compose. simpl. set_solver.
    - intros (T' & Hx). unfold compose. simpl.
      rewrite !fchans_rename. by eapply grounding_fchans. }
  set_solver.
Qed.

(** Conversely, every channel of a grounding's environment occurs in
    the value assigned to some available variable (tightness of V). *)
Lemma grounding_dom n Σ Δ γ ch :
  grounding n Σ Δ γ → ch ∈ dom Σ →
  ∃ x T, Δ !! x = Some (Some T) ∧ ¬ unlimited T ∧ ch ∈ fchans (γ x).
Proof.
  induction Δ as [|[T0|] Δ' IH] in Σ, γ |- *; simpl; intros Hg Hch.
  - subst. rewrite dom_empty_L in Hch. set_solver.
  - destruct Hg as (Σ1 & Σ2 & [-> _] & HV & Hg).
    rewrite dom_union_L in Hch. apply elem_of_union in Hch as [Hch|Hch].
    + exists 0, T0. split_and!; [done| |].
      * (* an unlimited entry owns no channels, so ch cannot be here *)
        intros Hu. rewrite (Vrel_unl_empty _ _ _ _ Hu HV) in Hch.
        rewrite dom_empty_L in Hch. set_solver.
      * rewrite (Vrel_fchans _ _ _ _ HV). done.
    + destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
  - destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
Qed.

(** Groundings of all-□ contexts carry no channels, and are preserved
    by □-weakening (the dropped entries own nothing). *)
Lemma grounding_unl_empty n Σ Δ γ :
  grounding n Σ Δ γ → lenv_unl Δ → Σ = ∅.
Proof.
  induction Δ as [|o Δ' IH] in Σ, γ |- *; simpl; intros Hg HΔ; [done|].
  destruct o as [T|].
  - destruct (HΔ (Some T) ltac:(constructor)) as [?|(U & HU & Hu)]; [done|].
    simplify_eq.
    destruct Hg as (Σ1 & Σ2 & [-> Hd] & HV & Hg').
    rewrite (Vrel_unl_empty _ _ _ _ Hu HV).
    rewrite (IH _ _ Hg'); [by rewrite (left_id ∅ (∪))|].
    intros o Ho. apply HΔ. rewrite elem_of_cons. auto.
  - apply (IH _ (γ ∘ S)); [done|].
    intros o Ho. apply HΔ. rewrite elem_of_cons. auto.
Qed.

Lemma grounding_wk n Σ Δ' Δ γ :
  lenv_wk Δ' Δ → grounding n Σ Δ γ → grounding n Σ Δ' γ.
Proof.
  intros Hwk. revert Σ γ. induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros Σ γ Hg; simpl in *; [done| |].
  - destruct o as [T|]; [|by eauto].
    destruct Hg as (Σ1 & Σ2 & ? & ? & ?). exists Σ1, Σ2. eauto.
  - destruct Hg as (Σ1 & Σ2 & [-> Hd] & HV & Hg').
    rewrite (Vrel_unl_empty _ _ _ _ Hu HV).
    rewrite (left_id ∅ (∪)). eauto.
Qed.

(** A grounding for Δ, x:U also grounds Δ, x:U, y:U by aliasing the
    two variables — an unlimited value owns no channels, so the copy
    costs nothing in the Σ-split. *)
Lemma grounding_contract n Σ Δ U γ :
  unlimited U →
  grounding n Σ (Some U :: Δ) γ →
  grounding n Σ (Some U :: Some U :: Δ) (λ x, γ (pred x)).
Proof.
  intros Hu Hg. simpl in Hg |- *.
  destruct Hg as (Σ1 & Σ2 & Hsp & HV & Hg').
  pose proof (Vrel_unl_empty _ _ _ _ Hu HV) as ->.
  destruct Hsp as [-> Hd].
  exists ∅, Σ2. split_and!; [split; done|exact HV|].
  exists ∅, Σ2. split_and!; [apply senv_split_empty_l|exact HV|exact Hg'].
Qed.

(** Availability across □-weakening. *)
Lemma lenv_wk_avail Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail Δ' x → lenv_avail Δ x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by exists T|].
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
Qed.

Lemma lenv_wk_avail_lin Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail_lin Δ x → lenv_avail_lin Δ' x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx & Hnb); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    + exists T. auto.
    + destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by destruct (Hnb Hu)|].
    destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
Qed.

Lemma lenv_empty_no_avail Δ x : lenv_empty Δ → ¬ lenv_avail Δ x.
Proof.
  intros HΔ (T & Hx). apply list_elem_of_lookup_2 in Hx.
  apply HΔ in Hx. done.
Qed.

(** E-Conv at the value level: a channel inhabits every session type
    with the same unfolding as its stored protocol. *)
Lemma Vrel_sess_conv n Σ s s' v :
  unfoldS s = unfoldS s' →
  Vrel n Σ (TSess s) v → Vrel n Σ (TSess s') v.
Proof.
  rewrite !Vrel_sess_iff. intros Hu (c & s0 & -> & -> & Hu0).
  exists c, s0. split_and!; [done|done|congruence].
Qed.

(** E-Conv: the term relation reads a session result type up to
    unfolding — every clause inspects Σ through [unfoldS] and the type
    only through its head, so conversion costs no steps. *)
Lemma Erel_sess_conv n Σ s s' e :
  unfoldS s = unfoldS s' →
  Erel n Σ (TSess s) e → Erel n Σ (TSess s') e.
Proof.
  revert Σ s s' e. induction n as [n IHn] using lt_wf_ind;
    intros Σ s s' e Hu HE.
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff in HE as (Hval & Hstep).
  apply Erel_S_iff. split.
  { intros Hirr. eapply Vrel_sess_conv; eauto. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c w]; simpl in Hstep |- *.
  - eapply IHn; [lia|done|done].
  - destruct Hstep as (Σ1 & U & u & Hhd & Hc & H).
    exists Σ1, U, u. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HV.
    eapply IHn; [lia|done|]. by apply H.
  - destruct Hstep as (Σ1 & Σ2 & U & u & Hhd & Hd & Hc1 & Hc2 & HV & HE').
    exists Σ1, Σ2, U, u. split_and!; try done.
    eapply IHn; [lia|done|done].
  - destruct Hstep as (Σ1 & Hhd & Hc & HE').
    exists Σ1. split_and!; [done|done|]. eapply IHn; [lia|done|done].
  - destruct Hstep as (c & d & Σ1 & sc & sd & -> & ? & -> & ? & ? & ? & HE').
    eexists _, _, _, _, _. split_and!; [done..|].
    eapply IHn; [lia|done|done].
  - intros Hcd. specialize (Hstep Hcd) as (Σ1 & Σ2 & sf & Hsp & HV & HE').
    exists Σ1, Σ2, sf. split_and!; [done|done|].
    eapply IHn; [lia|done|done].
Qed.

(** ** Canonical values *)

Lemma Vrel_unit n : Vrel n ∅ TUnit EUnit.
Proof. by apply Vrel_unit_iff. Qed.

Lemma Vrel_chan n c s : Vrel n {[c := s]} (TSess s) (Chan c).
Proof. apply Vrel_sess_iff. exists c, s. auto. Qed.

Lemma Vrel_pair n Σ1 Σ2 T U v1 v2 :
  Σ1 ##ₘ Σ2 → Vrel n Σ1 T v1 → Vrel n Σ2 U v2 →
  Vrel n (Σ1 ∪ Σ2) (TProd T U) (Pair v1 v2).
Proof.
  intros. apply Vrel_prod_iff. exists v1, v2, Σ1, Σ2.
  split_and!; auto. by split.
Qed.

Lemma Vrel_inj1 n Σ T U v :
  Vrel n Σ T v → Vrel n Σ (TSum T U) (Inj1 v).
Proof. intros. apply Vrel_sum_iff. left. eauto. Qed.

Lemma Vrel_inj2 n Σ T U v :
  Vrel n Σ U v → Vrel n Σ (TSum T U) (Inj2 v).
Proof. intros. apply Vrel_sum_iff. right. eauto. Qed.

Lemma Vrel_box n T eb :
  fchans eb = ∅ →
  (∀ j, j < n → Erel j ∅ T (subst1 (EBox eb) eb)) →
  Vrel n ∅ (TBox T) (EBox eb).
Proof. intros. apply Vrel_box_iff. eauto. Qed.

(** ** Closure under evaluation frames

    [Erel_bind]: to run [fill_frame f e], run e — while e is not a
    value the composite's transitions are exactly e's, with the
    frame's environment Σf inert — and hand over to the continuation
    once e has become a value (at any index and any environment the
    hole may have evolved to). *)
Lemma Erel_bind n f Σh Σf Th T eh :
  frame_val f → Σh ##ₘ Σf →
  frame_chans f ⊆ dom Σf →
  Erel n Σh Th eh →
  (∀ j Σh' v, j ≤ n → Σh' ##ₘ Σf → Vrel j Σh' Th v →
     Erel j (Σh' ∪ Σf) T (fill_frame f v)) →
  Erel n (Σh ∪ Σf) T (fill_frame f eh).
Proof.
  revert f Σh Σf Th T eh.
  induction n as [n IHn] using lt_wf_ind.
  intros f Σh Σf Th T eh Hf Hd Hfc HE HK.
  destruct (is_val eh) eqn:Hval.
  { assert (is_val eh) as Hv by (by rewrite Hval).
    destruct n as [|n']; [apply Erel_0|].
    apply HK; [lia|done|].
    apply Erel_S_iff in HE as (H1 & _). auto using val_irred. }
  assert (¬ is_val eh) as Hv by (rewrite Hval; intros []).
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. apply Hv.
    assert (irred eh) as Hirr1.
    { intros α eh' Hst. eapply Hirr. by eapply tstep_fill. }
    apply Erel_S_iff in HE as (H1 & _). eauto using Vrel_val. }
  intros α E' Hst.
  apply tstep_fill_inv in Hst as (eh' & Hst & ->); [|done|done].
  pose proof (Erel_S_step _ _ _ _ _ _ HE Hst) as Hc.
  destruct α as [|[c w|c w|c|cd]|c w]; simpl in Hc |- *.
  - (* β *)
    eapply (IHn n'); [lia|done|done|done|done|].
    intros j Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* recv *)
    destruct Hc as (Σh1 & U0 & s & (s0 & -> & Hunf) & Hcd & Hc).
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    exists (Σh1 ∪ Σf), U0, s. split_and!.
    { exists s0. split; [by rewrite insert_union_l|done]. }
    { apply not_elem_of_dom in Hcd. apply not_elem_of_dom.
      by rewrite lookup_union, Hcd, Hcf. }
    intros j Σn Hj Hdn Hcn HV.
    assert (Σn ##ₘ Σh1) by senv_disj.
    assert (Σn ##ₘ Σf) by senv_disj.
    specialize (Hc j Σn Hj ltac:(done) Hcn HV).
    replace (<[c:=s]> (Σh1 ∪ Σf ∪ Σn)) with (<[c:=s]> (Σh1 ∪ Σn) ∪ Σf)
      by senv_perm.
    eapply (IHn j); [lia|done|senv_disj|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* send *)
    destruct Hc as (Σh1 & Σh2 & U0 & s &
                    (s0 & -> & Hunf) & Hd12 & Hc1 & Hc2 & HV & HE').
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    assert (Σh1 ##ₘ Σf) by senv_disj.
    assert (Σh2 ##ₘ Σf) by senv_disj.
    exists (Σh1 ∪ Σf), Σh2, U0, s. split_and!.
    { exists s0. split; [senv_perm|done]. }
    { senv_disj. }
    { apply not_elem_of_dom in Hc1. apply not_elem_of_dom.
      by rewrite lookup_union, Hc1, Hcf. }
    { done. }
    { done. }
    replace (<[c:=s]> (Σh1 ∪ Σf)) with (<[c:=s]> Σh1 ∪ Σf)
      by (by rewrite insert_union_l).
    eapply (IHn n'); [lia|done|senv_disj|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* close *)
    destruct Hc as (Σh1 & (s0 & -> & Hunf) & Hcd & HE').
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    exists (Σh1 ∪ Σf). split_and!.
    { exists s0. split; [by rewrite insert_union_l|done]. }
    { apply not_elem_of_dom in Hcd. apply not_elem_of_dom.
      by rewrite lookup_union, Hcd, Hcf. }
    eapply (IHn n'); [lia|done|done|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* link *)
    destruct Hc as (c & d & Σh1 & sc & sd & -> & Hcd & -> & Hc1 & Hd1
                    & Hdu & HE').
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    apply map_disjoint_insert_l in Hd as [Hdf Hd].
    exists c, d, (Σh1 ∪ Σf), sc, sd. split_and!.
    { done. }
    { done. }
    { by rewrite !insert_union_l. }
    { apply not_elem_of_dom in Hc1. apply not_elem_of_dom.
      by rewrite lookup_union, Hc1, Hcf. }
    { apply not_elem_of_dom in Hd1. apply not_elem_of_dom.
      by rewrite lookup_union, Hd1, Hdf. }
    { done. }
    eapply (IHn n'); [lia|done|done|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* fork *)
    intros Hcdom. rewrite dom_union_L in Hcdom.
    assert (c ∉ dom Σh) as Hch by set_solver.
    assert (c ∉ dom Σf) as Hcf by set_solver.
    destruct (Hc Hch) as (Σa & Σb & s & [-> Hdab] & HV & HE').
    exists Σa, (Σb ∪ Σf), s. split_and!.
    { split; [by rewrite (assoc_L (∪))|senv_disj]. }
    { done. }
    replace (<[c:=dual s]> (Σb ∪ Σf)) with (<[c:=dual s]> Σb ∪ Σf)
      by (by rewrite insert_union_l).
    eapply (IHn n'); [lia|done|senv_disj|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
Qed.

(** ** Semantic head reductions *)

(** Applying a related function to a related argument. *)
Lemma Vrel_app_head n Σ1 Σ2 T U v1 v2 :
  Σ1 ##ₘ Σ2 →
  Vrel n Σ1 (TLolli T U) v1 → Vrel n Σ2 T v2 →
  Erel n (Σ1 ∪ Σ2) U (App v1 v2).
Proof.
  intros Hd HV1 HV2.
  pose proof (Vrel_val _ _ _ _ HV1) as Hv1.
  pose proof (Vrel_val _ _ _ _ HV2) as Hv2.
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff. split_and!.
  { (* an application of a related function is never stuck *)
    intros Hirr. exfalso.
    apply Vrel_lolli_iff in HV1
      as [(eb & -> & Hsup & HL)|(k & -> & -> & Hk)].
    { eapply (Hirr LBeta). apply TStepHead. by apply HeadApp. }
    inversion Hk; subst.
    - eapply (Hirr (LFork (fresh (∅ : gset chan)) v2)).
      apply TStepHead. by apply HeadFork.
    - apply Vrel_sess_iff in HV2 as (c & s0 & -> & -> & _).
      eapply (Hirr (LSess (SRecv c EUnit))). apply TStepHead.
      by apply HeadRecv.
    - apply Vrel_prod_iff in HV2
        as (w & vc & Σa & Σb & -> & Hsp & HVw & HVc).
      apply Vrel_sess_iff in HVc as (c & s0 & -> & -> & _).
      eapply (Hirr (LSess (SSend c w))). apply TStepHead.
      apply HeadSend. eauto using Vrel_val.
    - apply Vrel_sess_iff in HV2 as (c & s0 & -> & -> & _).
      eapply (Hirr (LSess (SClos c))). apply TStepHead. by apply HeadClos.
    - apply Vrel_prod_iff in HV2
        as (vc & vd & Σa & Σb & -> & [-> Hdab] & HVc & HVd).
      apply Vrel_sess_iff in HVc as (c & sc0 & -> & -> & _).
      apply Vrel_sess_iff in HVd as (d & sd0 & -> & -> & _).
      assert (c ≠ d) as Hcd.
      { apply map_disjoint_dom in Hdab. set_solver. }
      eapply (Hirr (LSess (SLink {[c; d]}))). apply TStepHead. by apply HeadLink.
    - apply Vrel_box_iff in HV2 as (_ & eb' & -> & _ & _).
      eapply (Hirr LBeta). apply TStepHead. by apply HeadForce. }
  intros α e'' Hst.
  apply tstep_app_inv in Hst
    as [(e1' & Hst1 & ->)|[(_ & e2' & Hst2 & ->)|(_ & _ & Hhd)]].
  { exfalso. eauto using val_no_tstep. }
  { exfalso. eauto using val_no_tstep. }
  inversion Hhd; subst; simpl.
  - (* HeadApp *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & Hsup & HL)|(k & Heq & _)]; simplify_eq.
    apply HL; [lia|senv_disj|]. eapply Vrel_down; [|done]. lia.
  - (* HeadFork *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    intros Hcdom.
    match type of HV2 with Vrel _ _ (TLolli (TSess ?s) TUnit) _ =>
      exists Σ2, ∅, s end.
    refine (conj _ (conj HV2 _)).
    { split; [senv_perm|apply map_disjoint_empty_r]. }
    apply Vrel_Erel. rewrite insert_empty. apply Vrel_chan.
  - (* HeadRecv *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_sess_iff in HV2 as (c' & s0 & Heqc & Heqs & Hu0).
    simplify_eq.
    match type of Hu0 with _ = unfoldS (SRcv ?t ?s) =>
      exists ∅, t, s end.
    refine (conj _ (conj _ _)).
    { eapply senv_hd_intro; [exact Hu0|senv_perm]. }
    { set_solver. }
    intros j Σn Hj _ Hcn HVw.
    rewrite (left_id ∅ (∪)).
    rewrite insert_as_union; [|done].
    apply Vrel_Erel, Vrel_pair; [|done|apply Vrel_chan].
    by apply map_disjoint_singleton_r, not_elem_of_dom.
  - (* HeadSend *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_prod_iff in HV2
      as (w' & vc & Σa & Σb & Heqp & [-> Hdab] & HVw & HVc).
    simplify_eq.
    apply Vrel_sess_iff in HVc as (c' & s0 & Heqc & -> & Hu0). simplify_eq.
    assert (Σa !! c' = None) as Hca.
    { by apply map_disjoint_singleton_r in Hdab. }
    match type of Hu0 with _ = unfoldS (SSnd ?t ?s) =>
      exists ∅, Σa, t, s end.
    refine (conj _ (conj _ (conj _ (conj _ (conj HVw _))))).
    { eapply senv_hd_intro; [exact Hu0|senv_perm]. }
    { apply map_disjoint_empty_l. }
    { set_solver. }
    { by apply not_elem_of_dom. }
    apply Vrel_Erel. rewrite insert_empty. apply Vrel_chan.
  - (* HeadClos *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_sess_iff in HV2 as (c' & s0 & Heqc & Heqs & Hu0).
    simplify_eq.
    exists ∅. refine (conj _ (conj _ _)).
    { eapply senv_hd_intro; [exact Hu0|senv_perm]. }
    { set_solver. }
    apply Vrel_Erel, Vrel_unit.
  - (* HeadForce *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_box_iff in HV2 as (-> & eb' & Heqb & Hfce & HK).
    simplify_eq.
    rewrite (left_id ∅ (∪)). apply HK. lia.
  - (* HeadLink *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_prod_iff in HV2
      as (vc & vd & Σa & Σb & Heqp & [-> Hdab] & HVc & HVd).
    simplify_eq.
    apply Vrel_sess_iff in HVc as (c' & sc0 & Heqc & -> & Huc). simplify_eq.
    apply Vrel_sess_iff in HVd as (d' & sd0 & Heqd & -> & Hud). simplify_eq.
    assert (c' ≠ d') as Hcd'.
    { apply map_disjoint_dom in Hdab. set_solver. }
    exists c', d', ∅, sc0, sd0. split_and!.
    { done. }
    { done. }
    { senv_perm. }
    { set_solver. }
    { set_solver. }
    { rewrite Hud, <-!dual_unfoldS, Huc. done. }
    apply Vrel_Erel, Vrel_unit.
Qed.

(** Reducing a let-unit / let-pair redex. *)
Lemma Erel_letu_val n Σ T e2 : Erel n Σ T e2 → Erel n Σ T (LetU EUnit e2).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros HE. apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead, HeadLetU. }
  intros α e' Hst.
  apply tstep_letu_inv in Hst as [(e1' & Hst1 & _)|(_ & -> & ->)].
  { exfalso. eapply val_no_tstep; [exact Hst1|done]. }
  simpl. eapply Erel_down; [|done]. lia.
Qed.

Lemma Erel_letp_val n Σ T u v f :
  is_val u → is_val v →
  fchans (LetP (Pair u v) f) ⊆ dom Σ →
  (∀ j, j < n → Erel j Σ T (subst2 u v f)) →
  Erel n Σ T (LetP (Pair u v) f).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros Hu Hv Hfc HK. apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead. by apply HeadLetP. }
  intros α e' Hst.
  apply tstep_letp_inv in Hst
    as [(e1' & Hst1 & _)|(u' & v' & Heq & _ & _ & -> & ->)].
  { exfalso. eapply val_no_tstep; [exact Hst1|]. simpl.
    by apply andb_True. }
  simplify_eq. simpl. apply HK. lia.
Qed.

(** Reducing a case redex on an injected value. *)
Lemma Erel_case_inj1 n Σ T v f1 f2 :
  is_val v →
  fchans (Case (Inj1 v) f1 f2) ⊆ dom Σ →
  (∀ j, j < n → Erel j Σ T (subst1 v f1)) →
  Erel n Σ T (Case (Inj1 v) f1 f2).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros Hv Hfc HK. apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead. by apply HeadCase1. }
  intros α e' Hst.
  apply tstep_case_inv in Hst
    as [(e'' & Hst' & _)|[(v' & Heq & _ & -> & ->)|(v' & Heq & _)]];
    simplify_eq.
  { exfalso. eapply val_no_tstep; [exact Hst'|done]. }
  simpl. apply HK. lia.
Qed.

Lemma Erel_case_inj2 n Σ T v f1 f2 :
  is_val v →
  fchans (Case (Inj2 v) f1 f2) ⊆ dom Σ →
  (∀ j, j < n → Erel j Σ T (subst1 v f2)) →
  Erel n Σ T (Case (Inj2 v) f1 f2).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros Hv Hfc HK. apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead. by apply HeadCase2. }
  intros α e' Hst.
  apply tstep_case_inv in Hst
    as [(e'' & Hst' & _)|[(v' & Heq & _)|(v' & Heq & _ & -> & ->)]];
    simplify_eq.
  { exfalso. eapply val_no_tstep; [exact Hst'|done]. }
  simpl. apply HK. lia.
Qed.

(** Forcing a thunk value: β to the suspended body, with the thunk
    substituted for its own recursive occurrence. *)
Lemma Erel_force_val n T eb :
  fchans eb ⊆ ∅ →
  (∀ j, j < n → Erel j ∅ T (subst1 (EBox eb) eb)) →
  Erel n ∅ T (App EForce (EBox eb)).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros Hfc HK. apply Erel_S_iff. split_and!.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead, HeadForce. }
  intros α e' Hst.
  apply tstep_app_inv in Hst
    as [(e'' & Hst' & _)|[(_ & e'' & Hst' & _)|(_ & _ & Hhd)]].
  { exfalso. eauto using val_no_tstep. }
  { exfalso. eauto using val_no_tstep. }
  inversion Hhd; simplify_eq. simpl. apply HK. lia.
Qed.

(** ** One lemma per term rule of Fig. 4 (Theorem 3.11)

    Kept together and in the order of the figure, so the whole
    family reads as the theorem it adds up to. *)

(** E-Unit *)
Lemma sem_typed_unit Δ : lenv_empty Δ → sem_typed ∅ Δ EUnit TUnit.
Proof.
  intros HΔ. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite level_at_eq. simpl. done.
Qed.

(** E-Const *)
Lemma sem_typed_konst Δ k T :
  lenv_empty Δ → konst_ty k T → sem_typed ∅ Δ (Konst k) T.
Proof.
  intros HΔ Hk. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite level_at_eq.
  destruct Hk; simpl; right; eexists; split_and!; eauto using konst_ty.
Qed.

(** E-LVar *)
Lemma sem_typed_var Δ x T : lenv_only Δ x T → sem_typed ∅ Δ (Var x) T.
Proof.
  intros Ho. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { destruct Ho as [Hlk _]. by exists T. }
  { intros x' (T' & Hx' & _). destruct Ho as [_ Huniq].
    by destruct (Huniq x' T' Hx') as [-> _]. }
  intros n Σ' γ Hdisj Hg. simpl.
  rewrite (left_id ∅ (∪)).
  apply Vrel_Erel. eauto using grounding_only.
Qed.

(** E-Ch *)
Lemma sem_typed_chan Δ c s :
  lenv_empty Δ → sem_typed {[c := s]} Δ (Chan c) (TSess s).
Proof.
  intros HΔ. split_and!; simpl.
  { by rewrite dom_singleton_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite level_at_eq. simpl.
  exists c, s. auto.
Qed.

(** E-Conv, judgment form. *)
Lemma sem_typed_conv Σ Δ e s s' :
  unfoldS s = unfoldS s' →
  sem_typed Σ Δ e (TSess s) → sem_typed Σ Δ e (TSess s').
Proof.
  intros Hu (Hfc & Hfv & Hrv & He). split_and!; [done|done|done|].
  intros n Σ' γ Hd Hg. eapply Erel_sess_conv; [done|]. by apply He.
Qed.

(** E-Abs *)
Lemma sem_typed_lam Σ Δ e T U :
  sem_typed Σ (Some T :: Δ) e U →
  sem_typed Σ Δ (Lam e) (TLolli T U).
Proof.
  intros (Hfc & Hfv & Hrv & He). split_and!; simpl; [done| | |].
  { eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
    - intros _. done.
    - intros (T' & HT'). by exists T'. }
  { intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  apply Vrel_Erel. apply Vrel_lolli_iff. left.
  exists (subst (up γ) e). split_and!; [done| |].
  { (* the substituted body owns exactly the channels of Σ ∪ Σ' *)
    apply (anti_symm (⊆)).
    - etrans; [apply (fchans_subst _ (up γ) (dom Σ'))|].
      + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
        * intros _. set_solver.
        * intros (T' & HT'). unfold compose. rewrite fchans_rename.
          eapply grounding_fchans; eauto.
      + rewrite dom_union_L. set_solver.
    - rewrite dom_union_L. intros ch Hch.
      apply elem_of_union in Hch as [Hch|Hch].
      + rewrite <-Hfc in Hch. by apply fchans_subst_super.
      + destruct (grounding_dom _ _ _ _ _ Hg Hch)
          as (x & T' & Hx & Hnb & Hcx).
        assert (freevar (S x) e) as Hfree
          by (apply Hrv; exists T'; auto).
        pose proof (fchans_subst_free e (S x) (up γ) Hfree) as Hsub.
        simpl in Hsub. unfold compose in Hsub.
        rewrite fchans_rename in Hsub. set_solver. }
  intros j Σn w Hj Hdn HVw.
  rewrite subst1_subst.
  replace (Σ ∪ Σ' ∪ Σn) with (Σ ∪ (Σn ∪ Σ')) by senv_perm.
  apply He.
  - senv_disj.
  - simpl. exists Σn, Σ'. split_and!.
    + split; [done|senv_disj].
    + exact HVw.
    + eapply grounding_down; [|exact Hg]. lia.
Qed.

(** E-App *)
Lemma sem_typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TLolli T U) → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (App e1 e2) U.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx & Hnb). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. exists T'. auto.
    - right. apply Hrv2. exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FAppL (subst γ e2)) _ _ (TLolli T U)); simpl.
  - done.
  - senv_disj.
  - eapply grounding_subst_fchans; [by rewrite Hfc2|exact Hfv2|exact Hg2].
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    replace (Σh' ∪ (Σ2 ∪ Σ'2)) with ((Σ2 ∪ Σ'2) ∪ Σh')
      by (apply map_union_comm; senv_disj).
    apply (Erel_bind j (FAppR v1) _ _ T); simpl.
    + eauto using Vrel_val.
    + senv_disj.
    + rewrite (Vrel_fchans _ _ _ _ HV1). done.
    + eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
    + intros j' Σf' v2 Hj' Hdf HV2.
      replace (Σf' ∪ Σh') with (Σh' ∪ Σf')
        by (apply map_union_comm; senv_disj).
      eapply Vrel_app_head; [senv_disj|..].
      * eapply Vrel_down; [|exact HV1]. lia.
      * exact HV2.
Qed.

(** E-Pair *)
Lemma sem_typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 T → sem_typed Σ2 Δ2 e2 U →
  sem_typed Σ Δ (Pair e1 e2) (TProd T U).
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx & Hnb). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. exists T'. auto.
    - right. apply Hrv2. exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FPairL (subst γ e2)) _ _ T); simpl.
  - done.
  - senv_disj.
  - eapply grounding_subst_fchans; [by rewrite Hfc2|exact Hfv2|exact Hg2].
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    replace (Σh' ∪ (Σ2 ∪ Σ'2)) with ((Σ2 ∪ Σ'2) ∪ Σh')
      by (apply map_union_comm; senv_disj).
    apply (Erel_bind j (FPairR v1) _ _ U); simpl.
    + eauto using Vrel_val.
    + senv_disj.
    + rewrite (Vrel_fchans _ _ _ _ HV1). done.
    + eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
    + intros j' Σf' v2 Hj' Hdf HV2.
      replace (Σf' ∪ Σh') with (Σh' ∪ Σf')
        by (apply map_union_comm; senv_disj).
      apply Vrel_Erel, Vrel_pair; [senv_disj| |done].
      eapply Vrel_down; [|exact HV1]. lia.
Qed.

(** E-Let* *)
Lemma sem_typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 TUnit → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (LetU e1 e2) T.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx & Hnb). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. exists T'. auto.
    - right. apply Hrv2. exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FLetU (subst γ e2)) _ _ TUnit); simpl.
  - done.
  - senv_disj.
  - eapply grounding_subst_fchans; [by rewrite Hfc2|exact Hfv2|exact Hg2].
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    apply Vrel_unit_iff in HV1 as [-> ->].
    rewrite (left_id ∅ (∪)).
    apply Erel_letu_val.
    eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
Qed.

(** E-LetPair *)
Lemma sem_typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TProd U V) →
  sem_typed Σ2 (Some V :: Some U :: Δ2) e2 T →
  sem_typed Σ Δ (LetP e1 e2) T.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl.
      + intros _. done.
      + intros _. done.
      + intros (T' & ?). exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx & Hnb). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. exists T'. auto.
    - right. apply (Hrv2 (S (S x))). exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FLetP (subst (up (up γ)) e2)) _ _ (TProd U V));
    simpl.
  - done.
  - senv_disj.
  - eapply grounding_subst_fchans_up2; [by rewrite Hfc2| |exact Hg2].
    eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl; done.
  - apply He1; [senv_disj|done].
  - intros j Σh' w Hj Hdh HVw.
    apply Vrel_prod_iff in HVw
      as (u & v & Σa & Σb & -> & [-> Hdab] & HVu & HVv).
    apply Erel_letp_val; [eauto using Vrel_val|eauto using Vrel_val| |].
    { simpl.
      rewrite (Vrel_fchans _ _ _ _ HVu), (Vrel_fchans _ _ _ _ HVv).
      assert (fchans (subst (up (up γ)) e2) ⊆ dom (Σ2 ∪ Σ'2)) as Hb.
      { eapply grounding_subst_fchans_up2; [by rewrite Hfc2| |exact Hg2].
        eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl; done. }
      rewrite !dom_union_L in Hb |- *. set_solver. }
    intros j' Hj'.
    rewrite subst2_subst.
    replace (Σa ∪ Σb ∪ (Σ2 ∪ Σ'2)) with (Σ2 ∪ (Σb ∪ (Σa ∪ Σ'2)))
      by senv_perm.
    apply He2.
    { senv_disj. }
    simpl. exists Σb, (Σa ∪ Σ'2). split_and!.
    { split; [done|senv_disj]. }
    { eapply Vrel_down; [|exact HVv]. lia. }
    exists Σa, Σ'2. split_and!.
    { split; [done|senv_disj]. }
    { eapply Vrel_down; [|exact HVu]. lia. }
    eapply grounding_down; [|exact Hg2]. lia.
Qed.

(** E-Inl / E-Inr *)
Lemma sem_typed_inj1 Σ Δ e T U :
  sem_typed Σ Δ e T → sem_typed Σ Δ (Inj1 e) (TSum T U).
Proof.
  intros (Hfc & Hfv & Hrv & He). split_and!; simpl; [done|done|done|].
  intros n Σ' γ Hdisj Hg. simpl.
  replace (Σ ∪ Σ') with ((Σ ∪ Σ') ∪ ∅) by (by rewrite (right_id ∅ (∪))).
  apply (Erel_bind n FInj1 _ _ T); simpl.
  - done.
  - apply map_disjoint_empty_r.
  - set_solver.
  - by apply He.
  - intros j Σh' v Hj Hdh HV.
    rewrite (right_id ∅ (∪)).
    apply Vrel_Erel. by apply Vrel_inj1.
Qed.

Lemma sem_typed_inj2 Σ Δ e T U :
  sem_typed Σ Δ e U → sem_typed Σ Δ (Inj2 e) (TSum T U).
Proof.
  intros (Hfc & Hfv & Hrv & He). split_and!; simpl; [done|done|done|].
  intros n Σ' γ Hdisj Hg. simpl.
  replace (Σ ∪ Σ') with ((Σ ∪ Σ') ∪ ∅) by (by rewrite (right_id ∅ (∪))).
  apply (Erel_bind n FInj2 _ _ U); simpl.
  - done.
  - apply map_disjoint_empty_r.
  - set_solver.
  - by apply He.
  - intros j Σh' v Hj Hdh HV.
    rewrite (right_id ∅ (∪)).
    apply Vrel_Erel. by apply Vrel_inj2.
Qed.

(** E-Case *)
Lemma sem_typed_case Σ Σ1 Σ2 Δ Δ1 Δ2 e e1 e2 U V T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e (TSum U V) →
  sem_typed Σ2 (Some U :: Δ2) e1 T →
  sem_typed Σ2 (Some V :: Δ2) e2 T →
  sem_typed Σ Δ (Case e e1 e2) T.
Proof.
  intros [-> HdΣ] HΔ (Hfc0 & Hfv0 & Hrv0 & He0)
    (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split_and!.
    - eapply allfv_mono; [|exact Hfv0]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv1]. intros [|x]; simpl.
      + intros _. done.
      + intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    - eapply allfv_mono; [|exact Hfv2]. intros [|x]; simpl.
      + intros _. done.
      + intros (T' & ?). exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx & Hnb). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv0. exists T'. auto.
    - right. left. apply (Hrv1 (S x)). exists T'. auto. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  assert (fchans (subst (up γ) e1) ⊆ dom (Σ2 ∪ Σ'2)) as Hk1.
  { eapply grounding_subst_fchans_up; [by rewrite Hfc1| |exact Hg2].
    eapply allfv_mono; [|exact Hfv1]. intros [|x]; simpl; done. }
  assert (fchans (subst (up γ) e2) ⊆ dom (Σ2 ∪ Σ'2)) as Hk2.
  { eapply grounding_subst_fchans_up; [by rewrite Hfc2| |exact Hg2].
    eapply allfv_mono; [|exact Hfv2]. intros [|x]; simpl; done. }
  apply (Erel_bind n (FCase (subst (up γ) e1) (subst (up γ) e2))
           _ _ (TSum U V)); simpl.
  - done.
  - senv_disj.
  - set_solver.
  - apply He0; [senv_disj|done].
  - intros j Σh' w Hj Hdh HVw.
    apply Vrel_sum_iff in HVw as [(v & -> & HVv)|(v & -> & HVv)].
    + apply Erel_case_inj1; [eauto using Vrel_val| |].
      { simpl. rewrite (Vrel_fchans _ _ _ _ HVv).
        rewrite !dom_union_L in Hk1, Hk2 |- *. set_solver. }
      intros j' Hj'.
      rewrite subst1_subst.
      replace (Σh' ∪ (Σ2 ∪ Σ'2)) with (Σ2 ∪ (Σh' ∪ Σ'2)) by senv_perm.
      apply He1.
      { senv_disj. }
      simpl. exists Σh', Σ'2. split_and!.
      { split; [done|senv_disj]. }
      { eapply Vrel_down; [|exact HVv]. lia. }
      eapply grounding_down; [|exact Hg2]. lia.
    + apply Erel_case_inj2; [eauto using Vrel_val| |].
      { simpl. rewrite (Vrel_fchans _ _ _ _ HVv).
        rewrite !dom_union_L in Hk1, Hk2 |- *. set_solver. }
      intros j' Hj'.
      rewrite subst1_subst.
      replace (Σh' ∪ (Σ2 ∪ Σ'2)) with (Σ2 ∪ (Σh' ∪ Σ'2)) by senv_perm.
      apply He2.
      { senv_disj. }
      simpl. exists Σh', Σ'2. split_and!.
      { split; [done|senv_disj]. }
      { eapply Vrel_down; [|exact HVv]. lia. }
      eapply grounding_down; [|exact Hg2]. lia.
Qed.

(** E-Box *)
Lemma sem_typed_box Δ e T :
  lenv_unl Δ →
  sem_typed ∅ (Some (TBox T) :: Δ) e T →
  sem_typed ∅ Δ (EBox e) (TBox T).
Proof.
  intros HΔ (Hfc & Hfv & Hrv & He). split_and!; simpl; [done| | |].
  { eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
    - intros _. done.
    - intros (T' & HT'). by exists T'. }
  { intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto. }
  intros n Σ' γ Hd Hg.
  pose proof (grounding_unl_empty _ _ _ _ Hg HΔ) as ->.
  rewrite (right_id ∅ (∪)). simpl.
  (* the substituted body owns no channels: index 0 is the thunk, which
     is channel-free, and every other free variable is grounded at ∅ *)
  assert (fchans (subst (up γ) e) = ∅) as Hfce.
  { apply (anti_symm (⊆)); [|set_solver].
    etrans; [apply (fchans_subst _ (up γ) ∅)|].
    - eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      + intros _. set_solver.
      + intros (T' & HT'). unfold compose. rewrite fchans_rename.
        etrans; [eapply grounding_fchans; eauto|]. by rewrite dom_empty_L.
    - rewrite Hfc, dom_empty_L. set_solver. }
  (* Lemma 4.3: forcing unrolls one step, so the thunk's membership at
     index m only ever appeals to its membership strictly below m —
     strong induction closes the loop. *)
  assert (∀ m, m ≤ n → Vrel m ∅ (TBox T) (EBox (subst (up γ) e))) as Hall.
  { intros m. induction m as [m IHm] using lt_wf_ind. intros Hm.
    apply Vrel_box; [done|]. intros j Hj.
    rewrite subst1_subst.
    replace (∅ : senv) with (∅ ∪ ∅ : senv)
      by (by rewrite (left_id ∅ (∪))).
    apply He; [apply map_disjoint_empty_l|].
    simpl. exists ∅, ∅. split_and!.
    - apply senv_split_empty_l.
    - apply IHm; lia.
    - eapply grounding_down; [|exact Hg]. lia. }
  apply Vrel_Erel, Hall. lia.
Qed.

(** E-Force, derived: force is a konst, so forcing is application and
    this is an instance of application compositionality — kept as its
    own lemma because the paper states it as a rule. *)
Lemma sem_typed_force Σ Δ e T :
  sem_typed Σ Δ e (TBox T) →
  sem_typed Σ Δ (App EForce e) T.
Proof.
  intros (Hfc & Hfv & Hrv & He). split_and!; simpl.
  - set_solver.
  - by split.
  - intros x Hx. right. by apply Hrv.
  - intros n Σ' γ Hd Hg.
    replace (Σ ∪ Σ') with ((Σ ∪ Σ') ∪ ∅) by (by rewrite (right_id ∅ (∪))).
    apply (Erel_bind n (FAppR EForce) _ _ (TBox T)); simpl.
    + done.
    + apply map_disjoint_empty_r.
    + set_solver.
    + by apply He.
    + intros j Σh' v Hj Hdh HV.
      apply Vrel_box_iff in HV as (-> & eb & -> & Hfce & HK).
      rewrite (left_id ∅ (∪)).
      apply Erel_force_val; [|exact HK]. set_solver.
Qed.

(** □-weakening *)
Lemma sem_typed_wk Σ Δ' Δ e T :
  sem_typed Σ Δ' e T → lenv_wk Δ' Δ → sem_typed Σ Δ e T.
Proof.
  intros (Hfc & Hfv & Hrv & He) Hwk. split_and!; [done| | |].
  - eapply allfv_mono; [|exact Hfv]. intros x Hx.
    eauto using lenv_wk_avail.
  - intros x Hx. apply Hrv. eauto using lenv_wk_avail_lin.
  - intros n Σ' γ Hd Hg. apply He; [done|].
    eapply grounding_wk; eauto.
Qed.

(** □-contraction (E-Contract): a duplicated unlimited hypothesis may
    be contracted, replacing the inner variable by the outer one
    (e[x/y] = rename pred e: indices 0,1 ↦ 0 and n+2 ↦ n+1).  For the
    paper's rule instantiate W := □T ([unlimited_box]). *)
Lemma sem_typed_contract Σ Δ U W e :
  unlimited W →
  sem_typed Σ (Some W :: Some W :: Δ) e U →
  sem_typed Σ (Some W :: Δ) (rename pred e) U.
Proof.
  intros Hu (Hfc & Hfv & Hrv & He). split_and!.
  - by rewrite fchans_rename.
  - apply allfv_rename. eapply allfv_mono; [|exact Hfv].
    intros [|[|x]] Hx; [by eexists|by eexists|exact Hx].
  - intros [|x] Hx.
    + destruct Hx as (T' & HT' & Hl). simpl in HT'. simplify_eq. done.
    + destruct Hx as (T' & HT' & Hl).
      apply (freevar_rename _ (S (S x)) pred). apply Hrv. by exists T'.
  - intros n Σ' γ Hd Hg. rewrite subst_rename.
    apply He; [done|]. by apply grounding_contract.
Qed.

(** □-weakening in cons form (E-Weak): a fresh unlimited hypothesis
    may be added, shifting the term — the paper's Δ ⊢ e becomes
    Δ, x:W ⊢ e with x unused.  (Contrast [sem_typed_wk], which
    un-spends entries positionally via [lenv_wk].) *)
Lemma sem_typed_weaken Σ Δ W U e :
  unlimited W →
  sem_typed Σ Δ e U →
  sem_typed Σ (Some W :: Δ) (rename S e) U.
Proof.
  intros Hu (Hfc & Hfv & Hrv & He). split_and!.
  - by rewrite fchans_rename.
  - apply allfv_rename. eapply allfv_mono; [|exact Hfv].
    intros x (T' & HT'). by exists T'.
  - intros [|x] Hx.
    + destruct Hx as (T' & HT' & Hl). simpl in HT'. simplify_eq. done.
    + destruct Hx as (T' & HT' & Hl).
      apply (freevar_rename _ x S). apply Hrv. by exists T'.
  - intros n Σ' γ Hd Hg. rewrite subst_rename.
    simpl in Hg. destruct Hg as (Σ1 & Σ2 & Hsp & HV & Hg').
    pose proof (Vrel_unl_empty _ _ _ _ Hu HV) as ->.
    destruct Hsp as [-> Hd2].
    apply map_disjoint_union_l in Hd as [_ Hd].
    rewrite (left_id ∅ (∪)).
    apply He; [done|exact Hg'].
Qed.

(** ** The fundamental property for terms (Theorem 3.13, term half;
    the process half lives in Compositionality.v) *)

Theorem fundamental_term Σ Δ e T : typed Σ Δ e T → sem_typed Σ Δ e T.
Proof.
  induction 1.
  - by apply sem_typed_unit.
  - by apply sem_typed_konst.
  - by apply sem_typed_var.
  - by apply sem_typed_chan.
  - by apply sem_typed_lam.
  - by eapply sem_typed_app.
  - by eapply sem_typed_pair.
  - by eapply sem_typed_letu.
  - by eapply sem_typed_letp.
  - by apply sem_typed_inj1.
  - by apply sem_typed_inj2.
  - by eapply sem_typed_case.
  - by apply sem_typed_box.
  - by eapply sem_typed_wk.
  - by eapply sem_typed_conv.
Qed.
