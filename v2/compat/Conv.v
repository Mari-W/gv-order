(** * R^κ along environments up to ≈ (stage S4)

    Two environments are ≈ when they hold the same ends at the same
    points with session types ≈ after erasure ([senv_eqv]). The relation
    reads an environment only through its domain, its points and the
    heads of its session types up to ≈, so V, E and P transport along
    ≈ ([Vrel_conv], [Erel_conv], [Prel_conv]), for every cost table.

    Composition needs it at a link. A link of a cut end o1 with an
    interface end o2 hands the partner of o1 the name o2, at the type of
    o1‾, and the interface keeps o2 at its own type. O-Link and Q-Link
    ask the two types dual up to ≈ only. *)

From GV Require Export compat.Rename.
From GV Require Import fuel.FuelMono.

(** ** Environments up to ≈ *)

Definition seqe (a b : sty * point) : Prop := a.2 = b.2 ∧ seqv a.1 b.1.

Definition senv_eqv (Θ Θ' : senv) : Prop := ∀ o, option_Forall2 seqe (Θ !! o) (Θ' !! o).

Section eqv.
  Implicit Types Θ : senv.

  Lemma senv_eqv_refl Θ : senv_eqv Θ Θ.
  Proof. intros o. destruct (Θ !! o) as [[S x]|]; constructor. split; [done|apply seqv_refl]. Qed.

  Lemma senv_eqv_sym Θ Θ' : senv_eqv Θ Θ' → senv_eqv Θ' Θ.
  Proof.
    intros H o. specialize (H o). inversion H as [[S x] [S' x'] [H1 H2]| ]; constructor.
    split; [done|by apply seqv_sym].
  Qed.

  Lemma senv_eqv_dom Θ Θ' : senv_eqv Θ Θ' → dom Θ = dom Θ'.
  Proof.
    intros H. apply set_eq. intros o. rewrite !elem_of_dom. specialize (H o).
    inversion H; split; intros [? Hx]; congruence || eauto.
  Qed.

  Lemma senv_eqv_lookup Θ Θ' o S x :
    senv_eqv Θ Θ' → Θ !! o = Some (S, x) → ∃ S', Θ' !! o = Some (S', x) ∧ seqv S S'.
  Proof.
    intros H Ho. specialize (H o). rewrite Ho in H. inversion H as [? [S' x'] [E1 E2]|]; subst.
    simpl in *. subst. eauto.
  Qed.

  Lemma senv_eqv_lookup_r Θ Θ' o S' x :
    senv_eqv Θ Θ' → Θ' !! o = Some (S', x) → ∃ S, Θ !! o = Some (S, x) ∧ seqv S S'.
  Proof.
    intros H Ho. destruct (senv_eqv_lookup Θ' Θ o S' x (senv_eqv_sym _ _ H) Ho) as (S & ? & ?).
    exists S. split; [done|by apply seqv_sym].
  Qed.

  Lemma senv_eqv_insert Θ Θ' o S S' x :
    senv_eqv Θ Θ' → seqv S S' → senv_eqv (<[o := (S, x)]> Θ) (<[o := (S', x)]> Θ').
  Proof.
    intros H Hs o'. destruct (decide (o' = o)) as [->|Hne].
    - rewrite !lookup_insert_eq. by constructor.
    - rewrite !lookup_insert_ne by done. apply H.
  Qed.

  Lemma senv_eqv_delete Θ Θ' o : senv_eqv Θ Θ' → senv_eqv (delete o Θ) (delete o Θ').
  Proof.
    intros H o'. destruct (decide (o' = o)) as [->|Hne].
    - rewrite !lookup_delete_eq. constructor.
    - rewrite !lookup_delete_ne by done. apply H.
  Qed.

  Lemma senv_eqv_union Θ1 Θ1' Θ2 Θ2' :
    senv_eqv Θ1 Θ1' → senv_eqv Θ2 Θ2' → senv_eqv (Θ1 ∪ Θ2) (Θ1' ∪ Θ2').
  Proof.
    intros H1 H2 o. rewrite !lookup_union. specialize (H1 o). specialize (H2 o).
    inversion H1; inversion H2; simpl; by constructor.
  Qed.

  Lemma senv_eqv_filter (P : cend * (sty * point) → Prop) `{∀ oe, Decision (P oe)} Θ Θ' :
    (∀ o a b, P (o, a) → P (o, b)) → senv_eqv Θ Θ' → senv_eqv (filter P Θ) (filter P Θ').
  Proof.
    intros HP HΘ o. rewrite !map_lookup_filter. specialize (HΘ o).
    inversion HΘ as [a b Hab|]; simpl; [|constructor].
    repeat case_guard; simpl; try by constructor.
    - exfalso. eauto.
    - exfalso. eauto.
  Qed.

  Lemma senv_eqv_split Θ1 Θ2 Θ' :
    senv_eqv (Θ1 ∪ Θ2) Θ' → Θ1 ##ₘ Θ2 →
    ∃ Θ1' Θ2', Θ' = Θ1' ∪ Θ2' ∧ Θ1' ##ₘ Θ2' ∧ senv_eqv Θ1 Θ1' ∧ senv_eqv Θ2 Θ2'.
  Proof.
    intros H Hd.
    exists (filter (λ oe : cend * (sty * point), oe.1 ∈ dom Θ1) Θ'),
      (filter (λ oe : cend * (sty * point), oe.1 ∉ dom Θ1) Θ').
    split_and!.
    - by rewrite map_filter_union_complement.
    - apply map_disjoint_filter_complement.
    - intros o. rewrite map_lookup_filter. specialize (H o). rewrite lookup_union in H.
      destruct (Θ1 !! o) eqn:E1, (Θ2 !! o) eqn:E2, (Θ' !! o) eqn:E3; simpl in *;
        inversion H; subst; simpl; try constructor;
        try (exfalso; by eapply map_disjoint_spec);
        repeat case_guard; simpl; try constructor; try done;
        match goal with
        | Hn : _ ∉ dom _ |- _ => exfalso; apply Hn; by eapply elem_of_dom_2
        | Hn : _ ∈ dom _ |- _ => apply elem_of_dom in Hn as [? ?]; congruence
        end.
    - intros o. rewrite map_lookup_filter. specialize (H o). rewrite lookup_union in H.
      destruct (Θ1 !! o) eqn:E1, (Θ2 !! o) eqn:E2, (Θ' !! o) eqn:E3; simpl in *;
        inversion H; subst; simpl; try constructor;
        try (exfalso; by eapply map_disjoint_spec);
        repeat case_guard; simpl; try constructor; try done;
        match goal with
        | Hn : ¬ (_ ∉ dom _) |- _ => apply Hn; by apply not_elem_of_dom
        | Hn : _ ∉ dom _ |- _ => exfalso; apply Hn; by eapply elem_of_dom_2
        | Hn : _ ∈ dom _ |- _ => apply elem_of_dom in Hn as [? ?]; congruence
        end.
  Qed.

  Lemma senv_eqv_heads Θ Θ' : senv_eqv Θ Θ' → senv_heads Θ = senv_heads Θ'.
  Proof.
    intros H. apply set_eq. intros y. rewrite !elem_of_senv_heads. split.
    - intros (o & S & x & Ho & ->). destruct (senv_eqv_lookup _ _ _ _ _ H Ho) as (S' & ? & _). eauto.
    - intros (o & S & x & Ho & ->). destruct (senv_eqv_lookup_r _ _ _ _ _ H Ho) as (S' & ? & _). eauto.
  Qed.

  Lemma senv_eqv_empty Θ : senv_eqv ∅ Θ → Θ = ∅.
  Proof. intros H. apply dom_empty_iff_L. by rewrite <-(senv_eqv_dom _ _ H), dom_empty_L. Qed.

  Lemma senv_eqv_singleton o S x Θ :
    senv_eqv {[o := (S, x)]} Θ → ∃ S', Θ = {[o := (S', x)]} ∧ seqv S S'.
  Proof.
    intros H. destruct (senv_eqv_lookup _ _ o S x H (lookup_singleton_eq _ _)) as (S' & HS' & Hs).
    exists S'. split; [|done]. apply map_eq. intros o'. destruct (decide (o' = o)) as [->|Hne].
    - by rewrite lookup_singleton_eq.
    - rewrite lookup_singleton_ne by done. specialize (H o'). rewrite lookup_singleton_ne in H by done.
      inversion H. done.
  Qed.

  Lemma senv_eqv_new_env Θ Θ' c S x : senv_eqv Θ Θ' → senv_eqv (new_env c S x Θ) (new_env c S x Θ').
  Proof. intros H. unfold new_env. apply senv_eqv_insert; [apply senv_eqv_insert|]; auto using seqv_refl. Qed.

  Lemma senv_eqv_cfresh Θ Θ' c : senv_eqv Θ Θ' → cfresh c Θ' → cfresh c Θ.
  Proof. intros H. unfold cfresh. by rewrite (senv_eqv_dom _ _ H). Qed.

  Lemma senv_eqv_gfresh Θ Θ' ℓ g : senv_eqv Θ Θ' → gfresh ℓ g Θ' → gfresh ℓ g Θ.
  Proof.
    intros H Hg o S x Ho. destruct (senv_eqv_lookup _ _ _ _ _ H Ho) as (S' & Ho' & _). by eapply Hg.
  Qed.

  Lemma senv_eqv_kinj Θ Θ' (h : cend → cend) : senv_eqv Θ Θ' → kinj h Θ → kinj h Θ'.
  Proof.
    intros H Hk o1 o2 v1 v2 H1 H2. apply elem_of_dom_2 in H1, H2.
    rewrite <-(senv_eqv_dom _ _ H) in H1, H2. apply elem_of_dom in H1 as [u1 U1], H2 as [u2 U2].
    by apply (Hk o1 o2 u1 u2).
  Qed.

  Lemma senv_eqv_kren Θ Θ' (h : cend → cend) :
    kinj h Θ → senv_eqv Θ Θ' → senv_eqv (kren h Θ) (kren h Θ').
  Proof.
    intros Hk H o'. pose proof (senv_eqv_kinj _ _ h H Hk) as Hk'.
    destruct (kren h Θ !! o') as [a|] eqn:E.
    - destruct (kren_lookup_inv _ _ _ _ E) as (o & -> & Ho). destruct a as [S x].
      destruct (senv_eqv_lookup _ _ _ _ _ H Ho) as (S' & Ho' & Hs).
      rewrite (kren_lookup h Θ' o _ Hk' Ho'). by constructor.
    - destruct (kren h Θ' !! o') as [b|] eqn:E'; [|constructor].
      destruct (kren_lookup_inv _ _ _ _ E') as (o & -> & Ho). destruct b as [S x].
      destruct (senv_eqv_lookup_r _ _ _ _ _ H Ho) as (S' & Ho' & _).
      by rewrite (kren_lookup h Θ o _ Hk Ho') in E.
  Qed.
End eqv.

(** ** Types of the environment, heads up to ≈ *)

Lemma sdual_conv S1 S2 S1' S2' : sdual S1 S2 → seqv S1 S1' → seqv S2 S2' → sdual S1' S2'.
Proof.
  unfold sdual, seqv. rewrite !sty_df_dual. intros H H1 H2.
  eapply sequiv_trans; [apply sequiv_sym, H2|]. eapply sequiv_trans; [exact H|].
  by apply sequiv_dual.
Qed.

Lemma teq_payload m U U' x : teq (ty_df U') (ty_df U) → teq (ty_df (payload_at m U' x)) (ty_df (payload_at m U x)).
Proof. intros H. rewrite <-!payload_at_df. unfold payload_at. by apply teq_pinst. Qed.

(** ** Readiness along ≈ *)

Lemma offered_t_conv Θ Θ' e o : senv_eqv Θ Θ' → offered_t Θ e o ↔ offered_t Θ' e o.
Proof. intros H. unfold offered_t. by rewrite (senv_eqv_dom _ _ H). Qed.

Lemma offered_p_conv Σ Σ' p o : senv_eqv Σ Σ' → offered_p Σ p o ↔ offered_p Σ' p o.
Proof. intros H. unfold offered_p. by rewrite (senv_eqv_dom _ _ H). Qed.

Lemma ready_t_conv W Θ Θ' F e : senv_eqv Θ Θ' → ready _ W(Θ ∣ F, e) → ready _ W(Θ' ∣ F, e).
Proof.
  intros H Hr Hs. destruct (Hr Hs) as [H1 H2]. split.
  - intros Hno. apply H1. intros o Ho. apply (Hno o). by apply (offered_t_conv _ _ _ _ H).
  - destruct H2 as [?|Hb]; [by left|right].
    intros o S x Ho Hx. destruct (senv_eqv_lookup_r _ _ _ _ _ H Hx) as (S0 & Hx0 & _).
    destruct (Hb o S0 x (proj2 (offered_t_conv _ _ _ _ H) Ho) Hx0) as [B1 B2]. split; [|done].
    intros o' S' x' Hx' Hno. destruct (senv_eqv_lookup_r _ _ _ _ _ H Hx') as (S1 & Hx1 & _).
    apply (B1 o' S1 x' Hx1). intros Hoff. by apply Hno, (offered_t_conv _ _ _ _ H).
Qed.

Lemma ready_p_conv W Σ Σ' p : senv_eqv Σ Σ' → ready _ W(Σ, p) → ready _ W(Σ', p).
Proof.
  intros H Hr Hs. destruct (Hr Hs) as [?|[H1 H2]]; [by left|right]. split.
  - intros Hno. apply H1. intros o Ho. apply (Hno o). by apply (offered_p_conv _ _ _ _ H).
  - intros o S x Hx Hno. destruct (senv_eqv_lookup_r _ _ _ _ _ H Hx) as (S0 & Hx0 & _).
    destruct (H2 o S0 x Hx0) as (o' & S' & x' & Ho' & Hx' & Hlt).
    { intros Hoff. by apply Hno, (offered_p_conv _ _ _ _ H). }
    destruct (senv_eqv_lookup _ _ _ _ _ H Hx') as (S1 & Hx1 & _).
    exists o', S1, x'. split_and!; [by apply (offered_p_conv _ _ _ _ H)|done|done].
Qed.

(** ** V and E along ≈ *)

Section rel.
  Context (κ : ctable).

  Definition VC n T : Prop := ∀ W Θ Θ' v, senv_eqv Θ Θ' → Vrel κ n W Θ T v → Vrel κ n W Θ' T v.
  Definition EC n T : Prop :=
    ∀ W Θ Θ' F e, senv_eqv Θ Θ' → Erel κ n W Θ T F e → Erel κ n W Θ' T F e.

  Lemma Vconv_step n T :
    (∀ j, j < n → ∀ T, VC j T ∧ EC j T) →
    (∀ T', tsize T' < tsize T → VC n T') →
    (c_beta κ = 0 → ∀ U, tsize U < tsize T → EC n U) →
    VC n T.
  Proof.
    intros IHl IHt IHe W Θ Θ' v HΘ.
    destruct T as [|ub lb c t T1 U a0|T1 U|T1 U|m kk C ub c t U|s x a0|lb m C T1].
    - intros [-> ->]%Vrel_unit_iff. apply Vrel_unit_iff. by rewrite (senv_eqv_empty _ HΘ).
    - intros (e & -> & Hfe & Hlb & H)%Vrel_lolli_iff. apply Vrel_lolli_iff.
      exists e. split_and!; [done|by rewrite <-(senv_eqv_dom _ _ HΘ)|by rewrite <-(senv_eqv_heads _ _ HΘ)|].
      intros W' j Θw w F HW Hj Hd Hub Hw.
      assert (EC j U) as HEU.
      { destruct (decide (j < n)); [by apply IHl|]. assert (j = n) as -> by lia. apply IHe; [lia|simpl; lia]. }
      apply (HEU W' (Θ ∪ Θw)); [apply senv_eqv_union; [done|apply senv_eqv_refl]|].
      apply H; [done|done| |done|done]. rewrite map_disjoint_dom in Hd |- *. by rewrite (senv_eqv_dom _ _ HΘ).
    - intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2)%Vrel_prod_iff. apply Vrel_prod_iff.
      destruct (senv_eqv_split _ _ _ HΘ Hd) as (Θ1' & Θ2' & -> & Hd' & E1 & E2).
      exists v1, v2, Θ1', Θ2'. split_and!; [done|done|done| |].
      + apply (IHt T1 ltac:(simpl; lia) W Θ1); done.
      + apply (IHt U ltac:(simpl; lia) W Θ2); done.
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; apply Vrel_sum_iff; [left|right]; exists v';
        (split; [done|]); (eapply IHt; [simpl; lia|exact HΘ|exact H]).
    - intros (-> & e & -> & Hfe & H)%Vrel_box_iff. apply Vrel_box_iff. rewrite (senv_eqv_empty _ HΘ).
      split; [done|]. exists e. split_and!; [done|done|]. exact H.
    - intros (o & s' & -> & -> & Hs)%Vrel_sess_iff. apply Vrel_sess_iff.
      destruct (senv_eqv_singleton _ _ _ _ HΘ) as (s'' & -> & Hs'). exists o, s''. split_and!; [done|done|].
      eapply seqv_trans; [apply seqv_sym, Hs'|exact Hs].
    - intros (Hlb & xs & Hxs & HC & H)%Vrel_ex_iff. apply Vrel_ex_iff. rewrite <-(senv_eqv_heads _ _ HΘ).
      split; [done|]. exists xs. split_and!; [done|done|]. eapply IHt; [|exact HΘ|exact H].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  Lemma Econv_step n T :
    (∀ j, j < n → ∀ T, VC j T ∧ EC j T) → VC n T → VC n TUnit →
    (c_give κ = 0 → ∀ T', VC n T') →
    EC n T.
  Proof.
    intros IHl HVT HVU HVP. destruct n as [|n]; [unfold EC; intros; apply Erel_0|].
    intros W Θ Θ' F e HΘ HE.
    cut (∀ W Θ T0 F e, Erel κ (S n) W Θ T0 F e → T0 = T ∨ T0 = TUnit →
           ∀ Θ', senv_eqv Θ Θ' → Erel κ (S n) W Θ' T0 F e);
      [intros H; by apply (H W Θ T F e HE (or_introl eq_refl))|].
    clear W Θ Θ' F e HΘ HE.
    refine (Erel_S_ind κ n _ _). intros W Θ T0 F e Hb HT0 Θ' HΘ.
    assert (VC (S n) T0) as HV0 by (destruct HT0 as [->| ->]; done).
    apply Erel_S_iff. intros W1 HW1.
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c Θa Θb e', senv_eqv Θa Θb →
      at_cost_E (S n) c (Erel κ) (λ W Θ T0 F e, Erel κ (S n) W Θ T0 F e ∧
          (T0 = T ∨ T0 = TUnit → ∀ Θ', senv_eqv Θ Θ' → Erel κ (S n) W Θ' T0 F e))
        W1 Θa T0 F e' →
      at_cost_E (S n) c (Erel κ) (Erel κ (S n)) W1 Θb T0 F e') as Hac.
    { intros c Θa Θb e' Hab [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc. apply (proj2 (IHl (S n - c) ltac:(lia) T0) _ Θa); [done|]. by apply A2. }
    split; [|split; [|unfold Esteps; split_and!]].
    - intros Hi. apply (HV0 _ Θ); [done|]. by apply Hs.
    - intros Hni. eapply ready_t_conv; [exact HΘ|]. by apply Hr.
    - intros e' Hst. apply (Hac _ Θ); [done|]. by apply H1.
    - intros ℓ c e' Hst Hc g Hg.
      destruct (H2 ℓ c e' Hst (senv_eqv_cfresh _ _ _ HΘ Hc) g (senv_eqv_gfresh _ _ _ _ HΘ Hg)) as [S HS].
      exists S. eapply Hac; [|exact HS]. by apply senv_eqv_new_env.
    - intros κf o c e' Hst Hc. destruct (H3 κf o c e' Hst (senv_eqv_cfresh _ _ _ HΘ Hc)) as (S0 & x & Ho & S & HS).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ Ho) as (S0' & Ho' & _).
      exists S0', x. split; [done|]. exists S. eapply Hac; [|exact HS]. by apply senv_eqv_new_env.
    - intros v e' Hst. destruct (H4 v e' Hst) as (ΘM & Θr & A1 & -> & A4 & A5).
      destruct (senv_eqv_split _ _ _ HΘ A1) as (ΘM' & Θr' & -> & Hd' & EM & Er).
      exists ΘM', Θr'. split_and!; [done|done| |by eapply Hac].
      destruct A4 as (e1 & -> & Hfe & _ & HA). exists e1.
      split_and!; [done|by rewrite <-(senv_eqv_dom _ _ EM)|done|].
      intros W' j Θ0 w F0 HW Hj Hd Hub.
      assert (ΘM ##ₘ Θ0) as Hd0 by (rewrite map_disjoint_dom in Hd |- *; by rewrite (senv_eqv_dom _ _ EM)).
      destruct (HA W' j Θ0 w F0 HW Hj Hd0 Hub) as [B1 B2]. split.
      + intros Hjn Hw. apply (proj2 (IHl j Hjn TUnit) _ (ΘM ∪ Θ0)).
        * apply senv_eqv_union; [done|apply senv_eqv_refl].
        * by apply B1.
      + intros -> Hw. destruct (B2 eq_refl Hw) as [_ B3]. apply B3; [by right|].
        apply senv_eqv_union; [done|apply senv_eqv_refl].
    - intros o w e' Hst.
      destruct (H5 o w e' Hst) as (S0 & x & m & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_snd S0' S0 m U S (seqv_sym _ _ Hs0) A2) as (U' & S' & A2' & HU & HS).
      assert (senv_eqv (ΘM ∪ Θr) (delete o Θ')) as Hdel by (rewrite <-A4; by apply senv_eqv_delete).
      destruct (senv_eqv_split _ _ _ Hdel A3) as (ΘM' & Θr' & Hdel' & Hd' & EM & Er).
      exists S0', x, m, U', S', ΘM', Θr'. split_and!; [done|done|done|done| |].
      + destruct A6 as [B1 B2]. split.
        * intros Hc. apply (proj2 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU))).
          apply (HVP Hc _ _ ΘM); [done|by apply B1].
        * intros Hc. apply (proj2 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU))).
          apply (proj1 (IHl (Datatypes.S n - c_give κ) ltac:(lia) _) _ ΘM); [done|by apply B2].
      + eapply Hac; [|exact A7]. apply senv_eqv_insert; [done|by apply seqv_sym].
    - intros o w e' Hst. destruct (H6 o w e' Hst) as (S0 & x & m & U & S & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_rcv S0' S0 m U S (seqv_sym _ _ Hs0) A2) as (U' & S' & A2' & HU & HS).
      exists S0', x, m, U', S'. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (proj2 (IHl j ltac:(lia) T0) _ (<[o := (S, x⁺)]> Θ ∪ Θin)).
      + apply senv_eqv_union; [|apply senv_eqv_refl]. apply senv_eqv_insert; [done|by apply seqv_sym].
      + apply A3; [done| |].
        * rewrite map_disjoint_dom in Hd |- *. by rewrite (senv_eqv_dom _ _ HΘ).
        * apply (proj1 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU))), Hw.
    - intros o e' Hst. destruct (H7 o e' Hst) as (S0 & x & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A1) as (S0' & A1' & Hs0).
      exists S0', x. split_and!; [done|by eapply seqv_unfold_end; [apply seqv_sym|]|].
      eapply Hac; [|exact A3]. by apply senv_eqv_delete.
    - intros o i e' Hst. destruct (H8 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_plus S0' S0 S1 S2 (seqv_sym _ _ Hs0) A2) as (S1' & S2' & A2' & E1 & E2).
      exists S0', x, S1', S2'. split_and!; [done|done|].
      eapply Hac; [|exact A3]. apply senv_eqv_insert; [done|]. apply seqv_sym. by apply seqv_bsel.
    - intros o i e' Hst. destruct (H9 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_with S0' S0 S1 S2 (seqv_sym _ _ Hs0) A2) as (S1' & S2' & A2' & E1 & E2).
      exists S0', x, S1', S2'. split_and!; [done|done|].
      eapply Hac; [|exact A3]. apply senv_eqv_insert; [done|]. apply seqv_sym. by apply seqv_bsel.
    - intros os e' Hst. destruct (H10 os e' Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A3) as (S1' & A3' & E1).
      destruct (senv_eqv_lookup _ _ _ _ _ HΘ A4) as (S2' & A4' & E2).
      exists o1, o2, S1', S2', x. split_and!; [done|done|done|done|by eapply sdual_conv|].
      eapply Hac; [|exact A6]. by apply senv_eqv_delete, senv_eqv_delete.
  Qed.

  Lemma conv_level n : ∀ T, VC n T ∧ EC n T.
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    assert (VC n TUnit) as HVU.
    { apply Vconv_step; [done|intros T' HT|intros _ U HU]; [pose proof (tsize_pos T')|pose proof (tsize_pos U)];
        simpl in *; lia. }
    destruct (decide (c_give κ = 0)) as [Hg|Hg].
    - assert (∀ T, VC n T) as HV.
      { intros T. induction T as [T IH] using tsize_ind. apply Vconv_step; [done|done|].
        intros Hb. pose proof (c_give_pos κ Hb). lia. }
      intros T. split; [done|]. by apply Econv_step.
    - intros T. induction T as [T IH] using tsize_ind.
      assert (VC n T) as HVT.
      { apply Vconv_step; [done| |]; intros; by apply IH. }
      split; [done|]. by apply Econv_step.
  Qed.
End rel.

Theorem Vrel_conv κ n W Θ Θ' T v :
  senv_eqv Θ Θ' → v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧ → v ∈ V[κ]^W _ n⟦Θ' ⊢ T⟧.
Proof. intros H Hv. by apply (conv_level κ n T) with Θ. Qed.

Theorem Erel_conv κ n W Θ Θ' T F e :
  senv_eqv Θ Θ' → e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F → e ∈ E[κ]^W _ n⟦Θ' ⊢ T⟧^F.
Proof. intros H He. by apply (conv_level κ n T) with Θ. Qed.

(** ** P along ≈ *)

Lemma pheld_conv Σ Σ' p o : senv_eqv Σ Σ' → pheld Σ p o ↔ pheld Σ' p o.
Proof. intros H. unfold pheld. by rewrite (senv_eqv_dom _ _ H). Qed.

Lemma dpairs_conv D Σ Σ' : senv_eqv Σ Σ' → dpairs D Σ' → dpairs D Σ.
Proof.
  intros H Hp o Ho. destruct (Hp o Ho) as (S & x & S' & H1 & H2 & Hs).
  destruct (senv_eqv_lookup_r _ _ _ _ _ H H1) as (S0 & H1' & E1).
  destruct (senv_eqv_lookup_r _ _ _ _ _ H H2) as (S0' & H2' & E2).
  exists S0, x, S0'. split_and!; [done|done|]. eapply sdual_conv; [exact Hs|by apply seqv_sym|by apply seqv_sym].
Qed.

Lemma fuse_ok_conv h D Σ Σ' p : senv_eqv Σ Σ' → fuse_ok h D Σ' p → fuse_ok h D Σ p.
Proof.
  intros H (Hd & Hi & Hn & HD & Hp). pose proof (pheld_conv Σ Σ' p) as Hc.
  split_and!; [done| | |done|].
  - intros o1 o2 H1 H2. apply Hi; by apply Hc.
  - intros o1 o2 H1 H2. apply Hn; by apply Hc.
  - eapply dpairs_conv; [|exact Hp]. apply senv_eqv_kren; [|done].
    intros o1 o2 v1 v2 H1 H2. apply Hi; left; rewrite <-(senv_eqv_dom _ _ H); by eapply elem_of_dom_2.
Qed.

Lemma senv_eqv_sdrop D Σ Σ' : senv_eqv Σ Σ' → senv_eqv (sdrop D Σ) (sdrop D Σ').
Proof. intros H. apply senv_eqv_filter; [by intros|done]. Qed.

Lemma chans_of_conv Σ Σ' : senv_eqv Σ Σ' → chans_of Σ = chans_of Σ'.
Proof. intros H. unfold chans_of. by rewrite (senv_eqv_dom _ _ H). Qed.

Lemma send_split_conv Σ Σ' Σe Θe : senv_eqv Σ Σ' → send_split Σ Σe Θe → send_split Σ' Σe Θe.
Proof.
  intros H (A1 & A2 & A3). pose proof (senv_eqv_dom _ _ H) as Hd. split_and!.
  - intros o Ho. rewrite <-Hd. by apply A1.
  - intros o. rewrite A2. done.
  - done.
Qed.

Lemma recv_ok_conv Σ Σ' Θ2 : senv_eqv Σ Σ' → recv_ok Σ' Θ2 → recv_ok Σ Θ2.
Proof.
  intros H [A1 A2]. split.
  - intros o Ho. rewrite (senv_eqv_dom _ _ H). by apply A1.
  - intros o S y S' y' H1 H2. rewrite lookup_union in H2.
    destruct (Σ !! edual o) as [[S0 y0]|] eqn:E.
    + simpl in H2. rewrite union_Some_l in H2. injection H2 as <- <-.
      destruct (senv_eqv_lookup _ _ _ _ _ H E) as (S1 & E1 & Hs).
      destruct (A2 o S y S1 y0 H1) as [-> Hd]; [by rewrite lookup_union, E1, union_Some_l|].
      split; [done|]. eapply sdual_conv; [exact Hd|apply seqv_refl|by apply seqv_sym].
    + assert (Θ2 !! edual o = Some (S', y')) as H2' by (by destruct (Θ2 !! edual o)).
      apply (A2 o S y S' y' H1). rewrite lookup_union, H2'.
      destruct (Σ' !! edual o) eqn:E'; [|done].
      exfalso. apply elem_of_dom_2 in E'. rewrite <-(senv_eqv_dom _ _ H) in E'.
      apply elem_of_dom in E' as [? ?]. congruence.
Qed.

Lemma recv_env_conv Σ Σ' Θ2 : senv_eqv Σ Σ' → senv_eqv (recv_env Σ Θ2) (recv_env Σ' Θ2).
Proof.
  intros H. unfold recv_env. rewrite (senv_eqv_dom _ _ H).
  apply senv_eqv_union; [apply senv_eqv_filter; [by intros|done]|apply senv_eqv_refl].
Qed.

Lemma recv_back_conv Σ Σ' Θ2 : senv_eqv Σ Σ' → recv_back Σ Θ2 = recv_back Σ' Θ2.
Proof. intros H. unfold recv_back. by rewrite (senv_eqv_dom _ _ H). Qed.

Section prel.
  Context (κ : ctable).

  Lemma Prel_conv_lvl m : ∀ W Σ T p, Prel κ m W Σ T p →
    ∀ Σ', senv_eqv Σ Σ' → Prel κ m W Σ' T p.
  Proof.
    induction m as [m IHm] using lt_wf_ind. destruct m as [|n]; [intros; apply Prel_0|].
    refine (Prel_S_ind κ n _ _). intros W Σ T p Hb Σ' HΣ.
    apply Prel_S_iff. intros W1 HW1 HS1 h D Hh.
    pose proof (fuse_ok_conv h D Σ Σ' p HΣ Hh) as Hh0.
    destruct (Hb W1 HW1 HS1 h D Hh0) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    assert (senv_eqv (sdrop D (kren h Σ)) (sdrop D (kren h Σ'))) as HΣh
      by (apply senv_eqv_sdrop, senv_eqv_kren; [by eapply fuse_ok_kinj|done]).
    clear Hb HΣ Hh Hh0.
    remember (pfuse h D p) as p0 eqn:Ep. remember (sdrop D (kren h Σ)) as Σ0 eqn:EΣ.
    remember (sdrop D (kren h Σ')) as Σ0' eqn:EΣ'.
    clear Ep EΣ EΣ' p Σ Σ' h D. rename p0 into p, Σ0 into Σ, Σ0' into Σ', HΣh into HΣ.
    assert (∀ c Σa Σb p', senv_eqv Σa Σb →
      at_cost_P (S n) c (Prel κ) (λ W Σ T p, Prel κ (S n) W Σ T p ∧
          (∀ Σ', senv_eqv Σ Σ' → Prel κ (S n) W Σ' T p)) W1 Σa T p' →
      at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W1 Σb T p') as Hac.
    { intros c Σa Σb p' Hab [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc. apply (IHm (S n - c) ltac:(lia) _ Σa); [by apply A2|done]. }
    split; [|split; [|unfold Psteps; split_and!]].
    - intros Hi. destruct (Hs Hi) as (v & E & -> & Hv & HE). exists v, E. split_and!; [done| |done].
      by apply (Vrel_conv κ _ _ Σ).
    - intros Hni. eapply ready_p_conv; [exact HΣ|]. by apply Hr.
    - intros q ev q' Hq Hst Hτ Hd. apply (Hac _ Σ); [done|]. apply (H1 q ev q' Hq Hst Hτ).
      by rewrite (chans_of_conv _ _ HΣ).
    - intros q i o w q' Hq Hst.
      destruct (H2 q i o w q' Hq Hst)
        as (S0 & x & m & U & S & Σv & Σr & Θe & Σe & A1 & A2 & A3 & A4 & A5 & A7 & A8 & A9).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_snd S0' S0 m U S (seqv_sym _ _ Hs0) A2) as (U' & S' & A2' & HU & HS).
      assert (senv_eqv (Σv ∪ Σr) (delete o Σ')) as Hdel by (rewrite <-A4; by apply senv_eqv_delete).
      destruct (senv_eqv_split _ _ _ Hdel A3) as (Σv' & Σr' & Hdel' & Hd' & Ev & Er).
      exists S0', x, m, U', S', Σv', Σr', Θe, Σe. split_and!; [done|done|done|done|done
        |by eapply send_split_conv| |].
      + destruct A8 as [B1 B2].
        assert (senv_eqv (Σv ∪ Θe) (Σv' ∪ Θe)) as EvΘ by (apply senv_eqv_union; [done|apply senv_eqv_refl]).
        split.
        * intros Hc. apply (proj2 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU))).
          apply (Vrel_conv κ _ _ (Σv ∪ Θe)); [done|by apply B1].
        * intros Hc. apply (proj2 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU))).
          apply (Vrel_conv κ _ _ (Σv ∪ Θe)); [done|by apply B2].
      + eapply Hac; [|exact A9]. apply senv_eqv_insert; [|by apply seqv_sym].
        apply senv_eqv_union; [done|apply senv_eqv_refl].
    - intros q i o w q' Hq Hst. destruct (H3 q i o w q' Hq Hst) as (S0 & x & m & U & S & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_rcv S0' S0 m U S (seqv_sym _ _ Hs0) A2) as (U' & S' & A2' & HU & HS).
      exists S0', x, m, U', S'. split_and!; [done|done|].
      intros j Θ2 Hj Hd Hok Hw.
      assert (senv_eqv (<[o := (S, x⁺)]> Σ) (<[o := (S', x⁺)]> Σ')) as HΣ2
        by (apply senv_eqv_insert; [done|by apply seqv_sym]).
      pose proof (A3 j Θ2 Hj Hd (recv_ok_conv _ _ _ HΣ2 Hok)
        (proj1 (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x HU)) Hw)) as HP.
      rewrite (recv_back_conv _ _ _ HΣ2) in HP.
      pose proof (c_take_pos κ).
      apply (IHm j ltac:(lia) _ (recv_env (<[o := (S, x⁺)]> Σ) Θ2)); [done|]. by apply recv_env_conv.
    - intros q i o q' Hq Hst. destruct (H4 q i o q' Hq Hst) as (S0 & x & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A1) as (S0' & A1' & Hs0).
      exists S0', x. split_and!; [done|by eapply seqv_unfold_end; [apply seqv_sym|]|].
      eapply Hac; [|exact A3]. by apply senv_eqv_delete.
    - intros q i o b q' Hq Hst. destruct (H5 q i o b q' Hq Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_plus S0' S0 S1 S2 (seqv_sym _ _ Hs0) A2) as (S1' & S2' & A2' & E1 & E2).
      exists S0', x, S1', S2'. split_and!; [done|done|].
      eapply Hac; [|exact A3]. apply senv_eqv_insert; [done|]. apply seqv_sym. by apply seqv_bsel.
    - intros q i o b q' Hq Hst. destruct (H6 q i o b q' Hq Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A1) as (S0' & A1' & Hs0).
      destruct (seqv_unfold_with S0' S0 S1 S2 (seqv_sym _ _ Hs0) A2) as (S1' & S2' & A2' & E1 & E2).
      exists S0', x, S1', S2'. split_and!; [done|done|].
      eapply Hac; [|exact A3]. apply senv_eqv_insert; [done|]. apply seqv_sym. by apply seqv_bsel.
    - intros q i os q' Hq Hst.
      destruct (H7 q i os q' Hq Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A3) as (S1' & A3' & E1).
      destruct (senv_eqv_lookup _ _ _ _ _ HΣ A4) as (S2' & A4' & E2).
      exists o1, o2, S1', S2', x. split_and!; [done|done|done|done|by eapply sdual_conv|].
      eapply Hac; [|exact A6]. by apply senv_eqv_delete, senv_eqv_delete.
  Qed.
End prel.

Theorem Prel_conv κ n W Σ Σ' T p :
  senv_eqv Σ Σ' → p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → p ∈ P[κ]^W _ n⟦Σ' ⊢ T⟧.
Proof.
  intros H Hp. by eapply Prel_conv_lvl.
Qed.
