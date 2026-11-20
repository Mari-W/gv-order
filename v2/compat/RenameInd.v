(** * E under a renaming, at one unfolding (stage S4, P-Term)

    The forward simulation of compat/Rename.v, stated for one unfolding of
    E with any reader X closed under renaming ([erel_ren]):

      Ebody_rename : erel_ren X → kinj h Θ → e ∈ E⟦Θ ⊢ T⟧^F →
        Ebody … X W Θ T F e → Ebody … X W (kren h Θ) T F (emap h e)

    and from it the induction over the steps of cost 0 whose predicate is
    closed under renaming ([Erel_S_ind_ren]). P-Term reads the clause
    (fuse) of P through it: a fusion of a single thread is a single thread
    renamed. *)

From GV Require Export compat.Rename.
From GV Require Import fuel.FuelMono.

Section ren_ind.
  Context (κ : ctable).

  Definition erel_ren (X : erel) : Prop :=
    ∀ W Θ T F e h, kinj h Θ → X W Θ T F e → X W (kren h Θ) T F (emap h e).

  Lemma Ebody_rename n (X : erel) W Θ T F e h :
    erel_ren X → kinj h Θ → Erel κ (S n) W Θ T F e →
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) X W Θ T F e →
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) X W (kren h Θ) T F (emap h e).
  Proof.
    intros HX Hk HE Hb.
    set (Xc := set_map (D:=gset chan) ech (dom Θ) ∪ fchans e).
    assert (∀ o, o ∈ dom Θ → ech o ∈ Xc) as HXd.
    { intros o Ho. apply elem_of_union_l, elem_of_map. by exists o. }
    assert (∀ h', (∀ o, ech o ∈ Xc → h' o = h o) → emap h' e = emap h e) as Hee.
    { intros h' Hh'. apply emap_ext_on. intros o Ho. apply Hh'.
      apply elem_of_union_r, elem_of_fchans. by exists o. }
    assert (∀ c, c ∉ Xc → cfresh c Θ) as Hcf.
    { intros c Hc. split; intros Hin; apply Hc, elem_of_union_l, elem_of_map; eexists; (split; [|exact Hin]); done. }
    intros W1 HW1.
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ σ e', tstep e (LSess σ) e' → sends σ ⊆ dom Θ) as Hsends.
    { intros σ e' Hst. exact (Erel_sends κ n W Θ T F e σ e' HE Hst). }
    assert (∀ c Θ' e' h', kinj h' Θ' →
      at_cost_E (S n) c (Erel κ) X W1 Θ' T F e' →
      at_cost_E (S n) c (Erel κ) X W1 (kren h' Θ') T F (emap h' e')) as Hac.
    { intros c Θ' e' h' Hk' [A1 A2]. split.
      - intros Hc. apply HX; [done|]. by apply A1.
      - intros Hc. apply (proj2 (rename_level κ (S n - c) T)); [done|]. by apply A2. }
    assert (∀ o v w, Θ !! o = Some w → kinj h (<[o := v]> Θ)) as Hkins.
    { intros o v w Ho. eapply kinj_sub; [|exact Hk]. rewrite dom_insert_L.
      apply elem_of_dom_2 in Ho. set_solver. }
    assert (∀ o, kinj h (delete o Θ)) as Hkdel.
    { intros o. eapply kinj_sub; [|exact Hk]. set_solver. }
    split; [|split; [|unfold Esteps; split_and!]].
    - (* (stop) *)
      intros Hi. apply irred_emap in Hi. apply (proj1 (rename_level κ (S n) T)); [done|]. by apply Hs.
    - (* (ready) *)
      intros Hni. apply ready_rename; [done|done|]. apply Hr. intros Hi. by apply Hni, irred_emap.
    - (* O-Beta *)
      intros x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      assert (a = ABeta) as -> by (destruct a; simpl in Ho; try contradiction; done).
      destruct (act_offer e ABeta LBeta Ha I) as [e0 He0].
      rewrite (tstep_emap_back h h e LBeta x LBeta e0 Hst He0 I eq_refl eq_refl).
      apply (Hac _ _ _ h Hk). by apply H1.
    - (* O-New *)
      intros ℓ c x Hst Hc g Hg. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      assert (a = ANew ℓ) as -> by (destruct a; simpl in Ho; try contradiction; by subst).
      destruct (fresh_pull h {[c]} Xc) as (kc & h' & K1 & _ & K3 & K4 & _).
      assert (kc c ∉ Xc) as Hc'' by (apply K1; set_solver).
      assert (h' (EPos (kc c)) = EPos c) as Hp by (apply (K3 (EPos c)); set_solver).
      assert (h' (ENeg (kc c)) = ENeg c) as Hn by (apply (K3 (ENeg c)); set_solver).
      destruct (act_offer e (ANew ℓ) (LNew ℓ (kc c)) Ha eq_refl) as [e0 He0].
      assert (lnew_ok h' (LNew ℓ (kc c))) as Hok by (unfold lnew_ok, gpol, gch; rewrite Hp; simpl; by rewrite Hn).
      assert (lmap h' (LNew ℓ (kc c)) = LNew ℓ c) as Hl by (simpl; unfold gch; by rewrite Hp).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 Hok Hl (Hee h' K4)).
      destruct (H2 ℓ (kc c) e0 He0 (Hcf _ Hc'') g (gfresh_kren h ℓ g Θ Hk Hg)) as [S HS]. exists S.
      destruct (kren_new_env h h' Θ c (kc c) S (pgen ℓ g) Hk Hc (Hcf _ Hc'') Hp Hn) as [Hk1 Heq].
      { intros o1 Ho1. by apply K4, HXd. }
      rewrite <-Heq. by apply Hac.
    - (* O-NewAt *)
      intros κf o' c x Hst Hc. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| |κa o| | | | | | |]; simpl in Ho; try contradiction. destruct Ho as [<- <-].
      destruct (fresh_pull h {[c]} Xc) as (kc & h' & K1 & _ & K3 & K4 & _).
      assert (kc c ∉ Xc) as Hc'' by (apply K1; set_solver).
      assert (h' (EPos (kc c)) = EPos c) as Hp by (apply (K3 (EPos c)); set_solver).
      assert (h' (ENeg (kc c)) = ENeg c) as Hn by (apply (K3 (ENeg c)); set_solver).
      destruct (act_offer e (ANewAt κa o) (LNewAt κa o (kc c)) Ha (conj eq_refl eq_refl)) as [e0 He0].
      destruct (H3 κa o (kc c) e0 He0 (Hcf _ Hc'')) as (S0 & x0 & Ho0 & S & HS).
      assert (h' o = h o) as Hho by (apply K4, HXd; by eapply elem_of_dom_2).
      assert (lnew_ok h' (LNewAt κa o (kc c))) as Hok by (unfold lnew_ok, gpol, gch; rewrite Hp; simpl; by rewrite Hn).
      assert (lmap h' (LNewAt κa o (kc c)) = LNewAt κa (h o) c) as Hl by (simpl; unfold gch; by rewrite Hp, Hho).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 Hok Hl (Hee h' K4)).
      exists S0, x0. split; [by apply kren_lookup|]. exists S.
      destruct (kren_new_env h h' Θ c (kc c) S (x0·κa) Hk Hc (Hcf _ Hc'') Hp Hn) as [Hk1 Heq].
      { intros o1 Ho1. by apply K4, HXd. }
      rewrite <-Heq. by apply Hac.
    - (* O-Spawn *)
      intros w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | |v| | | | | |]; simpl in Ho; try contradiction. subst w.
      destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e0 He0].
      assert (lmap h (LSpawn v) = LSpawn (emap h v)) as Hl by reflexivity.
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H4 _ _ He0) as (ΘM & Θr & A1 & -> & A4 & A5).
      assert (kinj h ΘM) as KM by (eapply kinj_sub; [|exact Hk]; rewrite dom_union_L; set_solver).
      assert (kinj h Θr) as Kr by (eapply kinj_sub; [|exact Hk]; rewrite dom_union_L; set_solver).
      exists (kren h ΘM), (kren h Θr). split_and!.
      + by apply kren_disjoint.
      + by apply kren_union.
      + destruct A4 as (e1 & -> & Hfe & HA). exists (emap h e1).
        split_and!; [done|by rewrite kren_dom, fends_emap, Hfe|].
        intros W' j Θ' w' HW Hj Hd. split.
        * intros Hjn [-> ->]%Vrel_unit_iff. rewrite map_union_empty.
          destruct (HA W' j ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [B1 _].
          rewrite map_union_empty in B1. change EUnit with (emap h EUnit). rewrite <-emap_subst1.
          apply (proj2 (rename_level κ j TUnit)); [done|]. apply B1; [done|by apply Vrel_unit_iff].
        * intros -> [-> ->]. rewrite map_union_empty.
          destruct (HA W' (S n) ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [_ B2].
          pose proof (B2 eq_refl (conj eq_refl eq_refl)) as B3. rewrite map_union_empty in B3.
          change EUnit with (emap h EUnit). rewrite <-emap_subst1. by apply HX; [|exact B3].
      + by apply Hac.
    - (* O-Send *)
      intros o' w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | |o v| | | |]; simpl in Ho; try contradiction. destruct Ho as (<- & <-).
      destruct (act_offer e (ASend o v) (LSess (SSend o v)) Ha
        (conj eq_refl eq_refl)) as [e0 He0].
      assert (lmap h (LSess (SSend o v)) = LSess (SSend (h o) (emap h v))) as Hl by reflexivity.
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H5 _ _ _ He0) as (S0 & x0 & m' & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      assert (dom ΘM ∪ dom Θr ⊆ dom Θ ∖ {[o]}) as Hdd by (rewrite <-dom_union_L, <-A4, dom_delete_L; done).
      assert (kinj h (ΘM ∪ Θr)) as KMr by (rewrite <-A4; apply Hkdel).
      assert (kinj h ΘM) as KM by (eapply kinj_sub; [|exact Hk]; set_solver).
      assert (kinj h (<[o := (S, x0⁺)]> Θr)) as Kr.
      { eapply kinj_sub; [|exact Hk]. rewrite dom_insert_L. apply elem_of_dom_2 in A1. set_solver. }
      exists S0, x0, m', U, S, (kren h ΘM), (kren h Θr). split_and!.
      + by apply kren_lookup.
      + done.
      + by apply kren_disjoint.
      + rewrite <-kren_union by done. rewrite <-A4. rewrite kren_delete; [done|done|by eapply elem_of_dom_2].
      + destruct A6 as [B1 B2]. split.
        * intros Hc. apply (proj1 (rename_level κ (Datatypes.S n) _)); [done|]. by apply B1.
        * intros Hc. apply (proj1 (rename_level κ (Datatypes.S n - c_give κ) _)); [done|]. by apply B2.
      + rewrite <-kren_insert by done. by apply Hac.
    - (* O-Recv *)
      intros o' w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | |o| | | | |]; simpl in Ho; try contradiction. destruct Ho as [<- Hw].
      destruct (act_offer e (ARecv o) (LSess (SRecv o EUnit)) Ha (conj eq_refl I)) as [e00 He00].
      destruct (H6 _ _ _ He00) as (S0 & x0 & m' & U & S & A1 & A2 & _).
      exists S0, x0, m', U, S. split_and!; [by apply kren_lookup|done|].
      intros j Θw Hj Hd HVw. pose proof (c_take_pos κ).
      destruct (pull_value κ j W1 (payload_at m' U x0) h Θ Θw w Xc (proj1 (rename_level κ j _)) Hk
        ltac:(set_solver) Hd HVw) as (h' & w0 & Θ0 & Hw0 & Hd0 & Hww & Hext & Hk' & Hren & _).
      assert (is_val w0) as Hv0 by (rewrite <-Hww, is_val_emap in Hw; done).
      destruct (act_offer e (ARecv o) (LSess (SRecv o w0)) Ha (conj eq_refl Hv0)) as [e0 He0].
      assert (h' o = h o) as Hho by (apply Hext, HXd; by eapply elem_of_dom_2).
      assert (lmap h' (LSess (SRecv o w0)) = LSess (SRecv (h o) w)) as Hl by (simpl; by rewrite Hww, Hho).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 I Hl (Hee h' Hext)).
      destruct (H6 _ _ _ He0) as (S0' & x0' & m'' & U' & S' & A1' & A2' & A3').
      rewrite A1 in A1'. injection A1' as <- <-. rewrite A2 in A2'. injection A2' as <- <- <-.
      assert (Erel κ j W1 (<[o := (S, x0⁺)]> Θ ∪ Θ0) T F e0) as HE0 by (apply A3'; [lia|done|done]).
      rewrite <-insert_union_l in HE0.
      assert (kinj h' (<[o := (S, x0⁺)]> (Θ ∪ Θ0))) as Hk2.
      { eapply kinj_sub; [|exact Hk']. rewrite dom_insert_L, dom_union_L.
        apply elem_of_dom_2 in A1. set_solver. }
      pose proof (proj2 (rename_level κ j T) W1 _ F e0 h' Hk2 HE0) as HR.
      rewrite kren_insert, Hren, Hho, insert_union_l in HR by done. exact HR.
    - (* O-Close *)
      intros o' x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | |o| | |]; simpl in Ho; try contradiction. subst o'.
      destruct (act_offer e (AClose o) (LSess (SClose o)) Ha eq_refl) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H7 _ _ He0) as (S0 & x0 & A1 & A2 & A3).
      exists S0, x0. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_delete; [by apply Hac|done|by eapply elem_of_dom_2].
    - (* O-Select *)
      intros o' i x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | | |o i0|]; simpl in Ho; try contradiction. destruct Ho as [<- <-].
      destruct (act_offer e (ASel o i0) (LSess (SSel o i0)) Ha (conj eq_refl eq_refl)) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H8 _ _ _ He0) as (S0 & x0 & S1 & S2 & A1 & A2 & A3).
      exists S0, x0, S1, S2. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_insert by (by eapply Hkins). by apply Hac; [eapply Hkins|].
    - (* O-Branch *)
      intros o' i x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | | | |o]; simpl in Ho; try contradiction. subst o'.
      destruct (act_offer e (ABra o) (LSess (SBra o i)) Ha eq_refl) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H9 _ _ _ He0) as (S0 & x0 & S1 & S2 & A1 & A2 & A3).
      exists S0, x0, S1, S2. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_insert by (by eapply Hkins). by apply Hac; [eapply Hkins|].
    - (* O-Link *)
      intros os' x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | |o1 o2| |]; simpl in Ho; try contradiction. subst os'.
      destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e0 He0].
      assert (lmap h (LSess (SLink ({[o1]} ∪ {[o2]}))) = LSess (SLink ({[h o1]} ∪ {[h o2]}))) as Hl
        by (simpl; by rewrite set_map_upair).
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H10 _ _ He0) as (p1 & p2 & S1 & S2 & x0 & A1 & A2 & A3 & A4 & A5 & A6).
      exists (h p1), (h p2), S1, S2, x0. split_and!.
      + rewrite <-set_map_upair, A1, set_map_union_L, !set_map_singleton_L. done.
      + intros Heq. apply A2. exact (Hk p1 p2 _ _ A3 A4 Heq).
      + by apply kren_lookup.
      + by apply kren_lookup.
      + done.
      + rewrite <-(kren_delete h Θ p2); [|done|by eapply elem_of_dom_2].
        rewrite <-(kren_delete h (delete p2 Θ) p1); [|done|].
        * apply Hac; [|done]. eapply kinj_sub; [|exact Hk]. set_solver.
        * apply elem_of_dom. rewrite lookup_delete_ne; [by eexists|done].
  Qed.

  (** The predicate Φ at every renaming. *)
  Definition Φren (Φ : erel) : erel :=
    λ W Θ T F e, ∀ h, kinj h Θ → Φ W (kren h Θ) T F (emap h e).

  Lemma Erel_S_ind_ren n (Φ : erel) :
    (∀ W Θ T F e,
       Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n))
         (λ W Θ T F e, Erel κ (S n) W Θ T F e ∧ Φren Φ W Θ T F e) W Θ T F e →
       Φ W Θ T F e) →
    ∀ W Θ T F e, Erel κ (S n) W Θ T F e → Φren Φ W Θ T F e.
  Proof.
    intros Hind. refine (Erel_S_ind κ n _ _). intros W Θ T F e Hb h Hk.
    assert (Erel κ (S n) W Θ T F e) as HE.
    { apply Erel_S_iff. revert Hb. apply Ebody_mapX. by intros ? ? ? ? ? [? _]. }
    apply Hind. apply Ebody_rename; [|done|done|done].
    intros W' Θ' T' F' e' h' Hk' [H1 H2]. split; [by apply Erel_rename|].
    intros g Hg. rewrite kren_kren by done. rewrite emap_emap. apply H2. by apply kinj_kren.
  Qed.
End ren_ind.
