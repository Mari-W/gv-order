(** * The bind lemma, once for every cost table (stage S4, proposal §2.8)

      e ∈ E[κ]^W _ n⟦Θ1 ⊢ T⟧^(F ∪ heads Θ2)
      ∀ W' ⊒ W, j ≤ n, Θv. v ∈ V[κ]^W' _ j⟦Θv ⊢ T⟧ ⟹ K[v] ∈ E[κ]^W' _ j⟦Θv ∪ Θ2 ⊢ U⟧^F
      ───────────────────────────────────────────────────────────────────────────
      K[e] ∈ E[κ]^W _ n⟦Θ1 ∪ Θ2 ⊢ U⟧^F

    for one evaluation frame K ([Erel_bind]). The frame holds Θ2, and
    the hole runs with the heads of Θ2 in its future. A step of the hole
    is a step of K[e] at the same cost, so a step of cost 0 uses the
    induction over the least fixpoint and a step of cost c > 0 the
    induction on the level. The ends a step of the hole acts on are ends
    of Θ1 ([Erel_sends]), so the frame's ends are never touched, and
    readiness of K[e] is the readiness of the hole with the heads of Θ2
    in its future. No strictness of W is needed. *)

From GV Require Export relation.Closure.

Section bind.
  Context (κ : ctable).

  (** ** The clauses of E at a positive level, in the current world *)

  Lemma Erel_S_stop n W Θ T F e : Erel κ (S n) W Θ T F e → irred e → Vrel κ (S n) W Θ T e.
  Proof. intros HE. apply Erel_S_iff in HE. by destruct (HE W (wext_refl W)) as (? & _). Qed.

  Lemma Erel_S_ready n W Θ T F e :
    Erel κ (S n) W Θ T F e → ¬ irred e → ready _ W(Θ ∣ F, e).
  Proof. intros HE. apply Erel_S_iff in HE. by destruct (HE W (wext_refl W)) as (_ & ? & _). Qed.

  (** The ends a step acts on are held. *)
  Lemma Erel_sends n W Θ T F e σ e' :
    Erel κ (S n) W Θ T F e → tstep e (LSess σ) e' → sends σ ⊆ dom Θ.
  Proof.
    intros HE Hst. pose proof (Erel_S_step κ n W W Θ T F e _ e' HE (wext_refl W) Hst) as H.
    destruct σ as [o w|o w|o|o i|o i|os]; simpl in H |- *.
    - destruct H as (? & ? & ? & ? & ? & ? & ? & Ho & _). apply elem_of_dom_2 in Ho. set_solver.
    - destruct H as (? & ? & ? & ? & ? & Ho & _). apply elem_of_dom_2 in Ho. set_solver.
    - destruct H as (? & ? & Ho & _). apply elem_of_dom_2 in Ho. set_solver.
    - destruct H as (? & ? & ? & ? & Ho & _). apply elem_of_dom_2 in Ho. set_solver.
    - destruct H as (? & ? & ? & ? & Ho & _). apply elem_of_dom_2 in Ho. set_solver.
    - destruct H as (o1 & o2 & ? & ? & ? & -> & _ & H1 & H2 & _).
      apply elem_of_dom_2 in H1. apply elem_of_dom_2 in H2. set_solver.
  Qed.

  (** ** Readiness under a frame *)

  Section readiness.
    Context (n : nat) (W : world) (Θ1 Θ2 : senv) (T : ty) (F F' : gset point).
    Context (f : frame) (e : expr) (Hf : frame_val f) (Hv : ¬ is_val e).
    Context (Hd : Θ1 ##ₘ Θ2) (HF : F ∪ senv_heads Θ2 ⊆ F').
    Context (HE : Erel κ (S n) W Θ1 T F' e).

    Lemma bind_offered_up o : offered_t Θ1 e o → offered_t (Θ1 ∪ Θ2) (fill_frame f e) o.
    Proof.
      intros [Ho (σ & e' & Hst & Hs)]. split; [rewrite dom_union_L; set_solver|].
      exists σ, (fill_frame f e'). split; [by apply tstep_fill|done].
    Qed.

    Lemma bind_offered_down o : offered_t (Θ1 ∪ Θ2) (fill_frame f e) o → offered_t Θ1 e o.
    Proof.
      intros [_ (σ & E' & Hst & Hs)].
      destruct (tstep_fill_inv _ _ _ _ Hf Hv Hst) as (e' & Hst' & ->).
      split; [by apply (Erel_sends _ _ _ _ _ _ _ _ HE Hst')|]. eauto.
    Qed.

    Lemma bind_ready : ready _ W(Θ1 ∪ Θ2 ∣ F, fill_frame f e).
    Proof.
      assert (¬ irred e) as Hni.
      { intros Hi. apply Hv. eapply Vrel_val, (Erel_S_stop _ _ _ _ _ _ HE Hi). }
      intros Hs. assert (stable_t e) as Hse.
      { intros α e' Hst. exact (Hs _ _ (tstep_fill _ _ _ _ Hf Hst)). }
      destruct (Erel_S_ready _ _ _ _ _ _ HE Hni Hse) as [Hval Hab]. split.
      - intros Hno. exfalso. apply Hv, Hval. intros o Ho. by apply (Hno o), bind_offered_up.
      - destruct Hab as [(os & e1 & Hl)|Hab].
        { left. exists os, (fill_frame f e1). by apply tstep_fill. }
        right. intros o S x Hoff Hx. pose proof (bind_offered_down o Hoff) as Hoff1.
        assert (Θ1 !! o = Some (S, x)) as Hx1.
        { destruct Hoff1 as [Hin _]. apply elem_of_dom in Hin as [[S1 x1] H1].
          rewrite (lookup_union_Some_l _ _ _ _ H1) in Hx. by simplify_eq. }
        destruct (Hab o S x Hoff1 Hx1) as [H1 H2]. split.
        + intros o' S' x' Hx' Hno.
          apply lookup_union_Some_raw in Hx' as [Hx'|[_ Hx']].
          * apply (H1 o' S' x' Hx'). intros Ho'. by apply Hno, bind_offered_up.
          * apply H2, HF, elem_of_union_r, elem_of_senv_heads. eauto.
        + intros y Hy. apply H2, HF. set_solver.
    Qed.
  End readiness.

  (** ** The bind lemma *)

  Lemma Erel_bind n : ∀ f W Θ1 Θ2 T U F e,
    frame_val f → Θ1 ##ₘ Θ2 →
    e ∈ E[κ]^W _ n⟦Θ1 ⊢ T⟧^(F ∪ senv_heads Θ2) →
    (∀ W' j Θv v, W ⊑ W' → j ≤ n → Θv ##ₘ Θ2 → v ∈ V[κ]^W' _ j⟦Θv ⊢ T⟧ →
       fill_frame f v ∈ E[κ]^W' _ j⟦Θv ∪ Θ2 ⊢ U⟧^F) →
    fill_frame f e ∈ E[κ]^W _ n⟦Θ1 ∪ Θ2 ⊢ U⟧^F.
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    intros f W Θ1 Θ2 T U F e Hf Hd HE HK.
    destruct n as [|n]; [apply Erel_0|].
    cut (∀ W Θ1 T F' e, Erel κ (S n) W Θ1 T F' e → ∀ Θ2, Θ1 ##ₘ Θ2 → F ∪ senv_heads Θ2 ⊆ F' →
           (∀ W' j Θv v, W ⊑ W' → j ≤ S n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
              Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) →
           Erel κ (S n) W (Θ1 ∪ Θ2) U F (fill_frame f e)).
    { intros H. eapply H; [exact HE|done|done|exact HK]. }
    clear W Θ1 Θ2 T e Hd HE HK.
    refine (Erel_S_ind κ n _ _).
    intros W Θ1 T F' e Hb Θ2 Hd HF HK.
    assert (Erel κ (S n) W Θ1 T F' e) as HE.
    { apply Erel_S_iff. revert Hb. apply Ebody_mono; [lia|intros; reflexivity|by intros
        |by intros|by intros|by intros ? ? ? ? []|by intros ? ? ? ? []]. }
    destruct (is_val e) eqn:Hv.
    { apply (HK W (S n) Θ1 e); [apply wext_refl|lia|done|].
      apply (Erel_S_stop _ _ _ _ _ _ HE), val_irred. by rewrite Hv. }
    assert (¬ is_val e) as Hnv by (rewrite Hv; intros []).
    apply Erel_S_iff. intros W1 HW1.
    pose proof (Erel_mono κ _ _ _ _ _ _ _ HW1 HE) as HE1.
    assert (∀ W' j Θv v, W1 ⊑ W' → j ≤ S n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
              Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) as HK1.
    { intros W' j Θv v HW' Hj Hd' HV. apply HK; [by eapply wext_trans|done..]. }
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    (* the continuation after a step of cost c *)
    assert (∀ c Θ1' e', Θ1' ##ₘ Θ2 →
      at_cost_E (S n) c (Erel κ)
        (λ W Θ1 T F' e, Erel κ (S n) W Θ1 T F' e ∧
          ∀ Θ2, Θ1 ##ₘ Θ2 → F ∪ senv_heads Θ2 ⊆ F' →
            (∀ W' j Θv v, W ⊑ W' → j ≤ S n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
               Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) →
            Erel κ (S n) W (Θ1 ∪ Θ2) U F (fill_frame f e)) W1 Θ1' T F' e' →
      at_cost_E (S n) c (Erel κ) (Erel κ (S n)) W1 (Θ1' ∪ Θ2) U F (fill_frame f e')) as Hac.
    { intros c Θ1' e' Hd' [A1 A2]. split.
      - intros Hc. destruct (A1 Hc) as [_ HΦ]. by apply HΦ.
      - intros Hc. eapply (IHn (S n - c)); [lia|done|done| |].
        + eapply Erel_future; [|exact (A2 Hc)]. done.
        + intros W' j Θv v HW' Hj Hd'' HV. apply HK1; [done|lia|done|done]. }
    split; [|split; [|unfold Esteps; split_and!]].
    - (* (stop) *)
      intros Hirr. exfalso. apply Hnv. eapply Vrel_val, Hs.
      intros α e' Hst. by apply (Hirr α (fill_frame f e')), tstep_fill.
    - (* (ready) *)
      intros _. exact (bind_ready n W1 Θ1 Θ2 T F F' f e Hf Hnv Hd HF HE1).
    - (* O-Beta *)
      intros E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      by apply Hac, H1.
    - (* O-New *)
      intros ℓ c E' Hst [Hc1 Hc2] g Hg. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      rewrite dom_union_L in Hc1, Hc2.
      destruct (H2 ℓ c e' Hst' ltac:(split; set_solver) g) as [S HS].
      { intros o S0 x Ho. apply (Hg o S0 x). by apply lookup_union_Some_l. }
      exists S. unfold new_env in *. rewrite !insert_union_l. apply Hac; [|exact HS].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|done].
    - (* O-NewAt *)
      intros κf o c E' Hst [Hc1 Hc2]. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      rewrite dom_union_L in Hc1, Hc2.
      destruct (H3 κf o c e' Hst' ltac:(split; set_solver)) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [by apply lookup_union_Some_l|]. exists S.
      unfold new_env in *. rewrite !insert_union_l. apply Hac; [|exact HS].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|done].
    - (* O-Spawn *)
      intros v E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H4 v e' Hst') as (ΘM & Θr & A1 & -> & A4 & A5).
      apply map_disjoint_union_l in Hd as [HdM Hdr].
      exists ΘM, (Θr ∪ Θ2). split_and!.
      + by apply map_disjoint_union_r.
      + by rewrite map_union_assoc.
      + revert A4. apply Vthunk_mono; [by intros|by intros|by intros|]. by intros _ ? ? ? ? [? _].
      + by apply Hac.
    - (* O-Send *)
      intros o w E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H5 o w e' Hst') as (S0 & x & m & U' & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      assert (ΘM ##ₘ Θ2 ∧ Θr ##ₘ Θ2) as [HdM Hdr].
      { apply map_disjoint_union_l. rewrite <-A4. by apply map_disjoint_delete_l. }
      exists S0, x, m, U', S, ΘM, (Θr ∪ Θ2). split_and!; try done.
      + by apply lookup_union_Some_l.
      + by apply map_disjoint_union_r.
      + by rewrite delete_union, A4, (delete_id Θ2 o Ho2), map_union_assoc.
      + rewrite insert_union_l. apply Hac; [|exact A7].
        by apply map_disjoint_insert_l.
    - (* O-Recv *)
      intros o w E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H6 o w e' Hst') as (S0 & x & m & U' & S & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x, m, U', S. split_and!; [by apply lookup_union_Some_l|done|].
      intros j Θin Hj Hdin Hw.
      apply map_disjoint_union_l in Hdin as [Hd1 Hd2].
      assert (<[o:=(S, x⁺)]> (Θ1 ∪ Θ2) ∪ Θin = (<[o:=(S, x⁺)]> Θ1 ∪ Θin) ∪ Θ2) as ->.
      { rewrite insert_union_l, <-!map_union_assoc. f_equal. by apply map_union_comm. }
      pose proof (c_take_pos κ).
      eapply (IHn j); [lia|done| |eapply Erel_future; [|apply A3; [lia|done|done]]; done|].
      + apply map_disjoint_union_l. split; [by apply map_disjoint_insert_l|by symmetry].
      + intros W' j' Θv v HW' Hj' Hd'' HV. apply HK1; [done|lia|done|done].
    - (* O-Close *)
      intros o E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H7 o e' Hst') as (S0 & x & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite delete_union, (delete_id Θ2 o Ho2). apply Hac; [|exact A3].
      by apply map_disjoint_delete_l.
    - (* O-Select *)
      intros o i E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H8 o i e' Hst') as (S0 & x & S1 & S2 & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x, S1, S2. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite insert_union_l. apply Hac; [|exact A3]. by apply map_disjoint_insert_l.
    - (* O-Branch *)
      intros o i E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H9 o i e' Hst') as (S0 & x & S1 & S2 & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x, S1, S2. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite insert_union_l. apply Hac; [|exact A3]. by apply map_disjoint_insert_l.
    - (* O-Link *)
      intros os E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H10 os e' Hst') as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      assert (Θ2 !! o1 = None) as Ho1 by (eapply map_disjoint_Some_l; eauto).
      assert (Θ2 !! o2 = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists o1, o2, S1, S2, x. split_and!; try done; try by apply lookup_union_Some_l.
      rewrite !delete_union, (delete_id Θ2 o2 Ho2), (delete_id Θ2 o1 Ho1).
      apply Hac; [|exact A6]. by do 2 apply map_disjoint_delete_l.
  Qed.
End bind.
