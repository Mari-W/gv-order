(** * The bind lemma for a hole that acts before it returns (stage S5)

      P e     e ∈ E[κ]^W _ n⟦Θ1 ⊢ T⟧^(F ∪ heads Θ2)
      ∀ W' ⊒ W, olt j n, Θv. v ∈ V[κ]^W' _ j⟦Θv ⊢ T⟧ ⟹ K[v] ∈ E[κ]^W' _ j⟦Θv ∪ Θ2 ⊢ U⟧^F
      ───────────────────────────────────────────────────────────────────────────
      K[e] ∈ E[κ]^W _ n⟦Θ1 ∪ Θ2 ⊢ U⟧^F                              [Erel_bind_acts]

    P is a property of terms that holds of no value and survives every
    step of cost 0. Then the hole takes a costly step before it returns,
    and the frame meets the value strictly below n. The guard uses it
    with P the terms that act ([acts], static/Guard.v) at a table where
    send, receive and their siblings cost one or more. A new fact about
    E, in a file of its own: the proof is the proof of [Erel_bind]
    (compat/Bind.v) inside one level, and [Erel_bind] itself once a
    costly step is taken. *)

From GV Require Export compat.Bind.

Section bind_acts.
  Context (κ : ctable).

  Lemma Erel_bind_acts (P : expr → Prop) n f W Θ1 Θ2 T U F e :
    (∀ e, P e → ¬ is_val e) →
    (∀ e α e', P e → tstep e α e' → tcost κ α = 0 → P e') →
    P e → frame_val f → Θ1 ##ₘ Θ2 →
    e ∈ E[κ]^W _ n⟦Θ1 ⊢ T⟧^(F ∪ senv_heads Θ2) →
    (∀ W' j Θv v, W ⊑ W' → olt j n → Θv ##ₘ Θ2 → v ∈ V[κ]^W' _ j⟦Θv ⊢ T⟧ →
       fill_frame f v ∈ E[κ]^W' _ j⟦Θv ∪ Θ2 ⊢ U⟧^F) →
    fill_frame f e ∈ E[κ]^W _ n⟦Θ1 ∪ Θ2 ⊢ U⟧^F.
  Proof.
    intros HPv HPs HPe Hf Hd HE HK.
    cut (∀ W Θ1 T F' e, Erel κ n W Θ1 T F' e → P e → ∀ Θ2, Θ1 ##ₘ Θ2 → F ∪ senv_heads Θ2 ⊆ F' →
           (∀ W' j Θv v, W ⊑ W' → olt j n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
              Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) →
           Erel κ n W (Θ1 ∪ Θ2) U F (fill_frame f e)).
    { intros H. eapply H; [exact HE|done|done|done|exact HK]. }
    clear W Θ1 Θ2 T e Hd HE HK HPe.
    refine (Erel_ind κ n _ _).
    intros W Θ1 T F' e Hb HPe Θ2 Hd HF HK.
    assert (Erel κ n W Θ1 T F' e) as HE.
    { apply Erel_iff. revert Hb. apply Ebody_mono; [intros; reflexivity|by intros
        |by intros|by intros|by intros ? ? ? ? []|by intros ? ? ? ? []]. }
    assert (¬ is_val e) as Hnv by (by apply HPv).
    apply Erel_iff. intros W1 HW1.
    pose proof (Erel_mono κ _ _ _ _ _ _ _ HW1 HE) as HE1.
    assert (∀ W' j Θv v, W1 ⊑ W' → olt j n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
              Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) as HK1.
    { intros W' j Θv v HW' Hj Hd' HV. apply HK; [by eapply wext_trans|done..]. }
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    (* the continuation after a step of cost c *)
    assert (∀ c Θ1' e', Θ1' ##ₘ Θ2 → (c = 0 → P e') →
      at_cost_E n c (Erel κ)
        (λ W Θ1 T F' e, Erel κ n W Θ1 T F' e ∧
          (P e → ∀ Θ2, Θ1 ##ₘ Θ2 → F ∪ senv_heads Θ2 ⊆ F' →
            (∀ W' j Θv v, W ⊑ W' → olt j n → Θv ##ₘ Θ2 → Vrel κ j W' Θv T v →
               Erel κ j W' (Θv ∪ Θ2) U F (fill_frame f v)) →
            Erel κ n W (Θ1 ∪ Θ2) U F (fill_frame f e))) W1 Θ1' T F' e' →
      at_cost_E n c (Erel κ) (Erel κ n) W1 (Θ1' ∪ Θ2) U F (fill_frame f e')) as Hac.
    { intros c Θ1' e' Hd' HPc [A1 A2]. split.
      - intros Hc. destruct (A1 Hc) as [_ HΦ]. apply HΦ; [by apply HPc|done|done|done].
      - intros Hc j Hj. eapply (Erel_bind κ j); [done|done| |].
        + eapply Erel_future; [|exact (A2 Hc j Hj)]. done.
        + intros W' j' Θv v HW' Hj' Hd'' HV. apply HK1; [done| |done|done].
          exact (ole_trans_lt _ _ _ Hj' (oadd_lt _ _ _ Hc Hj)). }
    split; [|split; [|unfold Esteps; split_and!]].
    - (* (stop) *)
      intros Hirr. exfalso. apply Hnv. eapply Vrel_val, Hs.
      intros α e' Hst. by apply (Hirr α (fill_frame f e')), tstep_fill.
    - (* (ready) *)
      intros _. exact (bind_ready κ n W1 Θ1 Θ2 T F F' f e Hf Hnv Hd HF HE1).
    - (* O-Beta *)
      intros E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      apply Hac; [done|intros Hc; exact (HPs _ _ _ HPe Hst' Hc)|by apply H1].
    - (* O-New *)
      intros ℓ c E' Hst [Hc1 Hc2] g Hg. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      rewrite dom_union_L in Hc1, Hc2.
      destruct (H2 ℓ c e' Hst' ltac:(split; set_solver) g) as [S HS].
      { intros o S0 x Ho. apply (Hg o S0 x). by apply lookup_union_Some_l. }
      exists S. unfold new_env in *. rewrite !insert_union_l.
      apply Hac; [|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact HS].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|done].
    - (* O-NewAt *)
      intros κf o c E' Hst [Hc1 Hc2]. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      rewrite dom_union_L in Hc1, Hc2.
      destruct (H3 κf o c e' Hst' ltac:(split; set_solver)) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [by apply lookup_union_Some_l|]. exists S.
      unfold new_env in *. rewrite !insert_union_l.
      apply Hac; [|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact HS].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|].
      apply map_disjoint_insert_l. split; [apply not_elem_of_dom; set_solver|done].
    - (* O-Spawn *)
      intros v E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H4 v e' Hst') as (ΘM & Θr & A1 & -> & A4 & A5).
      apply map_disjoint_union_l in Hd as [HdM Hdr].
      exists ΘM, (Θr ∪ Θ2). split_and!.
      + by apply map_disjoint_union_r.
      + by rewrite map_union_assoc.
      + revert A4. apply Varr_mono; [by intros|by intros|by intros|]. by intros _ ? ? ? ? ? ? [? _].
      + apply Hac; [done|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A5].
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
      + rewrite insert_union_l.
        apply Hac; [by apply map_disjoint_insert_l|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A7].
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
      eapply (Erel_bind κ j); [done| |eapply Erel_future; [|apply A3; [exact Hj|done|done]]; done|].
      + apply map_disjoint_union_l. split; [by apply map_disjoint_insert_l|by symmetry].
      + intros W' j' Θv v HW' Hj' Hd'' HV. apply HK1; [done| |done|done].
        exact (ole_trans_lt _ _ _ Hj' (c_take_lt κ n j Hj)).
    - (* O-Close *)
      intros o E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H7 o e' Hst') as (S0 & x & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite delete_union, (delete_id Θ2 o Ho2).
      apply Hac; [by apply map_disjoint_delete_l|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A3].
    - (* O-Select *)
      intros o i E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H8 o i e' Hst') as (S0 & x & S1 & S2 & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x, S1, S2. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite insert_union_l.
      apply Hac; [by apply map_disjoint_insert_l|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A3].
    - (* O-Branch *)
      intros o i E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H9 o i e' Hst') as (S0 & x & S1 & S2 & A1 & A2 & A3).
      assert (Θ2 !! o = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists S0, x, S1, S2. split_and!; [by apply lookup_union_Some_l|done|].
      rewrite insert_union_l.
      apply Hac; [by apply map_disjoint_insert_l|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A3].
    - (* O-Link *)
      intros os E' Hst. destruct (tstep_fill_inv _ _ _ _ Hf Hnv Hst) as (e' & Hst' & ->).
      destruct (H10 os e' Hst') as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      assert (Θ2 !! o1 = None) as Ho1 by (eapply map_disjoint_Some_l; eauto).
      assert (Θ2 !! o2 = None) as Ho2 by (eapply map_disjoint_Some_l; eauto).
      exists o1, o2, S1, S2, x. split_and!; try done; try by apply lookup_union_Some_l.
      rewrite !delete_union, (delete_id Θ2 o2 Ho2), (delete_id Θ2 o1 Ho1).
      apply Hac; [by do 2 apply map_disjoint_delete_l|intros Hc0; exact (HPs _ _ _ HPe Hst' Hc0)|exact A6].
  Qed.
End bind_acts.
