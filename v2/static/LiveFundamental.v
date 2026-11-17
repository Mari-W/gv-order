(** * The live fundamental theorem for guarded terms (stage S5, Appendix A.3)

      strict W ∧ Θ ; ∅ ; Δ ⊢^F_W t : T ∧ guarded t  ⟹  Θ ; Δ ⊫^F_W t : T
                                                          [live_fundamental]

    The induction of static/Fundamental.v, with the guard's marks. For
    every L that the guard admits for the term ([glive L t]) the term is
    in the judgment with marks L ([sem_later], compat/LiveRules.v). A
    rule of the guard picks the semantic rule: a frame keeps the marks or
    clears them after an acting hole ([kmarks]), a box marks its self, a
    contraction renames the marks. The proof is generic over a cost
    table where send, select and close cost one or more, and κ_L is one.

    D-SpawnLam has no semantic counterpart here either
    (compat/SpawnGap.v), and the theorem is proved from the semantic
    rule with marks as a premise ([spawn_lam_later]). *)

From GV Require Export static.Fundamental compat.LiveRules.

Section live.
  Context (κ : ctable) (Hg : 1 ≤ c_give κ) (Hsl : spawn_lam_later κ).

  Local Ltac heads_p :=
    rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?lenv_bot_pinst, ?heads_pinst, ?hbot_pinst,
      ?opt_heads_pinst.

  Local Ltac fut := etrans; [|apply den_unionb]; rewrite ?set_map_union_L; set_solver.

  Theorem dftyped_later W Θ Γ Δ F e T :
    world_wf W → Θ ; Γ ; Δ ⊢^F _ W e : T →
    ∀ L, glive L e → ∀ W1 σ ρ B, W ⊑ W1 → hsat W1 σ ρ Γ →
    sem_later κ W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) L (sf_den ρ B (sf_pinst σ F)) e (pinst_ty σ T).
  Proof.
    intros Hwf. induction 1 as
      [Γ Δ F HΔ
      |Γ Δ F x T a HΔ
      |Γ Δ F o S x a HΔ
      |Θ Γ Δ F e T aT U aU ub lb c t h φ Hφ Hlb Hb IH
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 ub lb c t h T aT U aU Hsp Hl Hub H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 Hsp Hl H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T Hsp Hl H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 b1 b2 T Hsp Hl H1 IH1 H2 IH2
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 b1 T Hsp Hl H1 IH1 H2 IH2
      |Θ Γ Δ F e T a U b H IH
      |Θ Γ Δ F e T a U b H IH
      |Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e e1 e2 T1 a1 T2 a2 b1 b2 T Hsp Hl H0 IH0 H1 IH1 H2 IH2
      |Γ Δ F e m k C ub c t U aU a φ HΔ Hφ Hb IH
      |Θ Γ Δ F e m k C ub c t U aU xs ss Hxs HC Hss Hsi Hub H IH
      |Θ Γ Δ F e S0 x m T b S ap aS Hu Hsc Hbot Hh Hub H IH
      |Θ Γ Δ F e S0 x m T b S b' a' Hu Hsc Hub H IH
      |Θ Γ Δ F e S0 x Hu Hub H IH
      |i Θ Γ Δ F e S0 x S1 S2 Hu Hf Hub H IH
      |Θ Γ Δ F e S0 x S1 S2 a1 a2 Hu Hf1 Hf2 Hub H IH
      |Θ Γ Δ F e S x a1 a2 H IH
      |Θ Γ Δ F e a1 H IH
      |Θ Γ Δ F e ub lb c' t' h a1 aU H IH
      |Γ Δ F ℓ S a1 a2 a3 HΔ Hℓ
      |Θ Γ Δ F e κf S0 x S a a1 a2 a3 H IH
      |Θ Γ Δ F e T T' a a' Hsub H IH
      |Θ Γ Δ' Δ F e T Hwk H IH
      |Θ Γ Δ U aU F e T Hu H IH
      |Θ Γ Δ F e lb m C T aT xs Hxs HC Hlbx H IH
      |Θ Γ Δ F e i lb m C T aT a b U Hi Hnu H IH];
      intros L Hgl W1 σ ρ B HW Hs; cbn [pinst_ty]; rewrite ?tenv_pinst_empty, ?tenv_pinst_singleton.
    - (* D-Unit *)
      by apply later_unit, lenv_empty_pinst.
    - (* D-Var *)
      inversion Hgl; subst. by eapply later_var; [apply lenv_only_pinst|].
    - (* D-Chan *)
      by apply later_chan, lenv_empty_pinst.
    - (* D-Abs *)
      assert (glive (false .: L) e) as Hgb by (inversion Hgl; subst; done).
      destruct (lb_sem W W1 Hwf HW σ ρ Γ _ _ _ Hs Hlb) as [Hbot Hlb'].
      apply later_abs.
      + apply tfacts_pinst, (tfacts_lam _ (Some (T, aT))). exact (dftyped_tfacts _ _ _ _ _ _ _ Hb).
      + by rewrite lenv_bot_pinst.
      + heads_p. rewrite <-set_map_union_L. exact Hlb'.
      + intros W2 F' HW2 Hub'.
        pose proof (IH _ Hgb W2 σ _ B (wext_trans _ _ _ HW HW2)
                      (hsat_fvar _ _ _ _ _ _ _ Hφ (hsat_mono _ _ _ _ _ HW2 Hs) Hub')) as Hb'.
        rewrite den_nil, den_fresh in Hb'. exact Hb'.
    - (* D-App *)
      assert (∃ L', kmarks κ L L' e1 ∧ glive L e1 ∧ glive L' e2) as (L' & Hk & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right]. }
      eapply later_app; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst
                        |exact (ub_sem W W1 Hwf HW σ ρ B Γ ub F Hs Hub)| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + eapply sem_later_future; [|apply (IH2 L' Hg2 W1 σ ρ B HW Hs)].
        rewrite den_union, opt_heads_pinst. done.
    - (* D-Pair *)
      assert (∃ L', kmarks κ L L' e1 ∧ glive L e1 ∧ glive L' e2) as (L' & Hk & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right]. }
      eapply later_pair; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |].
      + intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
      + intros B'. eapply sem_later_future; [|apply (IH2 L' Hg2 W1 σ ρ (B ∪ B') HW Hs)].
        heads_p. fut.
    - (* D-LetU *)
      assert (∃ L', kmarks κ L L' e1 ∧ glive L e1 ∧ glive L' e2) as (L' & Hk & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right]. }
      eapply later_letu; [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH2].
      intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-LetP *)
      assert (∃ L', kmarks κ L L' e1 ∧ glive L e1 ∧ glive (false .: false .: L') e2)
        as (L' & Hk & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right|].
        eapply glive_ext; [|done]. by intros [|[|x]]. }
      eapply (later_letp κ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 b1 b2);
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH2].
      intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-Let *)
      assert (∃ L', kmarks κ L L' e1 ∧ glive L e1 ∧ glive (false .: L') e2) as (L' & Hk & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right|].
        eapply glive_ext; [|done]. by intros [|x]. }
      eapply (later_let κ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) b1);
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH2].
      intros B'. eapply sem_later_future; [|apply (IH1 L Hg1 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-Inj1 *)
      inversion Hgl; subst. by apply later_inj1, IH.
    - (* D-Inj2 *)
      inversion Hgl; subst. by apply later_inj2, IH.
    - (* D-Case *)
      assert (∃ L', kmarks κ L L' e ∧ glive L e ∧ glive (false .: L') e1 ∧ glive (false .: L') e2)
        as (L' & Hk & Hg0 & Hg1 & Hg2).
      { inversion Hgl; subst; eexists; split_and!; try done; [by left|by right| |];
          (eapply glive_ext; [|done]; by intros [|x]). }
      eapply (later_case κ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinst_ty σ T1) a1 (pinst_ty σ T2) a2 b1 b2);
        [exact Hk|by apply tsplit_pinst|by apply lenv_split_pinst| |by apply IH1|by apply IH2].
      intros B'. eapply sem_later_future; [|apply (IH0 L Hg0 W1 σ ρ (B ∪ B') HW Hs)].
      heads_p. fut.
    - (* D-Box *)
      assert (glive (true .: L) e) as Hgb by (inversion Hgl; subst; done).
      destruct (slist_witness_inf k) as [ss0 [Hl0 Hs0]].
      pose proof (dftyped_tfacts _ _ _ _ _ _ _ (Hb ss0 Hl0 Hs0)) as Htf.
      rewrite <-(tenv_pinst_empty (pshift m)) in Htf.
      apply tfacts_unpinst, tfacts_box, (tfacts_pinst σ) in Htf. rewrite tenv_pinst_empty in Htf.
      apply later_box with (a := a); [exact Htf|by apply lenv_unl_pinst|].
      intros W2 xs ss F' HW2 Hxs Hss Hsc HC Hub'.
      assert (∀ a, pt_inst (pclose xs m σ) (pshift m a) = σ a) as Hτ by (by apply pclose_shift).
      assert (sinsts None (sty_df <$> ss)) as Hss'
        by (apply (sinsts_df (Some 0)); split; [done|discriminate]).
      assert (hsat W2 (pclose xs m σ) (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                (hc_fvar φ ub (hc_open m C Γ))) as Hs'.
      { apply hsat_fvar; [done|apply hsat_open; [exact Hxs|exact (hsat_mono _ _ _ _ _ HW2 Hs)|exact HC]|].
        destruct ub as [u|]; [|done]. simpl in Hub' |- *. by rewrite pclose_pt. }
      pose proof (IH (sty_df <$> ss) ltac:(by rewrite length_fmap) Hss' _ Hgb W2 (pclose xs m σ) _ B
                    (wext_trans _ _ _ HW HW2) Hs') as Hb'.
      rewrite tenv_pinst_empty, den_nil, den_fresh, (lenv_unshift _ σ m Hτ) in Hb'.
      rewrite pinst_sinst, pclose_ty in Hb'.
      eapply sem_later_blind; [|exact Hb'].
      rewrite !ty_df_sinst_map, <-list_fmap_compose.
      f_equal. f_equal. apply list_fmap_ext. intros _ s _. apply sty_df_idem.
    - (* D-Force *)
      assert (glive L e) as Hge by (inversion Hgl; subst; done).
      subst m. rewrite pinst_sinst, pinst_ty_inst.
      eapply (later_force κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|done|exact (proj1 Hsi)|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)| |by apply IH].
      assert (pt_inst σ <$> (pt_inst (plist xs) <$> ub) =
              pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup (length xs) σ) <$> ub)) as <-.
      { destruct ub; simpl; [|done]. f_equal. apply pt_inst_plist_inst. }
      exact (ub_sem W W1 Hwf HW σ ρ B Γ _ F Hs Hub).
    - (* D-Send *)
      inversion Hgl; subst. rewrite pt_inst_shift.
      eapply (later_send κ _ _ _ _ _ _ S0 (pt_inst σ x) m T b S ap aS Hu).
      + rewrite <-(pinst_payload_at σ) by done. rewrite hbot_pinst. unfold payload_at, ty_inst.
        by rewrite hbot_pinst.
      + intros y. rewrite <-(pinst_payload_at σ), heads_pinst by done.
        intros (y0 & -> & Hy)%elem_of_map. by eapply slt_sem, Hh.
      + exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub).
      + rewrite <-(pinst_payload_at σ) by done. by apply IH.
    - (* D-Recv *)
      inversion Hgl; subst. rewrite pinst_payload_at, pt_inst_shift by done.
      eapply later_recv; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Close *)
      inversion Hgl; subst.
      eapply later_close; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Select *)
      inversion Hgl; subst. rewrite pt_inst_sel.
      eapply later_select; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|by apply IH].
    - (* D-Branch *)
      inversion Hgl; subst. rewrite !pt_inst_bra.
      eapply later_branch; [exact Hu|exact (ub_sem W W1 Hwf HW σ ρ B Γ (Some x) F Hs Hub)|].
      exact (IH L ltac:(done) W1 σ ρ B HW Hs).
    - (* D-Link *)
      inversion Hgl; subst.
      pose proof (IH L ltac:(done) W1 σ ρ B HW Hs) as IH'. cbn [pinst_ty] in IH'. rewrite pt_inst_dual in IH'.
      eapply later_link, IH'.
    - (* D-SpawnLam *)
      assert (glive (false .: L) e) as Hgb.
      { inversion Hgl as [| | | | | |? ? ? Hgl'| | | | | | | | | | | | | |]; subst.
        by inversion Hgl'; subst. }
      apply (Hsl W1 _ _ _ _ e a1).
      + apply tfacts_pinst, (tfacts_lam _ (Some (TUnit, a1))). exact (dftyped_tfacts _ _ _ _ _ _ _ H).
      + intros W2 HW2. pose proof (IH _ Hgb W2 σ ρ B (wext_trans _ _ _ HW HW2) (hsat_mono _ _ _ _ _ HW2 Hs)) as H'.
        by rewrite den_nil, den_none in H'.
    - (* D-Spawn *)
      inversion Hgl; subst.
      pose proof (IH L ltac:(done) W1 σ ρ B HW Hs) as IH'. cbn [pinst_ty] in IH'. eapply later_spawn, IH'.
    - (* D-New *)
      rewrite pt_inst_dual, pt_inst_pup1_0.
      change (bcs_inst σ (bcs_of (w_laws W ℓ))) with (bcs_of (w_laws W ℓ)).
      apply later_new_ext; [done|by apply lenv_empty_pinst|done].
    - (* D-NewAt *)
      inversion Hgl; subst. rewrite pt_inst_dual, pt_inst_field. eapply later_new_at. by apply IH.
    - (* D-Conv *)
      eapply (later_conv κ _ _ _ _ _ _ (pinst_ty σ T)); [|by apply IH].
      rewrite !ty_df_pinst. by apply tsub_pinst.
    - (* D-Weak *)
      eapply later_weak; [by apply lenv_wk_pinst|by apply IH].
    - (* D-Contract *)
      change (lenv_pinst σ (Some (U, aU) :: Δ)) with (Some (pinst_ty σ U, aU) :: lenv_pinst σ Δ).
      apply later_contract; [by apply unlimited_pinst|].
      exact (IH _ (glive_rename e L pred Hgl) W1 σ ρ B HW Hs).
    - (* D-Pack *)
      subst m. eapply (later_pack κ _ _ _ _ _ _ _ _ _ _ _ (pt_inst σ <$> xs));
        [by rewrite length_fmap|exact (hold_sem W W1 Hwf HW σ ρ Γ C xs Hs HC)| |].
      + rewrite <-pinst_ty_inst. exact (lbx_sem W W1 Hwf HW σ ρ Γ lb (ty_inst xs T) Hs Hlbx).
      + rewrite <-pinst_ty_inst. by apply IH.
    - (* D-Open *)
      intros n W' Θ' γ HW' Hd HG.
      assert (lenv_pinst σ Δ !! i = Some (Some (TEx (lb_map (pt_inst σ) lb) m (bcs_inst σ C)
                (pinst_ty (pup m σ) T) aT, a))) as Hi' by (by rewrite lenv_pinst_lookup, Hi).
      destruct (GrelL_pick κ _ _ _ _ _ _ _ _ _ Hi' ltac:(intros []) HG) as (Θi & HVi & Hk).
      apply Vrel_ex_iff in HVi as (_ & xs & Hxs & HC & HVi).
      pose proof (pclose_shift xs m σ Hxs) as Hτ.
      pose proof (IH L Hgl W' (pclose xs m σ) ρ B (wext_trans _ _ _ HW HW')
                    (hsat_open _ _ _ _ _ _ _ Hxs (hsat_mono _ _ _ _ _ HW' Hs) HC)) as Hb'.
      rewrite (tenv_unshift _ σ m Hτ), lenv_pinst_insert, (lenv_unshift _ σ m Hτ),
        (sf_unshift _ σ m Hτ), (ty_unshift _ σ m Hτ), pclose_ty in Hb'.
      apply (Hb' n W' Θ' γ (wext_refl _) Hd). by apply Hk.
  Qed.
End live.

(** ** The theorems *)

(** The live fundamental theorem, from the semantic rule E-SpawnLam
    with marks. *)
Theorem live_fundamental_of_spawn_lam W Θ Δ F t T :
  spawn_lam_later κ_L → strict W → Θ ; hc_empty ; Δ ⊢^F _ W t : T → guarded t →
  Θ ; Δ ⊫^F _ W t : T.
Proof.
  intros Hsl HW Ht Hgd ρ B. apply sem_later_noL.
  pose proof (dftyped_later κ_L ltac:(simpl; lia) Hsl W Θ hc_empty Δ F t T (proj1 HW) Ht noL Hgd
                W pvar ρ B (wext_refl _) (hsat_empty _ _ _)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H. exact H.
Qed.

Theorem live_fundamental_typed_of_spawn_lam W N Θ Δ F t T a c ϑ :
  spawn_lam_later κ_L → strict W → Θ ; hc_empty ; Δ ⊢^F _{W,N} t : T ^ a ▷ c ; ϑ → guarded t →
  tenv_df Θ ; lenv_df Δ ⊫^F _ W t : ty_df T.
Proof.
  intros Hsl HW Ht Hgd. apply live_fundamental_of_spawn_lam; [done|done| |done].
  exact (typed_dftyped _ _ _ _ _ _ _ _ _ _ _ Ht).
Qed.
