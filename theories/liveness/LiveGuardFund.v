(** * The guarded live fundamental theorem for terms (liveness.md §10)

    A statically typed term whose boxes are all guarded is in the live
    E relation. The proof follows [typed_sem_rules] (static/Fundamental.v):
    one induction on the typing derivation, with the futures and point
    variables instantiated. It shows the later judgment for every marking
    the guard admits ([okR]), and, for a λ, V at level 0, which an applied
    λ with a guarded argument reads. E-Exp-Live takes the self as one more
    later variable ([lsem_later_box_live]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveGuardRules liveness.GuardMarks static.Fundamental liveness.GuardEx.

Set Default Proof Using "All".
Local Set Warnings "-register-all".

Lemma typed_live W Φ Ψ Θ Δ F e T :
  typed W Φ Ψ Θ Δ F e T → gallM e = true →
  ∀ W1 ρ σ, world_wf W → wext W W1 → inst_ok W1 (fhyps_pinst σ Φ) ρ →
  hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
  (∀ Lm, okR Lm e = true →
     lsem_later W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) Lm (sf_inst ρ (sf_pinst σ F)) e (pinst_ty σ T)) ∧
  (is_lam e = true → ∀ Lm, lsem_v0 W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) Lm e (pinst_ty σ T)).
Proof.
  induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk Hks
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ Hs Hk
    |Φ Ψ Θ Δ F e T U ub lb φ Hφ Hlb Hb IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |Φ Ψ Δ F e m k C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH
    |Φ Ψ Θ Δ F e lb m C T xs Hxs HK HC Hlb H IH
    |Φ Ψ Θ Δ F e i lb m C T U Hi Hnu Hb IH]; intros Hgall W1 ρ σ HW HW1 Hρ HΨ;
    pose proof HW1 as (HN & He & Hl & HS).
  - rewrite tenv_pinst_empty. split; [intros Lm _|done].
    apply lsem_later_free; [by apply lfree_empty, lenv_empty_pinst|]. apply lsem_typed_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. split; [intros Lm _|done].
    apply lsem_later_free; [by apply lfree_empty, lenv_empty_pinst|].
    apply lsem_typed_konst; [by apply lenv_empty_pinst|].
    apply (konst_ty_pinst W W1 σ HW HW1 (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
    + intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
    + intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    + intros x Hx. by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
  - rewrite tenv_pinst_empty. split; [intros Lm Hok|done].
    change (negb (marked Lm x) || false = true) in Hok. unfold marked in Hok.
    apply lsem_later_free; [apply (lfree_only _ _ x (pinst_ty σ T)); [by apply lenv_only_pinst|by destruct (Lm x)]|].
    apply lsem_typed_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl. split; [intros Lm _|done].
    apply lsem_later_free; [by apply lfree_empty, lenv_empty_pinst|].
    apply lsem_typed_chan; [by apply lenv_empty_pinst|done|by apply (seqs_pinst W W1 σ HW HW1 Ψ)].
  - cbn [pinst_ty]. unfold lb_below_hb in Hlb. destruct (lenv_bot Δ) eqn:Hbot; [done|].
    assert (term_wf (tenv_pinst σ Θ) (Some (pinst_ty σ T) :: lenv_pinst σ Δ) e) as Hwf'.
    { assert (term_wf Θ (lenv_pinst σ (Some T :: Δ)) e) as (Hfc & Hwf)
        by (rewrite term_wf_lenv_pinst; exact (typed_term_wf_s _ _ _ _ _ _ _ _ Hb)).
      split; [unfold tenv_pinst; by rewrite dom_fmap_L|exact Hwf]. }
    assert (lenv_bot (lenv_pinst σ Δ) = false) as Hbot' by (by rewrite lenv_bot_pinst).
    assert (lb_below W1 (pt_inst σ <$> lb) (tenv_heads (tenv_pinst σ Θ) ∪ lenv_heads (lenv_pinst σ Δ))) as Hlb'.
    { rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst W W1 σ HW HW1 Ψ). }
    split; [intros Lm Hok|intros _ Lm; by apply lsem_v0_lam].
    assert (okR (None .: Lm) e = true) as Hok'.
    { rewrite okR_eq in Hok. apply orb_true_iff in Hok as [Hok|Hok]; [|exact Hok].
      apply okM_okR, occursM_false_okM. simpl in Hok. by apply negb_true_iff in Hok. }
    apply lsem_later_lam; [done|done|done|].
    intros W2 F' HW2 Hub'. rewrite <-(sf_inst_fresh ρ φ F'), <-(sf_pinst_fresh σ φ).
    refine (proj1 (IH Hgall W2 _ σ HW (wext_trans _ _ _ HW1 HW2) _ _) _ Hok').
    + apply inst_ok_pinst_insert; [exact (inst_ok_mono _ _ _ _ HW2 Hρ)|exact Hub'].
    + exact (hyps_hold_wext _ _ _ HW2 HΨ).
  - (* E-App *)
    simpl in Hgall. apply andb_true_iff in Hgall as [Hg1 Hg2].
    destruct (IH1 Hg1 W1 ρ σ HW HW1 Hρ HΨ) as [IH1l IH1v].
    destruct (IH2 Hg2 W1 ρ σ HW HW1 Hρ HΨ) as [IH2l IH2v].
    assert (tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2)) as Hc'
      by (by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ)).
    assert (lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)) as Hsp' by (by apply lenv_split_pinst).
    assert (ub_below W1 (pt_inst σ <$> ub) (sf_inst ρ (sf_pinst σ F))) as Hub'.
    { apply (ub_below_s_inst W1 W1 (fhyps_pinst σ Φ)); [apply HS|exact (wext_refl _ HS)|done|].
      apply (ub_below_s_pinst W W1 σ Ψ []); [done|done| |done].
      by apply (hyps_hold_ground W W1 σ HW HW1). }
    split; [intros Lm Hok|done].
    change (okM Lm (App e1 e2) || false = true) in Hok. rewrite orb_false_r in Hok.
    destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->.
      change (match Lm y with Some f => f && gd e2 && okM Lm e2 | None => okM Lm e2 end = true) in Hok.
      destruct (Lm y) as [f|] eqn:HLy.
      * apply andb_true_iff in Hok as [Hok Hok2]. apply andb_true_iff in Hok as [-> Hgd].
        pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ H1) as Hwf1.
        destruct Hwf1 as (Hfc1 & Hav1 & Hrel1). simpl in Hav1. destruct Hav1 as [_ (T0 & HT0)].
        apply (lsem_later_app_force W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                 _ _ y (pinst_ty σ T0) _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T));
          [done|done|done|done| |done| | |].
        { by rewrite lenv_pinst_lookup, HT0. }
        { change (term_wf (tenv_pinst σ Θ1) (lenv_pinst σ Δ1) (App EForce (Var y))).
          rewrite term_wf_lenv_pinst. split_and!; [unfold tenv_pinst; by rewrite dom_fmap_L|by split; [|exists T0]|done]. }
        { future_pinst. apply lsem_later_now, IH1l, okR_noL. }
        { future_pinst. apply IH2l, okM_okR, Hok2. }
      * eapply (lsem_later_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                  _ _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)); [done|done|done| |].
        { future_pinst. apply IH1l. rewrite okR_eq. simpl. unfold marked. by rewrite HLy. }
        { future_pinst. apply IH2l, okM_okR, Hok. }
    + destruct (is_lam e1) eqn:Hil.
      * destruct e1 as [| | | |b| | | | | | | |]; try done.
        change (okM Lm e2 && (gd e2 || okM (None .: Lm) b) = true) in Hok.
        apply andb_true_iff in Hok as [Hok2 Hok1]. apply orb_true_iff in Hok1 as [Hgd|Hok1].
        { apply (lsem_later_app_lam W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                   _ _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)); [done|done|done|done| | |].
          - future_pinst. apply lsem_later_now, IH1l, okR_noL.
          - by apply IH1v.
          - future_pinst. apply IH2l, okM_okR, Hok2. }
        eapply (lsem_later_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                  _ _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)); [done|done|done| |].
        { future_pinst. apply IH1l. rewrite okR_eq. apply orb_true_iff. right. simpl. by apply okM_okR. }
        { future_pinst. apply IH2l, okM_okR, Hok2. }
      * rewrite okM_app_gen in Hok; [|done|done].
        apply andb_true_iff in Hok as [Hok1 Hok2]. apply orb_true_iff in Hok2 as [Hgd|Hok2].
        { apply (lsem_later_app_g W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                   _ _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)); [done|done|done|done| |].
          - future_pinst. apply IH1l, okM_okR, Hok1.
          - future_pinst. apply lsem_later_now, IH2l, okR_noL. }
        eapply (lsem_later_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                  _ _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)); [done|done|done| |].
        { future_pinst. apply IH1l, okM_okR, Hok1. }
        { future_pinst. apply IH2l, okM_okR, Hok2. }
  - (* E-Pair *)
    simpl in Hgall. apply andb_true_iff in Hgall as [Hg1 Hg2].
    destruct (IH1 Hg1 W1 ρ σ HW HW1 Hρ HΨ) as [IH1l IH1v].
    destruct (IH2 Hg2 W1 ρ σ HW HW1 Hρ HΨ) as [IH2l IH2v].
    assert (tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2)) as Hc'
      by (by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ)).
    assert (lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)) as Hsp' by (by apply lenv_split_pinst).
    split; [intros Lm Hok|done].
    change (okM Lm (Pair e1 e2) || false = true) in Hok. rewrite orb_false_r in Hok.
    apply andb_true_iff in Hok as [Hok1 Hok2]. apply orb_true_iff in Hok2 as [Hgd|Hok2].
    + apply (lsem_later_pair_g W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)); [done|done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * future_pinst. apply lsem_later_now, IH2l, okR_noL.
    + eapply (lsem_later_pair W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)); [done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * future_pinst. apply IH2l, okM_okR, Hok2.
  - (* E-Let* *)
    simpl in Hgall. apply andb_true_iff in Hgall as [Hg1 Hg2].
    destruct (IH1 Hg1 W1 ρ σ HW HW1 Hρ HΨ) as [IH1l IH1v].
    destruct (IH2 Hg2 W1 ρ σ HW HW1 Hρ HΨ) as [IH2l IH2v].
    assert (tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2)) as Hc'
      by (by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ)).
    assert (lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)) as Hsp' by (by apply lenv_split_pinst).
    split; [intros Lm Hok|done].
    change (okM Lm (LetU e1 e2) || false = true) in Hok. rewrite orb_false_r in Hok.
    apply andb_true_iff in Hok as [Hok1 Hok2]. apply orb_true_iff in Hok2 as [Hgd|Hok2].
    + apply (lsem_later_letu_g W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)); [done|done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * apply lsem_later_now, IH2l, okR_noL.
    + eapply (lsem_later_letu W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)); [done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * apply IH2l, okM_okR, Hok2.
  - (* E-LetPair *)
    simpl in Hgall. apply andb_true_iff in Hgall as [Hg1 Hg2].
    destruct (IH1 Hg1 W1 ρ σ HW HW1 Hρ HΨ) as [IH1l IH1v].
    destruct (IH2 Hg2 W1 ρ σ HW HW1 Hρ HΨ) as [IH2l IH2v].
    assert (tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2)) as Hc'
      by (by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ)).
    assert (lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)) as Hsp' by (by apply lenv_split_pinst).
    split; [intros Lm Hok|done].
    change (okM Lm (LetP e1 e2) || false = true) in Hok. rewrite orb_false_r in Hok.
    apply andb_true_iff in Hok as [Hok1 Hok2]. apply orb_true_iff in Hok2 as [Hgd|Hok2].
    + apply (lsem_later_letp_g W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2) _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)); [done|done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * apply lsem_later_now, IH2l, okR_noL.
    + eapply (lsem_later_letp W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2) _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)); [done|done| |].
      * future_pinst. apply IH1l, okM_okR, Hok1.
      * apply IH2l, okM_okR, Hok2.
  - cbn [pinst_ty]. destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl _]. split; [intros Lm Hok|done].
    apply lsem_later_inj1, IHl. change (okM Lm e || false = true) in Hok. rewrite orb_false_r in Hok. by apply okM_okR.
  - cbn [pinst_ty]. destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl _]. split; [intros Lm Hok|done].
    apply lsem_later_inj2, IHl. change (okM Lm e || false = true) in Hok. rewrite orb_false_r in Hok. by apply okM_okR.
  - (* E-Case *)
    simpl in Hgall. apply andb_true_iff in Hgall as [Hg Hg2]. apply andb_true_iff in Hg as [Hg0 Hg1].
    destruct (IH0 Hg0 W1 ρ σ HW HW1 Hρ HΨ) as [IH0l IH0v].
    destruct (IH1 Hg1 W1 ρ σ HW HW1 Hρ HΨ) as [IH1l IH1v].
    destruct (IH2 Hg2 W1 ρ σ HW HW1 Hρ HΨ) as [IH2l IH2v].
    assert (tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2)) as Hc'
      by (by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ)).
    assert (lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)) as Hsp' by (by apply lenv_split_pinst).
    split; [intros Lm Hok|done].
    change (okM Lm (Case e e1 e2) || false = true) in Hok. rewrite orb_false_r in Hok.
    apply andb_true_iff in Hok as [Hok0 Hok12]. apply orb_true_iff in Hok12 as [Hgd|Hok12].
    + apply (lsem_later_case_g W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
               _ _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)); [done|done|done| | |].
      * future_pinst. apply IH0l, okM_okR, Hok0.
      * apply lsem_later_now, IH1l, okR_noL.
      * apply lsem_later_now, IH2l, okR_noL.
    + apply andb_true_iff in Hok12 as [Hok1 Hok2].
      eapply (lsem_later_case W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
                _ _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)); [done|done| | |].
      * future_pinst. apply IH0l, okM_okR, Hok0.
      * apply IH1l, okM_okR, Hok1.
      * apply IH2l, okM_okR, Hok2.
  - cbn [pinst_ty]. rewrite tenv_pinst_empty. simpl in Hgall. apply andb_true_iff in Hgall as [Hgb0 Hgb].
    split; [intros Lm Hok|done].
    change (negb (occursM (None .: Lm) e) || false = true) in Hok. rewrite orb_false_r in Hok.
    apply negb_true_iff in Hok.
    apply lsem_later_box_live; [by apply lenv_unl_pinst| |].
    { destruct (slist_witness k) as (ss0 & Hss0 & Hsc0).
      pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ (Hb ss0 Hss0 Hsc0)) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf.
      change (term_wf ∅ (lenv_pinst σ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) e).
      by rewrite term_wf_lenv_pinst. }
    intros W2 xs ss F' HW2 Hxs Hss Hsc HC HK Hub'. subst m.
    assert (∀ a, pt_inst (pt_inst (plist xs) ∘ pup (length xs) σ) (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    set (m := length xs).
    assert (lenv_pinst (pt_inst (plist xs) ∘ pup m σ) (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ))
            = lenv_pinst σ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ)) as E1.
    { rewrite lenv_pinst_comp. apply lenv_pinst_ext. exact Hsh. }
    assert (pinst_ty (pt_inst (plist xs) ∘ pup m σ) (sinst_ty (slist ss) T)
            = sinst_ty (slist ss) (ty_inst xs (pinst_ty (pup m σ) T))) as E2.
    { unfold ty_inst. by rewrite pinst_sinst, pinst_ty_comp. }
    assert (fhyps_pinst (pt_inst (plist xs) ∘ pup m σ) (fhyps_pinst (pshift m) Φ)
            = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros i [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst (pt_inst (plist xs) ∘ pup m σ)
              (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    pose proof (IH ss Hss Hsc Hgb W2 (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                  (pt_inst (plist xs) ∘ pup m σ) HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    fold m in Hb'. rewrite tenv_pinst_empty, sf_pinst_fresh, sf_inst_fresh, E1, E2, E4 in Hb'.
    refine (proj1 (Hb' _ _) _ _).
    + apply inst_ok_pinst_insert.
      * rewrite E3. exact (inst_ok_mono _ _ _ _ HW2 Hρ).
      * destruct ub as [u|]; simpl in *; [|done]. by rewrite pt_inst_comp in Hub'.
    + apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done.
    + apply (okR_union e (Some (is_lam e) .: noL) (None .: Lm)); [by intros [|i]|exact Hgb0|exact Hok].

  - destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl IHv]. split.
    + intros Lm Hok. eapply lsem_later_wk; [by apply lenv_wk_pinst|by apply IHl].
    + intros Hil Lm. eapply lsem_v0_wk; [by apply lenv_wk_pinst|by apply IHv].
  - rewrite gallM_rename in Hgall. destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl IHv]. cbn [lenv_pinst]. split.
    + intros Lm Hok. rewrite (okR_rename _ pred Lm (λ x, Lm (pred x))) in Hok; [|done].
      apply lsem_later_contract; [by apply unlimited_pinst|by apply IHl].
    + intros Hil Lm. rewrite is_lam_rename in Hil.
      apply lsem_v0_contract; [by apply unlimited_pinst|by apply IHv].
  - destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl IHv]. split.
    + intros Lm Hok. eapply lsem_later_conv; [by apply (steq_teqW W W1 σ HW HW1 Ψ)|by apply IHl].
    + intros Hil Lm. eapply lsem_v0_conv; [by apply (steq_teqW W W1 σ HW HW1 Ψ)|by apply IHv].
  - (* E-Pack *)
    cbn [pinst_ty].
    assert (pinst_ty σ (ty_inst xs T) = ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)) as E.
    { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. symmetry.
      by apply plist_pup_comm. }
    destruct (IH Hgall W1 ρ σ HW HW1 Hρ HΨ) as [IHl IHv].
    assert (length (pt_inst σ <$> xs) = m ∧ Forall (pt_known W1) (pt_inst σ <$> xs) ∧
      bcs_hold (w_eq W1) (w_lt W1) (bcs_inst σ C) (pt_inst σ <$> xs) ∧
      lbx_below W1 (lb_map (pt_inst σ) lb) (heads (ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)))
        (hbot (ty_inst (pt_inst σ <$> xs) (pinst_ty (pup m σ) T)))) as (Hxs' & HK' & HC' & Hlb').
    { split_and!.
    - by rewrite length_fmap.
    - apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx.
      by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
    - apply (bcs_hold_inst (seqs W Ψ) _ (slt W Ψ)); [| |done].
      * intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
      * intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    - rewrite <-E, heads_pinst, hbot_pinst. by apply (lbx_below_h_pinst W W1 σ HW HW1 Ψ).
    }
    split.
    + intros Lm Hok. eapply (lsem_later_pack W1 _ _ _ _ _ _ m _ _ (pt_inst σ <$> xs)); [done..|].
      rewrite <-E. by apply IHl.
    + intros Hil Lm. eapply (lsem_v0_pack W1 _ _ _ _ _ m _ _ (pt_inst σ <$> xs)); [done..|].
      rewrite <-E. by apply IHv.
  - (* E-Open *)
    split.
    + intros Lm Hok.
      apply (lsem_later_open W1 _ _ _ _ _ i (lb_map (pt_inst σ) lb) m (bcs_inst σ C) (pinst_ty (pup m σ) T)).
      { by rewrite lenv_pinst_lookup, Hi. }
      intros W2 xs HW2 Hxs HK' HC'. subst m.

    set (σ' := pt_inst (plist xs) ∘ pup (length xs) σ).
    assert (∀ a, pt_inst σ' (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    pose proof (IH Hgall W2 ρ σ' HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    rewrite tenv_pinst_comp, (tenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite lenv_pinst_insert, lenv_pinst_comp, (lenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite sf_pinst_comp, (sf_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite pinst_ty_comp, (pinst_ty_ext _ _ σ) in Hb' by exact Hsh.
    assert (fhyps_pinst σ' (fhyps_pinst (pshift (length xs)) Φ) = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros j [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst σ' (hyps_inst (pshift (length xs)) Ψ ++
              [(bcs_inst (pshift (length xs)) C, ids (length xs))])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    rewrite E3, E4 in Hb'. cbn [fmap option_fmap option_map] in Hb'.
    assert (pinst_ty σ' T = ty_inst xs (pinst_ty (pup (length xs) σ) T)) as E2.
    { unfold ty_inst, σ'. by rewrite pinst_ty_comp. }
    rewrite E2 in Hb'. specialize (Hb' (inst_ok_mono _ _ _ _ HW2 Hρ)).
    lapply Hb'; cycle 1.
    { apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done. }
    clear Hb'; intros Hb'. by apply (proj1 Hb').
    + intros Hil Lm.
      apply (lsem_v0_open W1 _ _ _ _ i (lb_map (pt_inst σ) lb) m (bcs_inst σ C) (pinst_ty (pup m σ) T)).
      { by rewrite lenv_pinst_lookup, Hi. }
      intros W2 xs HW2 Hxs HK' HC'. subst m.

    set (σ' := pt_inst (plist xs) ∘ pup (length xs) σ).
    assert (∀ a, pt_inst σ' (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    pose proof (IH Hgall W2 ρ σ' HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    rewrite tenv_pinst_comp, (tenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite lenv_pinst_insert, lenv_pinst_comp, (lenv_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite sf_pinst_comp, (sf_pinst_ext _ σ) in Hb' by exact Hsh.
    rewrite pinst_ty_comp, (pinst_ty_ext _ _ σ) in Hb' by exact Hsh.
    assert (fhyps_pinst σ' (fhyps_pinst (pshift (length xs)) Φ) = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros j [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst σ' (hyps_inst (pshift (length xs)) Ψ ++
              [(bcs_inst (pshift (length xs)) C, ids (length xs))])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    rewrite E3, E4 in Hb'. cbn [fmap option_fmap option_map] in Hb'.
    assert (pinst_ty σ' T = ty_inst xs (pinst_ty (pup (length xs) σ) T)) as E2.
    { unfold ty_inst, σ'. by rewrite pinst_ty_comp. }
    rewrite E2 in Hb'. specialize (Hb' (inst_ok_mono _ _ _ _ HW2 Hρ)).
    lapply Hb'; cycle 1.
    { apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done. }
    clear Hb'; intros Hb'. by apply (proj2 Hb').
Qed.

(** ** The closed form

    No future variables, no hypotheses, the identity substitution, and
    no later variable. *)

Theorem live_fundamental_guarded W Θ Δ F e T :
  gtyped W ∅ [] Θ Δ (F, None) e T → strict W → lsem_typed W Θ Δ F e T.
Proof.
  intros [Ht Hg] HW.
  pose proof (typed_live _ _ _ _ _ _ _ _ Ht (gall_gallM _ Hg) W (λ _, ∅) pvar (proj1 HW) (wext_refl _ HW)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  assert (sf_inst (λ _, ∅) (F, None) = F) as Ef.
  { unfold sf_inst. simpl. by rewrite !union_empty_r_L. }
  rewrite Ef in H. apply lsem_later_now. refine (proj1 (H _ _) _ (okR_noL _)).
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - intros C xs Hgi. cbn in Hgi. by apply elem_of_nil in Hgi.
Qed.

(** A closed guarded typed term is in the live E relation at every index. *)
Corollary live_fundamental_guarded_closed W F e T :
  gtyped W ∅ [] ∅ [] (F, None) e T → strict W → ∀ n, LErel n W ∅ T F e.
Proof.
  intros Ht HW n. pose proof (live_fundamental_guarded _ _ _ _ _ _ Ht HW n W ∅ ∅ Var) as H.
  rewrite subst_ids in H. apply H; [by apply wext_refl|apply tenv_comp_empty_r|done].
Qed.

(** ** The examples of GuardEx.v as live terms *)

(** A closed guarded program over the hypotheses of its top-level
    channels is live in the world where its run starts (sharp edges
    172). *)
Corollary live_fundamental_guarded_created Ψ e T :
  gstyped ∅ Ψ [] (∅, None) e T → created (Wpo []) Ψ →
  ∃ W1 σ, strict W1 ∧ ∀ n, LErel n W1 ∅ (pinst_ty σ T) ∅ e.
Proof.
  intros [Ht Hg] HΨ.
  destruct (created_world (Wpo []) Ψ (Wpo_strict []) HΨ) as (W1 & σ & HW1 & Hh).
  pose proof (proj2 (proj2 (proj2 HW1))) as HS.
  exists W1, σ. split; [done|]. intros n.
  pose proof (typed_live _ _ _ _ _ _ _ _ (styped_typed (Wpo []) _ _ _ _ _ _ Ht) (gall_gallM _ Hg)
                W1 (λ _, ∅) σ (proj1 (Wpo_strict [])) HW1) as H.
  rewrite tenv_pinst_empty in H.
  assert (sf_inst (λ _, ∅) (sf_pinst σ (∅, None)) = ∅) as Ef.
  { unfold sf_inst, sf_pinst. simpl. rewrite set_map_empty. set_solver. }
  rewrite Ef in H.
  assert (lsem_typed W1 ∅ [] ∅ e (pinst_ty σ T)) as HL.
  { apply lsem_later_now. refine (proj1 (H _ _) _ (okR_noL _)); [|exact Hh].
    intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty. }
  pose proof (HL n W1 ∅ ∅ Var) as H'. rewrite subst_ids in H'.
  apply H'; [by apply wext_refl|apply tenv_comp_empty_r|done].
Qed.

Theorem fw_live : ∃ W, strict W ∧ ∀ n, LErel n W ∅ TUnit ∅ Forwarder.fw_main.
Proof.
  destruct (live_fundamental_guarded_created _ _ _ fw_gstyped Forwarder.fw_created) as (W & σ & HW & H).
  by exists W.
Qed.

Theorem tc_live : ∃ W, strict W ∧ ∀ n, LErel n W ∅ TUnit ∅ TailCall.tc_main.
Proof.
  destruct (live_fundamental_guarded_created _ _ _ tc_gstyped TailCall.tc_created) as (W & σ & HW & H).
  by exists W.
Qed.
