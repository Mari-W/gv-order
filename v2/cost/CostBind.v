(** * Sequencing for the semantic cost judgment (stage S7)

    Three forms of the bind lemma F1 ([FuelE_bind]) at a grounded
    instance, after theories/lockfree/CostFund.v.

    - [csem_bind0]: a hole that holds the whole environment, in a
      context that holds nothing (the frame of an operator or an
      injection).
    - [csem_bind1]: a hole beside the rest of the environment, which
      ages by the hole's cost. The context is a frame built from the
      grounding and the renaming.
    - [csem_bind2]: a hole beside a value that an earlier hole returned.
      The value ages by the hole's cost. *)

From GV Require Export cost.CostSem.

Lemma fle_fminus_anti i c f : fle (Some i) c → fle (fminus c f) (fminus (Some i) f).
Proof. unfold fminus. destruct c, f; simpl; lia. Qed.

Lemma cle_fminus_anti i c (φ : cenv) : fle (Some i) c → cle (fminus c <$> φ) (fminus (Some i) <$> φ).
Proof.
  intros H o. rewrite !lookup_fmap. destruct (φ !! o); simpl; [by apply fle_fminus_anti|done].
Qed.

Lemma kinj_union_l {Y : Type} (g : cend → cend) (m1 m2 : gmap cend Y) : kinj g (m1 ∪ m2) → kinj g m2.
Proof. apply kinj_dom. rewrite dom_union_L. set_solver. Qed.

Lemma csem_bind0 N Θ Δ e T1 a1 c1 t1 (K : ectx) σ d r N' n g γ Π φ tk r1 :
  ectx_ok K → (∀ g' : cend → cend, kemap g' K = K) → csem N Θ Δ e T1 a1 c1 t1 → fle c1 d → rle N N' →
  envf N' n Θ Δ g γ Π φ → meets t1 r1 tk →
  (∀ N'' j i v Πv φv tk', rle N' N'' → j ≤ n → fle (Some i) c1 → is_val v → r1 ≤ tk' →
     v ∈ FV^N'' _ j⟦RTy T1 a1⟧(Πv, φv) →
     efill K v ∈ F^N'' _ j⟦σ ▷ fsub d (Some i) ; r⟧(Πv, φv, tk')) →
  efill K (subst γ (emap g e)) ∈ F^N' _ n⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros HK HKe Hcs Hcd HN HE Hm Hk.
  rewrite <-(map_union_empty Π), <-(map_union_empty φ).
  apply (FuelE_bind n N' (RTy T1 a1) r1 σ r Π φ ∅ ∅ tk c1 d K).
  - done.
  - by eapply envf_dom.
  - by rewrite !dom_empty_L.
  - rewrite dom_empty_L. set_solver.
  - intros o f. by rewrite lookup_empty.
  - done.
  - intros N'' g' ΠK' φK' i j v Π1 φ1 tk' HN' _ _ R1 R2 Hi Hj Hv Hr _ _ HV.
    rewrite (renk_empty g' ΠK' R1), (renk_empty g' φK' R2), fmap_empty, !map_union_empty, HKe.
    by apply Hk.
  - by apply Hcs.
Qed.

Lemma csem_bind1 N Θ1 Δ1 e1 T1 a1 c1 t1 Θ2 Θ2' Δ2 Δ2'
    (fr : (nat → expr) → (cend → cend) → frame) σ d r N' n g γ Π1 φ1 Π2 φ2 tk r1 :
  (∀ (g' : cend → cend) γ g, frame_emap g' (fr γ g) = fr (λ x, emap g' (γ x)) (g' ∘ g)) →
  (∀ γ g, frame_val (fr γ g)) →
  csem N Θ1 Δ1 e1 T1 a1 c1 t1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' → fle c1 d → rle N N' →
  envf N' n Θ1 Δ1 g γ Π1 φ1 → envf N' n Θ2 Δ2 g γ Π2 φ2 → Π1 ##ₘ Π2 → φ1 ##ₘ φ2 →
  meets t1 r1 tk →
  (∀ N'' j g' γ' Π' φ' i v Πv φv tk', rle N' N'' → j ≤ n → fle (Some i) c1 → is_val v → r1 ≤ tk' →
     envf N'' j Θ2' Δ2' g' γ' Π' φ' → v ∈ FV^N'' _ j⟦RTy T1 a1⟧(Πv, φv) →
     Πv ##ₘ Π' → φv ##ₘ φ' →
     fill_frame (fr γ' g') v ∈ F^N'' _ j⟦σ ▷ fsub d (Some i) ; r⟧(Πv ∪ Π', φv ∪ φ', tk')) →
  fill_frame (fr γ g) (subst γ (emap g e1)) ∈ F^N' _ n⟦σ ▷ d ; r⟧(Π1 ∪ Π2, φ1 ∪ φ2, tk).
Proof.
  intros Hfe Hfv Hcs HaT HaD Hcd HN HE1 HE2 HdΠ Hdφ Hm Hk.
  change (fill_frame (fr γ g) (subst γ (emap g e1))) with (efill [fr γ g] (subst γ (emap g e1))).
  apply (FuelE_bind n N' (RTy T1 a1) r1 σ r Π1 φ1 Π2 φ2 tk c1 d [fr γ g]).
  - constructor; [apply Hfv|constructor].
  - by eapply envf_dom.
  - by eapply envf_dom.
  - by apply map_disjoint_dom.
  - exact (envf_age_above _ _ _ _ _ _ _ _ _ _ _ HaT HaD HE2).
  - done.
  - intros N'' g' ΠK' φK' i j v Πv φv tk' HN' Hk1 Hk2 R1 R2 Hi Hj Hv Hr HdΠ' Hdφ' HV. simpl. rewrite Hfe.
    apply (Hk N'' j (g' ∘ g) (λ x, emap g' (γ x)) ΠK' (fminus (Some i) <$> φK') i v Πv φv tk');
      try done.
    + eapply envf_mono; [exact HN'|exact Hj|apply cle_fminus_anti, Hi|].
      eapply envf_age; [exact HaT|exact HaD|]. by eapply envf_rename.
    + apply map_disjoint_dom. rewrite dom_fmap_L. by apply map_disjoint_dom.
  - by apply Hcs.
Qed.

Lemma csem_bind2 N Θ Δ e T2 a2 c2 t2 (fr : expr → frame) Tv av Tv' av' σ d r N' n g γ Π φ v Πv φv tk r2 :
  (∀ (g' : cend → cend) v, frame_emap g' (fr v) = fr (emap g' v)) → (∀ v, is_val v → frame_val (fr v)) →
  csem N Θ Δ e T2 a2 c2 t2 → tage c2 (Tv, av) (Tv', av') → fle c2 d → rle N N' → is_val v →
  envf N' n Θ Δ g γ Π φ → v ∈ FV^N' _ n⟦RTy Tv av⟧(Πv, φv) → Π ##ₘ Πv → φ ##ₘ φv →
  meets t2 r2 tk →
  (∀ N'' j v' Πv' φv' u Πu φu i tk', rle N' N'' → j ≤ n → fle (Some i) c2 → is_val u → r2 ≤ tk' →
     is_val v' → v' ∈ FV^N'' _ j⟦RTy Tv' av'⟧(Πv', φv') → u ∈ FV^N'' _ j⟦RTy T2 a2⟧(Πu, φu) →
     Πu ##ₘ Πv' → φu ##ₘ φv' →
     fill_frame (fr v') u ∈ F^N'' _ j⟦σ ▷ fsub d (Some i) ; r⟧(Πu ∪ Πv', φu ∪ φv', tk')) →
  fill_frame (fr v) (subst γ (emap g e)) ∈ F^N' _ n⟦σ ▷ d ; r⟧(Π ∪ Πv, φ ∪ φv, tk).
Proof.
  intros Hfe Hfv Hcs Ha Hcd HN Hvv HE HV HdΠ Hdφ Hm Hk.
  change (fill_frame (fr v) (subst γ (emap g e))) with (efill [fr v] (subst γ (emap g e))).
  apply (FuelE_bind n N' (RTy T2 a2) r2 σ r Π φ Πv φv tk c2 d [fr v]).
  - constructor; [by apply Hfv|constructor].
  - by eapply envf_dom.
  - by eapply Vfuel_dom.
  - by apply map_disjoint_dom.
  - exact (Vfuel_age_above _ _ _ _ _ _ _ _ _ _ Ha HV).
  - done.
  - intros N'' g' ΠK' φK' i j u Πu φu tk' HN' Hk1 Hk2 R1 R2 Hi Hj Hu Hr HdΠ' Hdφ' HU. simpl. rewrite Hfe.
    apply (Hk N'' j (emap g' v) ΠK' (fminus (Some i) <$> φK') u Πu φu i tk'); try done.
    + by rewrite is_val_emap.
    + eapply Vfuel_mono; [exact HN'|apply cle_fminus_anti, Hi|].
      eapply Vfuel_down; [exact Hj|]. eapply Vfuel_age; [exact Ha|].
      by eapply Vfuel_rename.
    + apply map_disjoint_dom. rewrite dom_fmap_L. by apply map_disjoint_dom.
  - by apply Hcs.
Qed.
