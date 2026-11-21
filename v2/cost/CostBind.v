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

Lemma fle_fminus_anti i c f : fle (Some i) c → ple (fminus c f) (fminus (Some i) f).
Proof. unfold fminus, ple. destruct c, f as [[f|] m]; simpl; split; try done; lia. Qed.

Lemma cle_fminus_anti i c (φ : cenv) : fle (Some i) c → cle (fminus c <$> φ) (fminus (Some i) <$> φ).
Proof.
  intros H o. rewrite !lookup_fmap. destruct (φ !! o); simpl; [by apply fle_fminus_anti|done].
Qed.

Lemma csem_bind0 N Θ Δ e T1 c1 (K : ectx) σ d n g γ Π φ :
  ectx_ok K → (∀ g' : cend → cend, kemap g' K = K) → csem N Θ Δ e T1 c1 → fle c1 d →
  envf N n Θ Δ g γ Π φ →
  (∀ j i v Πv φv, ole j n → fle (Some i) c1 → is_val v →
     v ∈ FV^N _ j⟦RTy T1⟧(Πv, φv) →
     efill K v ∈ F^N _ j⟦σ ▷ fsub d (Some i)⟧(Πv, φv)) →
  efill K (subst γ (emap g e)) ∈ F^N _ n⟦σ ▷ d⟧(Π, φ).
Proof.
  intros HK HKe Hcs Hcd HE Hk.
  rewrite <-(map_union_empty Π), <-(map_union_empty φ).
  apply (FuelE_bind n N (RTy T1) σ Π φ ∅ ∅ c1 d K).
  - done.
  - by eapply envf_dom.
  - by rewrite !dom_empty_L.
  - rewrite dom_empty_L. set_solver.
  - intros o f. by rewrite lookup_empty.
  - done.
  - intros g' ΠK' φK' i j v Π1 φ1 _ _ R1 R2 Hi Hj Hv _ _ HV.
    rewrite (renk_empty g' ΠK' R1), (renk_empty g' φK' R2), fmap_empty, !map_union_empty, HKe.
    by apply Hk.
  - by apply Hcs.
Qed.

Lemma csem_bind1 N Θ1 Δ1 e1 T1 c1 Θ2 Θ2' Δ2 Δ2'
    (fr : (nat → expr) → (cend → cend) → frame) σ d n g γ Π1 φ1 Π2 φ2 :
  (∀ (g' : cend → cend) γ g, frame_emap g' (fr γ g) = fr (λ x, emap g' (γ x)) (g' ∘ g)) →
  (∀ γ g, frame_val (fr γ g)) →
  csem N Θ1 Δ1 e1 T1 c1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' → fle c1 d →
  envf N n Θ1 Δ1 g γ Π1 φ1 → envf N n Θ2 Δ2 g γ Π2 φ2 → Π1 ##ₘ Π2 → φ1 ##ₘ φ2 →
  (∀ j g' γ' Π' φ' i v Πv φv, ole j n → fle (Some i) c1 → is_val v →
     envf N j Θ2' Δ2' g' γ' Π' φ' → v ∈ FV^N _ j⟦RTy T1⟧(Πv, φv) →
     Πv ##ₘ Π' → φv ##ₘ φ' →
     fill_frame (fr γ' g') v ∈ F^N _ j⟦σ ▷ fsub d (Some i)⟧(Πv ∪ Π', φv ∪ φ')) →
  fill_frame (fr γ g) (subst γ (emap g e1)) ∈ F^N _ n⟦σ ▷ d⟧(Π1 ∪ Π2, φ1 ∪ φ2).
Proof.
  intros Hfe Hfv Hcs HaT HaD Hcd HE1 HE2 HdΠ Hdφ Hk.
  change (fill_frame (fr γ g) (subst γ (emap g e1))) with (efill [fr γ g] (subst γ (emap g e1))).
  apply (FuelE_bind n N (RTy T1) σ Π1 φ1 Π2 φ2 c1 d [fr γ g]).
  - constructor; [apply Hfv|constructor].
  - by eapply envf_dom.
  - by eapply envf_dom.
  - by apply map_disjoint_dom.
  - exact (envf_age_above _ _ _ _ _ _ _ _ _ _ _ HaT HaD HE2).
  - done.
  - intros g' ΠK' φK' i j v Πv φv Hk1 Hk2 R1 R2 Hi Hj Hv HdΠ' Hdφ' HV. simpl. rewrite Hfe.
    apply (Hk j (g' ∘ g) (λ x, emap g' (γ x)) ΠK' (fminus (Some i) <$> φK') i v Πv φv);
      try done.
    + eapply envf_mono; [exact Hj|apply cle_fminus_anti, Hi|].
      eapply envf_age; [exact HaT|exact HaD|]. by eapply envf_rename.
    + apply map_disjoint_dom. rewrite dom_fmap_L. by apply map_disjoint_dom.
  - by apply Hcs.
Qed.

Lemma csem_bind2 N Θ Δ e T2 c2 (fr : expr → frame) Tv Tv' σ d n g γ Π φ v Πv φv :
  (∀ (g' : cend → cend) v, frame_emap g' (fr v) = fr (emap g' v)) → (∀ v, is_val v → frame_val (fr v)) →
  csem N Θ Δ e T2 c2 → tage c2 Tv Tv' → fle c2 d → is_val v →
  envf N n Θ Δ g γ Π φ → v ∈ FV^N _ n⟦RTy Tv⟧(Πv, φv) → Π ##ₘ Πv → φ ##ₘ φv →
  (∀ j v' Πv' φv' u Πu φu i, ole j n → fle (Some i) c2 → is_val u →
     is_val v' → v' ∈ FV^N _ j⟦RTy Tv'⟧(Πv', φv') → u ∈ FV^N _ j⟦RTy T2⟧(Πu, φu) →
     Πu ##ₘ Πv' → φu ##ₘ φv' →
     fill_frame (fr v') u ∈ F^N _ j⟦σ ▷ fsub d (Some i)⟧(Πu ∪ Πv', φu ∪ φv')) →
  fill_frame (fr v) (subst γ (emap g e)) ∈ F^N _ n⟦σ ▷ d⟧(Π ∪ Πv, φ ∪ φv).
Proof.
  intros Hfe Hfv Hcs Ha Hcd Hvv HE HV HdΠ Hdφ Hk.
  change (fill_frame (fr v) (subst γ (emap g e))) with (efill [fr v] (subst γ (emap g e))).
  apply (FuelE_bind n N (RTy T2) σ Π φ Πv φv c2 d [fr v]).
  - constructor; [by apply Hfv|constructor].
  - by eapply envf_dom.
  - by eapply Vfuel_dom.
  - by apply map_disjoint_dom.
  - exact (Vfuel_age_above _ _ _ _ _ _ _ _ Ha HV).
  - done.
  - intros g' ΠK' φK' i j u Πu φu Hk1 Hk2 R1 R2 Hi Hj Hu HdΠ' Hdφ' HU. simpl. rewrite Hfe.
    apply (Hk j (emap g' v) ΠK' (fminus (Some i) <$> φK') u Πu φu i); try done.
    + by rewrite is_val_emap.
    + eapply Vfuel_mono; [apply cle_fminus_anti, Hi|].
      eapply Vfuel_down; [exact Hj|]. eapply Vfuel_age; [exact Ha|].
      by eapply Vfuel_rename.
    + apply map_disjoint_dom. rewrite dom_fmap_L. by apply map_disjoint_dom.
  - by apply Hcs.
Qed.
