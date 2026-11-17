(** * The structural rules, for every cost table (stage S5)

    Each typing rule that is not an operator rule of compat/Rules.v is
    valid for the semantic judgment at a set of points ([gen_e_*]).
    The facts and futures of a rule are read in W, as in Rules.v. The
    fundamental theorem (static/Fundamental.v) reaches these forms by
    instantiating the point variables and the future variables of Γ.

    A rule that splits its context binds the first premise in a frame
    that holds the other part ([sem_bind]). The hole runs with the heads
    of that part in its future. The typing rule names the static heads,
    the heads of the types in Δ, and the values of a grounding hold
    their ends at or above those heads ([Grel_heads]). E is closed
    upwards in its future ([Erel_cover], compat/EFacts.v), so the static
    heads suffice. When Δ has the ⊥ flag, the static future carries an
    arbitrary set B, and the rule takes B to be the heads of the
    grounding.

    E-Abs and E-Box build values, and V at a λ and at a box asks the
    ends of the environment to be the ends the value mentions (Q14).
    A typing derivation gives the ends of the term and an entry for
    every free variable ([tfacts], cost/Exact.v), and the values of a
    grounding are exact ([Vrel_exact]), so the instance of the term
    mentions exactly the ends of its environment ([Grel_fends]).

    E-Box asks a positive cost of β ([gen_e_box]), true of κ_DF. The
    thunk of a box at level n reads the body below n, where the self is
    in V by induction on the level. The live table κ_L has β free, and
    there the box needs the guard (compat/LiveRules.v).

    E-SpawnLam has no rule here. Its semantic form is false for the
    relation of stage S3 (compat/SpawnGap.v). *)

From GV Require Export compat.Rules compat.EFacts cost.Exact.

(** ** Environments *)

Lemma senv_heads_erase Θ : senv_heads (tenv_erase Θ) = tenv_heads Θ.
Proof.
  apply set_eq. intros y. rewrite elem_of_senv_heads, elem_of_tenv_heads. unfold tenv_erase.
  setoid_rewrite lookup_fmap. split.
  - intros (o & S & x & Ho & ->). destruct (Θ !! o) as [e|] eqn:E; simplify_eq/=. eauto.
  - intros (o & e & Ho & ->). exists o, (te_sty e), (te_pt e). by rewrite Ho.
Qed.

Lemma dom_tenv_erase Θ : dom (tenv_erase Θ) = dom Θ.
Proof. unfold tenv_erase. apply dom_fmap_L. Qed.

Lemma tenv_erase_empty : tenv_erase ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_erase_singleton o S x a : tenv_erase {[o := TE S x a]} = {[o := (S, x)]}.
Proof. unfold tenv_erase. by rewrite map_fmap_singleton. Qed.

Lemma senv_heads_union Θ1 Θ2 y :
  y ∈ senv_heads (Θ1 ∪ Θ2) → y ∈ senv_heads Θ1 ∨ y ∈ senv_heads Θ2.
Proof.
  rewrite !elem_of_senv_heads. intros (o & S & x & Ho & ->).
  apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [left|right]; eauto.
Qed.

Lemma senv_heads_empty_iff Θ : senv_heads Θ = ∅ ↔ Θ = ∅.
Proof.
  split; [|intros ->; apply senv_heads_empty].
  intros H. apply map_empty. intros o. destruct (Θ !! o) as [[S x]|] eqn:E; [|done].
  exfalso. assert (x‾ ∈ senv_heads Θ) as Hy by (apply elem_of_senv_heads; eauto). set_solver.
Qed.

(** The two parts of a split typing environment beside the two parts
    of a split grounding environment. *)
Lemma env_split Θ Θ1 Θ2 (Θ' Θ1' Θ2' : senv) :
  tsplit Θ Θ1 Θ2 → Θ1' ##ₘ Θ2' → Θ' = Θ1' ∪ Θ2' → tenv_erase Θ ##ₘ Θ' →
  tenv_erase Θ1 ##ₘ Θ1' ∧ tenv_erase Θ2 ##ₘ Θ2' ∧
  (tenv_erase Θ1 ∪ Θ1') ##ₘ (tenv_erase Θ2 ∪ Θ2') ∧
  tenv_erase Θ ∪ Θ' = (tenv_erase Θ1 ∪ Θ1') ∪ (tenv_erase Θ2 ∪ Θ2').
Proof.
  intros [Hd ->] Hd' -> HdΘ. unfold tenv_erase in *. rewrite map_fmap_union in HdΘ |- *.
  apply map_disjoint_union_l in HdΘ as [Ha Hb].
  apply map_disjoint_union_r in Ha as [Ha1 Ha2]. apply map_disjoint_union_r in Hb as [Hb1 Hb2].
  assert ((λ e, (te_sty e, te_pt e)) <$> Θ1 ##ₘ (λ e, (te_sty e, te_pt e)) <$> Θ2) as Hd2
    by by apply map_disjoint_fmap.
  split_and!; [done|done| |].
  - apply map_disjoint_union_l. split; apply map_disjoint_union_r; split; try done; by symmetry.
  - rewrite !map_union_assoc. f_equal. rewrite <-!map_union_assoc. f_equal.
    by apply map_union_comm.
Qed.

(** ** Groundings *)

Section ground.
  Context (κ : ctable).

  Lemma Grel_only n W Θ Δ γ x T a :
    lenv_only Δ x (T, a) → Grel κ n W Θ Δ γ → Vrel κ n W Θ T (γ x).
  Proof.
    revert Θ γ x. induction Δ as [|o Δ IH]; intros Θ γ x [Hx Hy]; [done|].
    destruct x as [|x]; simpl in Hx.
    - injection Hx as ->. intros (Θ1 & Θ2 & _ & -> & HV & HG).
      assert (lenv_empty Δ) as He.
      { intros o Ho. destruct o as [σ|]; [|done]. apply list_elem_of_lookup in Ho as [i Hi].
        by destruct (Hy (S i) σ Hi). }
      rewrite (Grel_empty κ _ _ _ _ _ He HG), map_union_empty. done.
    - destruct o as [[T' a']|]; simpl.
      + by destruct (Hy 0 (T', a') eq_refl).
      + intros HG. apply (IH Θ (λ y, γ (S y)) x); [|done]. split; [done|].
        intros y σ' Hσ. destruct (Hy (S y) σ' Hσ) as [[= ->] ->]. done.
  Qed.

  Lemma Grel_unl n W Θ Δ γ : lenv_unl Δ → Grel κ n W Θ Δ γ → Θ = ∅.
  Proof.
    revert Θ γ. induction Δ as [|o Δ IH]; intros Θ γ HΔ; simpl; [done|].
    assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
    destruct (HΔ o ltac:(left)) as [->|(U & a & -> & HU)]; simpl.
    - apply IH, HΔ'.
    - intros (Θ1 & Θ2 & _ & -> & HV & HG).
      rewrite (Vrel_unl_empty κ _ _ _ _ _ HU HV), (IH _ _ HΔ' HG). apply map_empty_union.
  Qed.

  (** The ends of a grounding lie at or above the heads of Δ. *)
  Lemma Grel_heads n W Θ Δ γ :
    Grel κ n W Θ Δ γ → lenv_bot Δ = false →
    ∀ o S x, Θ !! o = Some (S, x) → ∃ h, h ∈ lenv_heads Δ ∧ w_le W h x‾.
  Proof.
    revert Θ γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ γ; simpl.
    - intros -> _ o S x Hx. by rewrite lookup_empty in Hx.
    - intros (Θ1 & Θ2 & _ & -> & HV & HG) Hb o S x Hx.
      apply orb_false_iff in Hb as [Hb1 Hb2].
      apply lookup_union_Some_raw in Hx as [Hx|[_ Hx]].
      + destruct (Vrel_heads κ _ _ _ _ _ HV Hb1 o S x Hx) as (h & ? & ?). exists h. set_solver.
      + destruct (IH _ _ HG Hb2 o S x Hx) as (h & ? & ?). exists h. set_solver.
    - intros HG Hb. by apply (IH _ _ HG Hb).
  Qed.

  Lemma Grel_ends n W Θ Δ γ : Grel κ n W Θ Δ γ →
    (∀ x σ, Δ !! x = Some (Some σ) → fends (γ x) ⊆ dom Θ) ∧
    (∀ o, o ∈ dom Θ → ∃ x T a, Δ !! x = Some (Some (T, a)) ∧ ¬ unlimited T ∧ o ∈ fends (γ x)).
  Proof.
    revert Θ γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ γ; simpl.
    - intros ->. split; [intros x σ; by rewrite lookup_nil|intros o; rewrite dom_empty_L; set_solver].
    - intros (Θ1 & Θ2 & Hd & -> & HV & HG).
      destruct (IH _ _ HG) as [A B]. pose proof (Vrel_exact κ _ _ _ _ _ HV) as Hx. split.
      + intros [|x] σ Hx'; simpl in Hx'; rewrite dom_union_L; [rewrite <-Hx; set_solver|].
        specialize (A x σ Hx'). set_solver.
      + intros o. rewrite dom_union_L. intros [Ho|Ho]%elem_of_union.
        * exists 0, T, a. split_and!; [done| |by rewrite <-Hx].
          intros Hu. rewrite (Vrel_unl_empty κ _ _ _ _ _ Hu HV) in Ho. set_solver.
        * destruct (B o Ho) as (x & T' & a' & ? & ? & ?). by exists (S x), T', a'.
    - intros HG. destruct (IH _ _ HG) as [A B]. split.
      + intros [|x] σ Hx'; simpl in Hx'; [done|]. by apply (A x σ).
      + intros o Ho. destruct (B o Ho) as (x & T' & a' & ? & ? & ?). by exists (S x), T', a'.
  Qed.

  (** The instance of a typed term mentions exactly the ends of its
      environment. *)
  Lemma Grel_fends n W Θ0 Θ Δ γ e :
    tfacts Θ0 Δ e → Grel κ n W Θ Δ γ → fends (subst γ e) = dom Θ0 ∪ dom Θ.
  Proof.
    intros (Hf & Hv1 & Hv2) HG. destruct (Grel_ends _ _ _ _ _ HG) as [A B].
    rewrite <-Hf. apply fends_subst_eq.
    - intros x Hx. destruct (Hv1 x Hx) as [σ Hσ]. exact (A x σ Hσ).
    - intros o Ho. destruct (B o Ho) as (x & T & a & Hx & Hu & Ho'). exists x. split; [|done].
      by apply (Hv2 x T a).
  Qed.

  Lemma Grel_wk n W Θ Δ' Δ γ : lenv_wk Δ' Δ → Grel κ n W Θ Δ γ → Grel κ n W Θ Δ' γ.
  Proof.
    intros Hwk. revert Θ γ. induction Hwk as [|o Δ' Δ Hwk IH|U a Δ' Δ Hu Hwk IH]; intros Θ γ; simpl.
    - done.
    - destruct o as [[T a]|]; [|apply IH].
      intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; auto.
    - intros (Θ1 & Θ2 & Hd & -> & HV & HG).
      rewrite (Vrel_unl_empty κ _ _ _ _ _ Hu HV), map_empty_union. by apply IH.
  Qed.

  Lemma Grel_contract n W Θ U a Δ γ :
    unlimited U → Grel κ n W Θ (Some (U, a) :: Δ) γ →
    Grel κ n W Θ (Some (U, a) :: Some (U, a) :: Δ) (λ x, γ (pred x)).
  Proof.
    intros Hu HG. pose proof HG as (Θ1 & Θ2 & Hd & -> & HV & HG').
    pose proof (Vrel_unl_empty κ _ _ _ _ _ Hu HV) as ->.
    rewrite map_empty_union in HG |- *.
    exists ∅, Θ2. split_and!; [apply map_disjoint_empty_l|by rewrite map_empty_union|done|].
    eapply Grel_ext; [|exact HG]. by intros x.
  Qed.

  (** A grounding at an entry i, and the same grounding with another
      type at i that its value meets. *)
  Lemma Grel_pick n W Θ Δ γ i T1 a :
    Δ !! i = Some (Some (T1, a)) → Grel κ n W Θ Δ γ →
    ∃ Θi, Vrel κ n W Θi T1 (γ i) ∧
      ∀ T2 b, Vrel κ n W Θi T2 (γ i) → Grel κ n W Θ (<[i := Some (T2, b)]> Δ) γ.
  Proof.
    revert Θ γ i. induction Δ as [|o Δ IH]; intros Θ γ i Hi; [done|].
    destruct i as [|i]; simpl in Hi |- *.
    - injection Hi as ->. intros (Θ1 & Θ2 & Hd & -> & HV & HG).
      exists Θ1. split; [done|]. intros T2 b HV2. exists Θ1, Θ2. split_and!; done.
    - destruct o as [[U c]|]; simpl.
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG).
        destruct (IH _ _ i Hi HG) as (Θi & HVi & Hk). exists Θi. split; [done|].
        intros T2 b HV2. exists Θ1, Θ2. split_and!; auto.
      + intros HG. destruct (IH _ _ i Hi HG) as (Θi & HVi & Hk). exists Θi. split; [done|].
        intros T2 b HV2. by apply Hk.
  Qed.
End ground.

(** ** The rules *)

Section rules.
  Context (κ : ctable).

  Lemma sem_typed_at_blind W Θ Δ F t T T' :
    ty_df T = ty_df T' → sem_typed_at κ W Θ Δ F t T → sem_typed_at κ W Θ Δ F t T'.
  Proof. intros H He n W' Θ' γ HW Hd HG. eapply (Erel_blind κ); [|by apply He]. done. Qed.

  (** A frame that holds the second part of a split context. *)
  Lemma sem_bind (mk : (nat → expr) → frame) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e t T U :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ γ, subst γ t = fill_frame (mk γ) (subst γ e)) → (∀ γ, frame_val (mk γ)) →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e T) →
    (∀ W' j Θv v Θ2' γ, W ⊑ W' → tenv_erase Θ2 ##ₘ Θ2' → Grel κ j W' Θ2' Δ2 γ →
       Θv ##ₘ tenv_erase Θ2 ∪ Θ2' → Vrel κ j W' Θv T v →
       fill_frame (mk γ) v ∈ E[κ]^W' _ j⟦Θv ∪ (tenv_erase Θ2 ∪ Θ2') ⊢ U⟧^F) →
    sem_typed_at κ W Θ Δ F t U.
  Proof.
    intros Hs Hl Ht Hf He Hk n W' Θ' γ HW Hd HG.
    destruct (Grel_split κ _ _ _ _ _ _ _ Hl HG) as (Θ1' & Θ2' & Hd' & -> & HG1 & HG2).
    destruct (env_split _ _ _ _ _ _ Hs Hd' eq_refl Hd) as (Hd1 & Hd2 & Hd12 & ->).
    rewrite Ht. apply (Erel_bind κ n (mk γ) W' _ _ T); [done|done| |].
    - eapply Erel_cover; [|exact (He (senv_heads (tenv_erase Θ2 ∪ Θ2')) n W' Θ1' γ HW Hd1 HG1)].
      intros y [Hy|Hy]%elem_of_union.
      { exists y. split; [set_solver|by left]. }
      destruct (lenv_bot Δ2) eqn:Hb.
      { exists y. split; [set_solver|by left]. }
      apply senv_heads_union in Hy as [Hy|Hy].
      + exists y. split; [|by left]. rewrite senv_heads_erase in Hy. set_solver.
      + apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
        destruct (Grel_heads κ _ _ _ _ _ HG2 Hb o S x Ho) as (h & Hh & Hle).
        exists h. split; [set_solver|done].
    - intros W'' j Θv v HW' Hj Hdv HV. apply (Hk W'' j Θv v Θ2' γ); [by eapply wext_trans|done| |done|done].
      eapply Grel_down; [exact Hj|]. by eapply Grel_mono.
  Qed.

  (** A frame that holds nothing. *)
  Lemma sem_frame0 (f : frame) W Θ Δ F e t Targ Tres :
    frame_val f → (∀ γ, subst γ t = fill_frame f (subst γ e)) →
    (∀ W' j Θv v, W ⊑ W' → Vrel κ j W' Θv Targ v → Erel κ j W' Θv Tres F (fill_frame f v)) →
    sem_typed_at κ W Θ Δ F e Targ → sem_typed_at κ W Θ Δ F t Tres.
  Proof.
    intros Hf Ht Hred He n W' Θ' γ HW Hd HG. rewrite Ht.
    rewrite <-(map_union_empty (tenv_erase Θ ∪ Θ')).
    apply (Erel_bind κ n f W' _ ∅ Targ Tres F (subst γ e)); [done|apply map_disjoint_empty_r| |].
    - rewrite senv_heads_empty, union_empty_r_L. by apply He.
    - intros W'' j Θv v HW' _ _ Hv. rewrite map_union_empty. apply Hred; [by eapply wext_trans|done].
  Qed.

  (** *** Values *)

  Lemma gen_e_unit W Δ F : lenv_empty Δ → sem_typed_at κ W ∅ Δ F EUnit TUnit.
  Proof.
    intros HΔ n W' Θ' γ HW Hd HG. rewrite (Grel_empty κ _ _ _ _ _ HΔ HG), tenv_erase_empty, map_union_empty.
    apply Vrel_Erel. by apply Vrel_unit_iff.
  Qed.

  Lemma gen_e_var W Δ F x T a : lenv_only Δ x (T, a) → sem_typed_at κ W ∅ Δ F (Var x) T.
  Proof.
    intros HΔ n W' Θ' γ HW Hd HG. rewrite tenv_erase_empty, map_empty_union.
    apply Vrel_Erel. by eapply Grel_only.
  Qed.

  Lemma gen_e_chan W Δ F o S x a :
    lenv_empty Δ → sem_typed_at κ W {[o := TE S x a]} Δ F (Chan o) (TSess S x).
  Proof.
    intros HΔ n W' Θ' γ HW Hd HG. rewrite (Grel_empty κ _ _ _ _ _ HΔ HG), map_union_empty, tenv_erase_singleton.
    apply Vrel_Erel. apply Vrel_sess_iff. exists o, S. split_and!; [done|done|apply seqv_refl].
  Qed.

  Lemma gen_e_abs W Θ Δ F e T aT U aU ub lb c t h :
    tfacts Θ Δ (Lam e) → lenv_bot Δ = false → lb_le W lb (tenv_heads Θ ∪ lenv_heads Δ) →
    (∀ W1 F', W ⊑ W1 → ub_lt W1 ub F' → sem_typed_at κ W1 Θ (Some (T, aT) :: Δ) F' e U) →
    sem_typed_at κ W Θ Δ F (Lam e) (TLolli ub lb c t h T aT U aU).
  Proof.
    intros Htf Hb Hlb Hbody n W' Θ' γ HW Hd HG. apply Vrel_Erel, Vrel_lolli_iff.
    exists (subst (up γ) e). split_and!.
    - done.
    - pose proof (Grel_fends κ _ _ _ _ _ _ _ Htf HG) as Hx. simpl in Hx.
      by rewrite Hx, dom_union_L, dom_tenv_erase.
    - destruct lb as [l|]; simpl in Hlb |- *.
      + intros y Hy. apply senv_heads_union in Hy as [Hy|Hy].
        * rewrite senv_heads_erase in Hy. eapply w_le_mono; [exact HW|]. apply Hlb. set_solver.
        * apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
          destruct (Grel_heads κ _ _ _ _ _ HG Hb o S x Ho) as (h0 & Hh & Hle).
          eapply w_le_trans; [|exact Hle]. eapply w_le_mono; [exact HW|]. apply Hlb. set_solver.
      + apply senv_heads_empty_iff.
        assert (tenv_heads Θ = ∅ ∧ lenv_heads Δ = ∅) as [H1 H2] by set_solver.
        assert (Θ' = ∅) as ->.
        { apply map_empty. intros o. destruct (Θ' !! o) as [[S x]|] eqn:E; [|done].
          destruct (Grel_heads κ _ _ _ _ _ HG Hb o S x E) as (h0 & Hh & _). set_solver. }
        rewrite map_union_empty. apply senv_heads_empty_iff. by rewrite senv_heads_erase.
    - intros W'' j Θ'' w F' HW' Hj Hd'' Hub Hw. rewrite subst1_subst.
      apply map_disjoint_union_l in Hd'' as [Hd1 Hd2].
      rewrite <-map_union_assoc, (map_union_comm Θ' Θ'') by done.
      apply (Hbody W'' F' (wext_trans _ _ _ HW HW') Hub j W'' (Θ'' ∪ Θ') (w .: γ) (wext_refl _)).
      + apply map_disjoint_union_r. split; [done|done].
      + exists Θ'', Θ'. split_and!; [by symmetry|done|done|].
        eapply Grel_down; [|by eapply Grel_mono]. lia.
  Qed.

  (** A box at a positive cost of β. *)
  Lemma gen_e_box W Δ F e m kk C ub c t U aU a :
    1 ≤ c_beta κ → tfacts ∅ Δ (EBox e) → lenv_unl Δ →
    (∀ W1 xs ss F', W ⊑ W1 → length xs = m → length ss = kk → Forall hcontractive ss →
       wholds W1 C xs → ub_lt W1 (pt_inst (plist xs) <$> ub) F' →
       sem_typed_at κ W1 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) F' e
         (sinst_ty (slist ss) (ty_inst xs U))) →
    sem_typed_at κ W ∅ Δ F (EBox e) (TBox m kk C ub c t U aU).
  Proof.
    intros Hβ Htf Hu Hbody n W' Θ' γ HW Hd HG.
    pose proof (Grel_fends κ _ _ _ _ _ _ _ Htf HG) as Hx.
    pose proof (Grel_unl κ _ _ _ _ _ Hu HG) as ->.
    rewrite tenv_erase_empty, map_union_empty. simpl in Hx. rewrite !dom_empty_L, union_empty_r_L in Hx.
    set (eb := subst (up γ) e). fold eb in Hx.
    apply Vrel_Erel.
    assert (∀ j W2, j ≤ n → W' ⊑ W2 → Vrel κ j W2 ∅ (TBox m kk C ub c t U aU) (EBox eb)) as Hlob.
    { induction j as [j IH] using lt_wf_ind. intros W2 Hj HW2. apply Vrel_box_iff.
      split; [done|]. exists eb. split_and!; [done|done|].
      intros W3 xs ss HW3 Hxs Hss Hsc HC. apply Vrel_lolli_iff.
      exists (rename S (subst1 (EBox eb) eb)). split_and!.
      - done.
      - rewrite dom_empty_L, fends_rename. unfold subst1.
        assert (fends (subst (EBox eb .: Var) eb) ⊆ fends eb ∪ ∅) as Hsub.
        { apply fends_subst, allfv_forall. intros [|y]; simpl; [rewrite Hx|]; set_solver. }
        set_solver.
      - done.
      - intros W4 j' Θ'' w F' HW4 Hj' _ Hub Hw.
        apply Vrel_unit_iff in Hw as [-> ->]. rewrite map_union_empty, thunk_app.
        unfold eb. rewrite subst1_subst.
        assert (W ⊑ W4) as HW04.
        { eapply wext_trans; [exact HW|]. eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
        assert (W' ⊑ W4) as HW'4.
        { eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
        assert (Grel κ j' W4 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) (EBox eb .: γ)) as HG'.
        { exists ∅, ∅. split_and!; [apply map_disjoint_empty_l|by rewrite map_union_empty| |].
          - apply IH; [lia|lia|done].
          - eapply Grel_down; [|eapply Grel_mono; [exact HW'4|exact HG]]. lia. }
        pose proof (Hbody W4 xs ss F' HW04 Hxs Hss Hsc (wholds_mono _ _ _ _ HW4 HC) Hub
                      j' W4 ∅ (EBox eb .: γ) (wext_refl _)
                      ltac:(rewrite tenv_erase_empty; apply map_disjoint_empty_l) HG') as Hb.
        by rewrite tenv_erase_empty, map_union_empty in Hb. }
    apply Hlob; [lia|apply wext_refl].
  Qed.

  (** *** Frames *)

  Lemma gen_e_app W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb c t h T aT U aU :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_lt W ub F →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1
            (TLolli ub lb c t h T aT U aU)) →
    sem_typed_at κ W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
    sem_typed_at κ W Θ Δ F (App e1 e2) U.
  Proof.
    intros Hs Hl Hub He1 He2.
    apply (sem_bind (λ γ, FAppL (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 _ (TLolli ub lb c t h T aT U aU) U Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hvv.
    pose proof HV as (eb & -> & _ & Hlbv & _)%Vrel_lolli_iff.
    rewrite (map_union_comm Θv) by done.
    change (App (Lam eb) (subst γ e2)) with (fill_frame (FAppR (Lam eb)) (subst γ e2)).
    apply (Erel_bind κ j _ W' _ _ T); [done|by symmetry| |].
    - eapply Erel_cover; [|exact (He2 j W' Θ2' γ HW Hd2 HG2)].
      intros y [Hy|Hy]%elem_of_union; [exists y; split; [set_solver|by left]|].
      destruct lb as [l|]; simpl in Hlbv.
      + exists l. split; [set_solver|by apply Hlbv].
      + rewrite Hlbv in Hy. set_solver.
    - intros W'' j' Θw w HW' Hj' Hdw Hw. simpl. rewrite map_union_comm by done.
      apply (Erel_app κ j' W'' Θv Θw ub lb c t h T aT U aU); [by symmetry| | |done].
      + eapply ub_lt_mono; [eapply wext_trans; [exact HW|exact HW']|exact Hub].
      + eapply Vrel_down; [exact Hj'|]. by eapply Vrel_mono.
  Qed.

  Lemma gen_e_pair W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1 T1) →
    (∀ B, sem_typed_at κ W Θ2 Δ2 (F ∪ heads T1 ∪ (if hbot T1 then B else ∅)) e2 T2) →
    sem_typed_at κ W Θ Δ F (Pair e1 e2) (TProd T1 a1 T2 a2).
  Proof.
    intros Hs Hl He1 He2.
    apply (sem_bind (λ γ, FPairL (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 _ T1 _ Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hvv.
    rewrite (map_union_comm Θv) by done.
    change (Pair v (subst γ e2)) with (fill_frame (FPairR v) (subst γ e2)).
    apply (Erel_bind κ j _ W' _ _ T2); [done|by symmetry| |].
    - eapply Erel_cover; [|exact (He2 (senv_heads Θv) j W' Θ2' γ HW Hd2 HG2)].
      intros y [Hy|Hy]%elem_of_union; [exists y; split; [set_solver|by left]|].
      destruct (hbot T1) eqn:Hb; [exists y; split; [set_solver|by left]|].
      apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x Ho) as (h0 & ? & ?).
      exists h0. split; [set_solver|done].
    - intros W'' j' Θw w HW' Hj' Hdw Hw. simpl. rewrite map_union_comm by done.
      apply Vrel_Erel, Vrel_prod_iff. exists v, w, Θv, Θw. split_and!; [done|by symmetry|done| |done].
      eapply Vrel_down; [exact Hj'|]. by eapply Vrel_mono.
  Qed.

  (** A β redex whose only step is β. *)
  Lemma beta_det e e' :
    (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') → tstep e LBeta e' →
    ∀ n W Θ T F, Erel κ (n - c_beta κ) W Θ T F e' → Erel κ n W Θ T F e.
  Proof. intros Hd Hs n W Θ T F H. by eapply Erel_beta. Qed.

  Lemma gen_e_letu W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1 TUnit) →
    sem_typed_at κ W Θ2 Δ2 F e2 T →
    sem_typed_at κ W Θ Δ F (LetU e1 e2) T.
  Proof.
    intros Hs Hl He1 He2.
    apply (sem_bind (λ γ, FLetU (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 _ TUnit _ Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply Vrel_unit_iff in HV as [-> ->]. rewrite map_empty_union.
    apply (beta_det _ (subst γ e2)).
    - intros α e'' Hst. assert (head_step (LetU EUnit (subst γ e2)) α e'') as Hh by head_only.
      inversion Hh; by subst.
    - apply tstep_head, t_act_let_unit.
    - apply He2; [done|done|]. eapply Grel_down; [|exact HG2]. lia.
  Qed.

  Lemma gen_e_letp W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 a1 T2 a2 b1 b2 T :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1
            (TProd T1 a1 T2 a2)) →
    sem_typed_at κ W Θ2 (Some (T2, b2) :: Some (T1, b1) :: Δ2) F e2 T →
    sem_typed_at κ W Θ Δ F (LetP e1 e2) T.
  Proof.
    intros Hs Hl He1 He2.
    apply (sem_bind (λ γ, FLetP (subst (up (up γ)) e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 _ (TProd T1 a1 T2 a2) _ Hs Hl);
      [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply Vrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hdab & -> & H1 & H2).
    pose proof (Vrel_val κ _ _ _ _ _ H1) as Hv1. pose proof (Vrel_val κ _ _ _ _ _ H2) as Hv2.
    apply (beta_det _ (subst (v2 .: v1 .: γ) e2)).
    - intros α e'' Hst. assert (head_step (LetP (Pair v1 v2) (subst (up (up γ)) e2)) α e'') as Hh
        by head_only.
      inversion Hh; subst. split; [done|]. by rewrite subst2_subst.
    - rewrite <-(subst2_subst v1 v2 γ e2). by apply tstep_head, t_act_let_pair.
    - apply map_disjoint_union_l in Hdv as [Hda Hdb].
      apply map_disjoint_union_r in Hda as [Hda1 Hda2]. apply map_disjoint_union_r in Hdb as [Hdb1 Hdb2].
      assert ((Θa ∪ Θb) ∪ (tenv_erase Θ2 ∪ Θ2') = tenv_erase Θ2 ∪ (Θb ∪ (Θa ∪ Θ2'))) as ->.
      { rewrite (map_union_comm Θa Θb) by done.
        rewrite <-(map_union_assoc Θb Θa), (map_union_assoc Θa (tenv_erase Θ2) Θ2').
        rewrite (map_union_comm Θa (tenv_erase Θ2)) by done.
        rewrite <-(map_union_assoc (tenv_erase Θ2) Θa Θ2'), (map_union_assoc Θb (tenv_erase Θ2)).
        rewrite (map_union_comm Θb (tenv_erase Θ2)) by done.
        by rewrite <-(map_union_assoc (tenv_erase Θ2) Θb). }
      apply He2; [done| |].
      + apply map_disjoint_union_r. split; [by symmetry|].
        apply map_disjoint_union_r. split; [by symmetry|done].
      + exists Θb, (Θa ∪ Θ2'). split_and!.
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * done.
        * eapply Vrel_down; [|exact H2]. lia.
        * exists Θa, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact H1]. lia. }
          { eapply Grel_down; [|exact HG2]. lia. }
  Qed.

  Lemma gen_e_let W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 b1 T :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1 T1) →
    sem_typed_at κ W Θ2 (Some (T1, b1) :: Δ2) F e2 T →
    sem_typed_at κ W Θ Δ F (ELet e1 e2) T.
  Proof.
    intros Hs Hl He1 He2.
    apply (sem_bind (λ γ, FLet (subst (up γ) e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 _ T1 _ Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hv.
    apply (beta_det _ (subst (v .: γ) e2)).
    - intros α e'' Hst. assert (head_step (ELet v (subst (up γ) e2)) α e'') as Hh by head_only.
      inversion Hh; subst. split; [done|]. by rewrite subst1_subst.
    - rewrite <-(subst1_subst v γ e2). by apply tstep_head, t_act_let.
    - apply map_disjoint_union_r in Hdv as [Hdv1 Hdv2].
      rewrite map_union_assoc, (map_union_comm Θv (tenv_erase Θ2)), <-map_union_assoc by done.
      apply He2; [done| |].
      + apply map_disjoint_union_r. split; [by symmetry|done].
      + exists Θv, Θ2'. split_and!; [done|done| |].
        * eapply Vrel_down; [|exact HV]. lia.
        * eapply Grel_down; [|exact HG2]. lia.
  Qed.

  Lemma gen_e_case W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 a1 T2 a2 b1 b2 T :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_typed_at κ W Θ1 Δ1 (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e
            (TSum T1 a1 T2 a2)) →
    sem_typed_at κ W Θ2 (Some (T1, b1) :: Δ2) F e1 T →
    sem_typed_at κ W Θ2 (Some (T2, b2) :: Δ2) F e2 T →
    sem_typed_at κ W Θ Δ F (Case e e1 e2) T.
  Proof.
    intros Hs Hl He He1 He2.
    apply (sem_bind (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 F e _ (TSum T1 a1 T2 a2) _ Hs Hl);
      [done|done|exact He|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply map_disjoint_union_r in Hdv as [Hdv1 Hdv2].
    rewrite map_union_assoc, (map_union_comm Θv (tenv_erase Θ2)), <-map_union_assoc by done.
    apply Vrel_sum_iff in HV as [(v' & -> & HV)|(v' & -> & HV)];
      pose proof (Vrel_val κ _ _ _ _ _ HV) as Hv.
    - apply (beta_det _ (subst (v' .: γ) e1)).
      + intros α e'' Hst. assert (head_step (Case (Inj1 v') (subst (up γ) e1) (subst (up γ) e2)) α e'')
          as Hh by head_only.
        inversion Hh; subst. split; [done|]. by rewrite subst1_subst.
      + rewrite <-(subst1_subst v' γ e1). by apply tstep_head, t_act_case_inl.
      + apply He1; [done| |].
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * exists Θv, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact HV]. lia. }
          { eapply Grel_down; [|exact HG2]. lia. }
    - apply (beta_det _ (subst (v' .: γ) e2)).
      + intros α e'' Hst. assert (head_step (Case (Inj2 v') (subst (up γ) e1) (subst (up γ) e2)) α e'')
          as Hh by head_only.
        inversion Hh; subst. split; [done|]. by rewrite subst1_subst.
      + rewrite <-(subst1_subst v' γ e2). by apply tstep_head, t_act_case_inr.
      + apply He2; [done| |].
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * exists Θv, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact HV]. lia. }
          { eapply Grel_down; [|exact HG2]. lia. }
  Qed.

  Lemma gen_e_inj1 W Θ Δ F e T a U b :
    sem_typed_at κ W Θ Δ F e T → sem_typed_at κ W Θ Δ F (Inj1 e) (TSum T a U b).
  Proof.
    apply (sem_frame0 FInj1); [done|done|]. intros W' j Θv v _ HV.
    apply Vrel_Erel, Vrel_sum_iff. left. eauto.
  Qed.

  Lemma gen_e_inj2 W Θ Δ F e T a U b :
    sem_typed_at κ W Θ Δ F e U → sem_typed_at κ W Θ Δ F (Inj2 e) (TSum T a U b).
  Proof.
    apply (sem_frame0 FInj2); [done|done|]. intros W' j Θv v _ HV.
    apply Vrel_Erel, Vrel_sum_iff. right. eauto.
  Qed.

  (** *** Structure *)

  Lemma gen_e_weak W Θ Δ' Δ F e T :
    lenv_wk Δ' Δ → sem_typed_at κ W Θ Δ' F e T → sem_typed_at κ W Θ Δ F e T.
  Proof. intros Hwk He n W' Θ' γ HW Hd HG. apply He; [done|done|]. by eapply Grel_wk. Qed.

  Lemma gen_e_contract W Θ Δ U aU F e T :
    unlimited U → sem_typed_at κ W Θ (Some (U, aU) :: Some (U, aU) :: Δ) F e T →
    sem_typed_at κ W Θ (Some (U, aU) :: Δ) F (rename pred e) T.
  Proof.
    intros Hu He n W' Θ' γ HW Hd HG. rewrite subst_rename.
    apply He; [done|done|]. by apply Grel_contract.
  Qed.

  (** V is monotone along subtyping. *)
  Lemma Vrel_tsub T a T' a' : tsub T a T' a' → ∀ n W Θ v, Vrel κ n W Θ T v → Vrel κ n W Θ T' v.
  Proof.
    induction 1 as [a a' _
      |ub lb c t h T1 a1 U a2 c' t' h' T1' a1' U' a2' a a' _ _ _ _ _ IH1 _ IH2
      |T1 a1 U a2 T1' a1' U' a2' a a' _ IH1 _ IH2
      |T1 a1 U a2 T1' a1' U' a2' a a' _ IH1 _ IH2
      |m kk C ub c t U U' aU c' t' a a' _ _ HU
      |s s' x a a' Hs _
      |lb m C C' T T' aT aT' a a' Henv Hf Heq _]; intros n W Θ v.
    - done.
    - rewrite !Vrel_lolli_iff. intros (e & -> & Hfe & Hlb & H). exists e. split_and!; [done|done|done|].
      intros W' j Θ' w F HW Hj Hd Hub Hw. eapply Erel_ty_mono; [|apply H; [done..|by apply IH1]].
      intros m' W2 Θ2 v' _ _. apply IH2.
    - rewrite !Vrel_prod_iff. intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
      exists v1, v2, Θ1, Θ2. split_and!; auto.
    - rewrite !Vrel_sum_iff. intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - rewrite !Vrel_box_iff. intros (-> & e & -> & Hfe & H). split; [done|]. exists e. split_and!; [done|done|].
      intros W' xs ss HW Hxs Hss Hsc HC. specialize (H W' xs ss HW Hxs Hss Hsc HC).
      destruct kk as [|kk]; simpl in HU; [|by subst].
      destruct ss; [|simpl in Hss; lia]. rewrite !sinst_ty_slist_nil in H |- *.
      eapply Vrel_teq; [|exact H]. apply teq_thunk. rewrite <-!ty_inst_df. apply teq_pinst. apply teq_df. first [done|by apply teq_sym].
    - rewrite !Vrel_sess_iff. intros (o & s0 & -> & -> & Hs0). exists o, s0. split_and!; [done|done|].
      unfold seqv in *. eapply sequiv_trans; [exact Hs0|]. by apply sequiv_df.
    - rewrite !Vrel_ex_iff. intros (Hlb & xs & Hxs & HC & H). split; [done|].
      exists xs. split_and!; [done| |].
      + intros x y (g0 & (f & Hf' & Hsc & ->) & Hg). apply HC.
        exists (fact_map (pt_inst (pup (length xs) (plist (bc_env C)))) f). split; [|by rewrite Henv].
        exists f. split_and!; [by apply Hf|by rewrite Henv|by rewrite Henv].
      + eapply Vrel_teq; [|exact H]. rewrite <-!ty_inst_df. apply teq_pinst. apply teq_df. first [done|by apply teq_sym].
  Qed.

  (** D-Conv: subtyping of the erasures. *)
  Lemma gen_e_conv W Θ Δ F e T T' a a' :
    tsub (ty_df T) a (ty_df T') a' → sem_typed_at κ W Θ Δ F e T → sem_typed_at κ W Θ Δ F e T'.
  Proof.
    intros Hsub He n W' Θ' γ HW Hd HG. specialize (He n W' Θ' γ HW Hd HG).
    rewrite (Erel_blind κ _ _ _ T' (ty_df T')) by (by rewrite ty_df_idem).
    rewrite (Erel_blind κ _ _ _ T (ty_df T)) in He by (by rewrite ty_df_idem).
    eapply Erel_ty_mono; [|exact He]. intros m W2 Θ2 v _ _. by apply (Vrel_tsub _ _ _ _ Hsub).
  Qed.

  (** The lower bound of an existential, read in W. *)
  Definition lbx_ok (W : world) (lb : lbound) (X : ty) : Prop :=
    match lb with
    | LBot => True
    | LNone => heads X = ∅ ∧ hbot X = false
    | LPt x => (∀ y, y ∈ heads X → w_le W x y) ∧ hbot X = false
    end.

  Lemma lbx_ok_mono W W' lb X : W ⊑ W' → lbx_ok W lb X → lbx_ok W' lb X.
  Proof.
    intros HW. destruct lb; simpl; try done. intros [H ->]. split; [|done].
    intros y Hy. eapply w_le_mono; [exact HW|]. by apply H.
  Qed.

  Lemma gen_e_pack W Θ Δ F e lb m C T aT xs :
    length xs = m → wholds W C xs → lbx_ok W lb (ty_inst xs T) →
    sem_typed_at κ W Θ Δ F e (ty_inst xs T) → sem_typed_at κ W Θ Δ F e (TEx lb m C T aT).
  Proof.
    intros Hxs HC Hlb He n W' Θ' γ HW Hd HG. specialize (He n W' Θ' γ HW Hd HG).
    eapply Erel_ty_mono; [|exact He]. intros m' W2 Θ2 v HW2 _ HV.
    assert (W ⊑ W2) as HW02 by by eapply wext_trans.
    apply Vrel_ex_iff. split; [|exists xs; split_and!; [done|by eapply wholds_mono|done]].
    pose proof (lbx_ok_mono _ _ _ _ HW02 Hlb) as Hlb2.
    destruct lb as [| |l]; simpl in Hlb2 |- *; [|done|].
    - destruct Hlb2 as [Hh Hb]. apply senv_heads_empty_iff. apply map_empty. intros o.
      destruct (Θ2 !! o) as [[S x]|] eqn:E; [|done].
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x E) as (h0 & Hh0 & _). set_solver.
    - destruct Hlb2 as [Hh Hb]. intros y Hy. apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x Ho) as (h0 & Hh0 & Hle).
      eapply w_le_trans; [by apply Hh|exact Hle].
  Qed.
End rules.
