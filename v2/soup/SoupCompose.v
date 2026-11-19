(** * Composition of soups (stage S9, proposal §2.14)

      soup_term    : one thread over Σ and the restricted ends Θ_B
                     ⟹ a soup of (C0, {t}) over Σ
      soup_par     : soups over Σa and Σb with disjoint thread ids
                     ⟹ a soup of (C1 ∪ C2, M1 ∪ M2) over Σa ∪ Σb
      soup_nu      : a soup over Σ ∪ Σ_R, Σ_R both ends of each of its
                     channels at dual types and points
                     ⟹ a soup of (C ∪ chans Σ_R, M) over Σ
      soup_connect : soup_nu after soup_par, at the cut Σ_C ∪ Σ̄_C of
                     P-Connect and P-Join

    A soup reads its world only through E[live], so the composite lives
    at W1 ⊔ W2 by monotonicity of E in the world. It reads its refill only
    through FuelE, so the composite takes the larger refill by
    monotonicity of FuelE in N. No clause compares the points of two
    threads, so the families of the two sides need no renaming. The
    ownership, the tickets and the result types are the unions of the two
    sides, split by the thread ids of the first.

    The cut is exact: Σ̄_C holds the partners at the dual session type,
    as P-Connect types them. The soup pairs the two ends of a restricted
    channel in Π up to ≈ with annotations ([sp_pdual]), and [sp_psig]
    puts an interface end into Π at the session type of its entry. A
    cut dual only up to annotations ([cut_dual] of compat/Connect.v)
    would not give that pairing (docs/redesign/progress.md, S8, F-Link). *)

From stdpp Require Import relations.
From GV Require Export soup.Relabel.
From GV Require Import fuel.FuelMono.

(** ** Maps *)

Lemma union_lookup_in_l {Y : Type} (m1 m2 : gmap cend Y) o v :
  (m1 ∪ m2) !! o = Some v → o ∈ dom m1 → m1 !! o = Some v.
Proof.
  intros H Hd. apply lookup_union_Some_raw in H as [H|[Hn _]]; [done|].
  apply not_elem_of_dom in Hn. done.
Qed.

Lemma union_lookup_out_l {Y : Type} (m1 m2 : gmap cend Y) o v :
  (m1 ∪ m2) !! o = Some v → o ∉ dom m1 → m2 !! o = Some v.
Proof.
  intros H Hd. apply lookup_union_Some_raw in H as [H|[_ H]]; [|done].
  exfalso. apply Hd. by eapply elem_of_dom_2.
Qed.

Lemma chans_of_elem (Σ : senv) o : o ∈ dom Σ → ech o ∈ chans_of Σ.
Proof. intros H. unfold chans_of. apply elem_of_map. by exists o. Qed.

Lemma chans_dom_disj (Σ1 Σ2 : senv) : chans_of Σ1 ## chans_of Σ2 → dom Σ1 ## dom Σ2.
Proof. intros H o H1 H2. apply (H (ech o)); by apply chans_of_elem. Qed.

Local Instance edual_inj_c : base.Inj eq eq edual.
Proof. intros o o' H. by rewrite <-(edual_edual o), H, edual_edual. Qed.

(** Σ̄ holds the partner of each end of Σ at the dual type and point. *)
Lemma senv_dual_lookup (Σ : senv) o S (x : point) : Σ !! o = Some (S, x) → senv_dual Σ !! edual o = Some (dual S, (pt_dual x)).
Proof. intros H. unfold senv_dual. rewrite lookup_kmap; [by rewrite lookup_fmap, H|apply edual_inj_c]. Qed.

Lemma senv_dual_lookup_inv (Σ : senv) o y :
  senv_dual Σ !! o = Some y → ∃ S x, Σ !! edual o = Some (S, x) ∧ y = (dual S, (pt_dual x)).
Proof.
  unfold senv_dual. intros H. rewrite lookup_kmap_Some in H; [|apply edual_inj_c]. destruct H as (i & -> & Hi).
  apply lookup_fmap_Some in Hi as ([S x] & <- & Hi). rewrite edual_edual. by exists S, x.
Qed.

Lemma dom_senv_dual (Σ : senv) o : o ∈ dom (senv_dual Σ) ↔ edual o ∈ dom Σ.
Proof.
  rewrite !elem_of_dom. split.
  - intros [y Hy]. apply senv_dual_lookup_inv in Hy as (S & x & H & _). by eexists.
  - intros [[S x] H]. apply senv_dual_lookup in H. rewrite edual_edual in H. by eexists.
Qed.

Lemma chans_of_senv_dual (Σ : senv) : chans_of (senv_dual Σ) = chans_of Σ.
Proof.
  unfold chans_of. apply set_eq. intros c. rewrite !elem_of_map. split.
  - intros (o & -> & Ho). exists (edual o). rewrite ech_edual. split; [done|by apply dom_senv_dual].
  - intros (o & -> & Ho). exists (edual o). rewrite ech_edual. split; [done|]. apply dom_senv_dual.
    by rewrite edual_edual.
Qed.

(** The cut Σ_C ∪ Σ̄_C pairs every end with its partner. *)
Lemma cut_pair (ΣC : senv) o S (x : point) :
  (∀ o, o ∈ dom ΣC → edual o ∉ dom ΣC) →
  (ΣC ∪ senv_dual ΣC) !! o = Some (S, x) → (ΣC ∪ senv_dual ΣC) !! edual o = Some (dual S, (pt_dual x)).
Proof.
  intros Hf H. apply lookup_union_Some_raw in H as [H|[_ H]].
  - rewrite lookup_union_r; [by apply senv_dual_lookup|]. apply not_elem_of_dom, Hf. by eapply elem_of_dom_2.
  - apply senv_dual_lookup_inv in H as (S0 & x0 & H & [= -> ->]). apply lookup_union_Some_l.
    by rewrite H, dual_involutive, pt_dual_dual.
Qed.

(** ** The facts of one soup *)

Section facts.
  Context (N n : nat) (W : world) (Σ : senv) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W Σ T a A Π U).

  Lemma soup_dom_A : dom A = dom (s_K a).
  Proof.
    pose proof (f_equal dom (sp_pts _ _ _ _ _ _ _ _ Hs)) as H. by rewrite !dom_fmap_L in H.
  Qed.

  Lemma soup_dom_P : dom Π = dom (s_K a).
  Proof. exact (sp_dom _ _ _ _ _ _ _ _ Hs). Qed.

  Lemma soup_owner o h : s_K a !! o = Some h → h.(h_th) ∈ dom (s_q a).2.
  Proof. intros Ho. apply elem_of_dom. exact (sp_owner _ _ _ _ _ _ _ _ Hs o h Ho). Qed.
End facts.

(** ** Unions of ownership *)

Lemma kres_union_l {Y : Type} (K1 K2 : own) (m1 m2 : gmap cend Y) t :
  K1 ##ₘ K2 → dom m1 = dom K1 → (∀ o h, K2 !! o = Some h → h.(h_th) ≠ t) →
  kres (K1 ∪ K2) t (m1 ∪ m2) = kres K1 t m1.
Proof.
  intros HK H1 Ht. apply map_eq_some. intros o v. rewrite !lookup_kres. split.
  - intros (Hm & h & Hk & Hth). apply (lookup_union_Some _ _ _ _ HK) in Hk as [Hk|Hk]; [|by destruct (Ht o h Hk)].
    split; [|eauto]. apply (union_lookup_in_l _ _ _ _ Hm). rewrite H1. by eapply elem_of_dom_2.
  - intros (Hm & h & Hk & Hth). split; [by apply lookup_union_Some_l|]. exists h. split; [by apply lookup_union_Some_l|done].
Qed.

Lemma ctrs_union_l (K1 K2 : own) t :
  K1 ##ₘ K2 → (∀ o h, K2 !! o = Some h → h.(h_th) ≠ t) → ctrs (K1 ∪ K2) t = ctrs K1 t.
Proof.
  intros HK Ht. apply map_eq_some. intros o f. rewrite !lookup_ctrs. split.
  - intros (h & Hk & Hth & Hc). apply (lookup_union_Some _ _ _ _ HK) in Hk as [Hk|Hk]; [eauto|by destruct (Ht o h Hk)].
  - intros (h & Hk & Hth & Hc). exists h. split_and!; [by apply lookup_union_Some_l|done|done].
Qed.

(** Thread t reads the first map when t ∈ X, the second otherwise. *)
Definition tsel {Y : Type} (X : gset nat) (f g : nat → Y) : nat → Y :=
  λ t, if decide (t ∈ X) then f t else g t.

(** ** Parallel composition *)

Section par.
  Context (N1 N2 n : nat) (W1 W2 : world) (Σa Σb : senv) (T : ty) (C1 C2 : gset chan)
    (M1 M2 : gmap nat expr) (K1 K2 : own) (tk1 tk2 : nat → nat)
    (A1 A2 : senv) (Π1 Π2 : penv) (U1 U2 : nat → ty).
  Context (Hs1 : soup_inv N1 n W1 Σa T (LFState (C1, M1) K1 tk1) A1 Π1 U1).
  Context (Hs2 : soup_inv N2 n W2 Σb TUnit (LFState (C2, M2) K2 tk2) A2 Π2 U2).
  Context (HM : M1 ##ₘ M2) (HΣ : dom Σa ## dom Σb) (HC : C1 ## C2)
    (HC1 : C1 ## chans_of Σb) (HC2 : C2 ## chans_of Σa).

  Local Lemma cl1 o : o ∈ dom K1 → ech o ∈ C1 ∨ o ∈ dom Σa.
  Proof. exact (sp_closed _ _ _ _ _ _ _ _ Hs1 o). Qed.
  Local Lemma cl2 o : o ∈ dom K2 → ech o ∈ C2 ∨ o ∈ dom Σb.
  Proof. exact (sp_closed _ _ _ _ _ _ _ _ Hs2 o). Qed.

  Local Lemma dA1 : dom A1 = dom K1.
  Proof. exact (soup_dom_A _ _ _ _ _ _ _ _ _ Hs1). Qed.
  Local Lemma dA2 : dom A2 = dom K2.
  Proof. exact (soup_dom_A _ _ _ _ _ _ _ _ _ Hs2). Qed.
  Local Lemma dP1 : dom Π1 = dom K1.
  Proof. exact (soup_dom_P _ _ _ _ _ _ _ _ _ Hs1). Qed.
  Local Lemma dP2 : dom Π2 = dom K2.
  Proof. exact (soup_dom_P _ _ _ _ _ _ _ _ _ Hs2). Qed.

  Local Lemma Kdisj : K1 ##ₘ K2.
  Proof.
    apply map_disjoint_dom. intros o H1 H2.
    destruct (cl1 o H1) as [Hc1|Hd1], (cl2 o H2) as [Hc2|Hd2].
    - set_solver.
    - apply (HC1 (ech o)); [done|by apply chans_of_elem].
    - apply (HC2 (ech o)); [done|by apply chans_of_elem].
    - set_solver.
  Qed.

  Local Lemma Adisj : A1 ##ₘ A2.
  Proof. apply map_disjoint_dom. rewrite dA1, dA2. apply map_disjoint_dom, Kdisj. Qed.
  Local Lemma Pdisj : Π1 ##ₘ Π2.
  Proof. apply map_disjoint_dom. rewrite dP1, dP2. apply map_disjoint_dom, Kdisj. Qed.

  Local Lemma th1 o h : K1 !! o = Some h → h.(h_th) ∈ dom M1.
  Proof. exact (soup_owner _ _ _ _ _ _ _ _ _ Hs1 o h). Qed.
  Local Lemma th2 o h : K2 !! o = Some h → h.(h_th) ∈ dom M2.
  Proof. exact (soup_owner _ _ _ _ _ _ _ _ _ Hs2 o h). Qed.

  Local Lemma kres1 {Y : Type} (m1 m2 : gmap cend Y) t :
    dom m1 = dom K1 → t ∈ dom M1 → kres (K1 ∪ K2) t (m1 ∪ m2) = kres K1 t m1.
  Proof.
    intros Hd Ht. apply kres_union_l; [exact Kdisj|done|]. intros o h Ho <-.
    apply (map_disjoint_dom M1 M2) in HM. apply (HM (h_th h)); [done|exact (th2 o h Ho)].
  Qed.

  Local Lemma kres2 {Y : Type} (m1 m2 : gmap cend Y) t :
    m1 ##ₘ m2 → dom m2 = dom K2 → t ∈ dom M2 → kres (K1 ∪ K2) t (m1 ∪ m2) = kres K2 t m2.
  Proof.
    intros Hm Hd Ht. rewrite (map_union_comm K1 K2) by exact Kdisj. rewrite (map_union_comm m1 m2) by exact Hm.
    apply kres_union_l; [symmetry; exact Kdisj|done|]. intros o h Ho <-.
    apply (map_disjoint_dom M1 M2) in HM. apply (HM (h_th h)); [exact (th1 o h Ho)|done].
  Qed.

  Local Lemma ctrs1 t : t ∈ dom M1 → ctrs (K1 ∪ K2) t = ctrs K1 t.
  Proof.
    intros Ht. apply ctrs_union_l; [exact Kdisj|]. intros o h Ho <-.
    apply (map_disjoint_dom M1 M2) in HM. apply (HM (h_th h)); [done|exact (th2 o h Ho)].
  Qed.

  Local Lemma ctrs2 t : t ∈ dom M2 → ctrs (K1 ∪ K2) t = ctrs K2 t.
  Proof.
    intros Ht. rewrite (map_union_comm K1 K2) by exact Kdisj. apply ctrs_union_l; [symmetry; exact Kdisj|].
    intros o h Ho <-. apply (map_disjoint_dom M1 M2) in HM. apply (HM (h_th h)); [exact (th1 o h Ho)|done].
  Qed.

  (** An end of a channel of C1 held by the composite is held by side 1. *)
  Local Lemma side1 o : o ∈ dom (K1 ∪ K2) → ech o ∈ C1 → o ∈ dom K1.
  Proof.
    rewrite dom_union_L, elem_of_union. intros [H|H] Hc; [done|]. exfalso.
    destruct (cl2 o H) as [Hc2|Hd2]; [set_solver|]. apply (HC1 (ech o)); [done|by apply chans_of_elem].
  Qed.

  Local Lemma side2 o : o ∈ dom (K1 ∪ K2) → ech o ∈ C2 → o ∈ dom K2 ∧ o ∉ dom K1.
  Proof.
    rewrite dom_union_L, elem_of_union. intros [H|H] Hc.
    - exfalso. destruct (cl1 o H) as [Hc1|Hd1]; [set_solver|]. apply (HC2 (ech o)); [done|by apply chans_of_elem].
    - split; [done|]. intros H1. by apply ((proj1 (map_disjoint_dom K1 K2) Kdisj) o).
  Qed.

  Local Lemma dom_K_of {Y : Type} (m1 m2 : gmap cend Y) o v :
    dom m1 = dom K1 → dom m2 = dom K2 → (m1 ∪ m2) !! o = Some v → o ∈ dom (K1 ∪ K2).
  Proof. intros H1 H2 H. apply elem_of_dom_2 in H. by rewrite dom_union_L, <-H1, <-H2, <-dom_union_L. Qed.

  Theorem soup_par :
    soup_inv (N1 `max` N2) n (wjoin W1 W2) (Σa ∪ Σb) T
      (LFState (C1 ∪ C2, M1 ∪ M2) (K1 ∪ K2) (tsel (dom M1) tk1 tk2))
      (A1 ∪ A2) (Π1 ∪ Π2) (tsel (dom M1) U1 U2).
  Proof.
    unfold soup_inv. constructor; simpl.
    - exact (sp_tfree _ _ _ _ _ _ _ _ Hs1).
    - intros t e He. unfold tsel. apply (lookup_union_Some _ _ _ _ HM) in He as [He|He].
      + assert (t ∈ dom M1) as Ht by (by eapply elem_of_dom_2). rewrite decide_True by done.
        rewrite kres1 by (done || exact dA1). eapply Erel_mono; [apply wext_join_l|].
        exact (sp_rel _ _ _ _ _ _ _ _ Hs1 t e He).
      + assert (t ∈ dom M2) as Ht by (by eapply elem_of_dom_2).
        assert (t ∉ dom M1) as Ht1 by (apply (map_disjoint_dom M1 M2) in HM; set_solver).
        rewrite decide_False by done. rewrite kres2 by (done || exact Adisj || exact dA2).
        eapply Erel_mono; [apply wext_join_r|]. exact (sp_rel _ _ _ _ _ _ _ _ Hs2 t e He).
    - intros t e He. unfold tsel. apply (lookup_union_Some _ _ _ _ HM) in He as [He|He].
      + rewrite decide_True by (by eapply elem_of_dom_2). exact (sp_ty _ _ _ _ _ _ _ _ Hs1 t e He).
      + assert (t ∉ dom M1) as Ht1.
        { apply (map_disjoint_dom M1 M2) in HM. apply elem_of_dom_2 in He. set_solver. }
        rewrite decide_False by done. right. by destruct (sp_ty _ _ _ _ _ _ _ _ Hs2 t e He).
    - intros t e He. unfold tsel. apply (lookup_union_Some _ _ _ _ HM) in He as [He|He].
      + assert (t ∈ dom M1) as Ht by (by eapply elem_of_dom_2). rewrite decide_True by done.
        rewrite kres1, ctrs1 by (done || exact dP1). apply (FuelE_refill_mono (Some N1)); [simpl; lia|].
        exact (sp_fuel _ _ _ _ _ _ _ _ Hs1 t e He).
      + assert (t ∈ dom M2) as Ht by (by eapply elem_of_dom_2).
        assert (t ∉ dom M1) as Ht1 by (apply (map_disjoint_dom M1 M2) in HM; set_solver).
        rewrite decide_False by done. rewrite kres2, ctrs2 by (done || exact Pdisj || exact dP2).
        apply (FuelE_refill_mono (Some N2)); [simpl; lia|]. exact (sp_fuel _ _ _ _ _ _ _ _ Hs2 t e He).
    - rewrite !map_fmap_union. f_equal; [exact (sp_pts _ _ _ _ _ _ _ _ Hs1)|exact (sp_pts _ _ _ _ _ _ _ _ Hs2)].
    - rewrite !dom_union_L. f_equal; [exact dP1|exact dP2].
    - intros o h Ho. rewrite lookup_union_is_Some. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]].
      + left. exact (sp_owner _ _ _ _ _ _ _ _ Hs1 o h Ho).
      + right. exact (sp_owner _ _ _ _ _ _ _ _ Hs2 o h Ho).
    - intros o. rewrite dom_union_L, elem_of_union. intros [Ho|Ho].
      + destruct (cl1 o Ho); [left; set_solver|right; set_solver].
      + destruct (cl2 o Ho); [left; set_solver|right; set_solver].
    - intros o Ho Hc. apply elem_of_union in Hc as [Hc|Hc].
      + pose proof (side1 o Ho Hc) as H1. pose proof (sp_pair _ _ _ _ _ _ _ _ Hs1 o H1 Hc) as H.
        rewrite dom_union_L. set_solver.
      + destruct (side2 o Ho Hc) as [H2 _]. pose proof (sp_pair _ _ _ _ _ _ _ _ Hs2 o H2 Hc) as H.
        rewrite dom_union_L. set_solver.
    - intros o S x S' x' H1 H2 Hc.
      pose proof (dom_K_of _ _ _ _ dA1 dA2 H1) as Ho. pose proof (dom_K_of _ _ _ _ dA1 dA2 H2) as Ho'.
      apply elem_of_union in Hc as [Hc|Hc].
      + assert (ech (edual o) ∈ C1) as Hc' by by rewrite ech_edual.
        apply (sp_sdual _ _ _ _ _ _ _ _ Hs1 o S x S' x'); [| |done].
        * apply (union_lookup_in_l _ _ _ _ H1). rewrite dA1. by apply side1.
        * apply (union_lookup_in_l _ _ _ _ H2). rewrite dA1. by apply side1.
      + assert (ech (edual o) ∈ C2) as Hc' by by rewrite ech_edual.
        apply (sp_sdual _ _ _ _ _ _ _ _ Hs2 o S x S' x'); [| |done].
        * apply (union_lookup_out_l _ _ _ _ H1). rewrite dA1. by apply side2.
        * apply (union_lookup_out_l _ _ _ _ H2). rewrite dA1. by apply side2.
    - intros o P P' H1 H2 Hc.
      pose proof (dom_K_of _ _ _ _ dP1 dP2 H1) as Ho. pose proof (dom_K_of _ _ _ _ dP1 dP2 H2) as Ho'.
      apply elem_of_union in Hc as [Hc|Hc].
      + assert (ech (edual o) ∈ C1) as Hc' by by rewrite ech_edual.
        apply (sp_pdual _ _ _ _ _ _ _ _ Hs1 o P P'); [| |done].
        * apply (union_lookup_in_l _ _ _ _ H1). rewrite dP1. by apply side1.
        * apply (union_lookup_in_l _ _ _ _ H2). rewrite dP1. by apply side1.
      + assert (ech (edual o) ∈ C2) as Hc' by by rewrite ech_edual.
        apply (sp_pdual _ _ _ _ _ _ _ _ Hs2 o P P'); [| |done].
        * apply (union_lookup_out_l _ _ _ _ H1). rewrite dP1. by apply side2.
        * apply (union_lookup_out_l _ _ _ _ H2). rewrite dP1. by apply side2.
    - intros o y Hy. apply lookup_union_Some_raw in Hy as [Hy|[_ Hy]].
      + apply lookup_union_Some_l. exact (sp_sig _ _ _ _ _ _ _ _ Hs1 o y Hy).
      + apply lookup_union_Some_r; [exact Adisj|]. exact (sp_sig _ _ _ _ _ _ _ _ Hs2 o y Hy).
    - intros o h Ho. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]].
      + exact (sp_fin _ _ _ _ _ _ _ _ Hs1 o h Ho).
      + exact (sp_fin _ _ _ _ _ _ _ _ Hs2 o h Ho).
    - intros o S x Hy. apply lookup_union_Some_raw in Hy as [Hy|[_ Hy]].
      + apply lookup_union_Some_l. exact (sp_psig _ _ _ _ _ _ _ _ Hs1 o S x Hy).
      + apply lookup_union_Some_r; [exact Pdisj|]. exact (sp_psig _ _ _ _ _ _ _ _ Hs2 o S x Hy).
  Qed.
End par.

(** ** Restriction *)

Section nu.
  Context (N n : nat) (W : world) (Σ ΣR : senv) (T : ty) (C : gset chan) (M : gmap nat expr)
    (K : own) (tk : nat → nat) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W (Σ ∪ ΣR) T (LFState (C, M) K tk) A Π U).
  Context (HCR : C ## chans_of ΣR) (HΣR : chans_of Σ ## chans_of ΣR)
    (Hpair : ∀ o S (x : point), ΣR !! o = Some (S, x) → ΣR !! edual o = Some (dual S, (pt_dual x))).

  Local Lemma lookup_R o y : ΣR !! o = Some y → (Σ ∪ ΣR) !! o = Some y.
  Proof.
    intros H. rewrite lookup_union_r; [done|]. apply not_elem_of_dom. intros Ho.
    apply (chans_dom_disj _ _ HΣR o Ho). by eapply elem_of_dom_2.
  Qed.

  (** A held end of a restricted channel of Σ_R is an end of Σ_R. *)
  Local Lemma side o : o ∈ dom K → ech o ∈ chans_of ΣR → o ∈ dom ΣR.
  Proof.
    intros Ho Hc. destruct (sp_closed _ _ _ _ _ _ _ _ Hs o Ho) as [H|H]; simpl in H.
    - exfalso. by apply (HCR (ech o)).
    - rewrite dom_union_L, elem_of_union in H. destruct H as [H|H]; [|done].
      exfalso. apply (HΣR (ech o)); [by apply chans_of_elem|done].
  Qed.

  Local Lemma entries o : o ∈ dom K → ech o ∈ chans_of ΣR →
    ∃ S (x : point), A !! o = Some (S, x) ∧ A !! edual o = Some (dual S, (pt_dual x)) ∧
           Π !! o = Some S ∧ Π !! edual o = Some (dual S).
  Proof.
    intros Ho Hc. apply side, elem_of_dom in Ho as [[S x] HR]; [|done].
    pose proof (Hpair o S x HR) as HR'. exists S, x. split_and!.
    - exact (sp_sig _ _ _ _ _ _ _ _ Hs o _ (lookup_R o _ HR)).
    - exact (sp_sig _ _ _ _ _ _ _ _ Hs _ _ (lookup_R _ _ HR')).
    - exact (sp_psig _ _ _ _ _ _ _ _ Hs o S x (lookup_R o _ HR)).
    - exact (sp_psig _ _ _ _ _ _ _ _ Hs _ _ _ (lookup_R _ _ HR')).
  Qed.

  Theorem soup_nu : soup_inv N n W Σ T (LFState (C ∪ chans_of ΣR, M) K tk) A Π U.
  Proof.
    pose proof (soup_dom_A _ _ _ _ _ _ _ _ _ Hs) as HdA. pose proof (soup_dom_P _ _ _ _ _ _ _ _ _ Hs) as HdP.
    simpl in HdA, HdP. unfold soup_inv. constructor; simpl.
    - exact (sp_tfree _ _ _ _ _ _ _ _ Hs).
    - exact (sp_rel _ _ _ _ _ _ _ _ Hs).
    - exact (sp_ty _ _ _ _ _ _ _ _ Hs).
    - exact (sp_fuel _ _ _ _ _ _ _ _ Hs).
    - exact (sp_pts _ _ _ _ _ _ _ _ Hs).
    - exact (sp_dom _ _ _ _ _ _ _ _ Hs).
    - exact (sp_owner _ _ _ _ _ _ _ _ Hs).
    - intros o Ho. destruct (sp_closed _ _ _ _ _ _ _ _ Hs o Ho) as [H|H]; simpl in H; [left; set_solver|].
      rewrite dom_union_L, elem_of_union in H. destruct H as [H|H]; [by right|].
      left. apply elem_of_union_r. by apply chans_of_elem.
    - intros o Ho Hc. apply elem_of_union in Hc as [Hc|Hc]; [exact (sp_pair _ _ _ _ _ _ _ _ Hs o Ho Hc)|].
      destruct (entries o Ho Hc) as (S & x & _ & H & _). rewrite <-HdA. by eapply elem_of_dom_2.
    - intros o S x S' x' H1 H2 Hc. apply elem_of_union in Hc as [Hc|Hc].
      + exact (sp_sdual _ _ _ _ _ _ _ _ Hs o S x S' x' H1 H2 Hc).
      + assert (o ∈ dom K) as Ho by (rewrite <-HdA; by eapply elem_of_dom_2).
        destruct (entries o Ho Hc) as (S0 & x0 & E1 & E2 & _). rewrite E1 in H1. rewrite E2 in H2.
        injection H1 as <- <-. injection H2 as <- <-. split; [done|]. apply sequiv_refl.
    - intros o P P' H1 H2 Hc. apply elem_of_union in Hc as [Hc|Hc].
      + exact (sp_pdual _ _ _ _ _ _ _ _ Hs o P P' H1 H2 Hc).
      + assert (o ∈ dom K) as Ho by (rewrite <-HdP; by eapply elem_of_dom_2).
        destruct (entries o Ho Hc) as (S0 & x0 & _ & _ & E1 & E2). rewrite E1 in H1. rewrite E2 in H2.
        injection H1 as <-. injection H2 as <-. apply sequiv_refl.
    - intros o y Hy. apply (sp_sig _ _ _ _ _ _ _ _ Hs). by apply lookup_union_Some_l.
    - exact (sp_fin _ _ _ _ _ _ _ _ Hs).
    - intros o S x Hy. apply (sp_psig _ _ _ _ _ _ _ _ Hs o S x). by apply lookup_union_Some_l.
  Qed.
End nu.

(** ** P-Connect and P-Join *)

(** The two components of P-Connect over the cut Σ_C, with the side
    conditions of [p_connect] (static/Typing.v). P-Join has the same
    soup, because the soup reads no strictness of the world. *)
Theorem soup_connect N1 N2 n W1 W2 Σ1 Σ2 ΣC T C1 C2 M1 M2 K1 K2 tk1 tk2 A1 A2 Π1 Π2 U1 U2 :
  soup_inv N1 n W1 (Σ1 ∪ ΣC) T (LFState (C1, M1) K1 tk1) A1 Π1 U1 →
  soup_inv N2 n W2 (Σ2 ∪ senv_dual ΣC) TUnit (LFState (C2, M2) K2 tk2) A2 Π2 U2 →
  M1 ##ₘ M2 →
  (∀ o, o ∈ dom ΣC → edual o ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  soup_inv (N1 `max` N2) n (wjoin W1 W2) (Σ1 ∪ Σ2) T
    (LFState (C1 ∪ C2 ∪ chans_of ΣC, M1 ∪ M2) (K1 ∪ K2) (tsel (dom M1) tk1 tk2))
    (A1 ∪ A2) (Π1 ∪ Π2) (tsel (dom M1) U1 U2).
Proof.
  intros Hs1 Hs2 HM Hf H12 H1C H2C HC HC1 HC2.
  set (ΣD := senv_dual ΣC).
  assert (chans_of ΣD = chans_of ΣC) as HD by apply chans_of_senv_dual.
  assert (dom ΣC ## dom ΣD) as HCD.
  { intros o H1 H2. apply dom_senv_dual in H2. by apply (Hf o H1). }
  assert (ΣC ##ₘ Σ2) as HC2m by (apply map_disjoint_dom, chans_dom_disj; set_solver).
  assert ((Σ1 ∪ ΣC) ∪ (Σ2 ∪ ΣD) = (Σ1 ∪ Σ2) ∪ (ΣC ∪ ΣD)) as Heq.
  { rewrite <-!(assoc_L (∪)). f_equal. rewrite !(assoc_L (∪)). f_equal. by apply map_union_comm. }
  pose proof (soup_par N1 N2 n W1 W2 (Σ1 ∪ ΣC) (Σ2 ∪ ΣD) T C1 C2 M1 M2 K1 K2 tk1 tk2 A1 A2 Π1 Π2 U1 U2
    Hs1 Hs2 HM) as Hp.
  rewrite Heq in Hp.
  assert (chans_of (ΣC ∪ ΣD) = chans_of ΣC) as Hcu.
  { rewrite chans_of_union, HD. set_solver. }
  rewrite <-Hcu. apply (soup_nu _ _ _ _ (ΣC ∪ ΣD)).
  - apply Hp; [|done| |].
    + rewrite !dom_union_L. pose proof (chans_dom_disj Σ1 Σ2 H12). pose proof (chans_dom_disj Σ1 ΣC H1C).
      pose proof (chans_dom_disj Σ1 ΣD ltac:(by rewrite HD)). pose proof (chans_dom_disj Σ2 ΣC H2C).
      set_solver.
    + by rewrite chans_of_union, HD.
    + by rewrite chans_of_union.
  - rewrite Hcu. set_solver.
  - rewrite Hcu, chans_of_union. set_solver.
  - intros o S x Ho. by apply cut_pair.
Qed.

(** ** One thread *)

(** The ownership of a single thread 0 holding every end of Θ, at its
    point, with counter N. *)
Definition kterm (N : nat) (Θ : tenv) : own := (λ te, Hold 0 (te_pt te) (Some N)) <$> Θ.

Section term.
  Context (N n : nat) (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr) (T : ty) (tk : nat).
  Local Abbreviation Θ := (tenv_of (Some N) Σ ∪ ΘB).
  Context (Hp : tfree T) (HB : ∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) (HΣ : chans_of Σ ## C0)
    (Hd : ∀ c, c ∈ C0 → ∃ S (x : point), ΘB !! (c⁺)%cend = Some (TE S x (Some N)) ∧
                               ΘB !! (c⁻)%cend = Some (TE (dual S) (pt_dual x) (Some N)))
    (He : t ∈ E[live]^W _ n⟦tenv_erase Θ ⊢ T⟧^∅)
    (Hf : t ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(te_sty <$> Θ, const (Some N) <$> (te_sty <$> Θ), tk)).

  Local Lemma kres_term {Y : Type} (m : gmap cend Y) : dom m = dom Θ → kres (kterm N Θ) 0 m = m.
  Proof.
    intros Hdm. apply map_eq_some. intros o v. rewrite lookup_kres. split; [by intros [? _]|].
    intros Hm. split; [done|]. assert (o ∈ dom Θ) as Ho by (rewrite <-Hdm; by eapply elem_of_dom_2).
    apply elem_of_dom in Ho as [te Hte]. eexists. unfold kterm. rewrite lookup_fmap, Hte. by split.
  Qed.

  Local Lemma ctrs_term : ctrs (kterm N Θ) 0 = const (Some N) <$> (te_sty <$> Θ).
  Proof.
    apply map_eq_some. intros o f. rewrite lookup_ctrs, !lookup_fmap. unfold kterm. rewrite lookup_fmap.
    destruct (Θ !! o) as [te|]; simpl; split.
    - intros (h & [= <-] & _ & <-). done.
    - intros [= <-]. by eexists.
    - by intros (h & ? & _).
    - done.
  Qed.

  (** An end of a restricted channel is an end of Θ_B, at its entry. *)
  Local Lemma lookup_B o : ech o ∈ C0 → Θ !! o = ΘB !! o.
  Proof.
    intros Hc. apply lookup_union_r. unfold tenv_of. rewrite lookup_fmap.
    destruct (Σ !! o) eqn:E; [|done]. exfalso. apply (HΣ (ech o)); [|done].
    apply chans_of_elem. by eapply elem_of_dom_2.
  Qed.

  Local Lemma restricted o : ech o ∈ C0 →
    ∃ S (x : point), Θ !! o = Some (TE S x (Some N)) ∧ Θ !! edual o = Some (TE (dual S) (pt_dual x) (Some N)).
  Proof.
    intros Hc. rewrite (lookup_B o Hc), (lookup_B (edual o)) by by rewrite ech_edual.
    destruct (Hd (ech o) Hc) as (S & x & H1 & H2). destruct o as [c|c]; simpl in *.
    - by exists S, x.
    - exists (dual S), (pt_dual x). rewrite dual_involutive, pt_dual_dual. done.
  Qed.

  Theorem soup_term :
    soup_inv N n W Σ T (LFState (C0, {[0 := t]}) (kterm N Θ) (λ _, tk))
      (tenv_erase Θ) (te_sty <$> Θ) (λ _, T).
  Proof.
    assert (dom (tenv_erase Θ) = dom Θ) as HdA by (unfold tenv_erase; apply dom_fmap_L).
    assert (dom (te_sty <$> Θ) = dom Θ) as HdP by apply dom_fmap_L.
    assert (dom (kterm N Θ) = dom Θ) as HdK by (unfold kterm; apply dom_fmap_L).
    unfold soup_inv. constructor; simpl.
    - done.
    - intros t' e Ht'. apply lookup_singleton_Some in Ht' as [<- <-]. by rewrite kres_term.
    - by left.
    - intros t' e Ht'. apply lookup_singleton_Some in Ht' as [<- <-]. by rewrite kres_term, ctrs_term.
    - unfold tenv_erase, kterm. rewrite <-!map_fmap_compose. by apply map_fmap_ext.
    - by rewrite HdP, HdK.
    - intros o h Ho. unfold kterm in Ho. apply lookup_fmap_Some in Ho as (te & <- & _). simpl.
      rewrite lookup_singleton_eq. by eexists.
    - intros o Ho. rewrite HdK, dom_union_L, elem_of_union in Ho. destruct Ho as [Ho|Ho].
      + right. unfold tenv_of in Ho. by rewrite dom_fmap_L in Ho.
      + left. by apply HB.
    - intros o Ho Hc. rewrite HdK, dom_union_L. apply elem_of_union_r, HB. by rewrite ech_edual.
    - intros o S x S' x' H1 H2 Hc. destruct (restricted o Hc) as (S0 & x0 & E1 & E2).
      unfold tenv_erase in H1, H2. rewrite lookup_fmap, E1 in H1. rewrite lookup_fmap, E2 in H2.
      simpl in H1, H2. injection H1 as <- <-. injection H2 as <- <-. split; [done|]. apply sequiv_refl.
    - intros o P P' H1 H2 Hc. destruct (restricted o Hc) as (S0 & x0 & E1 & E2).
      rewrite lookup_fmap, E1 in H1. rewrite lookup_fmap, E2 in H2. simpl in H1, H2.
      injection H1 as <-. injection H2 as <-. apply sequiv_refl.
    - intros o [S x] Hy. unfold tenv_erase. rewrite lookup_fmap.
      rewrite (lookup_union_Some_l _ _ o (TE S x (Some N))); [done|]. unfold tenv_of. by rewrite lookup_fmap, Hy.
    - intros o h Ho. unfold kterm in Ho. apply lookup_fmap_Some in Ho as (te & <- & _). by eexists.
    - intros o S x Hy. rewrite lookup_fmap.
      rewrite (lookup_union_Some_l _ _ o (TE S x (Some N))); [done|]. unfold tenv_of. by rewrite lookup_fmap, Hy.
  Qed.
End term.
