(** * No τ-divergence from the soup (stage S8, proposal §2.12, Q12)

      soup_no_tau_divergence :
        (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → no_tau_divergence (erase (s_q a))

    The τ steps of κ_L cost nothing, so the live relation reads them
    inside the least fixpoint of one level. A thread in E[live] at a
    positive level therefore admits no infinite sequence of
    administrative steps, its spawned children included, because O-Spawn
    reads the child at the parent's level inside the same fixpoint
    ([Erel_tacc]). The τ steps of a soup replace one thread by smaller
    ones and rename the others, so the multiset of the erased threads
    decreases in the multiset extension of the per-thread order
    ([mstep_acc]). The live process conjunct of LF is not needed. *)

From stdpp Require Import relations.
From GV Require Export soup.SoupRun.

(** ** The order of one thread with its children *)

Definition tRs (y x : expr) : Prop :=
  tR y x ∨ ∃ M v x', tstep x (LSpawn M v) x' ∧ y = cerase (App v EUnit).

(** A step of the erased term comes from a step of the term, with a new
    name chosen outside X. *)
Lemma admin_back e α x' (X : gset chan) :
  tstep (cerase e) α x' → admin_lbl α →
  ∃ α0 e0, tstep e α0 e0 ∧ admin_lbl α0 ∧ cerase x' = cerase e0 ∧
    (∀ ℓ c, α0 = LNew ℓ c → c ∉ X) ∧ (∀ κ o c, α0 = LNewAt κ o c → c ∉ X) ∧
    (∀ M v, α = LSpawn M v → ∃ M0 v0, α0 = LSpawn M0 v0 ∧ cerase (App v EUnit) = cerase (App v0 EUnit)).
Proof.
  intros Hst Hα.
  destruct (act_step _ _ _ Hst) as (a' & Ha' & Ho). rewrite act_cerase in Ha'.
  destruct (act e) as [a|] eqn:Ha; [|done]. simpl in Ha'. injection Ha' as <-.
  assert (∀ α0 e0, tstep e α0 e0 → lerase α0 = lerase α → cerase x' = cerase e0) as Hdet.
  { intros α0 e0 Hs0 Hl. destruct (tstep_cerase e α0 e0 Hs0) as (x0 & Hx0 & <-).
    eapply tstep_det_cerase; [exact Hst|exact Hx0|]. by rewrite lerase_idem, Hl. }
  set (c0 := fresh (X ∪ fchans e)). assert (c0 ∉ X ∪ fchans e) as Hc0 by apply is_fresh.
  destruct a as [|ℓ|κ o|v|o|o v|o|o1 o2|o i|o]; simpl in Ho;
    destruct α as [|ℓ' c1|κ' o' c1|M w|[| | | | |os]]; simpl in Hα; try contradiction.
  - destruct (act_offer e ABeta LBeta Ha I) as [e0 He0].
    exists LBeta, e0. split_and!; [done|done|by apply (Hdet _ _ He0)|intros; discriminate..].
  - destruct (act_offer e (ANew ℓ) (LNew ℓ c0) Ha eq_refl) as [e0 He0].
    exists (LNew ℓ c0), e0. split_and!; [done|done| |intros ? ? [= _ <-]; set_solver|intros; discriminate|intros; discriminate].
    apply (Hdet _ _ He0). simpl in *. by subst.
  - destruct (act_offer e (ANewAt κ o) (LNewAt κ o c0) Ha (conj eq_refl eq_refl)) as [e0 He0].
    exists (LNewAt κ o c0), e0. split_and!; [done|done| |intros; discriminate|intros ? ? ? [= _ _ <-]; set_solver|intros; discriminate].
    apply (Hdet _ _ He0). simpl in *. destruct Ho. by subst.
  - destruct (act_offer e (ASpawn v) (LSpawn (fends v) v) Ha (conj eq_refl eq_refl)) as [e0 He0].
    destruct Ho as [<- ->].
    exists (LSpawn (fends v) v), e0. split_and!; [done|done| |intros; discriminate|intros; discriminate|].
    + apply (Hdet _ _ He0). simpl. rewrite fends_emap. fold cerase. by rewrite set_map_erase_idem, cerase_idem.
    + intros M' v' [= _ <-]. exists (fends v), v. split; [done|]. unfold cerase. simpl. by rewrite emap_emap.
  - destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e0 He0].
    simpl in Ho. subst os. exists (LSess (SLink ({[o1]} ∪ {[o2]}))), e0.
    split_and!; [done|done| |intros; discriminate|intros; discriminate|intros; discriminate].
    apply (Hdet _ _ He0). simpl. f_equal. f_equal. set_solver.
Qed.

Lemma gfresh_exists ℓ (Θ : senv) : ∃ g, gfresh ℓ g Θ.
Proof.
  set (G := list_to_set (omap (λ p : cend * (sty * point),
    match pt_root p.2.2 with NGen ℓ' g => if decide (ℓ' = ℓ) then Some g else None | _ => None end)
    (map_to_list Θ)) : gset nat).
  exists (fresh G). intros o S x Ho Hr. apply (is_fresh G). apply elem_of_list_to_set, list_elem_of_omap.
  exists (o, (S, x)). split; [by apply elem_of_map_to_list|]. simpl. rewrite Hr. by rewrite decide_True.
Qed.

(** A thread in E[live] at a positive level, with its children, takes
    no infinite sequence of administrative steps. *)
Lemma Erel_tacc n : ∀ W Θ T F e, Erel live (S n) W Θ T F e → Acc tRs (cerase e).
Proof.
  apply (Erel_S_ind live n (λ W Θ T F e, Acc tRs (cerase e))).
  intros W Θ T F e H. destruct (H W (wext_refl W)) as (_ & _ & Hsteps).
  pose proof (proj1 (Esteps_iff _ _ _ _ _ _ _ _ _ _ _) Hsteps) as Hobl. clear H Hsteps.
  constructor. intros y Hy.
  assert (∀ α x', tstep (cerase e) α x' → admin_lbl α → Acc tRs (cerase x') ∧
            ∀ M v, α = LSpawn M v → Acc tRs (cerase (App v EUnit))) as Hall.
  { intros α x' Hst Hα.
    destruct (admin_back e α x' (set_map ech (dom Θ)) Hst Hα) as (α0 & e0 & Hs0 & Hα0 & -> & Hn1 & Hn2 & Hsp).
    pose proof (Hobl α0 e0 Hs0) as Ho.
    destruct α0 as [|ℓ c|κ o c|M0 v0|[| | | | |os]]; simpl in Hα0; try contradiction; cbn [Eobl] in Ho.
    - split; [|intros M1 v1 Hα1; destruct (Hsp M1 v1 Hα1) as (? & ? & Heq & _); discriminate Heq]. by destruct (proj1 Ho eq_refl).
    - split; [|intros M1 v1 Hα1; destruct (Hsp M1 v1 Hα1) as (? & ? & Heq & _); discriminate Heq]. unfold o_new in Ho.
      assert (cfresh c Θ) as Hcf.
      { pose proof (Hn1 ℓ c eq_refl) as Hc. split; intros Hd; apply Hc; apply elem_of_map; [exists (EPos c)|exists (ENeg c)]; done. }
      destruct (gfresh_exists ℓ Θ) as [g Hg]. destruct (Ho Hcf g Hg) as [S HS].
      by destruct (proj1 HS eq_refl).
    - split; [|intros M1 v1 Hα1; destruct (Hsp M1 v1 Hα1) as (? & ? & Heq & _); discriminate Heq]. unfold o_new_at in Ho.
      assert (cfresh c Θ) as Hcf.
      { pose proof (Hn2 κ o c eq_refl) as Hc. split; intros Hd; apply Hc; apply elem_of_map; [exists (EPos c)|exists (ENeg c)]; done. }
      destruct (Ho Hcf) as (S0 & x & _ & S & HS). by destruct (proj1 HS eq_refl).
    - unfold o_spawn in Ho. destruct Ho as (ΘM & Θr & _ & _ & _ & Hth & Hpar).
      split; [by destruct (proj1 Hpar eq_refl)|].
      intros M v -> . destruct (Hsp M v eq_refl) as (M1 & v1 & [= <- <-] & ->).
      destruct Hth as (eb & -> & _ & Hb).
      destruct (Hb W (S n) ∅ EUnit (wext_refl W) ltac:(cbn; lia) (map_disjoint_empty_r _)) as [_ Hb2].
      destruct (Hb2 eq_refl (conj eq_refl eq_refl)) as [_ Hacc].
      constructor. intros y' [(α' & x'' & _ & Hs' & ->)|(M' & v' & x'' & Hs' & _)].
      + unfold cerase in Hs'. simpl in Hs'. fold cerase in Hs'.
        apply tstep_inv in Hs' as [Hh|(f & e1 & e1' & Hf & Heq & -> & Hs1)].
        * inversion Hh; subst. rewrite cerase_subst1, cerase_idem. rewrite cerase_subst1 in Hacc. exact Hacc.
        * exfalso. destruct f; simpl in Heq; try discriminate; injection Heq as <- <-;
            apply (val_no_tstep _ _ _ Hs1); simpl; rewrite ?is_val_emap; done.
      + exfalso. unfold cerase in Hs'. simpl in Hs'.
        apply tstep_inv in Hs' as [Hh|(f & e1 & e1' & Hf & Heq & -> & Hs1)]; [inversion Hh|].
        destruct f; simpl in Heq; try discriminate; injection Heq as <- <-;
          apply (val_no_tstep _ _ _ Hs1); simpl; rewrite ?is_val_emap; done.
    - split; [|intros M1 v1 Hα1; destruct (Hsp M1 v1 Hα1) as (? & ? & Heq & _); discriminate Heq]. unfold o_link in Ho.
      destruct Ho as (o1 & o2 & S1 & S2 & x & _ & _ & _ & _ & _ & Hc). by destruct (proj1 Hc eq_refl). }
  destruct Hy as [(α & x' & Hα & Hst & ->)|(M & v & x' & Hst & ->)].
  - by destruct (Hall α x' Hst Hα).
  - by apply (proj2 (Hall _ x' Hst I) M v).
Qed.
