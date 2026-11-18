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

(** ** The multiset extension *)

Lemma ms_cancel (M M0 : gmultiset expr) x : M ⊎ {[+ x +]} = M0 ⊎ {[+ x +]} → M0 = M.
Proof. multiset_solver. Qed.
Lemma ms_in (M M0 : gmultiset expr) x z : z ≠ x → M ⊎ {[+ x +]} = M0 ⊎ {[+ z +]} → z ∈ M.
Proof. multiset_solver. Qed.
Lemma ms_rest (M M0 : gmultiset expr) x z :
  M ⊎ {[+ x +]} = M0 ⊎ {[+ z +]} → z ≠ x → z ∈ M → M0 = (M ∖ {[+ z +]}) ⊎ {[+ x +]}.
Proof. multiset_solver. Qed.
Lemma ms_swap (M Y : gmultiset expr) x : M ⊎ {[+ x +]} ⊎ Y = (M ⊎ Y) ⊎ {[+ x +]}.
Proof. multiset_solver. Qed.
Lemma ms_swap' (M Y : gmultiset expr) y : M ⊎ ({[+ y +]} ⊎ Y) = (M ⊎ Y) ⊎ {[+ y +]}.
Proof. multiset_solver. Qed.
Lemma ms_split (M : gmultiset expr) z : z ∈ M → M = M ∖ {[+ z +]} ⊎ {[+ z +]}.
Proof. multiset_solver. Qed.
Lemma ms_empty (M0 : gmultiset expr) x : (∅ : gmultiset expr) = M0 ⊎ {[+ x +]} → False.
Proof. multiset_solver. Qed.
Lemma ms_in_l (Y : gmultiset expr) y : y ∈ {[+ y +]} ⊎ Y.
Proof. multiset_solver. Qed.
Lemma ms_in_r (Y : gmultiset expr) y z : z ∈ Y → z ∈ {[+ y +]} ⊎ Y.
Proof. multiset_solver. Qed.

Section mstep.
  Context (R : expr → expr → Prop).

  (** One element x is replaced by finitely many smaller ones. *)
  Definition mstep (M' M : gmultiset expr) : Prop :=
    ∃ x Y M0, M = M0 ⊎ {[+ x +]} ∧ M' = M0 ⊎ Y ∧ ∀ y, y ∈ Y → R y x.

  Lemma mstep_union_acc (M Y : gmultiset expr) x :
    (∀ x', R x' x → ∀ M, Acc mstep M → Acc mstep (M ⊎ {[+ x' +]})) →
    (∀ y, y ∈ Y → R y x) → Acc mstep M → Acc mstep (M ⊎ Y).
  Proof.
    intros IH HY HM. induction Y as [|y Y IHY] using gmultiset_ind.
    - by rewrite (right_id_L ∅ (⊎)).
    - rewrite ms_swap'. apply (IH y); [apply HY, ms_in_l|]. apply IHY. intros z Hz. by apply HY, ms_in_r.
  Qed.

  Lemma mstep_acc_add x : Acc R x → ∀ M, Acc mstep M → Acc mstep (M ⊎ {[+ x +]}).
  Proof.
    induction 1 as [x _ IHx]. intros M HM. induction HM as [M HMacc IHM].
    constructor. intros N' (z & Y & M0 & Heq & -> & HY).
    destruct (decide (z = x)) as [->|Hne].
    - rewrite (ms_cancel M M0 x Heq).
      apply (mstep_union_acc M Y x); [exact IHx|exact HY|]. constructor. exact HMacc.
    - pose proof (ms_in M M0 x z Hne Heq) as Hz.
      rewrite (ms_rest M M0 x z Heq Hne Hz), ms_swap.
      apply IHM. exists z, Y, (M ∖ {[+ z +]}). split_and!; [by apply ms_split|done|done].
  Qed.

  Lemma mstep_acc M : (∀ x, x ∈ M → Acc R x) → Acc mstep M.
  Proof.
    induction M as [|x M IH] using gmultiset_ind; intros H.
    - constructor. intros N' (z & Y & M0 & Heq & _). exfalso. by apply (ms_empty M0 z).
    - rewrite (comm_L (⊎)). apply mstep_acc_add; [apply H, ms_in_l|].
      apply IH. intros y Hy. by apply H, ms_in_r.
  Qed.
End mstep.

(** ** The τ steps of a soup *)

Definition cmset (E : gmultiset expr) : gmultiset expr := gmultiset_map cerase E.

Lemma cmset_union E1 E2 : cmset (E1 ⊎ E2) = cmset E1 ⊎ cmset E2.
Proof. apply gmultiset_map_disj_union. Qed.
Lemma cmset_singleton e : cmset {[+ e +]} = {[+ cerase e +]}.
Proof. apply gmultiset_map_singleton. Qed.

Lemma cmset_emapE g E : cmset (emapE g E) = cmset E.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold emapE. by rewrite gmultiset_map_empty.
  - by rewrite emapE_disj_union, emapE_singleton, !cmset_union, IH, !cmset_singleton, cerase_emap.
Qed.

(** A τ step of a soup is a step of the multiset of its erased threads. *)
Lemma padmin_mstep p p' : padmin p p' → mstep tRs (cmset p'.2) (cmset p.2).
Proof.
  intros (q & ev & q' & <- & Hst & <- & Had).
  destruct Hst as [C M i e e' Hi Hs|C M i e ℓ c e' Hi Hs|C M i e κ o c e' Hi Hs|C M i j e Mv v e' Hi Hs Hj
    | | | |C M i e o1 o2 e' Hi Hs HC|]; simpl in Had; try contradiction; unfold erase; cbn [fst snd].
  - rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi), !cmset_union, !cmset_singleton.
    exists (cerase e), {[+ cerase e' +]}, (cmset (soup (delete i M))). split_and!; [done|done|].
    intros y Hy. apply gmultiset_elem_of_singleton in Hy as ->. left. by eapply tR_step; [|exact Hs].
  - rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi), !cmset_union, !cmset_singleton.
    exists (cerase e), {[+ cerase e' +]}, (cmset (soup (delete i M))). split_and!; [done|done|].
    intros y Hy. apply gmultiset_elem_of_singleton in Hy as ->. left. by eapply tR_step; [|exact Hs].
  - rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi), !cmset_union, !cmset_singleton.
    exists (cerase e), {[+ cerase e' +]}, (cmset (soup (delete i M))). split_and!; [done|done|].
    intros y Hy. apply gmultiset_elem_of_singleton in Hy as ->. left. by eapply tR_step; [|exact Hs].
  - assert (i ≠ j) by (intros ->; congruence).
    rewrite soup_insert by (rewrite lookup_insert_ne; done).
    rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi), !cmset_union, !cmset_singleton.
    exists (cerase e), ({[+ cerase e' +]} ⊎ {[+ cerase (App v EUnit) +]}), (cmset (soup (delete i M))).
    split_and!; [done|by rewrite (assoc_L (⊎))|]. intros y Hy.
    apply gmultiset_elem_of_disj_union in Hy as [Hy|Hy]; apply gmultiset_elem_of_singleton in Hy as ->.
    + left. by eapply tR_step; [|exact Hs].
    + right. destruct (tstep_cerase _ _ _ Hs) as (x' & Hx & _). simpl in Hx.
      exists (set_map (λ _, EPos "") Mv), (cerase v), x'. split; [done|]. unfold cerase. simpl. by rewrite emap_emap.
  - rewrite soup_fmap. change (gmultiset_map (emap (csub o1 o2)) (soup (<[i:=e']> M))) with
      (emapE (csub o1 o2) (soup (<[i:=e']> M))). rewrite cmset_emapE.
    rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi), !cmset_union, !cmset_singleton.
    exists (cerase e), {[+ cerase e' +]}, (cmset (soup (delete i M))). split_and!; [done|done|].
    intros y Hy. apply gmultiset_elem_of_singleton in Hy as ->. left. by eapply tR_step; [|exact Hs].
Qed.

Lemma padmin_acc (ME : gmultiset expr) :
  Acc (mstep tRs) ME → ∀ p, cmset p.2 = ME → Acc (λ y x, padmin x y) p.
Proof.
  induction 1 as [ME _ IH]. intros p <-. constructor. intros p' Hpa.
  apply (IH (cmset p'.2)); [by apply padmin_mstep|done].
Qed.

(** ** No τ-divergence *)

Theorem soup_no_tau_divergence N W T a :
  (∀ n, a ∈ S^{N,W} _ n⟦∅ ⊢ T⟧) → no_tau_divergence (erase (s_q a)).
Proof.
  intros Hs p Hp. destruct (pred_star_lift _ _ Hp) as (q' & Hq' & <-).
  destruct (lfsoup_isteps N W T a q' Hs Hq') as (a' & <- & Hs').
  apply (padmin_acc (cmset (soup (s_q a').2))); [|done].
  apply mstep_acc. intros x Hx. unfold cmset in Hx. apply elem_of_gmultiset_map in Hx as (e & -> & He).
  apply elem_of_soup in He as [t Ht].
  destruct (Hs' 1) as (A & Π & U & Hsi).
  exact (Erel_tacc 0 W _ _ _ e (s_rel Hsi t e Ht)).
Qed.
