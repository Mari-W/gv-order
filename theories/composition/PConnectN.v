(** * P-Connectⁿ (spec §11, sharp edges 55)

      Σᵢ, Σ_Cᵢ ⊨_{Wᵢ} (Cᵢ, Eᵢ) : Tᵢ   (i = 1 … n), T₁ = T, the others ∗,
      the Σ_Cᵢ hold both ends of every channel of C₀, each end once, dual,
      W₁ ⊔ … ⊔ Wₙ strict
      ⇒  Σ₁, …, Σₙ ⊨_{W₁ ⊔ … ⊔ Wₙ} (C₁ ∪ … ∪ Cₙ ∪ C₀, E₁ ⊎ … ⊎ Eₙ) : T

    Proof: lift every component to the full amalgam (monotonicity),
    then fold P-Connect at that one world ([Prel_connect_list]). Each
    step connects the composite so far with the next component over the
    channels the two share. Channels of C₀ with an end further down the
    list stay in the composite's interface. A component's interface is
    one map Γ here, and the cut is read off the list of entries the
    components hold for a channel ([ends]): two dual entries on C₀, at
    most one elsewhere. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export composition.PConnect.

Set Default Proof Using "All".

(** One world for both components: W ⊔ W lies below W (as in Static.v,
    restated here so that this file does not depend on the static system). *)
Lemma wext_join_self' W : strict W → wext (wjoin W W) W.
Proof.
  intros HW.
  destruct (wgen_in_world W (λ x y, w_eq W x y ∨ w_eq W x y)
              (λ x y, w_lt W x y ∨ w_lt W x y)) as [Heq Hlt];
    [apply HW|naive_solver|naive_solver|].
  split_and!; [simpl; set_solver|exact Heq|exact Hlt|exact HW].
Qed.

(** ** Components with one interface map *)

Record comp := Comp { cΓ : senv; cC : gset chan; cE : gmultiset expr }.

Definition ends (c : chan) (ps : list comp) : list (sty * point) :=
  omap (λ p, cΓ p !! c) ps.

Definition munion {A} (f : A → senv) (ps : list A) : senv := foldr (λ p acc, f p ∪ acc) ∅ ps.
Definition cunion {A} (f : A → gset chan) (ps : list A) : gset chan :=
  foldr (λ p acc, f p ∪ acc) ∅ ps.
Definition eunion {A} (f : A → gmultiset expr) (ps : list A) : gmultiset expr :=
  foldr (λ p acc, f p ⊎ acc) ∅ ps.

Definition cut_out (D : gset chan) (Σ : senv) : senv := filter (λ kv, kv.1 ∉ D) Σ.
Definition cut_in (D : gset chan) (Σ : senv) : senv := filter (λ kv, kv.1 ∈ D) Σ.

Record conn_ok (W : world) (C0 : gset chan) (ps : list comp) : Prop := {
  ok_cut c : c ∈ C0 → ∃ e e', ends c ps = [e; e'] ∧ w_eq W e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1;
  ok_one c : c ∉ C0 → length (ends c ps) ≤ 1;
  ok_C c : length (filter (λ p, c ∈ cC p) ps) ≤ 1;
  ok_C0 p : p ∈ ps → cC p ## C0;
  ok_CΓ p q : p ∈ ps → q ∈ ps → cC p ## dom (cΓ q)
}.

(** ** Lookups *)

Lemma ends_cons c p ps :
  ends c (p :: ps) = match cΓ p !! c with Some e => e :: ends c ps | None => ends c ps end.
Proof. done. Qed.
Lemma munion_cons {A} (f : A → senv) p ps : munion f (p :: ps) = f p ∪ munion f ps.
Proof. done. Qed.
Lemma cunion_cons {A} (f : A → gset chan) p ps : cunion f (p :: ps) = f p ∪ cunion f ps.
Proof. done. Qed.
Lemma eunion_cons {A} (f : A → gmultiset expr) p ps : eunion f (p :: ps) = f p ⊎ eunion f ps.
Proof. done. Qed.

Lemma omap_cons' {A B} (f : A → option B) x (l : list A) :
  omap f (x :: l) = match f x with Some y => y :: omap f l | None => omap f l end.
Proof. done. Qed.

Lemma omap_fmap' {A B C} (f : B → option C) (g : A → B) (l : list A) :
  omap f (g <$> l) = omap (λ x, f (g x)) l.
Proof.
  induction l as [|x l IH]; [done|]. rewrite fmap_cons, !omap_cons', IH. done.
Qed.

Lemma in_here {A} (x : A) l : x ∈ x :: l.
Proof. apply elem_of_cons. by left. Qed.
Lemma in_there {A} (x y : A) l : x ∈ l → x ∈ y :: l.
Proof. intros H. apply elem_of_cons. by right. Qed.

Lemma lookup_cut_out D Σ c :
  cut_out D Σ !! c = if decide (c ∈ D) then None else Σ !! c.
Proof.
  unfold cut_out. rewrite map_lookup_filter.
  destruct (Σ !! c); simpl; repeat case_decide; simplify_option_eq; done.
Qed.

Lemma lookup_cut_in D Σ c :
  cut_in D Σ !! c = if decide (c ∈ D) then Σ !! c else None.
Proof.
  unfold cut_in. rewrite map_lookup_filter.
  destruct (Σ !! c); simpl; repeat case_decide; simplify_option_eq; done.
Qed.

Lemma dom_cut_in D Σ : dom (cut_in D Σ) = dom Σ ∩ D.
Proof.
  apply set_eq. intros c. rewrite elem_of_intersection, !elem_of_dom, lookup_cut_in.
  case_decide; naive_solver.
Qed.

Lemma dom_cut_out D Σ : dom (cut_out D Σ) = dom Σ ∖ D.
Proof.
  apply set_eq. intros c. rewrite elem_of_difference, !elem_of_dom, lookup_cut_out.
  case_decide; naive_solver.
Qed.

Lemma cut_split D Σ : cut_out D Σ ∪ cut_in D Σ = Σ.
Proof.
  apply map_eq. intros c. rewrite lookup_union, lookup_cut_out, lookup_cut_in.
  case_decide; destruct (Σ !! c); done.
Qed.

Lemma lookup_munion {A} (f : A → senv) ps c :
  munion f ps !! c = head (omap (λ p, f p !! c) ps).
Proof.
  induction ps as [|p ps IH]; [apply lookup_empty|].
  rewrite munion_cons, omap_cons', lookup_union, IH. by destruct (f p !! c), (omap _ ps).
Qed.

Lemma omap_nil_none {A} (f : A → senv) ps c p :
  omap (λ p, f p !! c) ps = [] → p ∈ ps → f p !! c = None.
Proof.
  induction ps as [|q ps IH]; [by intros _ ?%elem_of_nil|]. rewrite omap_cons'.
  destruct (f q !! c) eqn:E; [done|]. intros H [->|Hp]%elem_of_cons; auto.
Qed.

Lemma omap_ext_in {A B} (f g : A → option B) (ps : list A) :
  (∀ p, p ∈ ps → f p = g p) → omap f ps = omap g ps.
Proof.
  induction ps as [|p ps IH]; intros H; [done|]. rewrite !omap_cons'.
  rewrite (H p) by set_solver. rewrite IH; [done|]. intros q Hq. apply H. set_solver.
Qed.

Lemma length_filter_cons {A} (P : A → Prop) `{∀ x, Decision (P x)} x l :
  length (filter P (x :: l)) = (if decide (P x) then 1 else 0) + length (filter P l).
Proof. rewrite filter_cons. by case_decide. Qed.

(** ** One step: merge the first two components *)

Section merge.
  Context (W : world) (C0 : gset chan) (h r : comp) (rs : list comp).
  Context (Hok : conn_ok W C0 (h :: r :: rs)).

  Definition Cc : gset chan := dom (cΓ h) ∩ dom (cΓ r).
  Definition merged : comp :=
    Comp (cut_out Cc (cΓ h) ∪ cut_out Cc (cΓ r)) (cC h ∪ cC r ∪ Cc) (cE h ⊎ cE r).

  Lemma Cc_sub : Cc ⊆ C0.
  Proof.
    intros c Hc. destruct (decide (c ∈ C0)) as [|Hn]; [done|].
    pose proof (ok_one _ _ _ Hok c Hn) as Hl. unfold Cc in Hc.
    apply elem_of_intersection in Hc as [Hh Hr]. apply elem_of_dom in Hh as [e He].
    apply elem_of_dom in Hr as [e' He'].
    rewrite !ends_cons, He, He' in Hl. simpl in Hl. lia.
  Qed.

  Lemma Cc_ends c : c ∈ Cc → ∃ e e',
    cΓ h !! c = Some e ∧ cΓ r !! c = Some e' ∧ ends c rs = [] ∧
    w_eq W e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1.
  Proof.
    intros Hc. pose proof (Cc_sub c Hc) as HC0.
    destruct (ok_cut _ _ _ Hok c HC0) as (e0 & e0' & Hends & Heq & Hd).
    unfold Cc in Hc. apply elem_of_intersection in Hc as [Hh Hr].
    apply elem_of_dom in Hh as [e He]. apply elem_of_dom in Hr as [e' He'].
    rewrite !ends_cons, He, He' in Hends. simplify_eq.
    exists e0, e0'. split_and!; [done|done| |done|done]. done.
  Qed.

  Lemma lookup_merged c :
    cΓ merged !! c = if decide (c ∈ Cc) then None else
                     match cΓ h !! c with Some e => Some e | None => cΓ r !! c end.
  Proof.
    simpl. rewrite lookup_union, !lookup_cut_out. case_decide; [done|].
    by destruct (cΓ h !! c), (cΓ r !! c).
  Qed.

  Lemma ends_merged_out c : c ∉ Cc → ends c (merged :: rs) = ends c (h :: r :: rs).
  Proof.
    intros Hc. rewrite !ends_cons, lookup_merged.
    rewrite decide_False by done.
    destruct (cΓ h !! c) eqn:Eh, (cΓ r !! c) eqn:Er; try done.
    exfalso. apply Hc. unfold Cc. apply elem_of_intersection.
    split; apply elem_of_dom; eauto.
  Qed.

  Lemma ends_merged_in c : c ∈ Cc → ends c (merged :: rs) = [].
  Proof.
    intros Hc. destruct (Cc_ends c Hc) as (e & e' & _ & _ & Hrs & _).
    rewrite ends_cons, lookup_merged, decide_True by done. done.
  Qed.

  Lemma Cc_not_rest c q : c ∈ Cc → q ∈ rs → cΓ q !! c = None.
  Proof.
    intros Hc Hq. destruct (Cc_ends c Hc) as (e & e' & _ & _ & Hrs & _).
    exact (omap_nil_none cΓ rs c q Hrs Hq).
  Qed.

  Lemma merged_ok : conn_ok W (C0 ∖ Cc) (merged :: rs).
  Proof.
    split.
    - intros c Hc. apply elem_of_difference in Hc as [HC0 Hn].
      rewrite ends_merged_out by done. by apply (ok_cut _ _ _ Hok).
    - intros c Hc. destruct (decide (c ∈ Cc)) as [Hin|Hout].
      + rewrite ends_merged_in by done. simpl. lia.
      + rewrite ends_merged_out by done. apply (ok_one _ _ _ Hok).
        intros HC0. apply Hc. by apply elem_of_difference.
    - intros c. pose proof (ok_C _ _ _ Hok c) as Hl.
      rewrite length_filter_cons, (length_filter_cons _ r rs) in Hl.
      rewrite length_filter_cons.
      destruct (decide (c ∈ cC merged)) as [Hin|];
        [|destruct (decide (c ∈ cC h)), (decide (c ∈ cC r)); lia].
      simpl in Hin.
      destruct (decide (c ∈ cC h)), (decide (c ∈ cC r)); try lia.
      assert (c ∈ Cc) as HCc by set_solver.
      assert (length (filter (λ p, c ∈ cC p) rs) = 0) as H0; [|lia].
      destruct (filter (λ p, c ∈ cC p) rs) as [|q l] eqn:E; [done|exfalso].
      assert (q ∈ filter (λ p, c ∈ cC p) rs) as Hq by (rewrite E; set_solver).
      apply list_elem_of_filter in Hq as [Hcq Hq].
      pose proof (ok_CΓ _ _ _ Hok q h (in_there _ _ _ (in_there _ _ _ Hq)) (in_here _ _)) as Hd.
      unfold Cc in HCc. set_solver.
    - intros p [->|Hp]%elem_of_cons.
      + simpl. pose proof (ok_C0 _ _ _ Hok h (in_here _ _)).
        pose proof (ok_C0 _ _ _ Hok r (in_there _ _ _ (in_here _ _))). set_solver.
      + pose proof (ok_C0 _ _ _ Hok p (in_there _ _ _ (in_there _ _ _ Hp))). set_solver.
    - assert (dom (cΓ merged) ⊆ dom (cΓ h) ∪ dom (cΓ r)) as Hdm.
      { simpl. rewrite dom_union_L, !dom_cut_out. set_solver. }
      intros p q Hp Hq. apply elem_of_cons in Hp as [->|Hp]; apply elem_of_cons in Hq as [->|Hq].
      + simpl. rewrite dom_union_L, !dom_cut_out.
        pose proof (ok_CΓ _ _ _ Hok h h (in_here _ _) (in_here _ _)).
        pose proof (ok_CΓ _ _ _ Hok h r (in_here _ _) (in_there _ _ _ (in_here _ _))).
        pose proof (ok_CΓ _ _ _ Hok r h (in_there _ _ _ (in_here _ _)) (in_here _ _)).
        pose proof (ok_CΓ _ _ _ Hok r r (in_there _ _ _ (in_here _ _)) (in_there _ _ _ (in_here _ _))).
        set_solver.
      + simpl. apply elem_of_disjoint. intros c Hc Hcq.
        apply elem_of_union in Hc as [Hc|Hc].
        * pose proof (ok_CΓ _ _ _ Hok h q (in_here _ _) (in_there _ _ _ (in_there _ _ _ Hq))) as H1.
          pose proof (ok_CΓ _ _ _ Hok r q (in_there _ _ _ (in_here _ _)) (in_there _ _ _ (in_there _ _ _ Hq))) as H2.
          clear -Hc Hcq H1 H2. set_solver.
        * apply elem_of_dom in Hcq as [? Hcq]. by rewrite (Cc_not_rest c q Hc Hq) in Hcq.
      + pose proof (ok_CΓ _ _ _ Hok p h (in_there _ _ _ (in_there _ _ _ Hp)) (in_here _ _)) as H1.
        pose proof (ok_CΓ _ _ _ Hok p r (in_there _ _ _ (in_there _ _ _ Hp)) (in_there _ _ _ (in_here _ _))) as H2.
        clear -Hdm H1 H2. set_solver.
      + apply (ok_CΓ _ _ _ Hok); set_solver.
  Qed.

  Lemma merged_typed T :
    strict W → prim T →
    sem_ptyped W (cΓ h) (cC h, cE h) T → sem_ptyped W (cΓ r) (cC r, cE r) TUnit →
    sem_ptyped W (cΓ merged) (cC merged, cE merged) T.
  Proof.
    intros HW HT Hh Hr.
    assert (strict (wjoin W W)) as HWW by (by apply wjoin_sub_strict, wext_refl).
    pose proof (ok_CΓ _ _ _ Hok h h (in_here _ _) (in_here _ _)) as Hhh.
    pose proof (ok_CΓ _ _ _ Hok h r (in_here _ _) (in_there _ _ _ (in_here _ _))) as Hhr.
    pose proof (ok_CΓ _ _ _ Hok r h (in_there _ _ _ (in_here _ _)) (in_here _ _)) as Hrh.
    pose proof (ok_CΓ _ _ _ Hok r r (in_there _ _ _ (in_here _ _)) (in_there _ _ _ (in_here _ _))) as Hrr.
    assert (cC h ## cC r) as Hhr'.
    { apply elem_of_disjoint. intros c Hc1 Hc2. pose proof (ok_C _ _ _ Hok c) as Hl.
      rewrite !length_filter_cons in Hl. rewrite !decide_True in Hl by done. lia. }
    intros n. eapply Prel_mono; [apply HWW|by apply wext_join_self'|].
    revert n.
    apply (Prel_connect W W (cut_out Cc (cΓ h)) (cut_out Cc (cΓ r))
             (cut_in Cc (cΓ h)) (cut_in Cc (cΓ r)) Cc (cC h) (cC r) (cE h) (cE r) T).
    - done.
    - by rewrite cut_split.
    - by rewrite cut_split.
    - rewrite dom_cut_in. unfold Cc. set_solver.
    - rewrite dom_cut_in. unfold Cc. set_solver.
    - intros c e e' He He'. rewrite lookup_cut_in in He, He'.
      case_decide as Hc; [|done].
      destruct (Cc_ends c Hc) as (e0 & e0' & H1 & H2 & _ & Heq & Hd).
      simplify_eq. split; [by apply wjoin_l|done].
    - rewrite dom_cut_out. clear -Hhr. set_solver.
    - rewrite dom_cut_out. clear -Hrh. set_solver.
    - done.
    - apply HW.
    - apply HW.
    - apply map_disjoint_spec. intros c ? ? H1 H2.
      rewrite lookup_cut_out in H1. rewrite lookup_cut_in in H2. case_decide; congruence.
    - apply map_disjoint_spec. intros c ? ? H1 H2.
      rewrite lookup_cut_out in H1. rewrite lookup_cut_in in H2. case_decide; congruence.
    - apply map_disjoint_spec. intros c ? ? H1 H2.
      rewrite lookup_cut_out in H1, H2. case_decide; [done|].
      apply H. unfold Cc. apply elem_of_intersection. split; apply elem_of_dom; eauto.
    - rewrite dom_cut_out. clear -Hhh. set_solver.
    - rewrite dom_cut_out. clear -Hrr. set_solver.
    - unfold Cc. clear -Hhh. set_solver.
    - unfold Cc. clear -Hrr. set_solver.
    - done.
  Qed.

  Lemma merged_iface :
    cut_out (C0 ∖ Cc) (munion cΓ (merged :: rs)) = cut_out C0 (munion cΓ (h :: r :: rs)).
  Proof.
    apply map_eq. intros c. rewrite !lookup_cut_out, !lookup_munion.
    fold (ends c (merged :: rs)). fold (ends c (h :: r :: rs)).
    pose proof Cc_sub as Hsub.
    destruct (decide (c ∈ Cc)) as [Hin|Hout].
    - rewrite ends_merged_in by done.
      rewrite decide_False by set_solver. rewrite decide_True by set_solver. done.
    - rewrite ends_merged_out by done.
      destruct (decide (c ∈ C0)); repeat case_decide; set_solver.
  Qed.
End merge.

(** ** P-Connect over a list, at one world *)

Lemma Prel_connect_list W T rs : ∀ C0 h,
  strict W → prim T →
  sem_ptyped W (cΓ h) (cC h, cE h) T →
  Forall (λ p, sem_ptyped W (cΓ p) (cC p, cE p) TUnit) rs →
  conn_ok W C0 (h :: rs) →
  sem_ptyped W (cut_out C0 (munion cΓ (h :: rs)))
    (cunion cC (h :: rs) ∪ C0, eunion cE (h :: rs)) T.
Proof.
  induction rs as [|r rs IH]; intros C0 h HW HT Hh Hrs Hok.
  - assert (C0 = ∅) as ->.
    { apply set_eq. intros c. split; [|set_solver]. intros Hc.
      destruct (ok_cut _ _ _ Hok c Hc) as (e & e' & Hends & _).
      rewrite ends_cons in Hends. destruct (cΓ h !! c); done. }
    assert (cut_out ∅ (munion cΓ [h]) = cΓ h) as ->.
    { apply map_eq. intros c. rewrite lookup_cut_out, decide_False by set_solver.
      rewrite lookup_munion. simpl. by destruct (cΓ h !! c). }
    rewrite !cunion_cons, !eunion_cons. cbn [cunion eunion foldr].
    rewrite !union_empty_r_L, gmultiset_disj_union_right_id. done.
  - inversion Hrs as [|? ? Hr Hrs']; subst.
    pose proof (merged_typed W C0 h r rs Hok T HW HT Hh Hr) as Hm.
    pose proof (IH (C0 ∖ Cc h r) (merged h r) HW HT Hm Hrs' (merged_ok W C0 h r rs Hok)) as H.
    rewrite (merged_iface W C0 h r rs Hok) in H.
    assert (cunion cC (merged h r :: rs) ∪ C0 ∖ Cc h r = cunion cC (h :: r :: rs) ∪ C0) as E1.
    { pose proof (Cc_sub W C0 h r rs Hok). rewrite !cunion_cons. cbn [cC merged].
      apply set_eq. intros c.
      destruct (decide (c ∈ Cc h r)); set_solver. }
    assert (eunion cE (merged h r :: rs) = eunion cE (h :: r :: rs)) as E2.
    { rewrite !eunion_cons. cbn [cE merged]. by rewrite gmultiset_disj_union_assoc. }
    rewrite E1, E2 in H. exact H.
Qed.

(** ** The spec form: interface and cut ends apart, one world per component *)

Record compn := CompN { nΣ : senv; nΣC : senv; nC : gset chan; nE : gmultiset expr; nW : world }.

(** W₁ ⊔ … ⊔ Wₙ *)
Definition wjoins (ws : list world) : world :=
  wgen (⋃ (w_names <$> ws)) (λ x y, ∃ W, W ∈ ws ∧ w_eq W x y)
    (λ x y, ∃ W, W ∈ ws ∧ w_lt W x y).

Lemma wext_wjoins W ws : W ∈ ws → strict (wjoins ws) → wext W (wjoins ws).
Proof.
  intros HW Hs. split_and!; [|..|done].
  - intros p Hp. simpl. apply elem_of_union_list. exists (w_names W).
    split; [|done]. by apply list_elem_of_fmap_2.
  - intros x y H. apply geq_base. eauto.
  - intros x y H. apply glt_base. eauto.
Qed.

Definition to_comp (p : compn) : comp := Comp (nΣ p ∪ nΣC p) (nC p) (nE p).

Lemma cunion_map ps : cunion cC (to_comp <$> ps) = cunion nC ps.
Proof. induction ps; [done|]. rewrite fmap_cons, !cunion_cons. simpl. congruence. Qed.
Lemma eunion_map ps : eunion cE (to_comp <$> ps) = eunion nE ps.
Proof. induction ps; [done|]. rewrite fmap_cons, !eunion_cons. simpl. congruence. Qed.

Lemma filter_to_comp c (l : list compn) :
  length (filter (λ q, c ∈ cC q) (to_comp <$> l)) = length (filter (λ q, c ∈ nC q) l).
Proof.
  induction l as [|p l IH]; [done|]. rewrite fmap_cons, !length_filter_cons, IH.
  simpl. done.
Qed.

Theorem Prel_connect_n T C0 h rs :
  let ps := h :: rs in
  let Wall := wjoins (nW <$> ps) in
  prim T →
  sem_ptyped (nW h) (nΣ h ∪ nΣC h) (nC h, nE h) T →
  Forall (λ p, sem_ptyped (nW p) (nΣ p ∪ nΣC p) (nC p, nE p) TUnit) rs →
  (∀ c, c ∈ C0 → ∃ e e', omap (λ p, nΣC p !! c) ps = [e; e'] ∧
     w_eq Wall e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  (∀ p, p ∈ ps → dom (nΣC p) ⊆ C0 ∧ dom (nΣ p) ## C0) →
  (∀ c, length (omap (λ p, nΣ p !! c) ps) ≤ 1) →
  (∀ c, length (filter (λ p, c ∈ nC p) ps) ≤ 1) →
  (∀ p, p ∈ ps → nC p ## C0) →
  (∀ p q, p ∈ ps → q ∈ ps → nC p ## dom (nΣ q)) →
  strict Wall → (∀ p, p ∈ ps → world_wf (nW p)) →
  sem_ptyped Wall (munion nΣ ps) (cunion nC ps ∪ C0, eunion nE ps) T.
Proof.
  intros ps Wall HT Hh Hrs Hcut Hdom HΣ HC HC0 HCΣ HW Hwf.
  assert (∀ p c, p ∈ ps → c ∈ C0 → nΣ p !! c = None) as HΣC0.
  { intros p c Hp Hc. apply not_elem_of_dom. destruct (Hdom p Hp). set_solver. }
  assert (∀ p c, p ∈ ps → c ∉ C0 → nΣC p !! c = None) as HCC0.
  { intros p c Hp Hc. apply not_elem_of_dom. destruct (Hdom p Hp). set_solver. }
  assert (∀ c, ends c (to_comp <$> ps) = omap (λ p, (nΣ p ∪ nΣC p) !! c) ps) as Hends.
  { intros c. unfold ends. rewrite omap_fmap'. done. }
  assert (∀ p, p ∈ ps → wext (nW p) Wall) as Hext.
  { intros p Hp. apply wext_wjoins; [|done]. by apply list_elem_of_fmap_2. }
  pose proof (Prel_connect_list Wall T (to_comp <$> rs) C0 (to_comp h) HW HT) as H.
  assert (munion nΣ ps = cut_out C0 (munion cΓ (to_comp <$> ps))) as EΣ.
  { apply map_eq. intros c. rewrite lookup_cut_out, !lookup_munion.
    rewrite omap_fmap'. simpl (cΓ (to_comp _)). case_decide as Hc.
    - destruct (omap (λ p, nΣ p !! c) ps) as [|s l] eqn:E; [done|exfalso].
      assert (s ∈ omap (λ p, nΣ p !! c) ps) as Hs by (rewrite E; set_solver).
      apply list_elem_of_omap in Hs as (p & Hp & Hps). by rewrite HΣC0 in Hps.
    - f_equal. apply omap_ext_in. intros p Hp. rewrite lookup_union, (HCC0 p c Hp Hc).
      by destruct (nΣ p !! c). }
  rewrite EΣ, <-cunion_map, <-eunion_map. apply H.
  - intros n. eapply Prel_mono; [apply (Hwf h), in_here|apply Hext, in_here|]. apply Hh.
  - apply Forall_fmap, Forall_forall. intros p Hp n. simpl.
    apply list_elem_of_In in Hp as Hp'.
    eapply Prel_mono; [apply (Hwf p), in_there, Hp'|apply Hext, in_there, Hp'|].
    by apply (proj1 (Forall_forall _ _) Hrs p Hp).
  - change (to_comp h :: (to_comp <$> rs)) with (to_comp <$> ps). split.
    + intros c Hc. rewrite (Hends c). destruct (Hcut c Hc) as (e & e' & E & ?).
      exists e, e'. split; [|done]. rewrite <-E. apply omap_ext_in. intros p Hp.
      rewrite lookup_union, (HΣC0 p c Hp Hc). by destruct (nΣC p !! c).
    + intros c Hc. rewrite (Hends c).
      erewrite omap_ext_in; [apply (HΣ c)|]. intros p Hp.
      rewrite lookup_union, (HCC0 p c Hp Hc). by destruct (nΣ p !! c).
    + intros c. rewrite filter_to_comp. apply HC.
    + intros p Hp. apply list_elem_of_fmap in Hp as (p' & -> & Hp'). by apply HC0.
    + intros p q Hp Hq. apply list_elem_of_fmap in Hp as (p' & -> & Hp').
      apply list_elem_of_fmap in Hq as (q' & -> & Hq'). simpl.
      rewrite dom_union_L. pose proof (HCΣ p' q' Hp' Hq') as K1. pose proof (HC0 p' Hp') as K2.
      destruct (Hdom q' Hq') as [K3 _]. apply disjoint_union_r. split; [done|].
      apply elem_of_disjoint. intros x Hx1 Hx2. apply K3 in Hx2.
      exact (proj1 (elem_of_disjoint _ _) K2 x Hx1 Hx2).
Qed.
