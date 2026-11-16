(** * Composition of the lock-free judgment (lock-freedom plan §17.4)

    [LFP_term] is P-Term for [LFP]. The live part is [LPrel_term]. The
    soup has one thread, thread 0, whose environment is the one of the
    typing, [tenv_of Σ ∪ ΘB]. Its points are a map π on exactly the
    ends of that environment, and its counters start full ([fsem]).

    [LFP_connect] is P-Connect for [LFP], and [LFP_join] P-Join. The
    live part is [LPrel_connect]. The two configurations join with the
    threads of the left one at even ids and those of the right one at odd
    ids ([mcat]), and the environments, points and counters join by
    thread ([tsel]). The point map takes the ends held on the right from
    the right ([mrem] of [held]). FuelE moves from W1 and W2 to the joined
    world by [FuelE_wbext], which asks that W1 and W2 agree on budgets at
    the names they share. An end of a cut channel finds its partner on
    the other side through [lf_sig] and [lf_own]. *)

From stdpp Require Import base gmap gmultiset.
From LRGV Require Export lockfree.LFSoup.
From LRGV Require Import lockfree.LFFuel liveness.LivePConnect.

Set Default Proof Using "Type".

Lemma soup_singleton_map (t : expr) : soup {[0 := t]} = {[+ t +]}.
Proof.
  rewrite <-insert_empty, soup_insert by apply lookup_empty.
  by rewrite soup_empty, (left_id_L ∅ (⊎)).
Qed.

(** P-Term (§11) for the lock-free judgment. Over [LPrel_term] it asks
    the points π of the held ends and full counters at them. *)
Theorem LFP_term (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr) (T : ty)
    (π : gmap cend point) :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  lsem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  dom π = tenv_ends (tenv_of Σ ∪ ΘB) →
  (∀ o x, tenv_end (tenv_of Σ ∪ ΘB) o = Some x → π !! o = Some x.2) →
  fsem W π t →
  LFP W Σ T (C0, {[+ t +]}).
Proof.
  intros HT HW Hd Hdj Hb Hdu Ht Hdπ Hπ Hf. split.
  { by apply (LPrel_term W Σ ΘB C0 t T). }
  set (Θ := tenv_of Σ ∪ ΘB).
  (* a channel of Θ is a channel of Σ, with one entry, or of ΘB, with two *)
  assert (HΘ : ∀ c, Θ !! c = (One <$> Σ !! c) ∨ (Σ !! c = None ∧ Θ !! c = ΘB !! c)).
  { intros c. unfold Θ. rewrite lookup_union, lookup_tenv_of.
    destruct (Σ !! c) eqn:Hs; simpl.
    - left. assert (ΘB !! c = None) as ->; [|done].
      apply not_elem_of_dom. rewrite Hd. intros Hc. apply (Hdj c); [|done].
      by apply elem_of_dom.
    - right. split; [done|]. by destruct (ΘB !! c). }
  assert (Hbip : tenv_bipol Θ).
  { intros c e1 e2 Hc. destruct (HΘ c) as [H|[_ H]]; rewrite H in Hc.
    - by destruct (Σ !! c).
    - destruct (Hdu c e1 e2 Hc) as [He _]. rewrite He, pt_pol_dual. by destruct (pt_pol e2.2). }
  exists (C0, {[0 := t]}), π, (λ _, π), (λ _, w_bud W <$> π). split.
  { unfold erase. simpl. by rewrite soup_singleton_map. }
  intros n. exists (λ _, Θ), (λ _, T). simpl. split; [split|]; simpl.
  - done.
  - intros s e Hs. apply lookup_singleton_Some in Hs as [_ <-].
    pose proof (Ht n W ∅ _ Var (wext_refl W HW) (tenv_comp_empty_r _ _) eq_refl) as H.
    by rewrite subst_ids in H.
  - done.
  - by left.
  - intros s e o x _ Hx. by apply Hπ.
  - intros s s' e e' Hne Hs Hs'.
    apply lookup_singleton_Some in Hs as [<- _]. apply lookup_singleton_Some in Hs' as [<- _].
    done.
  - intros s e o x Hs Hx Ho. exists 0, t.
    destruct o as [c b]. simpl in Ho.
    assert (Σ !! c = None) as HΣ by (by apply not_elem_of_dom).
    unfold tenv_end in Hx |- *. simpl in Hx |- *.
    destruct (HΘ c) as [H|[_ H]]; rewrite H in Hx |- *; [by rewrite HΣ in Hx|].
    destruct (ΘB !! c) as [oc|] eqn:Hc; [|done].
    destruct (Hb c oc Hc) as (e1 & e2 & ->).
    destruct (Hdu c e1 e2 Hc) as [He Hs12].
    assert (pt_pol e1.2 ≠ pt_pol e2.2) as Hp
      by (rewrite He, pt_pol_dual; by destruct (pt_pol e2.2)).
    rewrite lookup_singleton_eq. unfold cdual. simpl.
    case_bool_decide as H1.
    + injection Hx as <-. subst b. exists e2.
      rewrite (bool_decide_false (pt_pol e1.2 = negb (pt_pol e1.2)))
        by (by destruct (pt_pol e1.2)).
      rewrite bool_decide_true by (destruct (pt_pol e1.2), (pt_pol e2.2); done).
      split_and!; try done. by apply eq_dual_sym.
    + case_bool_decide as H2; [|done]. injection Hx as <-. subst b.
      exists e1. rewrite bool_decide_true by (destruct (pt_pol e1.2), (pt_pol e2.2); done).
      split_and!; try done. by apply sdual_sym.
  - intros s e _. unfold Θ. rewrite dom_union_L. unfold tenv_of. rewrite dom_fmap_L, Hd.
    set_solver.
  - intros s e [c b] x _ Hx Ho. simpl in Ho |- *. apply elem_of_dom in Ho as [y Hy].
    unfold tenv_end in Hx. simpl in Hx.
    destruct (HΘ c) as [H|[H _]]; [|congruence]. rewrite H, Hy in Hx. simpl in Hx.
    case_bool_decide; congruence.
  - intros c x Hx. exists 0, t. split; [by rewrite lookup_singleton_eq|].
    unfold tenv_end. simpl. destruct (HΘ c) as [H|[H _]]; [|congruence].
    rewrite H, Hx. simpl. by rewrite bool_decide_true.
  - intros s e Hs. simpl in Hs. apply lookup_singleton_Some in Hs as [_ <-].
    split_and!; [by apply fsem_FuelE|done|by rewrite dom_fmap_L|done].
Qed.

(** ** Joining two configurations *)

Definition lthr (t : nat) : nat := 2 * t.
Definition rthr (t : nat) : nat := 2 * t + 1.

Global Instance lthr_inj : Inj eq eq lthr.
Proof. intros a b H. unfold lthr in H. lia. Qed.
Global Instance rthr_inj : Inj eq eq rthr.
Proof. intros a b H. unfold rthr in H. lia. Qed.

Lemma lthr_rthr a b : lthr a ≠ rthr b.
Proof. unfold lthr, rthr. lia. Qed.

Lemma thr_cases t : (∃ a, t = lthr a) ∨ (∃ b, t = rthr b).
Proof.
  destruct (Nat.Even_or_Odd t) as [[a ->]|[b ->]]; [left|right]; exists a || exists b; done.
Qed.

Definition mcat (M1 M2 : gmap nat expr) : gmap nat expr := kmap lthr M1 ∪ kmap rthr M2.

Lemma mcat_l M1 M2 a : mcat M1 M2 !! lthr a = M1 !! a.
Proof.
  unfold mcat. rewrite lookup_union, lookup_kmap.
  assert (kmap rthr M2 !! lthr a = None) as ->.
  { apply lookup_kmap_None. all: try (intros b Hb; exfalso; exact (lthr_rthr a b Hb)). all: apply _. }
  destruct (M1 !! a); simpl; try done. all: apply _.
Qed.

Lemma mcat_r M1 M2 b : mcat M1 M2 !! rthr b = M2 !! b.
Proof.
  unfold mcat. rewrite lookup_union, lookup_kmap.
  assert (kmap lthr M1 !! rthr b = None) as ->.
  { apply lookup_kmap_None. all: try (intros a Ha; exfalso; exact (lthr_rthr a b (eq_sym Ha))). all: apply _. }
  destruct (M2 !! b); simpl; try done. all: apply _.
Qed.

Lemma mcat_lookup M1 M2 t e :
  mcat M1 M2 !! t = Some e →
  (∃ a, t = lthr a ∧ M1 !! a = Some e) ∨ (∃ b, t = rthr b ∧ M2 !! b = Some e).
Proof.
  intros H. destruct (thr_cases t) as [[a ->]|[b ->]]; [left|right]; eexists; (split; [done|]).
  - by rewrite mcat_l in H.
  - by rewrite mcat_r in H.
Qed.

Lemma soup_kmap (f : nat → nat) `{!Inj eq eq f} (M : gmap nat expr) : soup (kmap f M) = soup M.
Proof.
  induction M as [|i e M Hi IH] using map_ind.
  - by rewrite kmap_empty, !soup_empty.
  - rewrite kmap_insert. rewrite (soup_insert (kmap f M)) by (by rewrite lookup_kmap).
    rewrite (soup_insert M) by done. rewrite IH. all: try done. all: apply _.
Qed.

Lemma soup_union (M1 M2 : gmap nat expr) : M1 ##ₘ M2 → soup (M1 ∪ M2) = soup M1 ⊎ soup M2.
Proof.
  revert M2. induction M1 as [|i e M1 Hi IH] using map_ind; intros M2 Hd.
  - by rewrite (left_id_L ∅ (∪)), soup_empty, (left_id_L ∅ (⊎)).
  - apply map_disjoint_insert_l in Hd as [Hi2 Hd].
    rewrite <-insert_union_l.
    rewrite soup_insert by (by apply lookup_union_None).
    rewrite (soup_insert M1) by done. rewrite IH by done. multiset_solver.
Qed.

Lemma mcat_soup M1 M2 : soup (mcat M1 M2) = soup M1 ⊎ soup M2.
Proof.
  unfold mcat. rewrite soup_union, (soup_kmap lthr), (soup_kmap rthr); [done|].
  apply map_disjoint_spec. intros i x y Hx Hy.
  apply lookup_kmap_Some in Hx as (a & -> & _); [|apply _].
  apply lookup_kmap_Some in Hy as (b & Hab & _); [|apply _]. by apply (lthr_rthr a b).
Qed.

Definition tsel {X : Type} (f g : nat → X) (t : nat) : X :=
  if Nat.even t then f (Nat.div2 t) else g (Nat.div2 t).

Lemma tsel_l {X : Type} (f g : nat → X) a : tsel f g (lthr a) = f a.
Proof.
  unfold tsel, lthr. rewrite Nat.even_mul, Nat.div2_double. reflexivity.
Qed.

Lemma tsel_r {X : Type} (f g : nat → X) b : tsel f g (rthr b) = g b.
Proof.
  unfold tsel, rthr. rewrite Nat.add_1_r, Nat.even_succ, Nat.odd_mul, Nat.div2_succ_double.
  reflexivity.
Qed.

(** The ends held by the threads of M, read off their point maps. *)
Definition held (M : gmap nat expr) (P : nat → gmap cend point) : gset cend :=
  ⋃ ((λ a, dom (P a)) <$> elements (dom M)).

Lemma elem_of_held M P o : o ∈ held M P ↔ ∃ a e, M !! a = Some e ∧ o ∈ dom (P a).
Proof.
  unfold held. rewrite elem_of_union_list. split.
  - intros (X & HX & Ho). apply list_elem_of_fmap in HX as (a & -> & Ha).
    apply elem_of_elements, elem_of_dom in Ha as [e He]. eauto.
  - intros (a & e & He & Ho). exists (dom (P a)). split; [|done].
    apply list_elem_of_fmap. exists a. split; [done|].
    apply elem_of_elements, elem_of_dom. eauto.
Qed.

Lemma pcat_l (X : gset cend) (π1 π2 : gmap cend point) o v :
  π1 !! o = Some v → o ∉ X → (mrem X π1 ∪ π2) !! o = Some v.
Proof.
  intros H Ho. rewrite lookup_union, lookup_mrem, decide_False by done. rewrite H.
  by destruct (π2 !! o).
Qed.

Lemma pcat_r (X : gset cend) (π1 π2 : gmap cend point) o :
  o ∈ X → (mrem X π1 ∪ π2) !! o = π2 !! o.
Proof.
  intros Ho. rewrite lookup_union, lookup_mrem, decide_True by done. by destruct (π2 !! o).
Qed.

Lemma ulook_l (m1 m2 : senv) c x : m1 !! c = Some x → (m1 ∪ m2) !! c = Some x.
Proof. intros H. rewrite lookup_union, H. by destruct (m2 !! c). Qed.

Lemma ulook_r (m1 m2 : senv) c : m1 !! c = None → (m1 ∪ m2) !! c = m2 !! c.
Proof. intros H. rewrite lookup_union, H. by destruct (m2 !! c). Qed.

(** W1 and W2 agree on budgets and floors at the names they share. *)
Definition wbud_agree (W1 W2 : world) : Prop :=
  ∀ x, pt_root x ∈ w_names W1 → pt_root x ∈ w_names W2 →
    w_bud W1 x = w_bud W2 x ∧ w_pay W1 x = w_pay W2 x.

Lemma wbext_join_l W1 W2 : wbext W1 (wjoin W1 W2).
Proof. split; [simpl; set_solver|apply wext_bud_join_l]. Qed.

Lemma wbext_join_r W1 W2 : wbud_agree W1 W2 → wbext W2 (wjoin W1 W2).
Proof.
  intros Hag. split; [simpl; set_solver|].
  intros x Hx. unfold pt_known in Hx. unfold wjoin, wjoin_bud. simpl.
  case_decide as H1; [|done]. destruct (Hag x H1 Hx) as [-> ->]. done.
Qed.

(** P-Connect (§11) for the lock-free judgment. Over [LPrel_connect] it
    asks that W1 and W2 agree on budgets at the names they share. *)
Theorem LFP_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  prim T →
  LFP W1 (Σ1 ∪ ΣC) T (C1, E1) → LFP W2 (Σ2 ∪ ΣC') TUnit (C2, E2) →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  strict (wjoin W1 W2) → world_wf W1 → world_wf W2 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  wbud_agree W1 W2 →
  LFP (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Proof.
  intros HT [HL1 (q1 & π1 & P1 & F1 & Hq1 & HS1)] [HL2 (q2 & π2 & P2 & F2 & Hq2 & HS2)]
    HC0 HC0' Hcut HC1Σ2 HC2Σ1 HW HW1 HW2 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 Hag.
  split.
  { by apply (LPrel_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T). }
  destruct q1 as [C1' M1], q2 as [C2' M2]. unfold erase in Hq1, Hq2. simpl in Hq1, Hq2.
  injection Hq1 as -> HM1. injection Hq2 as -> HM2.
  (* the channels *)
  pose proof (map_disjoint_dom_1 _ _ Hd1) as Hd1'. pose proof (map_disjoint_dom_1 _ _ Hd2) as Hd2'.
  pose proof (map_disjoint_dom_1 _ _ Hd12) as Hd12'.
  rewrite HC0 in Hd1'. rewrite HC0' in Hd2'.
  assert (HΣ1C : dom (Σ1 ∪ ΣC) = dom Σ1 ∪ C0) by (by rewrite dom_union_L, HC0).
  assert (HΣ2C : dom (Σ2 ∪ ΣC') = dom Σ2 ∪ C0) by (by rewrite dom_union_L, HC0').
  set (π := mrem (held M2 P2) π1 ∪ π2).
  exists (C1 ∪ C2 ∪ C0, mcat M1 M2), π, (tsel P1 P2), (tsel F1 F2). split.
  { unfold erase. simpl. by rewrite mcat_soup, HM1, HM2. }
  intros n.
  destruct (HS1 n) as (A1 & U1 & Hc1 & HF1). destruct (HS2 n) as (A2 & U2 & Hc2 & HF2).
  simpl in HF1, HF2.
  (* the cut: a channel of both sides is a channel of C0 *)
  assert (Hcl1 : ∀ a e, M1 !! a = Some e → dom (A1 a) ⊆ C1 ∪ dom Σ1 ∪ C0).
  { intros a e Ha. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc1 a e Ha) as H. simpl in H.
    rewrite HΣ1C in H. set_solver. }
  assert (Hcl2 : ∀ b f, M2 !! b = Some f → dom (A2 b) ⊆ C2 ∪ dom Σ2 ∪ C0).
  { intros b f Hb. pose proof (lf_closed _ _ _ _ _ _ _ _ Hc2 b f Hb) as H. simpl in H.
    rewrite HΣ2C in H. set_solver. }
  (* an end of a cut channel held on the left is at the entry of ΣC *)
  assert (Hsig1 : ∀ a e o x, M1 !! a = Some e → tenv_end (A1 a) o = Some x → o.1 ∈ C0 →
            ΣC !! o.1 = Some x).
  { intros a e o x Ha Hx Ho.
    pose proof (lf_sig _ _ _ _ _ _ _ _ Hc1 a e o x Ha Hx) as H.
    rewrite HΣ1C in H. rewrite ulook_r in H; [set_solver|].
    apply not_elem_of_dom. set_solver. }
  assert (Hsig2 : ∀ b f o x, M2 !! b = Some f → tenv_end (A2 b) o = Some x → o.1 ∈ C0 →
            ΣC' !! o.1 = Some x).
  { intros b f o x Hb Hx Ho.
    pose proof (lf_sig _ _ _ _ _ _ _ _ Hc2 b f o x Hb Hx) as H.
    rewrite HΣ2C in H. rewrite ulook_r in H; [set_solver|].
    apply not_elem_of_dom. set_solver. }
  assert (HLR : ∀ a e b f o, M1 !! a = Some e → M2 !! b = Some f →
            o ∈ tenv_ends (A1 a) → o ∈ tenv_ends (A2 b) → False).
  { intros a e b f o Ha Hb [x Hx]%tenv_ends_end [y Hy]%tenv_ends_end.
    assert (o.1 ∈ C0) as Ho.
    { pose proof (tenv_end_dom _ _ _ Hx). pose proof (tenv_end_dom _ _ _ Hy).
      pose proof (Hcl1 a e Ha). pose proof (Hcl2 b f Hb). set_solver. }
    destruct (Hcut o.1 x y (Hsig1 a e o x Ha Hx Ho) (Hsig2 b f o y Hb Hy Ho)) as [Hxy _].
    pose proof (tenv_end_pol _ _ _ Hx) as Px. pose proof (tenv_end_pol _ _ _ Hy) as Py.
    rewrite Hxy, pt_pol_dual, Py in Px. by destruct o.2. }
  assert (Hheld : ∀ b f o, M2 !! b = Some f → o ∈ tenv_ends (A2 b) → o ∈ held M2 P2).
  { intros b f o Hb Ho. apply elem_of_held. exists b, f. split; [done|].
    by destruct (HF2 b f Hb) as (_ & -> & _). }
  assert (Hnheld : ∀ a e o, M1 !! a = Some e → o ∈ tenv_ends (A1 a) → o ∉ held M2 P2).
  { intros a e o Ha Ho (b & f & Hb & Hob)%elem_of_held.
    destruct (HF2 b f Hb) as (_ & Hd & _). rewrite Hd in Hob. by apply (HLR a e b f o). }
  exists (tsel A1 A2), (tsel U1 U2). split; [split|]; simpl.
  - done.
  - intros t e He. destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r.
    + apply (LErel_mono n W1); [right; by apply wext_join_l'|].
      apply (lf_rel _ _ _ _ _ _ _ _ Hc1 a e Ha).
    + apply (LErel_mono n W2); [right; by apply wext_join_r'|].
      apply (lf_rel _ _ _ _ _ _ _ _ Hc2 b e Hb).
  - intros t e He. destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r.
    + apply (lf_bipol _ _ _ _ _ _ _ _ Hc1 a e Ha).
    + apply (lf_bipol _ _ _ _ _ _ _ _ Hc2 b e Hb).
  - intros t e He. destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r.
    + apply (lf_ty _ _ _ _ _ _ _ _ Hc1 a e Ha).
    + right. by destruct (lf_ty _ _ _ _ _ _ _ _ Hc2 b e Hb).
  - intros t e o x He Hx. destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r in Hx.
    + apply pcat_l; [apply (lf_pt _ _ _ _ _ _ _ _ Hc1 a e o x Ha Hx)|].
      apply (Hnheld a e o Ha). by eapply tenv_end_ends.
    + unfold π. rewrite pcat_r; [apply (lf_pt _ _ _ _ _ _ _ _ Hc2 b e o x Hb Hx)|].
      apply (Hheld b e o Hb). by eapply tenv_end_ends.
  - intros t s e es Hts He Hes.
    destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)],
      (mcat_lookup _ _ _ _ Hes) as [(a' & -> & Ha')|(b' & -> & Hb')];
      rewrite ?tsel_l, ?tsel_r.
    + apply (lf_disj _ _ _ _ _ _ _ _ Hc1 a a' e es); [|done|done]. intros ->. done.
    + intros o H1 H2. by apply (HLR a e b' es o).
    + intros o H1 H2. by apply (HLR a' es b e o).
    + apply (lf_disj _ _ _ _ _ _ _ _ Hc2 b b' e es); [|done|done]. intros ->. done.
  - intros t e o x He Hx Ho. rewrite dom_union_L in Ho.
    destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r in Hx.
    + destruct (decide (o.1 ∈ C0)) as [H0|H0].
      * pose proof (Hsig1 a e o x Ha Hx H0) as Hx1.
        assert (is_Some (ΣC' !! o.1)) as [x' Hx'] by (apply elem_of_dom; by rewrite HC0').
        destruct (Hcut o.1 x x' Hx1 Hx') as [Hxx Hs].
        assert ((Σ2 ∪ ΣC') !! o.1 = Some x') as Hx2.
        { rewrite ulook_r; [done|]. apply not_elem_of_dom. set_solver. }
        destruct (lf_own _ _ _ _ _ _ _ _ Hc2 o.1 x' Hx2) as (b & f & Hb & Hy).
        exists (rthr b), f, x'. rewrite mcat_r, tsel_r.
        assert (cdual o = (o.1, pt_pol x'.2)) as ->.
        { pose proof (tenv_end_pol _ _ _ Hx) as Px. rewrite Hxx, pt_pol_dual in Px.
          unfold cdual. rewrite <-Px. by destruct (pt_pol x'.2). }
        split_and!; [done|done|by apply eq_dual_sym|done].
      * destruct (lf_pair _ _ _ _ _ _ _ _ Hc1 a e o x Ha Hx) as (s & es & y & Hs & Hy & ?);
          [rewrite HΣ1C; set_solver|].
        exists (lthr s), es, y. by rewrite mcat_l, tsel_l.
    + destruct (decide (o.1 ∈ C0)) as [H0|H0].
      * pose proof (Hsig2 b e o x Hb Hx H0) as Hx2.
        assert (is_Some (ΣC !! o.1)) as [x1 Hx1] by (apply elem_of_dom; by rewrite HC0).
        destruct (Hcut o.1 x1 x Hx1 Hx2) as [Hxx Hs].
        assert ((Σ1 ∪ ΣC) !! o.1 = Some x1) as Hx1'.
        { rewrite ulook_r; [done|]. apply not_elem_of_dom. set_solver. }
        destruct (lf_own _ _ _ _ _ _ _ _ Hc1 o.1 x1 Hx1') as (a & f & Ha & Hy).
        exists (lthr a), f, x1. rewrite mcat_l, tsel_l.
        assert (cdual o = (o.1, pt_pol x1.2)) as ->.
        { pose proof (tenv_end_pol _ _ _ Hx) as Px. rewrite Hxx, pt_pol_dual.
          unfold cdual. rewrite <-Px. by destruct (pt_pol x.2). }
        split_and!; [done|done|done|by apply sdual_sym].
      * destruct (lf_pair _ _ _ _ _ _ _ _ Hc2 b e o x Hb Hx) as (s & es & y & Hs & Hy & ?);
          [rewrite HΣ2C; set_solver|].
        exists (rthr s), es, y. by rewrite mcat_r, tsel_r.
  - intros t e He. rewrite dom_union_L.
    destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)]; rewrite ?tsel_l, ?tsel_r.
    + pose proof (Hcl1 a e Ha). set_solver.
    + pose proof (Hcl2 b e Hb). set_solver.
  - intros t e o x He Hx Ho. rewrite dom_union_L in Ho.
    destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r in Hx.
    + assert (o.1 ∈ dom Σ1) as Ho1.
      { pose proof (tenv_end_dom _ _ _ Hx). pose proof (Hcl1 a e Ha). set_solver. }
      apply elem_of_dom in Ho1 as [z Hz].
      assert ((Σ1 ∪ ΣC) !! o.1 = Some x) as H.
      { apply (lf_sig _ _ _ _ _ _ _ _ Hc1 a e o x Ha Hx).
        rewrite HΣ1C. apply elem_of_union_l, elem_of_dom. eauto. }
      rewrite (ulook_l _ _ _ _ Hz) in H. apply ulook_l. congruence.
    + assert (o.1 ∈ dom Σ2 ∧ o.1 ∉ dom Σ1) as [Ho2 Ho1].
      { pose proof (tenv_end_dom _ _ _ Hx). pose proof (Hcl2 b e Hb). set_solver. }
      apply elem_of_dom in Ho2 as [z Hz].
      assert ((Σ2 ∪ ΣC') !! o.1 = Some x) as H.
      { apply (lf_sig _ _ _ _ _ _ _ _ Hc2 b e o x Hb Hx).
        rewrite HΣ2C. apply elem_of_union_l, elem_of_dom. eauto. }
      rewrite (ulook_l _ _ _ _ Hz) in H. rewrite ulook_r by (by apply not_elem_of_dom). congruence.
  - intros c x Hx. destruct (Σ1 !! c) as [z|] eqn:HΣ1c.
    + rewrite (ulook_l _ _ _ _ HΣ1c) in Hx. injection Hx as <-.
      destruct (lf_own _ _ _ _ _ _ _ _ Hc1 c z (ulook_l _ _ _ _ HΣ1c)) as (a & e & Ha & Hy).
      exists (lthr a), e. by rewrite mcat_l, tsel_l.
    + rewrite (ulook_r _ _ _ HΣ1c) in Hx.
      destruct (lf_own _ _ _ _ _ _ _ _ Hc2 c x (ulook_l _ _ _ _ Hx)) as (b & e & Hb & Hy).
      exists (rthr b), e. by rewrite mcat_r, tsel_r.
  - intros t e He. destruct (mcat_lookup _ _ _ _ He) as [(a & -> & Ha)|(b & -> & Hb)];
      rewrite ?tsel_l, ?tsel_r.
    + destruct (HF1 a e Ha) as (Hf & Hp & Hq & Ho). split_and!; [|done|done|].
      * apply (FuelE_wbext n W1); [apply wbext_join_l|done].
      * intros o Hin. rewrite Ho by done.
        assert (is_Some (P1 a !! o)) as [v Hv] by (apply elem_of_dom; by rewrite Hp).
        rewrite Ho in Hv by done. unfold π. rewrite (pcat_l _ _ _ _ v Hv); [done|].
        by apply (Hnheld a e o Ha).
    + destruct (HF2 b e Hb) as (Hf & Hp & Hq & Ho). split_and!; [|done|done|].
      * apply (FuelE_wbext n W2); [by apply wbext_join_r|done].
      * intros o Hin. rewrite Ho by done. unfold π. rewrite pcat_r; [done|].
        by apply (Hheld b e o Hb).
Qed.

(** P-Join for the lock-free judgment, from [LPrel_join]. *)
Corollary LFP_join W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  prim T →
  LFP W1 (Σ1 ∪ ΣC) T (C1, E1) → LFP W2 (Σ2 ∪ ΣC') TUnit (C2, E2) →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  strict W1 → strict W2 →
  strict (wjoin (wrestrict W1 (w_names W1 ∩ w_names W2))
                (wrestrict W2 (w_names W1 ∩ w_names W2))) →
  wbud_agree W1 W2 →
  LFP (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Proof.
  intros HT HP1 HP2 HC0 HC0' Hcut HC1Σ2 HC2Σ1 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 HS1 HS2 HA Hag.
  assert (strict (wjoin W1 W2)) as HJ by (by apply amalgamation).
  eapply LFP_connect; try done; [apply HS1|apply HS2].
Qed.
