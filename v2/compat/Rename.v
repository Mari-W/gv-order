(** * R^κ is invariant under maps of ends injective on the held ends
      (stage S4, decision Q16)

    Let h be a map of ends that is injective on the ends of Θ, with no
    condition elsewhere. Then

      v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧     ⟹  emap h v ∈ V[κ]^W _ n⟦kren h Θ ⊢ T⟧     [Vrel_rename]
      e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F   ⟹  emap h e ∈ E[κ]^W _ n⟦kren h Θ ⊢ T⟧^F   [Erel_rename]

    for every cost table κ. [kren h Θ] renames every end of Θ by h, the
    map [kmap h Θ] of the paper. stdpp's [kmap] asks h injective
    everywhere, and h need not be.

    The proof is a forward simulation that extends h at every choice. A
    step of emap h e sits at the place of a step of e, because emap
    keeps the shape of a term ([act_emap]), and the continuations agree
    up to an extension h' of h ([tstep_emap_back], steps are
    deterministic for a fixed label). A creation of c by the renamed
    term is matched by a creation of a name c'' fresh for Θ and for the
    ends e mentions, with h' sending c''± to c±. A received value w and
    an argument w of a λ are pulled back to emap k w, with k sending the
    channels of w to fresh channels and h' sending them back
    ([fresh_pull]). Every action of a term in E is on a held end,
    because every obligation reads the subject's entry ([Erel_sends]),
    so the ends that h merges and e does not hold are never acted on.
    The transpositions of compat/Swap.v are the special case of an
    involution ([Vrel_swap_rename], [Erel_swap_rename]). *)

From GV Require Export compat.Bind compat.Redex compat.Swap relation.Adequacy.
From GV Require Import fuel.FuelMono.

(** ** Labels under a map of ends *)

Definition smap (g : cend → cend) (σ : slabel) : slabel :=
  match σ with
  | SSend o v => SSend (g o) (emap g v)
  | SRecv o v => SRecv (g o) (emap g v)
  | SClose o => SClose (g o)
  | SSel o i => SSel (g o) i
  | SBra o i => SBra (g o) i
  | SLink os => SLink (set_map g os)
  end.

Definition lmap (g : cend → cend) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LNew ℓ c => LNew ℓ (gch g c)
  | LNewAt κf o c => LNewAt κf (g o) (gch g c)
  | LSpawn v => LSpawn (emap g v)
  | LSess σ => LSess (smap g σ)
  end.

(** g keeps the polarity of the two ends of c. *)
Definition gpol (g : cend → cend) (c : chan) : Prop :=
  g (EPos c) = EPos (gch g c) ∧ g (ENeg c) = ENeg (gch g c).

Definition lnew_ok (g : cend → cend) (α : tlabel) : Prop :=
  match α with LNew _ c | LNewAt _ _ c => gpol g c | _ => True end.

Lemma sends_smap g σ : sends (smap g σ) = set_map g (sends σ).
Proof. destruct σ; simpl; set_solver. Qed.

Lemma emap_ext_on (g h : cend → cend) e : (∀ o, o ∈ fends e → g o = h o) → emap g e = emap h e.
Proof. induction e; simpl; intros H; f_equal; auto; set_solver. Qed.

(** ** Thread steps under a map of ends *)

Lemma head_step_emap g e α e' :
  head_step e α e' → lnew_ok g α → head_step (emap g e) (lmap g α) (emap g e').
Proof.
  destruct 1; simpl; intros Hok; rewrite ?emap_subst1, ?emap_subst2, ?set_map_upair, <-?fends_emap.
  all: try (match type of Hok with gpol _ _ => destruct Hok as [Hp Hn]; rewrite Hp, Hn; constructor end).
  all: try (constructor; by rewrite ?is_val_emap).
  all: try (match goal with |- context [inj_of ?i] => destruct i; constructor end).
Qed.

Lemma tstep_emap g e α e' :
  tstep e α e' → lnew_ok g α → tstep (emap g e) (lmap g α) (emap g e').
Proof.
  induction 1 as [e α e' Hh|f e α e' Hf Hs IH]; intros Hok.
  - apply tstep_head. by apply head_step_emap.
  - rewrite !emap_fill. apply t_act_ctx; [by apply frame_val_emap|by apply IH].
Qed.

Lemma head_step_det e α e1 e2 : head_step e α e1 → head_step e α e2 → e1 = e2.
Proof. intros H1 H2. inversion H1; subst; inversion H2; subst; simplify_eq; done. Qed.

(** Thread steps are deterministic for a fixed label. *)
Lemma tstep_det e α e1 e2 : tstep e α e1 → tstep e α e2 → e1 = e2.
Proof.
  intros H1. revert e2.
  induction H1 as [e α e' Hh|f e α e' Hf Hs IH]; intros e2 H2.
  - apply tstep_inv in H2 as [Hh2|(f & e0 & e0' & Hf & -> & -> & Hs0)].
    + by eapply head_step_det.
    + exfalso. apply (val_no_tstep e0 α e0' Hs0). by eapply head_redex_val.
  - apply tstep_inv in H2 as [Hh2|(f' & e0 & e0' & Hf' & Heq & -> & Hs0)].
    + exfalso. apply (val_no_tstep e α e' Hs). by eapply head_redex_val.
    + assert (¬ is_val e) as Hv1 by (intros Hv; exact (val_no_tstep e α e' Hs Hv)).
      assert (¬ is_val e0) as Hv2 by (intros Hv; exact (val_no_tstep e0 α e0' Hs0 Hv)).
      destruct (fill_frame_inj f f' e e0 Hf Hf' Hv1 Hv2 Heq) as [<- <-].
      f_equal. exact (IH _ Hs0).
Qed.

(** A step of the renamed term comes from the redex of the term. *)
Lemma tstep_emap_act g e α x : tstep (emap g e) α x → ∃ a, act e = Some a ∧ offers (amap g a) α.
Proof.
  intros Hs. destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho). rewrite act_emap in Ha'.
  destruct (act e) as [a|]; [|done]. injection Ha' as <-. eauto.
Qed.

(** The continuation of the renamed term, read off a step of the term. *)
Lemma tstep_emap_back g g' e α x α0 e0 :
  tstep (emap g e) α x → tstep e α0 e0 → lnew_ok g' α0 → lmap g' α0 = α →
  emap g' e = emap g e → x = emap g' e0.
Proof.
  intros H1 H0 Hok Hl He. eapply tstep_det; [exact H1|]. rewrite <-He, <-Hl. by apply tstep_emap.
Qed.

Lemma irred_act e : irred e ↔ act e = None.
Proof.
  split; [|apply act_None_irred]. intros Hi. destruct (act e) as [a|] eqn:Ha; [|done].
  exfalso. destruct (act_offer e a (alabel a) Ha (offers_alabel a)) as [e' He']. by apply (Hi _ _ He').
Qed.

Lemma irred_emap g e : irred (emap g e) ↔ irred e.
Proof. rewrite !irred_act, act_emap. by destruct (act e). Qed.

(** ** Fresh channels and the pull-back

    For a finite set Y of channels and a set X to avoid, kc sends the
    channels of Y injectively to channels outside X, and h' sends them
    back and agrees with h on the channels of X. *)

Lemma fresh_chans (Y X : gset chan) :
  ∃ kc kci : chan → chan, ∀ c, c ∈ Y → (kc c ∉ X) ∧ kci (kc c) = c.
Proof.
  induction Y as [|c Y Hc IH] using set_ind_L.
  - exists id, id. set_solver.
  - destruct IH as (kc & kci & H).
    set (d := fresh (X ∪ (set_map (D:=gset chan) kc Y))).
    assert (d ∉ X ∪ (set_map (D:=gset chan) kc Y)) as Hd by apply is_fresh.
    exists (λ y, if decide (y = c) then d else kc y), (λ z, if decide (z = d) then c else kci z).
    intros y Hy. destruct (decide (y = c)) as [->|Hne].
    + rewrite decide_True by done. set_solver.
    + apply elem_of_union in Hy as [Hy|Hy]; [set_solver|].
      destruct (H y Hy) as [H1 H2]. rewrite decide_False; [done|].
      intros Heq. apply Hd. apply elem_of_union_r, elem_of_map. by exists y.
Qed.

Lemma cmap_compose (f g : chan → chan) o : cmap f (cmap g o) = cmap (f ∘ g) o.
Proof. by destruct o. Qed.

Lemma cmap_id_on (f : chan → chan) o : f (ech o) = ech o → cmap f o = o.
Proof. destruct o; simpl; by intros ->. Qed.

Lemma fresh_pull (h : cend → cend) (Y X : gset chan) :
  ∃ (kc : chan → chan) (h' : cend → cend),
    (∀ c, c ∈ Y → kc c ∉ X) ∧
    (∀ c1 c2, c1 ∈ Y → c2 ∈ Y → kc c1 = kc c2 → c1 = c2) ∧
    (∀ o, ech o ∈ Y → h' (cmap kc o) = o) ∧
    (∀ o, ech o ∈ X → h' o = h o) ∧
    (dcomm h → dcomm h').
Proof.
  destruct (fresh_chans Y X) as (kc & kci & H).
  exists kc, (λ o, if decide (ech o ∈ (set_map (D:=gset chan) kc Y)) then cmap kci o else h o).
  split_and!.
  - intros c Hc. by apply H.
  - intros c1 c2 H1 H2 Heq. rewrite <-(proj2 (H c1 H1)), <-(proj2 (H c2 H2)). by rewrite Heq.
  - intros o Ho. rewrite ech_cmap, decide_True by (apply elem_of_map; by exists (ech o)).
    rewrite cmap_compose. apply cmap_id_on. simpl. by apply H.
  - intros o Ho. rewrite decide_False; [done|]. intros (c & Hc & Hc')%elem_of_map.
    apply (proj1 (H c Hc')). by rewrite <-Hc.
  - intros Hd o. rewrite ech_edual. case_decide; [apply cmap_edual|apply Hd].
Qed.

(** ** Renamed environments *)

Section kren.
  Implicit Types (h g : cend → cend) (Θ : senv).

  Lemma kren_lookup_inv h Θ o' v : kren h Θ !! o' = Some v → ∃ o, o' = h o ∧ Θ !! o = Some v.
  Proof.
    intros H. apply elem_of_list_to_map_2 in H.
    apply list_elem_of_fmap in H as ([o v'] & Heq & Hin). simpl in Heq. simplify_eq.
    apply elem_of_map_to_list in Hin. eauto.
  Qed.

  Lemma kren_lookup h Θ o v : kinj h Θ → Θ !! o = Some v → kren h Θ !! h o = Some v.
  Proof.
    intros Hk Ho. apply elem_of_list_to_map_1.
    - assert (((λ p : cend * (sty * point), (h p.1, p.2)) <$> map_to_list Θ).*1 =
              h <$> (map_to_list Θ).*1) as ->.
      { rewrite <-!list_fmap_compose. by apply list_fmap_ext. }
      apply NoDup_fmap_2_strong; [|apply NoDup_fst_map_to_list].
      intros o1 o2 (p1 & -> & Hp1)%list_elem_of_fmap (p2 & -> & Hp2)%list_elem_of_fmap Heq.
      destruct p1 as [o1 v1], p2 as [o2 v2]. apply elem_of_map_to_list in Hp1, Hp2.
      exact (Hk o1 o2 v1 v2 Hp1 Hp2 Heq).
    - apply list_elem_of_fmap. exists (o, v). split; [done|]. by apply elem_of_map_to_list.
  Qed.

  Lemma kren_renk h Θ : kinj h Θ → renk h Θ (kren h Θ).
  Proof.
    intros Hk. split; [intros; by apply kren_lookup|]. intros o' v H. by apply kren_lookup_inv.
  Qed.

  Lemma renk_kren h Θ Θ' : kinj h Θ → renk h Θ Θ' → kren h Θ = Θ'.
  Proof.
    intros Hk [A B]. apply map_eq. intros o'. destruct (kren h Θ !! o') eqn:E.
    - destruct (kren_lookup_inv _ _ _ _ E) as (o & -> & Ho). symmetry. by apply A.
    - destruct (Θ' !! o') eqn:E'; [|done]. destruct (B _ _ E') as (o & -> & Ho).
      by rewrite (kren_lookup h Θ o _ Hk Ho) in E.
  Qed.

  Lemma kren_lookup_held h Θ o v : kinj h Θ → o ∈ dom Θ → kren h Θ !! h o = Some v → Θ !! o = Some v.
  Proof.
    intros Hk [w Hw]%elem_of_dom H. destruct (kren_lookup_inv _ _ _ _ H) as (o1 & Heq & Ho1).
    rewrite <-(Hk o1 o v w Ho1 Hw (eq_sym Heq)). exact Ho1.
  Qed.

  Lemma kinj_sub h Θ Θ1 : dom Θ1 ⊆ dom Θ → kinj h Θ → kinj h Θ1.
  Proof. apply kinj_dom. Qed.

  Lemma kinj_empty h : kinj h (∅ : senv).
  Proof. intros ? ? ? ? H. by rewrite lookup_empty in H. Qed.

  Lemma kren_singleton h o v : kren h {[o := v]} = {[h o := v]}.
  Proof.
    assert (kinj h {[o := v]}) as Hk.
    { intros o1 o2 v1 v2 H1 H2 _. apply lookup_singleton_Some in H1 as [-> _].
      by apply lookup_singleton_Some in H2 as [-> _]. }
    apply renk_kren; [done|]. split.
    - intros o1 v1 (-> & ->)%lookup_singleton_Some. by rewrite lookup_singleton_eq.
    - intros o' v' (<- & ->)%lookup_singleton_Some. exists o. by rewrite lookup_singleton_eq.
  Qed.

  Lemma kren_insert h Θ o v : kinj h (<[o := v]> Θ) → kren h (<[o := v]> Θ) = <[h o := v]> (kren h Θ).
  Proof.
    intros Hk. assert (kinj h Θ) as Hk'.
    { intros o1 o2 v1 v2 H1 H2 Heq.
      destruct (decide (o1 = o)) as [->|N1]; destruct (decide (o2 = o)) as [->|N2]; [done| | |].
      - apply (Hk o o2 v v2); [by rewrite lookup_insert_eq|by rewrite lookup_insert_ne|done].
      - apply (Hk o1 o v1 v); [by rewrite lookup_insert_ne|by rewrite lookup_insert_eq|done].
      - apply (Hk o1 o2 v1 v2); [by rewrite lookup_insert_ne|by rewrite lookup_insert_ne|done]. }
    apply renk_kren; [done|]. split.
    - intros o1 v1 Ho1. destruct (decide (o1 = o)) as [->|Hne].
      + rewrite lookup_insert_eq in Ho1. simplify_eq. by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne in Ho1 by done. rewrite lookup_insert_ne; [by apply kren_lookup|].
        intros Heq. apply Hne. apply (Hk o1 o v1 v); [by rewrite lookup_insert_ne|by rewrite lookup_insert_eq|done].
    - intros o' v' Ho'. destruct (decide (h o = o')) as [<-|Hne].
      + rewrite lookup_insert_eq in Ho'. simplify_eq. exists o. by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne in Ho' by done. destruct (kren_lookup_inv _ _ _ _ Ho') as (o1 & -> & Ho1).
        exists o1. split; [done|]. rewrite lookup_insert_ne; [done|]. by intros ->.
  Qed.

  Lemma kren_delete h Θ o : kinj h Θ → o ∈ dom Θ → kren h (delete o Θ) = delete (h o) (kren h Θ).
  Proof.
    intros Hk [w Ho]%elem_of_dom.
    assert (kinj h (delete o Θ)) as Hk' by (apply (kinj_sub _ Θ); [set_solver|done]).
    apply renk_kren; [done|]. split.
    - intros o1 v1 (Hne & Ho1)%lookup_delete_Some. rewrite lookup_delete_ne; [by apply kren_lookup|].
      intros Heq. apply Hne. exact (Hk o o1 w v1 Ho Ho1 Heq).
    - intros o' v' (Hne & Ho')%lookup_delete_Some. destruct (kren_lookup_inv _ _ _ _ Ho') as (o1 & -> & Ho1).
      exists o1. split; [done|]. rewrite lookup_delete_ne; [done|]. by intros ->.
  Qed.

  Lemma kren_union h Θ1 Θ2 : kinj h (Θ1 ∪ Θ2) → kren h (Θ1 ∪ Θ2) = kren h Θ1 ∪ kren h Θ2.
  Proof.
    intros Hk.
    assert (kinj h Θ1) as K1 by (apply (kinj_sub _ (Θ1 ∪ Θ2)); [rewrite dom_union_L; set_solver|done]).
    assert (kinj h Θ2) as K2 by (apply (kinj_sub _ (Θ1 ∪ Θ2)); [rewrite dom_union_L; set_solver|done]).
    apply renk_kren; [done|]. split.
    - intros o v Ho. apply lookup_union_Some_raw in Ho as [Ho|[Hn Ho]].
      + apply lookup_union_Some_l. by apply kren_lookup.
      + rewrite lookup_union_r; [by apply kren_lookup|]. apply eq_None_not_Some. intros [w Hw].
        destruct (kren_lookup_inv _ _ _ _ Hw) as (o1 & Heq & Ho1).
        assert (o1 = o) as -> by (apply (Hk o1 o w v); [by apply lookup_union_Some_l|
          by rewrite lookup_union_r|done]). by rewrite Ho1 in Hn.
    - intros o' v Ho'. apply lookup_union_Some_raw in Ho' as [Ho'|[Hn Ho']];
        destruct (kren_lookup_inv _ _ _ _ Ho') as (o & -> & Ho); exists o; split; try done.
      + by apply lookup_union_Some_l.
      + destruct (Θ1 !! o) as [w|] eqn:E1; [|by rewrite lookup_union_r].
        by rewrite (kren_lookup h Θ1 o w K1 E1) in Hn.
  Qed.

  Lemma kren_dom h Θ : kinj h Θ → dom (kren h Θ) = set_map h (dom Θ).
  Proof. intros Hk. by apply renk_dom, kren_renk. Qed.

  Lemma kren_heads h Θ : kinj h Θ → senv_heads (kren h Θ) = senv_heads Θ.
  Proof.
    intros Hk. apply set_eq. intros y. rewrite !elem_of_senv_heads. split.
    - intros (o' & S & x & H & ->). destruct (kren_lookup_inv _ _ _ _ H) as (o & -> & Ho). eauto.
    - intros (o & S & x & H & ->). exists (h o), S, x. split; [by apply kren_lookup|done].
  Qed.

  Lemma kren_disjoint h Θ1 Θ2 : kinj h (Θ1 ∪ Θ2) → Θ1 ##ₘ Θ2 → kren h Θ1 ##ₘ kren h Θ2.
  Proof.
    intros Hk Hd. apply map_disjoint_spec. intros o' v1 v2 H1 H2.
    destruct (kren_lookup_inv _ _ _ _ H1) as (o1 & -> & Ho1).
    destruct (kren_lookup_inv _ _ _ _ H2) as (o2 & Heq & Ho2).
    assert (o2 = o1) as ->.
    { apply (Hk o2 o1 v2 v1); [|by apply lookup_union_Some_l|done].
      apply lookup_union_Some; [done|by right]. }
    by apply (map_disjoint_spec Θ1 Θ2) with o1 v1 v2 in Hd.
  Qed.

  Lemma kren_ext h g Θ : (∀ o, o ∈ dom Θ → h o = g o) → kren h Θ = kren g Θ.
  Proof.
    intros H. unfold kren. f_equal. apply list_fmap_ext. intros i [o v] Hi. simpl.
    rewrite H; [done|]. apply elem_of_dom_2 with v. apply elem_of_map_to_list.
    by eapply list_elem_of_lookup_2.
  Qed.

  Lemma kren_id h Θ : (∀ o, o ∈ dom Θ → h o = o) → kren h Θ = Θ.
  Proof.
    intros H. rewrite (kren_ext h id Θ H). apply renk_kren; [apply kinj_id|apply renk_id].
  Qed.

  Lemma kinj_kren g h Θ : kinj h Θ → kinj g (kren h Θ) → kinj (g ∘ h) Θ.
  Proof. intros Hh Hg. eapply kinj_compose; [by apply kren_renk|done|done]. Qed.

  Lemma kren_kren g h Θ : kinj h Θ → kinj g (kren h Θ) → kren g (kren h Θ) = kren (g ∘ h) Θ.
  Proof.
    intros Hh Hg. symmetry. apply renk_kren; [by apply kinj_kren|].
    eapply renk_compose; apply kren_renk; done.
  Qed.

  Lemma kinj_union h Θ1 Θ2 :
    kinj h Θ1 → kinj h Θ2 → (∀ o1 o2, o1 ∈ dom Θ1 → o2 ∈ dom Θ2 → h o1 ≠ h o2) →
    kinj h (Θ1 ∪ Θ2).
  Proof.
    intros K1 K2 Hx o1 o2 v1 v2 H1 H2 Heq.
    apply lookup_union_Some_raw in H1 as [H1|[_ H1]]; apply lookup_union_Some_raw in H2 as [H2|[_ H2]].
    - exact (K1 o1 o2 v1 v2 H1 H2 Heq).
    - exfalso. apply (Hx o1 o2); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
    - exfalso. apply (Hx o2 o1); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
    - exact (K2 o1 o2 v1 v2 H1 H2 Heq).
  Qed.

  Lemma gfresh_kren h ℓ (gr : nat) Θ : kinj h Θ → gfresh ℓ gr (kren h Θ) → gfresh ℓ gr Θ.
  Proof. intros Hk H o S x Hx. apply (H (h o) S x). by apply kren_lookup. Qed.

  (** A creation, renamed. *)
  Lemma kren_new_env h h' Θ c c'' S x :
    kinj h Θ → cfresh c (kren h Θ) → cfresh c'' Θ →
    h' (EPos c'') = EPos c → h' (ENeg c'') = ENeg c → (∀ o, o ∈ dom Θ → h' o = h o) →
    kinj h' (new_env c'' S x Θ) ∧ kren h' (new_env c'' S x Θ) = new_env c S x (kren h Θ).
  Proof.
    intros Hk [Hc1 Hc2] [Hd1 Hd2] Hp Hn Hext.
    assert (kinj h' Θ) as Hk'.
    { intros o1 o2 v1 v2 H1 H2 Heq. rewrite !Hext in Heq by (by eapply elem_of_dom_2).
      exact (Hk o1 o2 v1 v2 H1 H2 Heq). }
    assert (kinj h' (<[ENeg c'' := (dual S, x‾)]> Θ)) as Hk2.
    { rewrite insert_union_singleton_l. apply kinj_union; [|done|].
      - intros o1 o2 v1 v2 H1 H2 _. apply lookup_singleton_Some in H1 as [<- _].
        by apply lookup_singleton_Some in H2 as [<- _].
      - intros o1 o2 Ho1 Ho2. rewrite dom_singleton_L, elem_of_singleton in Ho1. subst o1. rewrite Hn, Hext by done. intros Heq.
        apply Hc2. rewrite kren_dom by done. apply elem_of_map. by exists o2. }
    assert (kinj h' (new_env c'' S x Θ)) as Hk1.
    { unfold new_env. rewrite insert_union_singleton_l. apply kinj_union; [|done|].
      - intros o1 o2 v1 v2 H1 H2 _. apply lookup_singleton_Some in H1 as [<- _].
        by apply lookup_singleton_Some in H2 as [<- _].
      - intros o1 o2 Ho1 Ho2. rewrite dom_singleton_L, elem_of_singleton in Ho1. subst o1. rewrite Hp.
        rewrite dom_insert_L in Ho2. apply elem_of_union in Ho2 as [->%elem_of_singleton|Ho2].
        + rewrite Hn. done.
        + rewrite Hext by done. intros Heq. apply Hc1. rewrite kren_dom by done.
          apply elem_of_map. by exists o2. }
    split; [done|]. unfold new_env. rewrite kren_insert by done. rewrite kren_insert by done.
    rewrite Hp, Hn. by rewrite (kren_ext h' h Θ Hext).
  Qed.

End kren.

Lemma kinj_cmap (kc : chan → chan) (Y : gset chan) (Θ : senv) :
  set_map ech (dom Θ) ⊆ Y → (∀ c1 c2, c1 ∈ Y → c2 ∈ Y → kc c1 = kc c2 → c1 = c2) →
  kinj (cmap kc) Θ.
Proof.
  intros HY Hi o1 o2 v1 v2 H1 H2 Heq.
  assert (ech o1 ∈ Y) as Y1 by (apply HY, elem_of_map; exists o1; split; [done|by eapply elem_of_dom_2]).
  assert (ech o2 ∈ Y) as Y2 by (apply HY, elem_of_map; exists o2; split; [done|by eapply elem_of_dom_2]).
  destruct o1 as [c1|c1], o2 as [c2|c2]; simpl in *; simplify_eq; f_equal; by apply Hi.
Qed.

Lemma emap_thunk g e : emap g (thunk e) = thunk (emap g e).
Proof. unfold thunk. simpl. by rewrite emap_rename, emap_subst1. Qed.

(** ** Readiness under a renaming

    The offered ends of the renamed term are the images of the offered
    ends of the term, because every session step of the term is on held
    ends, where h is injective. *)

Lemma tstep_emap_sess g e σ' x :
  tstep (emap g e) (LSess σ') x → ∃ σ e0, tstep e (LSess σ) e0 ∧ sends σ' = set_map g (sends σ).
Proof.
  intros Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
  destruct (act_offer e a (alabel a) Ha (offers_alabel a)) as [e0 He0].
  destruct a; simpl in Ho; destruct σ'; simpl in Ho; try contradiction; destruct_and?; subst.
  all: eexists _, e0; split; [exact He0|]; simpl.
  all: by rewrite ?set_map_singleton_L, ?set_map_upair.
Qed.

Lemma stable_emap g e : stable_t (emap g e) → stable_t e.
Proof.
  intros Hs α e0 Hst. destruct (act_step _ _ _ Hst) as (a & Ha & Hoff).
  assert (act (emap g e) = Some (amap g a)) as Ha' by (by rewrite act_emap, Ha).
  destruct (act_offer _ _ (alabel (amap g a)) Ha' (offers_alabel _)) as [x Hx].
  destruct (Hs _ _ Hx) as [σ Hσ].
  destruct a, α as [| | | |σ0]; simpl in *; try contradiction; try discriminate; eauto.
Qed.

Lemma ready_rename W Θ F e h :
  kinj h Θ → (∀ σ e', tstep e (LSess σ) e' → sends σ ⊆ dom Θ) →
  ready _ W(Θ ∣ F, e) → ready _ W(kren h Θ ∣ F, emap h e).
Proof.
  intros Hk Hsends H Hst. destruct (H (stable_emap h e Hst)) as [H1 H2].
  assert (∀ o, offered_t Θ e o → offered_t (kren h Θ) (emap h e) (h o)) as Hoff1.
  { intros o [Hd (σ & e' & Hs & Ho)]. split.
    - rewrite kren_dom by done. apply elem_of_map. by exists o.
    - exists (smap h σ), (emap h e'). split; [by apply (tstep_emap h e (LSess σ))|].
      rewrite sends_smap. apply elem_of_map. by exists o. }
  assert (∀ o', offered_t (kren h Θ) (emap h e) o' → ∃ o, o' = h o ∧ offered_t Θ e o) as Hoff2.
  { intros o' [Hd (σ' & x & Hs & Ho)]. rewrite kren_dom in Hd by done.
    apply elem_of_map in Hd as (o1 & -> & Ho1).
    destruct (tstep_emap_sess _ _ _ _ Hs) as (σ & e0 & Hs0 & Hσ). rewrite Hσ in Ho.
    apply elem_of_map in Ho as (o2 & Heq & Ho2).
    assert (o2 ∈ dom Θ) as Hd2 by (by apply (Hsends σ e0)).
    apply elem_of_dom in Ho1 as [v1 V1], Hd2 as [v2 V2].
    assert (o1 = o2) as <- by exact (Hk o1 o2 v1 v2 V1 V2 Heq).
    exists o1. split; [done|]. split; [by eapply elem_of_dom_2|]. eauto. }
  split.
  - intros Hno. rewrite is_val_emap. apply H1. intros o Ho. by apply (Hno (h o)), Hoff1.
  - destruct H2 as [(os & e' & Hl)|Hb]; [left|right].
    + apply (tstep_emap h e (LSess (SLink os))) in Hl; [|done]. by eexists _, _.
    + intros o' S x Ho' Hx. destruct (Hoff2 _ Ho') as (o & -> & Ho).
      apply kren_lookup_held in Hx; [|done|by destruct Ho].
      destruct (Hb _ _ _ Ho Hx) as [B1 B2]. split; [|done].
      intros o2' S' x' Hx' Hno. destruct (kren_lookup_inv _ _ _ _ Hx') as (o2 & -> & Ho2).
      apply (B1 _ _ _ Ho2). intros Hoff. by apply Hno, Hoff1.
Qed.

(** ** V and E under a renaming *)

Section rel.
  Context (κ : ctable).

  Definition VR n T : Prop :=
    ∀ W Θ v h, kinj h Θ → Vrel κ n W Θ T v → Vrel κ n W (kren h Θ) T (emap h v).
  Definition ER n T : Prop :=
    ∀ W Θ F e h, kinj h Θ → Erel κ n W Θ T F e → Erel κ n W (kren h Θ) T F (emap h e).

  (** An incoming value of the renamed term, pulled back to fresh
      channels. *)
  Lemma pull_value n W T1 h Θ Θw w (X : gset chan) :
    VR n T1 → kinj h Θ → set_map ech (dom Θ) ⊆ X →
    kren h Θ ##ₘ Θw → Vrel κ n W Θw T1 w →
    ∃ h' w0 Θ0, Vrel κ n W Θ0 T1 w0 ∧ Θ ##ₘ Θ0 ∧ emap h' w0 = w ∧
      (∀ o, ech o ∈ X → h' o = h o) ∧ kinj h' (Θ ∪ Θ0) ∧
      kren h' (Θ ∪ Θ0) = kren h Θ ∪ Θw ∧ (dcomm h → dcomm h').
  Proof.
    intros HV Hk HX Hd Hw.
    pose proof (Vrel_exact κ _ _ _ _ _ Hw) as Hex.
    destruct (fresh_pull h (set_map ech (dom Θw)) X) as (kc & h' & K1 & K2 & K3 & K4 & K5).
    assert (kinj (cmap kc) Θw) as Hkk by (eapply kinj_cmap; [reflexivity|done]).
    assert (∀ o, o ∈ dom Θw → h' (cmap kc o) = o) as Hback.
    { intros o Ho. apply K3. apply elem_of_map. by exists o. }
    assert (∀ o, o ∈ dom Θ → h' o = h o) as Hext.
    { intros o Ho. apply K4, HX, elem_of_map. by exists o. }
    assert (Θ ##ₘ kren (cmap kc) Θw) as Hd0.
    { apply map_disjoint_spec. intros o v1 v2 H1 H2.
      apply elem_of_dom_2 in H2. rewrite kren_dom in H2 by done.
      apply elem_of_map in H2 as (o1 & -> & Ho1).
      apply (K1 (ech o1)); [apply elem_of_map; by exists o1|].
      rewrite <-ech_cmap. apply HX, elem_of_map. eexists; split; [reflexivity|by eapply elem_of_dom_2]. }
    assert (kinj h' (Θ ∪ kren (cmap kc) Θw)) as Hk'.
    { apply kinj_union.
      - intros o1 o2 v1 v2 H1 H2 Heq.
        rewrite !Hext in Heq by (by eapply elem_of_dom_2). exact (Hk o1 o2 v1 v2 H1 H2 Heq).
      - intros o1 o2 v1 v2 H1 H2 Heq.
        destruct (kren_lookup_inv _ _ _ _ H1) as (a1 & -> & A1).
        destruct (kren_lookup_inv _ _ _ _ H2) as (a2 & -> & A2).
        rewrite !Hback in Heq by (by eapply elem_of_dom_2). by subst.
      - intros o1 o2 Ho1 Ho2. rewrite Hext by done.
        rewrite kren_dom in Ho2 by done. apply elem_of_map in Ho2 as (a & -> & Ha).
        rewrite Hback by done. intros Heq.
        apply elem_of_dom in Ha as [v Hv]. apply elem_of_dom in Ho1 as [u Hu].
        apply (proj1 (map_disjoint_spec (kren h Θ) Θw) Hd (h o1) u v); [by apply kren_lookup|].
        by rewrite Heq. }
    exists h', (emap (cmap kc) w), (kren (cmap kc) Θw). split_and!.
    - by apply HV.
    - done.
    - rewrite emap_emap. rewrite <-(emap_id w) at 2. apply emap_ext_on.
      intros o Ho. apply Hback. by rewrite Hex.
    - done.
    - done.
    - rewrite kren_union by done. rewrite (kren_ext h' h Θ Hext).
      rewrite kren_kren; [|done|].
      + f_equal. apply kren_id. intros o Ho. apply Hback, Ho.
      + eapply kinj_sub; [|exact Hk']. rewrite dom_union_L. set_solver.
    - done.
  Qed.

  (** One level of V, given E where the arrow reads it. *)
  Lemma V_step n T :
    (∀ j, j < n → ∀ T, VR j T ∧ ER j T) →
    (∀ T', tsize T' < tsize T → VR n T') →
    (c_beta κ = 0 → ∀ U, tsize U < tsize T → ER n U) →
    VR n T.
  Proof.
    intros IHl IHt IHe W Θ v h Hk.
    destruct T as [|ub lb c t hh T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a0|s x|lb m C T1 a0].
    - intros [-> ->]%Vrel_unit_iff. apply Vrel_unit_iff. by rewrite kren_empty.
    - intros (e & -> & Hfe & Hlb & H)%Vrel_lolli_iff. apply Vrel_lolli_iff.
      exists (emap h e). split_and!; [done|by rewrite kren_dom, fends_emap, Hfe|by rewrite kren_heads|].
      intros W' j Θw w F HW Hj Hd Hub Hw.
      assert (VR j T1) as HV1.
      { destruct (decide (j < n)); [by apply IHl|]. assert (j = n) as -> by lia. apply IHt. simpl; lia. }
      assert (ER j U) as HEU.
      { destruct (decide (j < n)); [by apply IHl|]. assert (j = n) as -> by lia. apply IHe; [lia|simpl; lia]. }
      destruct (pull_value j W' T1 h Θ Θw w (set_map ech (dom Θ) ∪ fchans e) HV1 Hk
        ltac:(set_solver) Hd Hw) as (h' & w0 & Θ0 & Hw0 & Hd0 & Hww & Hext & Hk' & Hren & _).
      assert (emap h' e = emap h e) as He.
      { apply emap_ext_on. intros o Ho. apply Hext. apply elem_of_union_r, elem_of_fchans. by exists o. }
      rewrite <-Hren, <-Hww, <-He, <-emap_subst1. apply HEU; [done|]. by apply H.
    - intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2)%Vrel_prod_iff. apply Vrel_prod_iff.
      exists (emap h v1), (emap h v2), (kren h Θ1), (kren h Θ2).
      split_and!; [done|by apply kren_disjoint|by apply kren_union| |].
      + apply IHt; [simpl; lia| |done]. eapply kinj_sub; [|exact Hk]. rewrite dom_union_L. set_solver.
      + apply IHt; [simpl; lia| |done]. eapply kinj_sub; [|exact Hk]. rewrite dom_union_L. set_solver.
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; apply Vrel_sum_iff; [left|right]; exists (emap h v');
        (split; [done|]); apply IHt; first [simpl; lia|done].
    - intros (-> & e & -> & Hfe & H)%Vrel_box_iff. apply Vrel_box_iff. rewrite kren_empty.
      split; [done|]. exists (emap h e). split_and!; [done|by rewrite fends_emap, Hfe, set_map_empty|].
      intros W' xs ss HW Hxs Hss Hsc HC. rewrite <-emap_thunk, <-(kren_empty h).
      apply IHt; [|apply kinj_empty|by apply H].
      rewrite tsize_tthunk. unfold ty_inst. rewrite tsize_sinst, tsize_pinst. simpl. lia.
    - intros (o & s' & -> & -> & Hs)%Vrel_sess_iff. apply Vrel_sess_iff. exists (h o), s'.
      by rewrite kren_singleton.
    - intros (Hlb & xs & Hxs & HC & H)%Vrel_ex_iff. apply Vrel_ex_iff. rewrite kren_heads by done.
      split; [done|]. exists xs. split_and!; [done|done|]. apply IHt; [|done|done].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.
  (** One level of E at T, given V at T and at the payloads of free sends. *)
  Lemma E_step n T :
    (∀ j, j < n → ∀ T, VR j T ∧ ER j T) → VR n T → VR n TUnit →
    (c_give κ = 0 → ∀ T', VR n T') →
    ER n T.
  Proof.
    intros IHl HVT HVU HVP. destruct n as [|n]; [unfold ER; intros; apply Erel_0|].
    intros W Θ F e h Hk HE.
    cut (∀ W Θ T0 F e, Erel κ (S n) W Θ T0 F e → T0 = T ∨ T0 = TUnit →
           ∀ h, kinj h Θ → Erel κ (S n) W (kren h Θ) T0 F (emap h e));
      [intros H; by apply (H W Θ T F e HE (or_introl eq_refl))|].
    clear W Θ F e h Hk HE.
    refine (Erel_S_ind κ n _ _). intros W Θ T0 F e Hb HT0 h Hk.
    assert (VR (S n) T0) as HV0 by (destruct HT0 as [->| ->]; done).
    assert (Erel κ (S n) W Θ T0 F e) as HE.
    { apply Erel_S_iff. revert Hb. apply Ebody_mapX. by intros ? ? ? ? ? [? _]. }
    set (X := set_map (D:=gset chan) ech (dom Θ) ∪ fchans e).
    assert (∀ o, o ∈ dom Θ → ech o ∈ X) as HXd.
    { intros o Ho. apply elem_of_union_l, elem_of_map. by exists o. }
    assert (∀ h', (∀ o, ech o ∈ X → h' o = h o) → emap h' e = emap h e) as Hee.
    { intros h' Hh'. apply emap_ext_on. intros o Ho. apply Hh'.
      apply elem_of_union_r, elem_of_fchans. by exists o. }
    assert (∀ c, c ∉ X → cfresh c Θ) as Hcf.
    { intros c Hc. split; intros Hin; apply Hc, elem_of_union_l, elem_of_map; eexists; (split; [|exact Hin]); done. }
    apply Erel_S_iff. intros W1 HW1.
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ σ e', tstep e (LSess σ) e' → sends σ ⊆ dom Θ) as Hsends.
    { intros σ e' Hst. exact (Erel_sends κ n W Θ T0 F e σ e' HE Hst). }
    assert (∀ c Θ' e' h', kinj h' Θ' →
      at_cost_E (S n) c (Erel κ) (λ W Θ T0 F e, Erel κ (S n) W Θ T0 F e ∧
          (T0 = T ∨ T0 = TUnit → ∀ h, kinj h Θ → Erel κ (S n) W (kren h Θ) T0 F (emap h e)))
        W1 Θ' T0 F e' →
      at_cost_E (S n) c (Erel κ) (Erel κ (S n)) W1 (kren h' Θ') T0 F (emap h' e')) as Hac.
    { intros c Θ' e' h' Hk' [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc. apply (proj2 (IHl (S n - c) ltac:(lia) T0)); [done|]. by apply A2. }
    assert (∀ o v w, Θ !! o = Some w → kinj h (<[o := v]> Θ)) as Hkins.
    { intros o v w Ho. eapply kinj_sub; [|exact Hk]. rewrite dom_insert_L.
      apply elem_of_dom_2 in Ho. set_solver. }
    assert (∀ o, kinj h (delete o Θ)) as Hkdel.
    { intros o. eapply kinj_sub; [|exact Hk]. set_solver. }
    split; [|split; [|unfold Esteps; split_and!]].
    - (* (stop) *)
      intros Hi. apply irred_emap in Hi. apply HV0; [done|]. by apply Hs.
    - (* (ready) *)
      intros Hni. apply ready_rename; [done|done|]. apply Hr. intros Hi. by apply Hni, irred_emap.
    - (* O-Beta *)
      intros x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      assert (a = ABeta) as -> by (destruct a; simpl in Ho; try contradiction; done).
      destruct (act_offer e ABeta LBeta Ha I) as [e0 He0].
      rewrite (tstep_emap_back h h e LBeta x LBeta e0 Hst He0 I eq_refl eq_refl).
      apply (Hac _ _ _ h Hk). by apply H1.
    - (* O-New *)
      intros ℓ c x Hst Hc g Hg. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      assert (a = ANew ℓ) as -> by (destruct a; simpl in Ho; try contradiction; by subst).
      destruct (fresh_pull h {[c]} X) as (kc & h' & K1 & _ & K3 & K4 & _).
      assert (kc c ∉ X) as Hc'' by (apply K1; set_solver).
      assert (h' (EPos (kc c)) = EPos c) as Hp by (apply (K3 (EPos c)); set_solver).
      assert (h' (ENeg (kc c)) = ENeg c) as Hn by (apply (K3 (ENeg c)); set_solver).
      destruct (act_offer e (ANew ℓ) (LNew ℓ (kc c)) Ha eq_refl) as [e0 He0].
      assert (lnew_ok h' (LNew ℓ (kc c))) as Hok by (unfold lnew_ok, gpol, gch; rewrite Hp; simpl; by rewrite Hn).
      assert (lmap h' (LNew ℓ (kc c)) = LNew ℓ c) as Hl by (simpl; unfold gch; by rewrite Hp).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 Hok Hl (Hee h' K4)).
      destruct (H2 ℓ (kc c) e0 He0 (Hcf _ Hc'') g (gfresh_kren h ℓ g Θ Hk Hg)) as [S HS]. exists S.
      destruct (kren_new_env h h' Θ c (kc c) S (pgen ℓ g) Hk Hc (Hcf _ Hc'') Hp Hn) as [Hk1 Heq].
      { intros o1 Ho1. by apply K4, HXd. }
      rewrite <-Heq. by apply Hac.
    - (* O-NewAt *)
      intros κf o' c x Hst Hc. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| |κa o| | | | | | |]; simpl in Ho; try contradiction. destruct Ho as [<- <-].
      destruct (fresh_pull h {[c]} X) as (kc & h' & K1 & _ & K3 & K4 & _).
      assert (kc c ∉ X) as Hc'' by (apply K1; set_solver).
      assert (h' (EPos (kc c)) = EPos c) as Hp by (apply (K3 (EPos c)); set_solver).
      assert (h' (ENeg (kc c)) = ENeg c) as Hn by (apply (K3 (ENeg c)); set_solver).
      destruct (act_offer e (ANewAt κa o) (LNewAt κa o (kc c)) Ha (conj eq_refl eq_refl)) as [e0 He0].
      destruct (H3 κa o (kc c) e0 He0 (Hcf _ Hc'')) as (S0 & x0 & Ho0 & S & HS).
      assert (h' o = h o) as Hho by (apply K4, HXd; by eapply elem_of_dom_2).
      assert (lnew_ok h' (LNewAt κa o (kc c))) as Hok by (unfold lnew_ok, gpol, gch; rewrite Hp; simpl; by rewrite Hn).
      assert (lmap h' (LNewAt κa o (kc c)) = LNewAt κa (h o) c) as Hl by (simpl; unfold gch; by rewrite Hp, Hho).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 Hok Hl (Hee h' K4)).
      exists S0, x0. split; [by apply kren_lookup|]. exists S.
      destruct (kren_new_env h h' Θ c (kc c) S (x0·κa) Hk Hc (Hcf _ Hc'') Hp Hn) as [Hk1 Heq].
      { intros o1 Ho1. by apply K4, HXd. }
      rewrite <-Heq. by apply Hac.
    - (* O-Spawn *)
      intros w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | |v| | | | | |]; simpl in Ho; try contradiction. subst w.
      destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e0 He0].
      assert (lmap h (LSpawn v) = LSpawn (emap h v)) as Hl by reflexivity.
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H4 _ _ He0) as (ΘM & Θr & A1 & -> & A4 & A5).
      assert (kinj h ΘM) as KM by (eapply kinj_sub; [|exact Hk]; rewrite dom_union_L; set_solver).
      assert (kinj h Θr) as Kr by (eapply kinj_sub; [|exact Hk]; rewrite dom_union_L; set_solver).
      exists (kren h ΘM), (kren h Θr). split_and!.
      + by apply kren_disjoint.
      + by apply kren_union.
      + destruct A4 as (e1 & -> & Hfe & HA). exists (emap h e1).
        split_and!; [done|by rewrite kren_dom, fends_emap, Hfe|].
        intros W' j Θ' w' HW Hj Hd. split.
        * intros Hjn [-> ->]%Vrel_unit_iff. rewrite map_union_empty.
          destruct (HA W' j ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [B1 _].
          rewrite map_union_empty in B1. change EUnit with (emap h EUnit). rewrite <-emap_subst1.
          apply (proj2 (IHl j Hjn TUnit)); [done|]. apply B1; [done|by apply Vrel_unit_iff].
        * intros -> [-> ->]. rewrite map_union_empty.
          destruct (HA W' (S n) ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [_ B2].
          destruct (B2 eq_refl (conj eq_refl eq_refl)) as [_ B3]. rewrite map_union_empty in B3.
          change EUnit with (emap h EUnit). rewrite <-emap_subst1. apply B3; [by right|done].
      + by apply Hac.
    - (* O-Send *)
      intros o' w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | |o v| | | |]; simpl in Ho; try contradiction. destruct Ho as (<- & <-).
      destruct (act_offer e (ASend o v) (LSess (SSend o v)) Ha
        (conj eq_refl eq_refl)) as [e0 He0].
      assert (lmap h (LSess (SSend o v)) = LSess (SSend (h o) (emap h v))) as Hl by reflexivity.
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H5 _ _ _ He0) as (S0 & x0 & m' & U & b' & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      assert (dom ΘM ∪ dom Θr ⊆ dom Θ ∖ {[o]}) as Hdd by (rewrite <-dom_union_L, <-A4, dom_delete_L; done).
      assert (kinj h (ΘM ∪ Θr)) as KMr by (rewrite <-A4; apply Hkdel).
      assert (kinj h ΘM) as KM by (eapply kinj_sub; [|exact Hk]; set_solver).
      assert (kinj h (<[o := (S, x0⁺)]> Θr)) as Kr.
      { eapply kinj_sub; [|exact Hk]. rewrite dom_insert_L. apply elem_of_dom_2 in A1. set_solver. }
      exists S0, x0, m', U, b', S, (kren h ΘM), (kren h Θr). split_and!.
      + by apply kren_lookup.
      + done.
      + by apply kren_disjoint.
      + rewrite <-kren_union by done. rewrite <-A4. rewrite kren_delete; [done|done|by eapply elem_of_dom_2].
      + destruct A6 as [B1 B2]. split.
        * intros Hc. apply HVP; [done|done|]. by apply B1.
        * intros Hc. apply (proj1 (IHl (Datatypes.S n - c_give κ) ltac:(lia) _)); [done|]. by apply B2.
      + rewrite <-kren_insert by done. by apply Hac.
    - (* O-Recv *)
      intros o' w x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | |o| | | | |]; simpl in Ho; try contradiction. destruct Ho as [<- Hw].
      destruct (act_offer e (ARecv o) (LSess (SRecv o EUnit)) Ha (conj eq_refl I)) as [e00 He00].
      destruct (H6 _ _ _ He00) as (S0 & x0 & m' & U & b' & S & A1 & A2 & _).
      exists S0, x0, m', U, b', S. split_and!; [by apply kren_lookup|done|].
      intros j Θw Hj Hd HVw. pose proof (c_take_pos κ).
      destruct (pull_value j W1 (payload_at m' U x0) h Θ Θw w X (proj1 (IHl j ltac:(lia) _)) Hk
        ltac:(set_solver) Hd HVw) as (h' & w0 & Θ0 & Hw0 & Hd0 & Hww & Hext & Hk' & Hren & _).
      assert (is_val w0) as Hv0 by (rewrite <-Hww, is_val_emap in Hw; done).
      destruct (act_offer e (ARecv o) (LSess (SRecv o w0)) Ha (conj eq_refl Hv0)) as [e0 He0].
      assert (h' o = h o) as Hho by (apply Hext, HXd; by eapply elem_of_dom_2).
      assert (lmap h' (LSess (SRecv o w0)) = LSess (SRecv (h o) w)) as Hl by (simpl; by rewrite Hww, Hho).
      rewrite (tstep_emap_back h h' e _ x _ e0 Hst He0 I Hl (Hee h' Hext)).
      destruct (H6 _ _ _ He0) as (S0' & x0' & m'' & U' & b'' & S' & A1' & A2' & A3').
      rewrite A1 in A1'. injection A1' as <- <-. rewrite A2 in A2'. injection A2' as <- <- <- <-.
      assert (Erel κ j W1 (<[o := (S, x0⁺)]> Θ ∪ Θ0) T0 F e0) as HE0 by (apply A3'; [lia|done|done]).
      rewrite <-insert_union_l in HE0.
      assert (kinj h' (<[o := (S, x0⁺)]> (Θ ∪ Θ0))) as Hk2.
      { eapply kinj_sub; [|exact Hk']. rewrite dom_insert_L, dom_union_L.
        apply elem_of_dom_2 in A1. set_solver. }
      pose proof (proj2 (IHl j ltac:(lia) T0) W1 _ F e0 h' Hk2 HE0) as HR.
      rewrite kren_insert, Hren, Hho, insert_union_l in HR by done. exact HR.
    - (* O-Close *)
      intros o' x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | |o| | |]; simpl in Ho; try contradiction. subst o'.
      destruct (act_offer e (AClose o) (LSess (SClose o)) Ha eq_refl) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H7 _ _ He0) as (S0 & x0 & A1 & A2 & A3).
      exists S0, x0. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_delete; [by apply Hac|done|by eapply elem_of_dom_2].
    - (* O-Select *)
      intros o' i x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | | |o i0|]; simpl in Ho; try contradiction. destruct Ho as [<- <-].
      destruct (act_offer e (ASel o i0) (LSess (SSel o i0)) Ha (conj eq_refl eq_refl)) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H8 _ _ _ He0) as (S0 & x0 & S1 & S2 & A1 & A2 & A3).
      exists S0, x0, S1, S2. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_insert by (by eapply Hkins). by apply Hac; [eapply Hkins|].
    - (* O-Branch *)
      intros o' i x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | | | |o]; simpl in Ho; try contradiction. subst o'.
      destruct (act_offer e (ABra o) (LSess (SBra o i)) Ha eq_refl) as [e0 He0].
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I eq_refl eq_refl).
      destruct (H9 _ _ _ He0) as (S0 & x0 & S1 & S2 & A1 & A2 & A3).
      exists S0, x0, S1, S2. split_and!; [by apply kren_lookup|done|].
      rewrite <-kren_insert by (by eapply Hkins). by apply Hac; [eapply Hkins|].
    - (* O-Link *)
      intros os' x Hst. destruct (tstep_emap_act _ _ _ _ Hst) as (a & Ha & Ho).
      destruct a as [| | | | | | |o1 o2| |]; simpl in Ho; try contradiction. subst os'.
      destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e0 He0].
      assert (lmap h (LSess (SLink ({[o1]} ∪ {[o2]}))) = LSess (SLink ({[h o1]} ∪ {[h o2]}))) as Hl
        by (simpl; by rewrite set_map_upair).
      rewrite (tstep_emap_back h h e _ x _ e0 Hst He0 I Hl eq_refl).
      destruct (H10 _ _ He0) as (p1 & p2 & S1 & S2 & x0 & A1 & A2 & A3 & A4 & A5 & A6).
      exists (h p1), (h p2), S1, S2, x0. split_and!.
      + rewrite <-set_map_upair, A1, set_map_union_L, !set_map_singleton_L. done.
      + intros Heq. apply A2. exact (Hk p1 p2 _ _ A3 A4 Heq).
      + by apply kren_lookup.
      + by apply kren_lookup.
      + done.
      + rewrite <-(kren_delete h Θ p2); [|done|by eapply elem_of_dom_2].
        rewrite <-(kren_delete h (delete p2 Θ) p1); [|done|].
        * apply Hac; [|done]. eapply kinj_sub; [|exact Hk]. set_solver.
        * apply elem_of_dom. rewrite lookup_delete_ne; [by eexists|done].
  Qed.

  Lemma rename_level n : ∀ T, VR n T ∧ ER n T.
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    assert (VR n TUnit) as HVU.
    { apply V_step; [done|intros T' HT|intros _ U HU]; [pose proof (tsize_pos T')|pose proof (tsize_pos U)];
        simpl in *; lia. }
    destruct (decide (c_give κ = 0)) as [Hg|Hg].
    - assert (∀ T, VR n T) as HV.
      { intros T. induction T as [T IH] using tsize_ind. apply V_step; [done|done|].
        intros Hb. pose proof (c_give_pos κ Hb). lia. }
      intros T. split; [done|]. by apply E_step.
    - intros T. induction T as [T IH] using tsize_ind.
      assert (VR n T) as HVT.
      { apply V_step; [done| |]; intros; by apply IH. }
      split; [done|]. by apply E_step.
  Qed.
End rel.

(** ** Decision Q16, held-ends form *)

Theorem Vrel_rename κ n W Θ T v h :
  kinj h Θ → v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧ → emap h v ∈ V[κ]^W _ n⟦kren h Θ ⊢ T⟧.
Proof. intros Hk Hv. by apply (rename_level κ n T). Qed.

Theorem Erel_rename κ n W Θ T F e h :
  kinj h Θ → e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F → emap h e ∈ E[κ]^W _ n⟦kren h Θ ⊢ T⟧^F.
Proof. intros Hk He. by apply (rename_level κ n T). Qed.

(** ** The transpositions of compat/Swap.v, as instances *)

Lemma kren_kmap (h : cend → cend) `{!Inj eq eq h} (Θ : senv) : kren h Θ = kmap h Θ.
Proof.
  assert (kinj h Θ) as Hk by (intros o1 o2 v1 v2 _ _ Heq; by apply (inj h)).
  apply renk_kren; [done|]. split.
  - intros o v Ho. by rewrite lookup_kmap.
  - intros o' v Ho'. apply lookup_kmap_Some in Ho' as (o & -> & Ho); [|apply _]. eauto.
Qed.

Lemma Vrel_swap_rename κ a b n W Θ T v :
  v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧ → eswap a b v ∈ V[κ]^W _ n⟦sswap a b Θ ⊢ T⟧.
Proof.
  intros Hv. unfold sswap. rewrite <-kren_kmap by apply _.
  apply Vrel_rename; [|done]. intros o1 o2 v1 v2 _ _. apply oswap_inj.
Qed.

Lemma Erel_swap_rename κ a b n W Θ T F e :
  e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F → eswap a b e ∈ E[κ]^W _ n⟦sswap a b Θ ⊢ T⟧^F.
Proof.
  intros He. unfold sswap. rewrite <-kren_kmap by apply _.
  apply Erel_rename; [|done]. intros o1 o2 v1 v2 _ _. apply oswap_inj.
Qed.

Lemma Vrel_swap κ a b n W Θ T v :
  Vrel κ n W Θ T v ↔ Vrel κ n W (sswap a b Θ) T (eswap a b v).
Proof.
  split; [apply Vrel_swap_rename|]. intros H.
  rewrite <-(sswap_inv a b Θ), <-(eswap_involutive a b v). by apply Vrel_swap_rename.
Qed.

Lemma Erel_swap κ a b n W Θ T F e :
  Erel κ n W Θ T F e ↔ Erel κ n W (sswap a b Θ) T F (eswap a b e).
Proof.
  split; [apply Erel_swap_rename|]. intros H.
  rewrite <-(sswap_inv a b Θ), <-(eswap_involutive a b e). by apply Erel_swap_rename.
Qed.

(** ** P under a renaming: a projection of the clause (rename) *)

Lemma ech_gch h o : dcomm h → ech (h o) = gch h (ech o).
Proof.
  intros Hd. destruct o as [c|c]; [done|]. unfold gch.
  change (ENeg c) with (edual (EPos c)). by rewrite Hd, ech_edual.
Qed.

Lemma gch_compose g h c : dcomm g → gch g (gch h c) = gch (g ∘ h) c.
Proof. intros Hd. unfold gch at 2 3. simpl. symmetry. by apply ech_gch. Qed.

Lemma pmap_pmap g h p : dcomm g → pmap g (pmap h p) = pmap (g ∘ h) p.
Proof.
  intros Hd. destruct p as [C E]. unfold pmap. simpl. rewrite emapE_emapE. f_equal.
  apply set_eq. intros c. rewrite !elem_of_map. split.
  - intros (c1 & -> & (c2 & -> & Hc2)%elem_of_map). exists c2. split; [|done].
    by rewrite gch_compose.
  - intros (c2 & -> & Hc2). exists (gch h c2). split; [|apply elem_of_map; by exists c2].
    by rewrite gch_compose.
Qed.

Lemma fuse_ok_kinj h D Σ p : fuse_ok h D Σ p → kinj h Σ.
Proof.
  intros (_ & Hi & _) o1 o2 v1 v2 H1 H2. apply Hi; left; by eapply elem_of_dom_2.
Qed.

Lemma pren_ok_kinj h Σ p : pren_ok h Σ p → kinj h Σ.
Proof. intros H. by eapply fuse_ok_kinj, pren_fuse_ok. Qed.

(** A map of an environment through the drop of channels. *)
Lemma kren_sdrop (g : cend → cend) (D1 D2 : gset chan) (M : senv) :
  kinj g M → (∀ o, o ∈ dom M → ech o ∈ D1 ↔ ech (g o) ∈ D2) →
  kren g (sdrop D1 M) = sdrop D2 (kren g M).
Proof.
  intros Hk HPQ. assert (kinj g (sdrop D1 M)) as Hk'.
  { eapply kinj_sub; [|exact Hk]. apply dom_filter_subseteq. }
  apply map_eq. intros o'. apply option_eq. intros v. unfold sdrop at 2. rewrite map_lookup_filter_Some. split.
  - intros Hl. destruct (kren_lookup_inv _ _ _ _ Hl) as (o & -> & Ho).
    unfold sdrop in Ho. apply map_lookup_filter_Some in Ho as [Ho HP]. split; [by apply kren_lookup|].
    simpl in *. rewrite <-HPQ; [done|by eapply elem_of_dom_2].
  - intros [Hl HQ]. destruct (kren_lookup_inv _ _ _ _ Hl) as (o & -> & Ho).
    apply kren_lookup; [done|]. unfold sdrop. apply map_lookup_filter_Some. split; [done|].
    simpl in *. rewrite HPQ; [done|by eapply elem_of_dom_2].
Qed.

Lemma sdrop_sdrop D1 D2 (Σ : senv) : sdrop D1 (sdrop D2 Σ) = sdrop (D1 ∪ D2) Σ.
Proof.
  unfold sdrop. rewrite map_filter_filter. apply map_filter_ext. intros i x _. simpl. set_solver.
Qed.

Lemma sdrop_lookup D (Σ : senv) o v : sdrop D Σ !! o = Some v ↔ Σ !! o = Some v ∧ ech o ∉ D.
Proof. unfold sdrop. by rewrite map_lookup_filter_Some. Qed.

Lemma ech_dual_inv (g : cend → cend) o c : dcomm g → ech (g o) = gch g c → o = EPos c ∨ o = ENeg c ∨
  (g o = g (EPos c) ∨ g o = g (ENeg c)).
Proof.
  intros Hd Hc. right; right. unfold gch in Hc. apply ech_eq in Hc as [Hc|Hc].
  - by left.
  - right. change (ENeg c) with (edual (EPos c)). by rewrite Hd, Hc, edual_edual.
Qed.

(** The held ends of a fusion are the images of the held ends. *)
Lemma pheld_fuse h D Σ p o : fuse_ok h D Σ p → pheld Σ p o → pheld (sdrop D (kren h Σ)) (pfuse h D p) (h o).
Proof.
  intros Hok [Ho|Ho].
  - destruct (decide (ech (h o) ∈ D)) as [HD|HD]; [right; simpl; set_solver|left].
    apply elem_of_dom in Ho as [v Hv]. apply elem_of_dom. exists v. apply sdrop_lookup.
    split; [|done]. apply kren_lookup; [by eapply fuse_ok_kinj|done].
  - right. simpl. apply elem_of_union_l. rewrite ech_gch by apply Hok. apply elem_of_map. by exists (ech o).
Qed.

Lemma pheld_fuse_inv h D Σ p o' : fuse_ok h D Σ p →
  pheld (sdrop D (kren h Σ)) (pfuse h D p) o' → ∃ o, o' = h o ∧ pheld Σ p o.
Proof.
  intros (Hd & Hi & _ & _ & Hp) [Ho|Ho].
  - apply elem_of_dom in Ho as [v Hv]. apply sdrop_lookup in Hv as [Hv _].
    destruct (kren_lookup_inv _ _ _ _ Hv) as (o & -> & Ho). exists o. split; [done|left; by eapply elem_of_dom_2].
  - simpl in Ho. apply elem_of_union in Ho as [Ho|Ho].
    + apply elem_of_map in Ho as (c & Hc & HcC). unfold gch in Hc. apply ech_eq in Hc as [Hc|Hc].
      * exists (EPos c). split; [done|by right].
      * exists (ENeg c). split; [|by right]. change (ENeg c) with (edual (EPos c)). by rewrite Hd, Hc, edual_edual.
    + destruct (Hp o' Ho) as (S & x & S' & Hl & _).
      destruct (kren_lookup_inv _ _ _ _ Hl) as (o & -> & Ho'). exists o. split; [done|left; by eapply elem_of_dom_2].
Qed.

Section fuse_compose.
  Context (h g : cend → cend) (D D' : gset chan) (Σ : senv) (p : proc).
  Context (Hh : fuse_ok h D Σ p) (Hg : fuse_ok g D' (sdrop D (kren h Σ)) (pfuse h D p)).

  Local Lemma g_inj o1 o2 : pheld Σ p o1 → pheld Σ p o2 → g (h o1) = g (h o2) → h o1 = h o2.
  Proof. intros H1 H2. apply Hg; by apply pheld_fuse. Qed.

  Local Lemma dheld o : ech o ∈ D → pheld (sdrop D (kren h Σ)) (pfuse h D p) o.
  Proof. intros Ho. right. simpl. set_solver. Qed.

  Local Lemma kinj_g : kinj g (kren h Σ).
  Proof.
    intros o1 o2 v1 v2 H1 H2. destruct (kren_lookup_inv _ _ _ _ H1) as (a1 & -> & A1).
    destruct (kren_lookup_inv _ _ _ _ H2) as (a2 & -> & A2). intros Heq.
    apply (g_inj a1 a2); [left; by eapply elem_of_dom_2|left; by eapply elem_of_dom_2|done].
  Qed.

  (** g keeps the channels of D apart from the other held channels. *)
  Local Lemma gch_D o : pheld (sdrop D (kren h Σ)) (pfuse h D p) o → ech o ∉ D →
    ech (g o) ∉ (set_map (gch g) D : gset chan).
  Proof.
    intros Ho HD Hin. apply elem_of_map in Hin as (c & Hc & HcD).
    destruct (ech_dual_inv g o c (proj1 Hg) Hc) as [->|[->|[E|E]]]; [done|done| |].
    - apply HD. assert (o = EPos c) as -> by (apply Hg; [done|by apply dheld|done]). done.
    - apply HD. assert (o = ENeg c) as -> by (apply Hg; [done|by apply dheld|done]). done.
  Qed.

  Lemma fuse_sdrop_compose :
    sdrop D' (kren g (sdrop D (kren h Σ))) = sdrop (D' ∪ set_map (gch g) D) (kren (g ∘ h) Σ).
  Proof.
    rewrite (kren_sdrop g D (set_map (gch g) D)).
    - rewrite sdrop_sdrop. rewrite kren_kren; [done|by eapply fuse_ok_kinj|apply kinj_g].
    - apply kinj_g.
    - intros o Ho. split.
      + intros HD. apply elem_of_map. exists (ech o). split; [|done]. by apply ech_gch, Hg.
      + intros Hin. destruct (decide (ech o ∈ D)) as [|HD]; [done|]. exfalso.
        apply (gch_D o); [|done|done]. left. apply elem_of_dom in Ho as [v Hv]. apply elem_of_dom.
        exists v. by apply sdrop_lookup.
  Qed.

  Lemma pfuse_compose : pfuse g D' (pfuse h D p) = pfuse (g ∘ h) (D' ∪ set_map (gch g) D) p.
  Proof.
    destruct p as [C E]. unfold pfuse. simpl. rewrite emapE_emapE. f_equal.
    assert (∀ y, gch g (gch h y) = gch (g ∘ h) y) as Hgc by (intros y; apply gch_compose, (proj1 Hg)).
    apply set_eq. intros c. set_unfold. split.
    - intros [(x & -> & [(y & -> & Hy)|Hx])|Hc].
      + left. exists y. by rewrite Hgc.
      + right; right. by exists x.
      + by right; left.
    - intros [(y & -> & Hy)|[Hc|(x & -> & Hx)]].
      + left. exists (gch h y). split; [by rewrite Hgc|]. left. by exists y.
      + by right.
      + left. exists x. by split; [|right].
  Qed.

  Lemma fuse_ok_compose : fuse_ok (g ∘ h) (D' ∪ set_map (gch g) D) Σ p.
  Proof.
    destruct Hh as (Hd & Hi & Hn & HD & Hp). destruct Hg as (Gd & Gi & Gn & GD & Gp).
    split_and!.
    - intros o. simpl. by rewrite Hd, Gd.
    - intros o1 o2 H1 H2 Heq. apply Hi; [done|done|]. by apply g_inj.
    - intros o1 o2 H1 H2 Heq. simpl in Heq.
      destruct (Gn (h o1) (h o2) (pheld_fuse _ _ _ _ _ Hh H1) (pheld_fuse _ _ _ _ _ Hh H2) Heq) as [E|E].
      + destruct (Hn o1 o2 H1 H2 E) as [?|E']; [by left|right].
        apply elem_of_union_r, elem_of_map. exists (ech (h o1)). split; [|done]. simpl. by apply ech_gch.
      + right. by apply elem_of_union_l.
    - apply disjoint_union_l. split.
      + intros c Hc Hc'. apply (GD c Hc). simpl. apply elem_of_map in Hc' as (c1 & -> & Hc1).
        apply elem_of_map. exists (gch h c1). split; [by rewrite gch_compose|]. apply elem_of_union_l.
        apply elem_of_map. by exists c1.
      + intros c Hc Hc'. apply elem_of_map in Hc as (d & -> & HdD).
        apply elem_of_map in Hc' as (c1 & Hc & Hc1).
        assert (pheld Σ p (EPos c1)) as Hp1 by (by right).
        apply (gch_D (h (EPos c1))); [by apply pheld_fuse| |].
        * intros Hin. apply (HD (ech (h (EPos c1))) Hin). apply elem_of_map. by exists c1.
        * apply elem_of_map. exists d. split; [|done]. rewrite Hc. reflexivity.
    - intros o Ho. apply elem_of_union in Ho as [Ho|Ho].
      + destruct (Gp o Ho) as (S & x & S' & H1 & H2 & Hs). exists S, x, S'.
        rewrite <-(kren_kren g h Σ (fuse_ok_kinj _ _ _ _ Hh) kinj_g).
        assert (∀ o v, kren g (sdrop D (kren h Σ)) !! o = Some v → kren g (kren h Σ) !! o = Some v) as Hsub.
        { intros o0 v Hv. destruct (kren_lookup_inv _ _ _ _ Hv) as (a & -> & Ha).
          apply sdrop_lookup in Ha as [Ha _]. by apply kren_lookup; [apply kinj_g|]. }
        split_and!; [by apply Hsub|by apply Hsub|done].
      + apply elem_of_map in Ho as (c & Hc & HcD).
        assert (o = g (EPos c) ∨ o = g (ENeg c)) as Ho'.
        { unfold gch in Hc. apply ech_eq in Hc as [Hc|Hc]; [by left|right].
          change (ENeg c) with (edual (EPos c)). by rewrite Gd, Hc, edual_edual. }
        rewrite <-(kren_kren g h Σ (fuse_ok_kinj _ _ _ _ Hh) kinj_g).
        destruct Ho' as [->| ->].
        * destruct (Hp (EPos c) HcD) as (S & x & S' & H1 & H2 & Hs). exists S, x, S'.
          rewrite <-Gd. split_and!; [by apply kren_lookup; [apply kinj_g|]|by apply kren_lookup; [apply kinj_g|]|done].
        * destruct (Hp (ENeg c) HcD) as (S & x & S' & H1 & H2 & Hs). exists S, x, S'.
          rewrite <-Gd. split_and!; [by apply kren_lookup; [apply kinj_g|]|by apply kren_lookup; [apply kinj_g|]|done].
  Qed.
End fuse_compose.

(** The clause (fuse) as a projection: a fusion of a process in P is in P. *)
Theorem Prel_fuse κ n W Σ T p h D :
  fuse_ok h D Σ p → p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → pfuse h D p ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧.
Proof.
  intros Hh HP. destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_iff in HP. apply Prel_S_iff. intros W1 HW1 HS1 g D' Hg.
  rewrite (fuse_sdrop_compose h g D D' Σ p Hh Hg), (pfuse_compose h g D D' Σ p Hh Hg).
  apply HP; [done|done|]. by apply fuse_ok_compose.
Qed.

(** Decision Q16 for P, D = ∅. *)
Theorem Prel_rename κ n W Σ T p h :
  pren_ok h Σ p → p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → pmap h p ∈ P[κ]^W _ n⟦kren h Σ ⊢ T⟧.
Proof.
  intros Hh HP. rewrite <-pfuse_empty, <-(sdrop_empty (kren h Σ)). by apply Prel_fuse; [apply pren_fuse_ok|].
Qed.

(** Internalize, h = id: the channels D, whose two ends Σ holds as dual
    pairs at dual points, become restricted. *)
Theorem Prel_internalize κ n W Σ T p D :
  dpairs D Σ → D ## p.1 →
  p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → (p.1 ∪ D, p.2) ∈ P[κ]^W _ n⟦sdrop D Σ ⊢ T⟧.
Proof.
  intros Hp HD HP.
  assert (fuse_ok id D Σ p) as Hok.
  { split_and!; [done|by intros ? ? _ _|by intros ? ? _ _ ?; left| |by rewrite kren_id_map].
    simpl. intros c Hc Hc'. apply elem_of_map in Hc' as (c' & -> & Hc'). unfold gch in Hc. simpl in Hc. set_solver. }
  pose proof (Prel_fuse κ n W Σ T p id D Hok HP) as H. rewrite kren_id_map in H.
  unfold pfuse in H. rewrite emapE_id_map in H.
  replace (set_map (gch id) p.1) with p.1 in H; [done|].
  apply set_eq. intros c. rewrite elem_of_map. unfold gch. simpl. split; [eauto|by intros (? & -> & ?)].
Qed.

(** ** The link substitution renames the other component (P-Connect)

    When a component links o1 with o2 and the other component holds o1‾
    but neither o1 nor o2, [csub o1 o2] is a renaming of the held ends of
    the other component, even when it holds o2‾. *)

Lemma csub_dcomm o1 o2 : ech o2 ≠ ech o1 → dcomm (csub o1 o2).
Proof.
  intros Hne o. unfold csub.
  destruct (decide (o = edual o1)) as [->|N1].
  - rewrite edual_edual, decide_False by (intros H; by apply (edual_ne o1)). rewrite decide_True by done. done.
  - destruct (decide (o = o1)) as [->|N2].
    + rewrite decide_True by done. by rewrite edual_edual.
    + rewrite decide_False by (intros H; apply N2; by apply edual_inj in H).
      rewrite decide_False; [done|]. intros H. apply N1. by rewrite <-H, edual_edual.
Qed.

Lemma pren_ok_csub o1 o2 Σ p :
  ech o2 ≠ ech o1 → ¬ pheld Σ p o1 → ¬ pheld Σ p o2 → ¬ pheld Σ p (edual o2) → pren_ok (csub o1 o2) Σ p.
Proof.
  intros Hne H1 H2 H3. split; [by apply csub_dcomm|].
  assert (∀ o, pheld Σ p o → csub o1 o2 o = o ∨ (o = edual o1 ∧ csub o1 o2 o = o2)) as Hc.
  { intros o Ho. unfold csub. destruct (decide (o = edual o1)) as [->|N1]; [by right|].
    rewrite decide_False; [by left|]. intros ->. done. }
  split.
  - intros oa ob Ha Hb Heq.
    destruct (Hc oa Ha) as [Ea|[-> Ea]], (Hc ob Hb) as [Eb|[-> Eb]]; rewrite ?Ea, ?Eb in Heq.
    + done.
    + subst oa. by exfalso.
    + subst ob. by exfalso.
    + done.
  - intros oa ob Ha Hb Heq.
    destruct (Hc oa Ha) as [Ea|[-> Ea]], (Hc ob Hb) as [Eb|[-> Eb]]; rewrite ?Ea, ?Eb in Heq.
    + done.
    + exfalso. apply H3. by rewrite Heq, edual_edual.
    + exfalso. apply H3. by rewrite <-Heq.
    + exfalso. apply (edual_ne o2). by symmetry.
Qed.
