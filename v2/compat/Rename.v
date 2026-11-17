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

From GV Require Export compat.Redex compat.PSwap relation.Adequacy fuel.FuelMono.

(** ** Labels under a map of ends *)

Definition smap (g : cend → cend) (σ : slabel) : slabel :=
  match σ with
  | SSend o M v => SSend (g o) (set_map g M) (emap g v)
  | SRecv o v => SRecv (g o) (emap g v)
  | SClose o => SClose (g o)
  | SSel o i => SSel (g o) i
  | SBra o i => SBra (g o) i
  | SLink os => SLink (set_map g os)
  end.

(** The channel of the image of c⁺. *)
Definition gch (g : cend → cend) (c : chan) : chan := ech (g (EPos c)).

Definition lmap (g : cend → cend) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LNew ℓ c => LNew ℓ (gch g c)
  | LNewAt κf o c => LNewAt κf (g o) (gch g c)
  | LSpawn M v => LSpawn (set_map g M) (emap g v)
  | LSess σ => LSess (smap g σ)
  end.

(** g keeps the polarity of the two ends of c. *)
Definition gpol (g : cend → cend) (c : chan) : Prop :=
  g (EPos c) = EPos (gch g c) ∧ g (ENeg c) = ENeg (gch g c).

Definition lnew_ok (g : cend → cend) (α : tlabel) : Prop :=
  match α with LNew _ c | LNewAt _ _ c => gpol g c | _ => True end.

(** g commutes with duality. *)
Definition dcomm (g : cend → cend) : Prop := ∀ o, g (edual o) = edual (g o).

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

Definition kren (h : cend → cend) (Θ : senv) : senv :=
  list_to_map ((λ p : cend * (sty * point), (h p.1, p.2)) <$> map_to_list Θ).

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

  Lemma kren_empty h : kren h ∅ = (∅ : senv).
  Proof. unfold kren. by rewrite map_to_list_empty. Qed.

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
