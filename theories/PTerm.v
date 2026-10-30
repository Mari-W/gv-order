(** * P-Term (§11)

    One thread holding both ends of every channel of its restricted
    set C₀ is a good process: Σ, Θ_B; · ⊨^∅_W t : T gives
    Σ ⊨_W (C₀, {t}) : T.

    The proof goes by induction on n and, at a fixed level S n', by
    induction on the syntactic size of the thread, as P-Connect does
    (sharp edges 46). A link of a restricted channel substitutes in the
    thread, and the substituted thread is not a giving successor, so the
    induction over the giving fixpoint of E does not reach it. Every
    giving step shrinks the thread, and a substitution keeps its size.
    The spawn case splits the thread's environment into the two threads
    and composes them with P-Connect at the lower level ([conn_all]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Connect3.

Set Default Proof Using "All".

(** ** Steps of a single thread *)

Lemma soup_single_inv (E : gmultiset expr) e t :
  E ⊎ {[+ e +]} = {[+ t +]} → E = ∅ ∧ e = t.
Proof. multiset_solver. Qed.

Lemma soup_single_two (E : gmultiset expr) e f t :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ t +]} → False.
Proof.
  intros H.
  assert (size (E ⊎ {[+ e +]} ⊎ {[+ f +]}) = size ({[+ t +]} : gmultiset expr))
    as Hsz by (by rewrite H).
  rewrite !gmultiset_size_disj_union, !gmultiset_size_singleton in Hsz. lia.
Qed.

Lemma single_step C t π p' :
  proc_step (C, {[+ t +]}) π p' →
  (∃ σ t', π = PSess σ ∧ tstep t (LSess σ) t' ∧ subjs σ ## C ∧
     p' = (C ∖ sentc σ, {[+ t' +]}))
  ∨ (∃ t', π = PTau ∧ tstep t LBeta t' ∧ p' = (C, {[+ t' +]}))
  ∨ (∃ c t', π = PTau ∧ tstep t (LNew c) t' ∧ c ∉ C ∧ c ∉ fchans t ∧
       p' = (C ∪ {[c]}, {[+ t' +]}))
  ∨ (∃ v t', π = PTau ∧ tstep t (LSpawn v) t' ∧
       p' = (C, {[+ t' +]} ⊎ {[+ App v EUnit +]}))
  ∨ (∃ c d t', π = PTau ∧ tstep t (LSess (SLink {[c; d]})) t' ∧ c ∈ C ∧
       p' = (C ∖ {[c]}, {[+ chsubst c d t' +]})).
Proof.
  intros Hst. inversion Hst; subst;
    try (exfalso; by eapply soup_single_two);
    match goal with H : _ ⊎ {[+ _ +]} = {[+ _ +]} |- _ =>
      apply soup_single_inv in H as [-> ->] end;
    rewrite ?(left_id_L ∅ (⊎)).
  - left. eauto 10.
  - right; left. eauto.
  - right; right; left. eauto 10.
  - right; right; right; left. eauto.
  - right; right; right; right. rewrite echsubst_singleton. eauto 10.
Qed.

(** A thread applied to ∗ by spawn: one β step to the body. *)
Lemma Erel_spawned n W Θ ub lb v :
  Vrel (S n) W Θ (TLolli ub lb TUnit TUnit) v → strict W →
  Erel n W Θ TUnit ∅ (App v EUnit).
Proof.
  intros HV HW. apply Vrel_lolli_iff in HV
    as [(eb & -> & _ & _ & HL)|(k & T0 & -> & -> & Hk & Heq)].
  - destruct n as [|n']; [apply Erel_0|].
    assert (tstep (App (Lam eb) EUnit) LBeta (subst1 EUnit eb)) as Hb
      by (constructor; by constructor).
    apply Erel_S_iff. split_and!.
    + intros Hirr. exfalso. by apply (Hirr _ _ Hb).
    + intros _ Hs. exfalso. exact (Hs _ _ Hb).
    + intros α e' Hst.
      inversion Hst as [? ? ? Hh| ? ? ? ? Hs| ? ? ? ? ? Hs| | | | | | |]; subst.
      * inversion Hh; subst. simpl.
        apply (HL W n' ∅ Θ EUnit ∅); [by apply wext_refl|lia| | |].
        3: destruct ub; simpl; [intros y Hy; set_solver|done].
        -- split; [intros c; rewrite lookup_empty; destruct (Θ !! c); constructor|].
           intros c e1 e2 _ H. by rewrite lookup_empty in H.
        -- by apply Vrel_unit_iff.
      * exfalso. by apply (val_no_tstep _ _ _ Hs).
      * exfalso. by apply (val_no_tstep _ _ _ Hs).
  - exfalso. inversion Hk; subst; simpl in Heq; naive_solver.
Qed.

(** ** Environments of a thread with restricted channels

    [tok W Σ ΘB C0]: the thread's environment is Σ, ΘB, where Σ is the
    interface and ΘB holds both ends of every channel of C₀, dual and
    at aliased points. *)

Record tok (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) : Prop := {
  tok_strict : strict W;
  tok_dom : dom ΘB = C0;
  tok_disj : dom Σ ## C0;
  tok_both : ∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2;
  tok_dual : tenv_dual (w_eq W) ΘB
}.

Lemma tok_mono W W' Σ ΘB C0 : wext W W' → tok W Σ ΘB C0 → tok W' Σ ΘB C0.
Proof.
  intros (_ & Heq & _ & HW') [HW Hd Hdj Hb Hdu]. split; try done.
  eapply tenv_dual_mono; [|exact Hdu]. exact Heq.
Qed.

(** Restricting a map to the keys of another, or to the keys missing
    from it. *)
Definition mkeep {A B} (m : gmap chan A) (k : gmap chan B) : gmap chan A :=
  merge (λ a b, match b with Some _ => a | None => None end) m k.
Definition mdrop {A B} (m : gmap chan A) (k : gmap chan B) : gmap chan A :=
  merge (λ a b, match b with Some _ => None | None => a end) m k.

Lemma lookup_mkeep {A B} (m : gmap chan A) (k : gmap chan B) x :
  mkeep m k !! x = match k !! x with Some _ => m !! x | None => None end.
Proof. unfold mkeep. rewrite lookup_merge. by destruct (m !! x), (k !! x). Qed.

Lemma lookup_mdrop {A B} (m : gmap chan A) (k : gmap chan B) x :
  mdrop m k !! x = match k !! x with Some _ => None | None => m !! x end.
Proof. unfold mdrop. rewrite lookup_merge. by destruct (m !! x), (k !! x). Qed.

(** The both-ends entries of Θ. *)
Definition tenv_boths (Θ : tenv) : tenv :=
  omap (λ o, match o with One _ => None | Both _ _ => Some o end) Θ.

Lemma lookup_tenv_of (Σ : senv) c : tenv_of Σ !! c = One <$> Σ !! c.
Proof. apply lookup_fmap. Qed.

Lemma ounion_Some {A} (x : A) (o : option A) : Some x ∪ o = Some x.
Proof. by destruct o. Qed.
Lemma ounion_None {A} (o : option A) : None ∪ o = o.
Proof. by destruct o. Qed.

Ltac tlk := repeat (progress (rewrite ?lookup_union, ?lookup_tenv_of, ?ounion_Some, ?ounion_None, ?lookup_fmap, ?lookup_omap,
                      ?lookup_mkeep, ?lookup_mdrop, ?lookup_insert_eq, ?lookup_delete_eq,
                      ?lookup_empty in * ) ||
                    (rewrite lookup_insert_ne in * by done) ||
                    (rewrite lookup_delete_ne in * by done)).

(** Pointwise facts of [tok]. *)
Lemma tok_at W Σ ΘB C0 x :
  tok W Σ ΘB C0 →
  (x ∈ C0 ↔ is_Some (ΘB !! x)) ∧ (Σ !! x = None ∨ ΘB !! x = None) ∧
  (∀ o, ΘB !! x = Some o → ∃ e1 e2, o = Both e1 e2 ∧ w_eq W e1.2 e2.2 ∧ sdual e1.1 e2.1).
Proof.
  intros [HW Hd Hdj Hb Hdu]. split_and!.
  - by rewrite <-Hd, elem_of_dom.
  - destruct (Σ !! x) eqn:E1; [right|by left].
    apply not_elem_of_dom. rewrite Hd. intros Hx. apply (Hdj x); [|done].
    by apply elem_of_dom_2 in E1.
  - intros o Ho. destruct (Hb x o Ho) as (e1 & e2 & ->). exists e1, e2.
    destruct (Hdu x e1 e2 Ho). done.
Qed.

Lemma tenv_roots_mono Θ Θ' : Θ ⊆ Θ' → tenv_roots Θ ⊆ tenv_roots Θ'.
Proof.
  intros Hs x. rewrite !elem_of_tenv_roots. intros (c0 & o & Ho & Hx).
  exists c0, o. split; [|done]. by apply (lookup_weaken Θ Θ').
Qed.

Lemma senv_roots_sub Σ ΘB : senv_roots Σ ⊆ tenv_roots (tenv_of Σ ∪ ΘB).
Proof. apply tenv_roots_mono, map_union_subseteq_l. Qed.

(** Θ = Θ1, x : e, pointwise. *)
Definition removed (Θ Θ1 : tenv) (x : chan) (e : sty * point) : Prop :=
  (Θ1 !! x = None ∧ Θ !! x = Some (One e)) ∨
  (∃ e', Θ1 !! x = Some (One e') ∧
     (Θ !! x = Some (Both e e') ∨ Θ !! x = Some (Both e' e))).

Lemma tenv_ext_inv Θ1 x e Θ :
  tenv_ext Θ1 x e Θ → removed Θ Θ1 x e ∧ ∀ y, y ≠ x → Θ1 !! y = Θ !! y.
Proof.
  intros [(H1 & ->)|(e' & H1 & [->| ->])]; (split; [|intros y Hy; by rewrite lookup_insert_ne]).
  - left. by rewrite lookup_insert_eq.
  - right. exists e'. rewrite lookup_insert_eq. auto.
  - right. exists e'. rewrite lookup_insert_eq. auto.
Qed.

(** The head entry of a channel of the interface. *)
Lemma hd_iface W Σ ΘB C0 c u k Θ1 :
  tok W Σ ΘB C0 → c ∉ C0 → tenv_hd (tenv_of Σ ∪ ΘB) c u k Θ1 →
  ∃ s0, Σ !! c = Some (s0, k) ∧ unfoldS s0 = u ∧ Θ1 = tenv_of (delete c Σ) ∪ ΘB.
Proof.
  intros Hok Hc (s0 & Hext & Hu).
  destruct (tok_at W Σ ΘB C0 c Hok) as (HC & _ & _).
  assert (ΘB !! c = None) as HBc.
  { destruct (ΘB !! c) eqn:E; [|done]. exfalso. apply Hc, HC. by eexists. }
  apply tenv_ext_inv in Hext as [Hr Ho].
  destruct Hr as [(H1 & H2)|(e' & H1 & [H2|H2])]; tlk; rewrite ?HBc in H2;
    destruct (Σ !! c) as [ec|] eqn:Ec; simpl in H2;
    rewrite ?ounion_Some, ?ounion_None in H2; simplify_eq.
  - exists s0. split_and!; [done|done|].
    apply map_eq. intros y. destruct (decide (y = c)) as [->|Hy].
    + rewrite H1. tlk. by rewrite HBc.
    + rewrite Ho by done. tlk. done.
Qed.

Lemma is_Some_Some_iff {A} (x : A) : is_Some (Some x) ↔ True.
Proof. split; [done|by eexists]. Qed.
Lemma is_Some_None_iff {A} : is_Some (@None A) ↔ False.
Proof. split; [by intros []|done]. Qed.

(** Close a propositional goal over [is_Some] of computed options. *)
Ltac fin_is := rewrite ?is_Some_Some_iff, ?is_Some_None_iff in *; tauto.

(** Membership in sets built from domains, read as lookups. *)
Ltac dset := rewrite ?elem_of_union, ?elem_of_intersection, ?elem_of_difference,
               ?elem_of_dom in *.

(** Destruct every lookup at x and simplify. *)
Ltac lkx x :=
  tlk;
  repeat match goal with
  | |- context [?M !! x] =>
      let E := fresh "L" in destruct (M !! x) as [[]|] eqn:E || destruct (M !! x) eqn:E;
      rewrite ?E in *
  | H : context [?M !! x] |- _ =>
      lazymatch type of H with
      | ?M !! x = _ => fail
      | _ => let E := fresh "L" in
             destruct (M !! x) as [[]|] eqn:E || destruct (M !! x) eqn:E; rewrite ?E in *
      end
  end;
  simpl in *; rewrite ?ounion_Some, ?ounion_None in *; simplify_eq; try done.

(** ** The receive case: the received channels whose both ends the
    thread now holds join the restricted set *)

Definition bpart (Σr : senv) (Θ2 : tenv) : tenv :=
  merge (λ a o, match a, o with
                | Some e1, Some (One e2) => Some (Both e1 e2)
                | None, Some (Both e1 e2) => Some (Both e1 e2)
                | _, _ => None
                end) Σr Θ2.

Lemma lookup_bpart Σr Θ2 x :
  bpart Σr Θ2 !! x =
    match Σr !! x, Θ2 !! x with
    | Some e1, Some (One e2) => Some (Both e1 e2)
    | None, Some (Both e1 e2) => Some (Both e1 e2)
    | _, _ => None
    end.
Proof. unfold bpart. rewrite lookup_merge. by destruct (Σr !! x), (Θ2 !! x) as [[]|]. Qed.

Lemma recv_comp W W' Σr ΘB C0 Θ2 :
  tok W Σr ΘB C0 → wext W W' → dom Θ2 ## C0 → recv_ok W' Σr Θ2 →
  tok W' (recv_env Σr Θ2) (ΘB ∪ bpart Σr Θ2) (C0 ∪ recv_back Σr Θ2) ∧
  tenv_comp (w_eq W') (tenv_of (recv_env Σr Θ2) ∪ (ΘB ∪ bpart Σr Θ2))
    (tenv_of Σr ∪ ΘB) Θ2.
Proof.
  intros Hok HW HdC (Hon & Hdu2 & Hbo).
  pose proof (tok_mono _ _ _ _ _ HW Hok) as Hok'.
  assert (∀ x, (x ∈ C0 ↔ is_Some (ΘB !! x)) ∧ (Σr !! x = None ∨ ΘB !! x = None) ∧
    (∀ o, ΘB !! x = Some o → ∃ e1 e2, o = Both e1 e2 ∧ w_eq W' e1.2 e2.2 ∧ sdual e1.1 e2.1))
    as Hat by (intros x; by apply tok_at).
  assert (∀ x, is_Some (Θ2 !! x) → ΘB !! x = None) as H2B.
  { intros x Hx. destruct (Hat x) as (HC & _). destruct (ΘB !! x) eqn:E; [|done].
    exfalso. apply (HdC x); [by apply elem_of_dom|apply HC; by eexists]. }
  assert (∀ x e1 e2, Θ2 !! x = Some (Both e1 e2) → Σr !! x = None) as H2Σ.
  { intros x e1 e2 Hx. apply not_elem_of_dom. intros Hy. apply (Hbo x); [|done].
    apply elem_of_difference. split; [by eapply elem_of_dom_2|].
    rewrite elem_of_dom. unfold tenv_ones. rewrite lookup_omap, Hx. simpl. by intros []. }
  assert (∀ x e1 e2, Σr !! x = Some e1 → Θ2 !! x = Some (One e2) →
            w_eq W' e1.2 e2.2 ∧ sdual e1.1 e2.1) as HΣ2.
  { intros x e1 e2 H1 H2. apply (Hon x); [done|]. unfold tenv_ones.
    rewrite lookup_omap, H2. done. }
  assert (∀ x, (ΘB !! x = None ∨ (∃ o, ΘB !! x = Some o ∧ Σr !! x = None ∧ Θ2 !! x = None)) ∧ True) as Hx0.
  { intros x. destruct (Hat x) as (HC & HΣB & _). split; [|done].
    destruct (ΘB !! x) as [o|] eqn:E; [right; exists o|by left]. split_and!; [done| |].
    + destruct HΣB; congruence.
    + destruct (Θ2 !! x) eqn:E2; [|done]. rewrite H2B in E; [done|by eexists]. }
  split; [split|split].
  - apply Hok'.
  - apply set_eq. intros x. unfold recv_back. dset. unfold tenv_ones.
    destruct (Hat x) as (HC & _). rewrite HC.
    specialize (H2Σ x).
    rewrite lookup_union, lookup_bpart, lookup_omap.
    destruct (Hx0 x) as [[->|(? & -> & -> & ->)] _];
      [|rewrite ounion_Some; fin_is].
    rewrite ?ounion_None.
    destruct (Θ2 !! x) as [[]|]; [|rewrite (H2Σ _ _ eq_refl)|];
      destruct (Σr !! x); simpl; fin_is.
  - intros x Hx1 Hx2. revert Hx1 Hx2. unfold recv_env, recv_back. dset.
    unfold tenv_ones. destruct (Hat x) as (HC & _). rewrite HC.
    specialize (H2Σ x).
    rewrite !lookup_union, !lookup_difference, !lookup_omap.
    destruct (Hx0 x) as [[->|(? & -> & -> & ->)] _]; [|simpl; fin_is].
    rewrite ?ounion_None.
    destruct (Θ2 !! x) as [[]|]; [|rewrite (H2Σ _ _ eq_refl)|];
      destruct (Σr !! x); simpl; fin_is.
  - intros x o. rewrite lookup_union, lookup_bpart.
    destruct (ΘB !! x) as [o'|] eqn:E.
    { rewrite ounion_Some. intros [= <-].
      destruct (Hat x) as (_ & _ & HB). destruct (HB o' E) as (? & ? & -> & _). eauto. }
    rewrite ?ounion_None. destruct (Σr !! x), (Θ2 !! x) as [[]|]; intros; simplify_eq; eauto.
  - intros x e1 e2. rewrite lookup_union, lookup_bpart.
    destruct (ΘB !! x) as [o'|] eqn:E.
    { rewrite ounion_Some. intros [= ->].
      destruct (Hat x) as (_ & _ & HB). by destruct (HB _ E) as (? & ? & [= -> ->] & ?). }
    rewrite ?ounion_None. specialize (HΣ2 x). specialize (Hdu2 x).
    destruct (Σr !! x), (Θ2 !! x) as [[]|]; intros; simplify_eq; eauto.
  - intros x. unfold recv_env, tenv_ones.
    specialize (H2Σ x).
    rewrite !lookup_union, !lookup_tenv_of, !lookup_union, !lookup_difference, lookup_bpart, !lookup_omap.
    destruct (Hx0 x) as [[->|(? & -> & -> & ->)] _]; [|simpl; rewrite ?ounion_Some, ?ounion_None; constructor].
    rewrite ?ounion_None.
    destruct (Θ2 !! x) as [[]|]; [|rewrite (H2Σ _ _ eq_refl)|];
      destruct (Σr !! x); simpl; rewrite ?ounion_Some, ?ounion_None; constructor.
  - intros x e1 e2. rewrite lookup_union, lookup_tenv_of.
    destruct (Hx0 x) as [[->|(? & -> & -> & ->)] _]; [|done].
    specialize (HΣ2 x e1 e2).
    destruct (Σr !! x); simpl; rewrite ?ounion_Some, ?ounion_None;
      intros; simplify_eq; eauto.
Qed.

(** ** Splitting the thread's environment *)

(** The shapes of a point of Θ = Θ1, Θ2 for Θ = Σ, ΘB. *)
Lemma comp_at W Σ ΘB C0 Θ1 Θ2 x :
  tok W Σ ΘB C0 → tenv_comp (w_eq W) (tenv_of Σ ∪ ΘB) Θ1 Θ2 →
  (ΘB !! x = None ∧ Σ !! x = None ∧ Θ1 !! x = None ∧ Θ2 !! x = None) ∨
  (∃ e, ΘB !! x = None ∧ Σ !! x = Some e ∧ Θ1 !! x = Some (One e) ∧ Θ2 !! x = None) ∨
  (∃ e, ΘB !! x = None ∧ Σ !! x = Some e ∧ Θ1 !! x = None ∧ Θ2 !! x = Some (One e)) ∨
  (∃ e1 e2, ΘB !! x = Some (Both e1 e2) ∧ Σ !! x = None ∧
     w_eq W e1.2 e2.2 ∧ sdual e1.1 e2.1 ∧
     ((Θ1 !! x = Some (Both e1 e2) ∧ Θ2 !! x = None) ∨
      (Θ1 !! x = None ∧ Θ2 !! x = Some (Both e1 e2)) ∨
      (Θ1 !! x = Some (One e1) ∧ Θ2 !! x = Some (One e2)) ∨
      (Θ1 !! x = Some (One e2) ∧ Θ2 !! x = Some (One e1)))).
Proof.
  intros Hok [Hj _]. destruct (tok_at W Σ ΘB C0 x Hok) as (_ & HΣB & HB).
  pose proof (Hj x) as J. rewrite lookup_union, lookup_tenv_of in J.
  destruct (ΘB !! x) as [o|] eqn:EB.
  - destruct (HB o eq_refl) as (e1 & e2 & -> & Hq & Hd).
    destruct HΣB as [HΣ|]; [|done]. rewrite HΣ in J |- *. simpl in J.
    right; right; right. exists e1, e2. split_and!; try done.
    inversion J; subst; [left|right; left|right; right; left|right; right; right]; done.
  - destruct (Σ !! x) as [e|] eqn:EΣ; simpl in J; rewrite ?ounion_Some, ?ounion_None in J.
    + inversion J; subst; [right; left|right; right; left]; by exists e.
    + left. inversion J; subst. done.
Qed.

Lemma tok_sub W Σ Σ' ΘB C0 : Σ' ⊆ Σ → tok W Σ ΘB C0 → tok W Σ' ΘB C0.
Proof.
  intros Hs [HW Hd Hdj Hb Hdu]. split; try done.
  pose proof (subseteq_dom Σ' Σ Hs). set_solver.
Qed.

Ltac cat_rw H1 H2 H3 H4 := rewrite ?H1, ?H2, ?H3, ?H4 in *.

(** The send case: the payload's part of the environment, the ends of
    restricted channels that leave with it ([Θe]) and those that stay
    ([Σe]). *)
Lemma send_env W Σ ΘB C0 Θ1 Θ2 c e :
  tok W Σ ΘB C0 → c ∉ C0 → c ∉ dom Σ →
  tenv_comp (w_eq W) (tenv_of Σ ∪ ΘB) Θ1 Θ2 →
  Θ2 = tenv_of (mkeep Σ Θ2) ∪ mkeep Θ2 ΘB ∧
  <[c := One e]> Θ1 = tenv_of (<[c := e]> (mdrop Σ Θ2 ∪ tenv_ones (mkeep Θ1 ΘB))) ∪ mdrop ΘB Θ2 ∧
  mdrop Σ Θ2 ##ₘ mkeep Σ Θ2 ∧ Σ = mdrop Σ Θ2 ∪ mkeep Σ Θ2 ∧
  dom (mkeep Θ2 ΘB) = dom Θ2 ∩ C0 ∧
  send_split W (tenv_ones (mkeep Θ1 ΘB)) (mkeep Θ2 ΘB) ∧
  dom (mkeep Θ2 ΘB) ## dom Σ ∪ {[c]} ∧
  tok W (<[c := e]> (mdrop Σ Θ2 ∪ tenv_ones (mkeep Θ1 ΘB))) (mdrop ΘB Θ2) (C0 ∖ dom Θ2).
Proof.
  intros Hok HcC HcΣ Hc.
  assert (∀ x, (x ∈ C0 ↔ is_Some (ΘB !! x))) as HC by (intros x; by apply (tok_at W Σ ΘB C0 x)).
  assert (Σ !! c = None) as HΣc by by apply not_elem_of_dom.
  assert (ΘB !! c = None) as HBc.
  { destruct (ΘB !! c) eqn:E; [|done]. exfalso. apply HcC, HC. by eexists. }
  assert (Θ1 !! c = None ∧ Θ2 !! c = None) as [H1c H2c].
  { destruct (comp_at W Σ ΘB C0 Θ1 Θ2 c Hok Hc) as
      [(_&_&?&?)|[(?&_&?&_)|[(?&_&?&_)|(?&?&?&_)]]]; first [by split|congruence]. }
  pose proof (λ x, comp_at W Σ ΘB C0 Θ1 Θ2 x Hok Hc) as Hca.
  split_and!.
  - apply map_eq. intros x. tlk. unfold tenv_ones.
    destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&_&_&H)]]];
      cat_rw H1 H2 H3 H4; simpl; rewrite ?ounion_Some, ?ounion_None; try done.
    destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; by cat_rw H3 H4 H4 H4.
  - apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
    { tlk. by rewrite HBc, H2c. }
    tlk. unfold tenv_ones. tlk.
    destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&_&_&H)]]];
      cat_rw H1 H2 H3 H4; simpl; rewrite ?ounion_Some, ?ounion_None; try done.
    destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; cat_rw H3 H4 H4 H4; simpl;
      rewrite ?ounion_Some, ?ounion_None; done.
  - apply map_disjoint_spec. intros x a b. tlk.
    destruct (Θ2 !! x); [|done]. by intros [=] _.
  - apply map_eq. intros x. tlk.
    destruct (Θ2 !! x), (Σ !! x); simpl; rewrite ?ounion_Some, ?ounion_None; done.
  - apply set_eq. intros x. dset. tlk. rewrite HC.
    destruct (Θ2 !! x), (ΘB !! x); fin_is.
  - split.
    + intros x. dset. unfold tenv_ones. tlk.
      destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&_&_&H)]]];
        cat_rw H1 H2 H3 H4; simpl; try fin_is.
      destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; cat_rw H3 H4 H4 H4; simpl; fin_is.
    + intros r o. unfold tenv_ones. tlk.
      destruct (Hca r) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&Hq&Hd&H)]]];
        cat_rw H1 H2 H3 H4; simpl; try discriminate.
      destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; cat_rw H3 H4 H4 H4; simpl;
        intros [= <-]; simpl; try done.
      * eexists. split; [done|]. done.
      * eexists. split; [done|].
        split; [by apply (wf_eq_sym _ (proj1 (tok_strict _ _ _ _ Hok)))|by apply sdual_sym].
  - intros x. dset. tlk. rewrite elem_of_singleton. intros Hx [Hy| ->].
    + destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&_&_&H)]]];
        cat_rw H1 H2 H3 H4; simpl in *; fin_is.
    + by rewrite HBc in Hx.
  - destruct Hok as [HW Hd Hdj Hb Hdu]. split.
    + done.
    + apply set_eq. intros x. dset. tlk. rewrite <-Hd, elem_of_dom.
      destruct (Θ2 !! x), (ΘB !! x); fin_is.
    + intros x. dset. intros Hx (Hx1 & Hx2). revert Hx. rewrite <-Hd in Hx1.
      destruct (decide (x = c)) as [->|Hxc]; [by rewrite elem_of_dom, HBc in Hx1|].
      dset. tlk. unfold tenv_ones. tlk.
      destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&_&_&H)]]];
        cat_rw H1 H2 H3 H4; simpl in *; try fin_is.
      destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; cat_rw H3 H4 H4 H4; simpl in *; fin_is.
    + intros x o. tlk. destruct (Θ2 !! x); [done|]. apply Hb.
    + intros x e1 e2. tlk. destruct (Θ2 !! x); [done|]. apply Hdu.
Qed.

Lemma lookup_tenv_ones Θ x :
  tenv_ones Θ !! x = match Θ !! x with Some (One e) => Some e | _ => None end.
Proof. unfold tenv_ones. rewrite lookup_omap. by destruct (Θ !! x) as [[]|]. Qed.

Lemma lookup_tenv_boths Θ x :
  tenv_boths Θ !! x = match Θ !! x with Some (Both e1 e2) => Some (Both e1 e2) | _ => None end.
Proof. unfold tenv_boths. rewrite lookup_omap. by destruct (Θ !! x) as [[]|]. Qed.

(** The spawn case: the spawned thread takes Θ1, the continuation Θ2.
    Restricted channels with both ends on one side stay restricted
    there, the others form the cut. *)
Lemma spawn_env W Σ ΘB C0 Θ1 Θ2 :
  tok W Σ ΘB C0 → tenv_comp (w_eq W) (tenv_of Σ ∪ ΘB) Θ1 Θ2 →
  Θ2 = tenv_of (mkeep Σ Θ2 ∪ tenv_ones (mkeep Θ2 ΘB)) ∪ tenv_boths Θ2 ∧
  Θ1 = tenv_of (mkeep Σ Θ1 ∪ tenv_ones (mkeep Θ1 ΘB)) ∪ tenv_boths Θ1 ∧
  tok W (mkeep Σ Θ2 ∪ tenv_ones (mkeep Θ2 ΘB)) (tenv_boths Θ2) (dom (tenv_boths Θ2)) ∧
  tok W (mkeep Σ Θ1 ∪ tenv_ones (mkeep Θ1 ΘB)) (tenv_boths Θ1) (dom (tenv_boths Θ1)) ∧
  cut_ok W (mkeep Σ Θ2) (mkeep Σ Θ1) (tenv_ones (mkeep Θ2 ΘB)) (tenv_ones (mkeep Θ1 ΘB))
    (dom (tenv_ones (mkeep Θ2 ΘB))) (dom (tenv_boths Θ2)) (dom (tenv_boths Θ1)) ∧
  mkeep Σ Θ2 ∪ mkeep Σ Θ1 = Σ ∧
  dom (tenv_boths Θ2) ∪ dom (tenv_boths Θ1) ∪ dom (tenv_ones (mkeep Θ2 ΘB)) = C0.
Proof.
  intros Hok Hc. pose proof (tok_strict _ _ _ _ Hok) as HW.
  assert (∀ x, (x ∈ C0 ↔ is_Some (ΘB !! x))) as HC by (intros x; by apply (tok_at W Σ ΘB C0 x)).
  pose proof (λ x, comp_at W Σ ΘB C0 Θ1 Θ2 x Hok Hc) as Hca.
  Ltac sp_cases Hca x :=
    destruct (Hca x) as [(H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|[(e0&H1&H2&H3&H4)|(e1&e2&H1&H2&Hq&Hd&H)]]];
    cat_rw H1 H2 H3 H4; simpl in *; rewrite ?ounion_Some, ?ounion_None in *;
    [..|destruct H as [(H3&H4)|[(H3&H4)|[(H3&H4)|(H3&H4)]]]; cat_rw H3 H4 H4 H4; simpl in *;
        rewrite ?ounion_Some, ?ounion_None in *].
  assert (∀ x y, w_eq W x y → w_eq W y x) as Hsym by apply (wf_eq_sym _ (proj1 HW)).
  split_and!.
  - apply map_eq. intros x. tlk. rewrite !lookup_tenv_ones, lookup_tenv_boths. tlk.
    sp_cases Hca x; done.
  - apply map_eq. intros x. tlk. rewrite !lookup_tenv_ones, lookup_tenv_boths. tlk.
    sp_cases Hca x; done.
  - split; [done|done| | |].
    + intros x. dset. tlk. rewrite !lookup_tenv_ones, lookup_tenv_boths. tlk.
      sp_cases Hca x; fin_is.
    + intros x o. rewrite lookup_tenv_boths. destruct (Θ2 !! x) as [[]|]; intros; simplify_eq; eauto.
    + intros x f1 f2. rewrite lookup_tenv_boths. intros Hx.
      sp_cases Hca x; simplify_eq; split; eauto using sdual_sym.
  - split; [done|done| | |].
    + intros x. dset. tlk. rewrite !lookup_tenv_ones, lookup_tenv_boths. tlk.
      sp_cases Hca x; fin_is.
    + intros x o. rewrite lookup_tenv_boths. destruct (Θ1 !! x) as [[]|]; intros; simplify_eq; eauto.
    + intros x f1 f2. rewrite lookup_tenv_boths. intros Hx.
      sp_cases Hca x; simplify_eq; split; eauto using sdual_sym.
  - split; [done| | | |done| | | | | | | | |].
    + apply map_disjoint_spec. intros x a b. rewrite lookup_tenv_ones. tlk.
      sp_cases Hca x; congruence.
    + apply map_disjoint_spec. intros x a b. rewrite lookup_tenv_ones. tlk.
      sp_cases Hca x; congruence.
    + apply map_disjoint_spec. intros x a b. tlk.
      sp_cases Hca x; congruence.
    + apply set_eq. intros x. dset. rewrite !lookup_tenv_ones. tlk.
      sp_cases Hca x; fin_is.
    + intros x a b. rewrite !lookup_tenv_ones. tlk.
      sp_cases Hca x; intros; simplify_eq; split; eauto using sdual_sym.
    + intros x. dset. rewrite lookup_tenv_boths. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite lookup_tenv_boths. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite lookup_tenv_boths. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite lookup_tenv_boths. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite lookup_tenv_boths, lookup_tenv_ones. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite lookup_tenv_boths, lookup_tenv_ones. tlk. sp_cases Hca x; fin_is.
    + intros x. dset. rewrite !lookup_tenv_boths. sp_cases Hca x; fin_is.
  - apply map_eq. intros x. tlk. sp_cases Hca x; done.
  - apply set_eq. intros x. dset. rewrite !lookup_tenv_boths, lookup_tenv_ones, HC. tlk.
    sp_cases Hca x; fin_is.
Qed.

(** ** The link case *)

Lemma chsubst_self c e : chsubst c c e = e.
Proof. induction e; simpl; f_equal; try done. by case_decide; subst. Qed.

Lemma removed_some Θ Θ1 x e : removed Θ Θ1 x e → is_Some (Θ !! x).
Proof. intros [(_ & ->)|(e' & _ & [->| ->])]; by eexists. Qed.

Lemma removed_both Σ ΘB Θ1 x e b1 b2 :
  removed (tenv_of Σ ∪ ΘB) Θ1 x e → Σ !! x = None → ΘB !! x = Some (Both b1 b2) →
  ∃ r, Θ1 !! x = Some (One r) ∧ ((b1 = e ∧ b2 = r) ∨ (b1 = r ∧ b2 = e)).
Proof.
  intros [(H1 & H2)|(e' & H1 & H2)] HΣ HB; revert H2; tlk; rewrite HΣ, HB; simpl;
    rewrite ?ounion_None; [discriminate|].
  intros [HH|HH]; injection HH as <- <-; eauto 10.
Qed.

Lemma removed_one Σ ΘB Θ1 x e a :
  removed (tenv_of Σ ∪ ΘB) Θ1 x e → Σ !! x = Some a → ΘB !! x = None →
  Θ1 !! x = None ∧ e = a.
Proof.
  intros [(H1 & H2)|(e' & H1 & H2)] HΣ HB; revert H2; tlk; rewrite HΣ; simpl;
    rewrite ?ounion_Some; [by intros [= ->]|].
  by intros [?|?].
Qed.

(** A link of the restricted channel c with d: the remaining end of c
    moves to d. For d restricted it fuses with the other end of d, for d
    in the interface it becomes the interface's end of d up to ≈ and ≡. *)
Lemma link_env W Σ ΘB C0 Θm Θ1 c' d' ec ed c d :
  tok W Σ ΘB C0 → c ∈ C0 → {[c'; d']} = ({[c; d]} : gset chan) →
  tenv_ext Θ1 d' ed Θm → tenv_ext Θm c' ec (tenv_of Σ ∪ ΘB) →
  sdual ed.1 ec.1 → w_eq W ec.2 ed.2 →
  (c = d ∧ Θ1 = tenv_of Σ ∪ delete c ΘB) ∨
  (c ≠ d ∧ ∃ Θ' ΘB', tenv_move W c d Θ1 Θ' ∧ tconv W Θ' (tenv_of Σ ∪ ΘB') ∧
     tok W Σ ΘB' (C0 ∖ {[c]})).
Proof.
  intros Hok HcC Hcd H1 H2 Hdu Heq.
  pose proof (tok_strict _ _ _ _ Hok) as HW.
  assert (∀ x y, w_eq W x y → w_eq W y x) as Hsym by apply (wf_eq_sym _ (proj1 HW)).
  assert (∀ x y z, w_eq W x y → w_eq W y z → w_eq W x z) as Htr by apply (wf_eq_trans _ (proj1 HW)).
  destruct (tok_at W Σ ΘB C0 c Hok) as (HC & HΣB & HB).
  destruct (proj1 HC HcC) as [oc Hoc].
  destruct (HB oc Hoc) as (c1 & c2 & -> & Hq12 & Hd12).
  assert (Σ !! c = None) as HΣc by (destruct HΣB; congruence).
  apply tenv_ext_inv in H1 as [Hr1 Ho1]. apply tenv_ext_inv in H2 as [Hr2 Ho2].
  destruct (decide (c = d)) as [<-|Hne].
  - left. split; [done|].
    assert (c' = c ∧ d' = c) as [-> ->].
    { assert (c' ∈ ({[c; c]} : gset chan)) as Hc' by (rewrite <-Hcd; clear; set_solver).
      assert (d' ∈ ({[c; c]} : gset chan)) as Hd' by (rewrite <-Hcd; clear; set_solver).
      clear -Hc' Hd'. set_solver. }
    apply map_eq. intros x. destruct (decide (x = c)) as [->|Hx].
    + destruct Hr2 as [(_ & HH)|(e' & HH & _)].
      { exfalso. revert HH. tlk. rewrite HΣc, Hoc. simpl. rewrite ounion_None. discriminate. }
      destruct Hr1 as [(HH1 & _)|(e'' & HH1 & [HH'|HH'])]; [|congruence|congruence].
      rewrite HH1. tlk. by rewrite HΣc.
    + rewrite Ho1, Ho2 by done. tlk. done.
  - right. split; [done|].
    assert (c' ≠ d') as Hne'.
    { intros ->. apply Hne.
      assert (c ∈ ({[d'; d']} : gset chan)) as Hc' by (rewrite Hcd; clear; set_solver).
      assert (d ∈ ({[d'; d']} : gset chan)) as Hd' by (rewrite Hcd; clear; set_solver).
      clear -Hc' Hd'. set_solver. }
    assert (removed (tenv_of Σ ∪ ΘB) Θ1 c' ec) as Rc'.
    { destruct Hr2 as [(HH & ?)|(e' & HH & ?)]; [left|right; exists e']; rewrite Ho1 by done; auto. }
    assert (removed (tenv_of Σ ∪ ΘB) Θ1 d' ed) as Rd'.
    { destruct Hr1 as [(HH & HH')|(e' & HH & HH')]; [left|right; exists e'];
        rewrite <-(Ho2 d') by done; auto. }
    assert (∀ y, y ≠ c → y ≠ d → Θ1 !! y = (tenv_of Σ ∪ ΘB) !! y) as Ho.
    { intros y Hy1 Hy2. assert (y ≠ c' ∧ y ≠ d') as [? ?].
      { assert (c' ∈ ({[c; d]} : gset chan)) as Hy by (rewrite <-Hcd; clear; set_solver).
        assert (d' ∈ ({[c; d]} : gset chan)) as Hy' by (rewrite <-Hcd; clear; set_solver).
        clear -Hy Hy' Hy1 Hy2. split; intros ->; set_solver. }
      rewrite Ho1, Ho2 by done. done. }
    (* the removed entries at c and d, linked *)
    assert (∃ xc xd, removed (tenv_of Σ ∪ ΘB) Θ1 c xc ∧ removed (tenv_of Σ ∪ ΘB) Θ1 d xd ∧
              sdual xc.1 xd.1 ∧ w_eq W xc.2 xd.2) as (xc & xd & Rc & Rd & Hxd & Hxq).
    { assert ((c' = c ∧ d' = d) ∨ (c' = d ∧ d' = c)) as [[-> ->]|[-> ->]].
      { assert (c ∈ ({[c'; d']} : gset chan)) as Hc' by (rewrite Hcd; clear; set_solver).
        assert (c' ∈ ({[c; d]} : gset chan)) as Hc'' by (rewrite <-Hcd; clear; set_solver).
        assert (d' ∈ ({[c; d]} : gset chan)) as Hd' by (rewrite <-Hcd; clear; set_solver).
        clear -Hc' Hc'' Hd' Hne'. set_solver. }
      - exists ec, ed. split_and!; [done|done|by apply sdual_sym|done].
      - exists ed, ec. split_and!; [done|done|done|by apply Hsym]. }
    (* the remaining end of c *)
    assert (∃ rc, Θ1 !! c = Some (One rc) ∧ sdual xc.1 rc.1 ∧ w_eq W xc.2 rc.2)
      as (rc & Hrc & Hrcd & Hrcq).
    { destruct (removed_both _ _ _ _ _ _ _ Rc HΣc Hoc) as (r & Hr & [[-> ->]|[-> ->]]);
        exists r; split_and!; eauto using sdual_sym. }
    assert (seq rc.1 xd.1) as Hseq by (eapply sdual_unique; [exact Hrcd|exact Hxd]).
    destruct (tok_at W Σ ΘB C0 d Hok) as (HCd & HΣBd & HBd).
    destruct (ΘB !! d) as [od|] eqn:Hod.
    + (* d restricted: fusion *)
      destruct (HBd od eq_refl) as (d1 & d2 & -> & Hq12' & Hd12').
      assert (Σ !! d = None) as HΣd by (destruct HΣBd; congruence).
      assert (∃ rd, Θ1 !! d = Some (One rd) ∧ sdual xd.1 rd.1 ∧ w_eq W xd.2 rd.2)
        as (rd & Hrd & Hrdd & Hrdq).
      { destruct (removed_both _ _ _ _ _ _ _ Rd HΣd Hod) as (r & Hr & [[-> ->]|[-> ->]]);
          exists r; split_and!; eauto using sdual_sym. }
      assert (sdual rc.1 rd.1) as Hrr by (eapply sdual_seq_l; [apply seq_sym, Hseq|exact Hrdd]).
      assert (w_eq W rc.2 rd.2) as Hrq by eauto.
      exists (<[d := Both rc rd]> (delete c Θ1)), (<[d := Both rc rd]> (delete c ΘB)). split_and!.
      * split_and!.
        -- tlk. done.
        -- intros k Hk1 Hk2. tlk. done.
        -- tlk. rewrite Hrc, Hrd. constructor.
        -- intros f1 f2. rewrite Hrc, Hrd. intros [= <-] [= <-]. done.
      * assert (<[d := Both rc rd]> (delete c Θ1) =
                tenv_of Σ ∪ <[d := Both rc rd]> (delete c ΘB)) as ->.
        { apply map_eq. intros x. destruct (decide (x = d)) as [->|Hxd'].
          { tlk. rewrite HΣd. simpl. by rewrite ounion_None. }
          destruct (decide (x = c)) as [->|Hxc].
          { tlk. rewrite HΣc. done. }
          tlk. rewrite Ho by done. tlk. done. }
        apply (tconv_refl W (proj1 HW)).
      * assert (d ∈ C0) as HdC by (apply HCd; by eexists).
        destruct Hok as [HW' Hd Hdj Hb Hdu']. split.
        -- done.
        -- rewrite dom_insert_L, dom_delete_L, Hd. apply set_eq. intros x.
           destruct (decide (x = d)); destruct (decide (x = c)); subst;
             clear -HdC HcC Hne; set_solver.
        -- clear -Hdj. set_solver.
        -- intros x o. destruct (decide (x = d)) as [->|Hxd']; [tlk; intros [= <-]; eauto|].
           destruct (decide (x = c)) as [->|Hxc]; [tlk; done|]. tlk. apply Hb.
        -- intros x f1 f2. destruct (decide (x = d)) as [->|Hxd']; [tlk; intros [= <- <-]; done|].
           destruct (decide (x = c)) as [->|Hxc]; [tlk; done|]. tlk. apply Hdu'.
    + (* d in the interface: the remaining end of c becomes d's *)
      destruct (Σ !! d) as [a|] eqn:HΣd.
      2: { exfalso. destruct (removed_some _ _ _ _ Rd) as [o Ho']. revert Ho'. tlk.
           rewrite HΣd, Hod. simpl. rewrite ounion_None. discriminate. }
      destruct (removed_one _ _ _ _ _ _ Rd HΣd Hod) as [Hd1 ->].
      exists (<[d := One rc]> (delete c Θ1)), (delete c ΘB). split_and!.
      * split_and!.
        -- tlk. done.
        -- intros k Hk1 Hk2. tlk. done.
        -- tlk. rewrite Hrc, Hd1. constructor.
        -- intros f1 f2. rewrite Hd1. discriminate.
      * intros x. destruct (decide (x = d)) as [->|Hxd'].
        { tlk. rewrite HΣd. simpl. rewrite ounion_Some. split; [done|]. eauto. }
        destruct (decide (x = c)) as [->|Hxc].
        { tlk. rewrite HΣc. done. }
        tlk. rewrite Ho by done. tlk. destruct ((One <$> Σ !! x) ∪ ΘB !! x); simpl; [apply (ends_conv_refl W (proj1 HW))|done].
      * destruct Hok as [HW' Hd Hdj Hb Hdu']. split.
        -- done.
        -- rewrite dom_delete_L, Hd. done.
        -- clear -Hdj. set_solver.
        -- intros x o. destruct (decide (x = c)) as [->|Hxc]; [tlk; done|]. tlk. apply Hb.
        -- intros x f1 f2. destruct (decide (x = c)) as [->|Hxc]; [tlk; done|]. tlk. apply Hdu'.
Qed.

(** ** Small facts for the step cases *)

Lemma tok_insert W Σ ΘB C0 c e : c ∉ C0 → tok W Σ ΘB C0 → tok W (<[c := e]> Σ) ΘB C0.
Proof.
  intros Hc [HW Hd Hdj Hb Hdu]. split; try done. rewrite dom_insert_L. clear -Hc Hdj. set_solver.
Qed.

Lemma tok_delete W Σ ΘB C0 c : tok W Σ ΘB C0 → tok W Σ (delete c ΘB) (C0 ∖ {[c]}).
Proof.
  intros [HW Hd Hdj Hb Hdu]. split; try done.
  - by rewrite dom_delete_L, Hd.
  - clear -Hdj. set_solver.
  - intros x o. destruct (decide (x = c)) as [->|Hx]; [tlk; done|]. tlk. apply Hb.
  - intros x f1 f2. destruct (decide (x = c)) as [->|Hx]; [tlk; done|]. tlk. apply Hdu.
Qed.

Lemma ins_one Σ ΘB c e :
  ΘB !! c = None → <[c := One e]> (tenv_of Σ ∪ ΘB) = tenv_of (<[c := e]> Σ) ∪ ΘB.
Proof.
  intros Hc. apply map_eq. intros x. destruct (decide (x = c)) as [->|Hx]; tlk; [|done].
  simpl. by rewrite ounion_Some.
Qed.

Lemma ins_both Σ ΘB c o :
  Σ !! c = None → <[c := o]> (tenv_of Σ ∪ ΘB) = tenv_of Σ ∪ <[c := o]> ΘB.
Proof.
  intros Hc. apply map_eq. intros x. destruct (decide (x = c)) as [->|Hx]; tlk; [|done].
  rewrite Hc. simpl. by rewrite ounion_None.
Qed.

Lemma removed_eq Θ Θ' Θ1 x e : Θ' !! x = Θ !! x → removed Θ Θ1 x e → removed Θ' Θ1 x e.
Proof. intros H. unfold removed. by rewrite H. Qed.

Lemma ptau_link_C p p' : ptau_link p p' → ∃ c, c ∈ p.1 ∧ p'.1 = p.1 ∖ {[c]}.
Proof. intros (C & E & e & c & d & e' & -> & _ & Hc & ->). by exists c. Qed.

Lemma ΘB_none_of W Σ ΘB C0 c : tok W Σ ΘB C0 → c ∉ C0 → ΘB !! c = None.
Proof.
  intros Hok Hc. destruct (tok_at W Σ ΘB C0 c Hok) as (HC & _).
  destruct (ΘB !! c) eqn:E; [|done]. exfalso. apply Hc, HC. by eexists.
Qed.

(** A thread at a primitive type that stops holds nothing. *)
Lemma tok_empty W Σ ΘB C0 : tok W Σ ΘB C0 → tenv_of Σ ∪ ΘB = ∅ → Σ = ∅ ∧ C0 = ∅.
Proof.
  intros Hok H. pose proof (map_positive_l _ _ H) as H1.
  rewrite H1, (left_id_L ∅ (∪)) in H. split; [by apply tenv_of_empty_inv|].
  rewrite <-(tok_dom _ _ _ _ Hok), H. apply dom_empty_L.
Qed.

(** ** P-Term *)

Definition term_at (n : nat) (T : ty) : Prop :=
  ∀ W Σ ΘB C0 t, tok W Σ ΘB C0 →
    Erel n W (tenv_of Σ ∪ ΘB) T ∅ t → Prel n W Σ T (C0, {[+ t +]}).

Section level.
  Context (n' : nat) (IHo : ∀ j T, j ≤ n' → prim T → term_at j T).
  Context (T : ty) (HT : prim T) (m : nat).
  Context (IHi : ∀ W Σ ΘB C0 t, esize t < m → tok W Σ ΘB C0 →
             Erel (S n') W (tenv_of Σ ∪ ΘB) T ∅ t → Prel (S n') W Σ T (C0, {[+ t +]})).
  Context (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr).
  Context (Hsz : esize t = m) (Hok : tok W Σ ΘB C0).
  Context (HE : Erel (S n') W (tenv_of Σ ∪ ΘB) T ∅ t).

  Local Notation Θ := (tenv_of Σ ∪ ΘB).

  Lemma HWs : strict W.
  Proof. apply (tok_strict _ _ _ _ Hok). Qed.

  Lemma case_recv c w t' :
    tstep t (LSess (SRecv c w)) t' → c ∉ C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) (PSess (SRecv c w)) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θ1 & m0 & U & s & k & Hhd & Hcont).
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    pose proof (ΘB_none_of _ _ _ _ _ Hok HcC) as HBc.
    exists (delete c Σ), m0, U, s, k. split_and!.
    - exists s0. split; [|done]. by rewrite insert_delete_id.
    - by rewrite dom_delete_L; clear; set_solver.
    - intros W' j Θ2 HW' Hj Hd Hrok HV. cbn [nlower pcost scost pred] in Hj.
      assert (tok W (<[c := (s, pt_shift 1 k)]> (delete c Σ)) ΘB C0) as Hok1.
      { apply tok_insert; [done|]. eapply tok_sub; [|exact Hok]. apply delete_subseteq. }
      destruct (recv_comp W W' _ ΘB C0 Θ2 Hok1 HW' Hd Hrok) as [Hok' Hcomp].
      simpl. eapply (IHo j T); [lia|done|exact Hok'|].
      eapply (Hcont W' j Θ2); [done|done| |exact Hcomp|done].
      left. split.
      + tlk. by rewrite HBc.
      + by rewrite ins_one.
  Qed.

  Lemma case_close c t' :
    tstep t (LSess (SClos c)) t' → c ∉ C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) (PSess (SClos c)) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θ1 & k & Hhd & HE').
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    exists (delete c Σ), k. split_and!.
    - exists s0. split; [|done]. by rewrite insert_delete_id.
    - by rewrite dom_delete_L; clear; set_solver.
    - apply (IHi W (delete c Σ) ΘB C0); [|eapply tok_sub; [apply delete_subseteq|exact Hok]|done].
      rewrite <-Hsz. by apply (tstep_giving_size _ _ _ Hst).
  Qed.

  Lemma case_send c w t' :
    tstep t (LSess (SSend c w)) t' → c ∉ C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) (PSess (SSend c w)) (C0 ∖ fchans w, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θr & Θ1 & Θ2 & m0 & U & s & k & Θ' & Hhd & Hcomp & HV & Hext & HE').
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    pose proof (ΘB_none_of _ _ _ _ _ Hok HcC) as HBc.
    assert (tok W (delete c Σ) ΘB C0) as Hok0 by (eapply tok_sub; [apply delete_subseteq|exact Hok]).
    assert (c ∉ dom (delete c Σ)) as HcΣ by (rewrite dom_delete_L; clear; set_solver).
    destruct (send_env W (delete c Σ) ΘB C0 Θ1 Θ2 c (s, pt_shift 1 k) Hok0 HcC HcΣ Hcomp)
      as (H2 & H1 & Hdj & HΣeq & Hdome & Hsplit & Hde & Hok').
    assert (Θ1 !! c = None) as H1c.
    { destruct (comp_at W (delete c Σ) ΘB C0 Θ1 Θ2 c Hok0 Hcomp) as
        [(_&_&?&_)|[(?&_&HH&_)|[(?&_&HH&_)|(?&?&HH&_)]]]; [done|..];
        rewrite ?lookup_delete_eq in HH; congruence. }
    assert (Θ' = <[c := One (s, pt_shift 1 k)]> Θ1) as ->.
    { destruct Hext as [(_ & ->)|(e' & HH & _)]; [done|congruence]. }
    exists (mdrop (delete c Σ) Θ2), (mkeep (delete c Σ) Θ2), m0, U, s, k,
      (tenv_ones (mkeep Θ1 ΘB)), (mkeep Θ2 ΘB). split_and!.
    - exists s0. split; [|done]. rewrite <-HΣeq. by rewrite insert_delete_id.
    - done.
    - intros Hin. apply HcΣ. rewrite HΣeq, dom_union_L. clear -Hin. set_solver.
    - intros Hin. apply HcΣ. rewrite HΣeq, dom_union_L. clear -Hin. set_solver.
    - simpl. by rewrite (Vrel_fchans _ _ _ _ _ HV).
    - done.
    - intros x Hx1 Hx2. apply (Hde x Hx1). rewrite dom_delete_L.
      destruct (decide (x = c)); [clear -e; set_solver|clear -Hx2 n; set_solver].
    - by rewrite <-H2.
    - rewrite (Vrel_fchans _ _ _ _ _ HV). apply (IHi W _ (mdrop ΘB Θ2) (C0 ∖ dom Θ2)); [|exact Hok'|by rewrite <-H1].
      rewrite <-Hsz. by apply (tstep_giving_size _ _ _ Hst).
  Qed.

  Lemma case_slink cd t' :
    tstep t (LSess (SLink cd)) t' → cd ## C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) (PSess (SLink cd)) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (c & d & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & Hdu & Heq & HE').
    assert (c ∉ C0 ∧ d ∉ C0) as [Hc0 Hd0] by (clear -HcC; set_solver).
    pose proof (ΘB_none_of _ _ _ _ _ Hok Hc0) as HBc.
    pose proof (ΘB_none_of _ _ _ _ _ Hok Hd0) as HBd.
    apply tenv_ext_inv in H1 as [Hr1 Ho1]. apply tenv_ext_inv in H2 as [Hr2 Ho2].
    destruct (Σ !! c) as [a|] eqn:HΣc.
    2: { exfalso. destruct (removed_some _ _ _ _ Hr2) as [o Ho]. revert Ho. tlk.
         rewrite HΣc, HBc. simpl. rewrite ounion_None. discriminate. }
    destruct (removed_one _ _ _ _ _ _ Hr2 HΣc HBc) as [Hmc Ha]. subst a.
    assert (c ≠ d) as Hne.
    { intros <-. destruct (removed_some _ _ _ _ Hr1) as [o Ho]. congruence. }
    apply (removed_eq _ (tenv_of Σ ∪ ΘB)) in Hr1; [|symmetry; by apply Ho2].
    destruct (Σ !! d) as [b|] eqn:HΣd.
    2: { exfalso. destruct (removed_some _ _ _ _ Hr1) as [o Ho]. revert Ho. tlk.
         rewrite HΣd, HBd. simpl. rewrite ounion_None. discriminate. }
    destruct (removed_one _ _ _ _ _ _ Hr1 HΣd HBd) as [H1d Hb]. subst b.
    exists c, d, (delete c (delete d Σ)), sc, sd, kc, kd. split_and!; try done.
    - apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc]; [tlk; done|].
      destruct (decide (x = d)) as [->|Hxd]; tlk; done.
    - rewrite dom_delete_L. clear. set_solver.
    - rewrite !dom_delete_L. clear. set_solver.
    - apply (IHi W _ ΘB C0); [| |].
      + rewrite <-Hsz. by apply (tstep_giving_size _ _ _ Hst).
      + eapply tok_sub; [|exact Hok]. etrans; apply delete_subseteq.
      + assert (Θ1 = tenv_of (delete c (delete d Σ)) ∪ ΘB) as <-; [|done].
        apply map_eq. intros x. destruct (decide (x = d)) as [->|Hxd].
        { rewrite H1d. tlk. by rewrite HBd. }
        destruct (decide (x = c)) as [->|Hxc].
        { rewrite Ho1 by done. rewrite Hmc. tlk. by rewrite HBc. }
        rewrite Ho1, Ho2 by done. tlk. done.
  Qed.

  Lemma no_ptau_link C' E' : C' = C0 → ¬ ptau_link (C0, {[+ t +]}) (C', E').
  Proof.
    intros -> Hl. destruct (ptau_link_C _ _ Hl) as (c & Hc & HC). simpl in *.
    assert (c ∈ C0 ∖ {[c]}) as Hc' by (by rewrite <-HC). clear -Hc'. set_solver.
  Qed.

  Lemma case_beta t' :
    tstep t LBeta t' → Pcase n' W Σ T (C0, {[+ t +]}) PTau (C0, {[+ t' +]}).
  Proof.
    intros Hst. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    split; [|intros Hl; exfalso; by eapply no_ptau_link].
    intros _. exists ∅, W. split_and!.
    - apply disjoint_empty_l.
    - apply wext_fresh_refl, HWs.
    - exact (IHo n' T (le_n _) HT W Σ ΘB C0 t' Hok Hc).
  Qed.

  Lemma tok_add_both W' c k1 k2 :
    tok W' Σ ΘB C0 → c ∉ dom Σ → c ∉ C0 → w_eq W' k1.2 k2.2 → sdual k1.1 k2.1 →
    tok W' Σ (<[c := Both k1 k2]> ΘB) (C0 ∪ {[c]}).
  Proof.
    intros [HW Hd Hdj Hb Hdu] HcΣ HcC Hq Hdd. split; try done.
    - by rewrite dom_insert_L, Hd, (comm_L (∪)).
    - clear -Hdj HcΣ. set_solver.
    - intros x o. destruct (decide (x = c)) as [->|Hx]; tlk; [intros [= <-]; eauto|apply Hb].
    - intros x f1 f2. destruct (decide (x = c)) as [->|Hx]; tlk; [intros [= <- <-]; done|apply Hdu].
  Qed.

  Lemma case_new c t' :
    tstep t (LNew c) t' → c ∉ C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) PTau (C0 ∪ {[c]}, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    split.
    2: { intros Hl. exfalso. destruct (ptau_link_C _ _ Hl) as (c' & Hc' & HC). simpl in *.
         assert (c' ∈ C0 ∖ {[c']}) as Hc'' by (rewrite <-HC; clear -Hc'; set_solver).
         clear -Hc''. set_solver. }
    intros Hd. simpl in Hd.
    assert (c ∉ dom Σ) as HcΣ by (clear -Hd; set_solver).
    destruct Hc as (a & s & s' & W' & Hfr & Hdd & Hwf & HE').
    { unfold tenv_of. rewrite dom_union_L, dom_fmap_L, (tok_dom _ _ _ _ Hok). clear -HcΣ HcC. set_solver. }
    exists {[NConst a]}, W'. split_and!; [|done|].
    - pose proof (senv_roots_sub Σ ΘB). clear -Hfr H. set_solver.
    - apply (IHo n' T (le_n _) HT W' Σ (<[c := Both (s, pconst a) (s', pconst a)]> ΘB)).
      + apply tok_add_both; [|done|done| |done].
        * eapply tok_mono; [exact (proj1 Hwf)|exact Hok].
        * apply (wf_eq_refl _ (proj1 (proj2 (proj2 (proj2 (proj1 Hwf)))))).
      + rewrite <-ins_both; [done|]. by apply not_elem_of_dom.
  Qed.

  Lemma case_spawn v t' :
    tstep t (LSpawn v) t' →
    Pcase n' W Σ T (C0, {[+ t +]}) PTau (C0, {[+ t' +]} ⊎ {[+ App v EUnit +]}).
  Proof.
    intros Hst. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    split; [|intros Hl; exfalso; by eapply no_ptau_link].
    intros _. exists ∅, W. split_and!; [apply disjoint_empty_l|apply wext_fresh_refl, HWs|].
    destruct Hc as (Θ1 & Θ2 & ub & lb & Hcomp & HV & HE2).
    destruct (spawn_env W Σ ΘB C0 Θ1 Θ2 Hok Hcomp) as (H2 & H1 & Hok2 & Hok1 & Hcut & HΣ & HC).
    pose proof (IHo n' T (le_n _) HT _ _ _ _ t' Hok2 ltac:(by rewrite <-H2)) as HP1.
    pose proof (IHo n' TUnit (le_n _) prim_unit _ _ _ _ (App v EUnit) Hok1
                  ltac:(rewrite <-H1; exact (Erel_spawned _ _ _ _ _ _ HV HWs))) as HP2.
    pose proof (conn_all n' T HT _ _ _ _ _ _ _ _ _ _ T TUnit ltac:(by left) Hcut HP1 HP2) as HP.
    by rewrite HΣ, HC in HP.
  Qed.

  Lemma case_tlink c d t' :
    tstep t (LSess (SLink {[c; d]})) t' → c ∈ C0 →
    Pcase n' W Σ T (C0, {[+ t +]}) PTau (C0 ∖ {[c]}, {[+ chsubst c d t' +]}).
  Proof.
    intros Hst HcC. pose proof (Erel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc.
    destruct Hc as (c' & d' & Θ1 & Θm & sc & sd & kc & kd & Hcd & H1 & H2 & Hdu & Heq & HE').
    assert (esize t' < m) as Hlt by (rewrite <-Hsz; by apply (tstep_giving_size _ _ _ Hst)).
    assert (Prel (S n') W Σ T (C0 ∖ {[c]}, {[+ chsubst c d t' +]})) as HP.
    { destruct (link_env W Σ ΘB C0 Θm Θ1 c' d' (sc, kc) (sd, kd) c d Hok HcC (eq_sym Hcd)
                  H1 H2 Hdu Heq) as [(<- & HΘ1)|(Hne & Θ' & ΘB' & Hmv & Hcv & Hok')].
      - rewrite chsubst_self. apply (IHi W Σ (delete c ΘB) (C0 ∖ {[c]})); [done|by apply tok_delete|].
        by rewrite <-HΘ1.
      - apply (IHi W Σ ΘB' (C0 ∖ {[c]})); [by rewrite esize_chsubst|done|].
        eapply Erel_econv; [apply HWs|exact Hcv|].
        exact (proj2 (rel_fuse (S n')) W Θ1 Θ' T ∅ t' c d HWs Hne Hmv HE'). }
    simpl. split.
    - intros _. exists ∅, W. split_and!; [apply disjoint_empty_l|apply wext_fresh_refl, HWs|].
      eapply Prel_down; [|exact HP]. lia.
    - intros _ _. exact HP.
  Qed.

  Lemma term_level : Prel (S n') W Σ T (C0, {[+ t +]}).
  Proof.
    pose proof HE as HE0. apply Erel_S_iff in HE0 as (Hval & Hrdy & _).
    assert (irred t → Σ = ∅ ∧ C0 = ∅ ∧ Vrel (S n') W ∅ T t) as Hstop.
    { intros Hirr. pose proof (Hval Hirr) as HV.
      pose proof (Vrel_prim_empty _ _ _ _ _ HT HV) as H0.
      destruct (tok_empty _ _ _ _ Hok H0) as [-> ->]. rewrite H0 in HV. done. }
    assert (¬ irred t → ready_p W Σ (C0, {[+ t +]})) as Hready.
    { intros Hn. destruct Hok as [HW Hd Hdj Hb Hdu].
      eapply (ready_term W Σ ΘB C0 t HW Hd Hdj Hb Hdu).
      all: first [exact (Hrdy Hn)|exact Hn|
        intros σ t' Hst; exact (offered_some _ _ _ _ _ _ _ _ HE Hst)]. }
    apply Prel_S_intro.
    - intros Hirr. destruct (tstep_progress t) as [Hi|(α & t' & Hs)].
      + destruct (Hstop Hi) as (-> & -> & HV). exists t, ∅. split_and!.
        * by rewrite (right_id_L ∅ (⊎)).
        * by eapply Vrel_val.
        * unfold tenv_of. by rewrite fmap_empty.
        * intros e He. exfalso. clear -He. multiset_solver.
      + exfalso. assert (¬ irred t) as Hn by (intros Hi; exact (Hi _ _ Hs)).
        destruct (Hready Hn (λ p' Hp', Hirr _ _ Hp')) as [Ht _].
        destruct (Ht (λ k Hk, match Hk with ex_intro _ σ (ex_intro _ q (conj Hq _)) => Hirr _ _ Hq end))
          as (v & E & Heq & Hv & _).
        injection Heq as _ HE'. assert (v ∈ ({[+ t +]} : gmultiset expr)) as Hin.
        { rewrite HE'. apply gmultiset_elem_of_disj_union. left. by apply gmultiset_elem_of_singleton. }
        apply gmultiset_elem_of_singleton in Hin as Htv. symmetry in Htv.
        rewrite <-Htv in Hv. exact (val_no_tstep _ _ _ Hs Hv).
    - intros Hn. destruct (tstep_progress t) as [Hi|(α & t' & Hs)].
      + exfalso. apply Hn. destruct (Hstop Hi) as (_ & -> & HV). apply vals_pirred.
        intros e He. apply gmultiset_elem_of_singleton in He as ->. by eapply Vrel_val.
      + apply Hready. intros Hi. exact (Hi _ _ Hs).
    - intros π p' Hst.
      destruct (single_step _ _ _ _ Hst) as
        [(σ & t' & -> & Hs & Hsub & ->)|[(t' & -> & Hs & ->)|[(c & t' & -> & Hs & Hc & _ & ->)
        |[(v & t' & -> & Hs & ->)|(c & d & t' & -> & Hs & Hc & ->)]]]].
      + destruct σ as [c w|c w|c|cd]; simpl in Hsub |- *.
        * rewrite difference_empty_L. apply case_recv; [done|clear -Hsub; set_solver].
        * apply case_send; [done|clear -Hsub; set_solver].
        * rewrite difference_empty_L. apply case_close; [done|clear -Hsub; set_solver].
        * rewrite difference_empty_L. by apply case_slink.
      + by apply case_beta.
      + by apply case_new.
      + by apply case_spawn.
      + by apply case_tlink.
  Qed.
End level.

Lemma term_all n : ∀ T, prim T → term_at n T.
Proof.
  induction n as [n IHn] using lt_wf_ind. intros T HT. destruct n as [|n'].
  { intros ? ? ? ? ? _ _. apply Prel_0. }
  assert (IHo : ∀ j T, j ≤ n' → prim T → term_at j T)
    by (intros j T' Hj HT'; apply IHn; [lia|done]).
  assert (∀ m W Σ ΘB C0 t, esize t < m → tok W Σ ΘB C0 →
            Erel (S n') W (tenv_of Σ ∪ ΘB) T ∅ t → Prel (S n') W Σ T (C0, {[+ t +]})) as Hlt.
  { intros m. induction m as [m IHm] using lt_wf_ind. intros W Σ ΘB C0 t Hsz Hok HE.
    exact (term_level n' IHo T HT (esize t)
             (λ W Σ ΘB C0 t' H, IHm (esize t) Hsz W Σ ΘB C0 t' H) W Σ ΘB C0 t eq_refl Hok HE). }
  intros W Σ ΘB C0 t Hok HE. exact (Hlt (S (esize t)) W Σ ΘB C0 t (Nat.lt_succ_diag_r _) Hok HE).
Qed.

(** P-Term (§11). Σ, Θ_B; · ⊨^∅_W t : T with Θ_B holding both ends of
    every channel of C₀ gives Σ ⊨_W (C₀, {t}) : T. The side conditions
    are the spec's implicit well-formedness: W strict, Θ_B holds both
    ends (dual, at aliased points) of exactly the channels of C₀, and
    the interface avoids C₀. *)
Theorem Prel_term W Σ ΘB C0 t T :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  sem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  sem_ptyped W Σ (C0, {[+ t +]}) T.
Proof.
  intros HT HW Hd Hdj Hb Hdu Ht n.
  apply (term_all n T HT W Σ ΘB C0 t); [by split|].
  pose proof (Ht n W ∅ _ Var (wext_refl W HW) (tenv_comp_empty_r _ _) eq_refl) as H.
  by rewrite subst_ids in H.
Qed.

(** ** Independence: P-Connect with an empty cut *)

Theorem Prel_indep W1 W2 Σ1 Σ2 C1 C2 E1 E2 T :
  prim T →
  sem_ptyped W1 Σ1 (C1, E1) T → sem_ptyped W2 Σ2 (C2, E2) TUnit →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  strict (wjoin W1 W2) → world_wf W1 → world_wf W2 → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C2 →
  sem_ptyped (wjoin W1 W2) (Σ1 ∪ Σ2) (C1 ∪ C2, E1 ⊎ E2) T.
Proof.
  intros HT HP1 HP2 H12 H21 HW HW1 HW2 Hd HC1 HC2 HC12.
  rewrite <-(right_id_L ∅ (∪) (C1 ∪ C2)).
  apply (Prel_connect W1 W2 Σ1 Σ2 ∅ ∅ ∅); try done.
  all: first [by rewrite (right_id_L ∅ (∪)) | apply dom_empty_L
             | (intros c e e' H; by rewrite lookup_empty in H)
             | apply map_disjoint_empty_r | apply disjoint_empty_r].
Qed.
