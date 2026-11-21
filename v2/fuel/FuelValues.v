(** * Fuel: values (stage S6, F2, F3, F5, F6)

    - Renamings of maps of ends ([renk_union_split], [renk_union],
      [renk_preimage]) and a fresh renaming by a string prefix that moves
      the ends of an argument out of the way of a closure.
    - F5. [Vfuel_rename] under an injective renaming and [Vfuel_age]
      (aging Γ − c, [tage]: the counters lose c and the credit pays for
      it). The capture of E-Abs is aging ([Vfuel_age] with
      [Vfuel_mono]).
    - F2. [FuelE_val]: a value in [Vfuel] satisfies FuelE.
    - F3. [FuelE_beta]: a head β step in an evaluation context lifts
      FuelE by one level.
    - F6. Values from their parts ([Vfuel_unit], [Vfuel_end],
      [Vfuel_pair], [Vfuel_inj], [Vfuel_pack]), points
      are not read ([Vfuel_pinst]), and a result type that implies
      another ([FuelE_res_mono], [FuelE_thread]). *)

From stdpp Require Import strings.
From GV Require Export fuel.FuelMono.

(** ** Renamings of maps of ends *)

Lemma renk_functional {Y : Type} (g : cend → cend) (m m1 m2 : gmap cend Y) :
  renk g m m1 → renk g m m2 → m1 = m2.
Proof.
  intros [A1 B1] [A2 B2]. apply map_eq. intros o'.
  destruct (m1 !! o') as [v|] eqn:E1.
  - destruct (B1 o' v E1) as (o & -> & Ho). symmetry. by apply A2.
  - destruct (m2 !! o') as [v|] eqn:E2; [|done].
    destruct (B2 o' v E2) as (o & -> & Ho). by rewrite (A1 o v Ho) in E1.
Qed.

Lemma renk_empty {Y : Type} (g : cend → cend) (m' : gmap cend Y) : renk g ∅ m' → m' = ∅.
Proof. intros H. apply (renk_functional g ∅); [done|]. split; intros ? ?; by rewrite lookup_empty. Qed.

Lemma renk_nil {Y : Type} (g : cend → cend) : renk (Y := Y) g ∅ ∅.
Proof. split; intros ? ?; by rewrite lookup_empty. Qed.

Lemma renk_singleton {Y : Type} (g : cend → cend) o (v : Y) m' :
  renk g {[o := v]} m' → m' = {[g o := v]}.
Proof.
  intros H. apply (renk_functional g {[o := v]}); [done|]. split.
  - intros o1 v1 H1. apply lookup_singleton_Some in H1 as [<- <-]. by rewrite lookup_singleton_eq.
  - intros o' v' H'. apply lookup_singleton_Some in H' as [<- <-]. exists o.
    split; [done|by rewrite lookup_singleton_eq].
Qed.

Lemma kinj_elem {Y : Type} (g : cend → cend) (m : gmap cend Y) o1 o2 :
  kinj g m → o1 ∈ dom m → o2 ∈ dom m → g o1 = g o2 → o1 = o2.
Proof. intros Hk [v1 H1]%elem_of_dom [v2 H2]%elem_of_dom. exact (Hk o1 o2 v1 v2 H1 H2). Qed.

Lemma renk_union {Y : Type} (g : cend → cend) (m1 m2 m1' m2' : gmap cend Y) :
  kinj g (m1 ∪ m2) → renk g m1 m1' → renk g m2 m2' → renk g (m1 ∪ m2) (m1' ∪ m2').
Proof.
  intros Hk [A1 B1] [A2 B2]. split.
  - intros o v Ho. apply lookup_union_Some_raw in Ho as [Ho|[Hn Ho]].
    + apply lookup_union_Some_l. by apply A1.
    + apply lookup_union_Some_raw. right. split; [|by apply A2].
      destruct (m1' !! g o) as [v1|] eqn:E; [|done].
      destruct (B1 _ _ E) as (o1 & Heq & Ho1). exfalso.
      assert (o1 = o) as ->.
      { apply (Hk o1 o v1 v); [by apply lookup_union_Some_l| |done].
        apply lookup_union_Some_raw. by right. }
      congruence.
  - intros o' v Ho'. apply lookup_union_Some_raw in Ho' as [Ho'|[Hn Ho']].
    + destruct (B1 _ _ Ho') as (o & -> & Ho). exists o. split; [done|]. by apply lookup_union_Some_l.
    + destruct (B2 _ _ Ho') as (o & -> & Ho). exists o. split; [done|].
      apply lookup_union_Some_raw. right. split; [|done].
      destruct (m1 !! o) as [v1|] eqn:E; [|done]. by rewrite (A1 o v1 E) in Hn.
Qed.

Lemma renk_union_split {Y : Type} (g : cend → cend) (m1 m2 m' : gmap cend Y) :
  kinj g (m1 ∪ m2) → m1 ##ₘ m2 → renk g (m1 ∪ m2) m' →
  ∃ m1' m2', m' = m1' ∪ m2' ∧ renk g m1 m1' ∧ renk g m2 m2' ∧ m1' ##ₘ m2'.
Proof.
  intros Hk Hd Hr.
  assert (kinj g m1) as Hk1 by (apply (kinj_dom g (m1 ∪ m2)); [rewrite dom_union_L; set_solver|done]).
  assert (kinj g m2) as Hk2 by (apply (kinj_dom g (m1 ∪ m2)); [rewrite dom_union_L; set_solver|done]).
  destruct (renk_exists g m1 Hk1) as [m1' H1]. destruct (renk_exists g m2 Hk2) as [m2' H2].
  exists m1', m2'. split_and!; [|done|done|].
  - eapply renk_functional; [exact Hr|by apply renk_union].
  - apply map_disjoint_dom. rewrite (renk_dom _ _ _ H1), (renk_dom _ _ _ H2).
    intros o' Ho1 Ho2.
    apply elem_of_map in Ho1 as (o1 & -> & Ho1). apply elem_of_map in Ho2 as (o2 & Heq & Ho2).
    assert (o1 = o2) as <-.
    { apply (kinj_elem g (m1 ∪ m2)); [done|rewrite dom_union_L; set_solver|rewrite dom_union_L; set_solver|done]. }
    apply map_disjoint_dom in Hd. by apply (Hd o1).
Qed.

Lemma renk_ext {Y : Type} (g g' : cend → cend) (m m' : gmap cend Y) :
  (∀ o, o ∈ dom m → g' o = g o) → renk g m m' → renk g' m m'.
Proof.
  intros He [A B]. split.
  - intros o v Ho. rewrite He by (by eapply elem_of_dom_2). by apply A.
  - intros o' v Ho'. destruct (B o' v Ho') as (o & -> & Ho). exists o.
    rewrite He by (by eapply elem_of_dom_2). done.
Qed.

Lemma kinj_ext {Y : Type} (g g' : cend → cend) (m : gmap cend Y) :
  (∀ o, o ∈ dom m → g' o = g o) → kinj g m → kinj g' m.
Proof.
  intros He Hk o1 o2 v1 v2 H1 H2. rewrite !He by (by eapply elem_of_dom_2). exact (Hk o1 o2 v1 v2 H1 H2).
Qed.

(** The inverse of an injective renaming h, on the renamed map. *)
Lemma renk_inv {Y : Type} (h g' : cend → cend) (m m0 : gmap cend Y) :
  (∀ o, g' (h o) = o) → renk h m m0 → renk g' m0 m.
Proof.
  intros Hi [A B]. split.
  - intros o0 v Ho0. destruct (B o0 v Ho0) as (o & -> & Ho). by rewrite Hi.
  - intros o v Ho. exists (h o). rewrite Hi. split; [done|]. by apply A.
Qed.

(** A map on the preimage of a renamed map. *)
Lemma renk_preimage {Y Z : Type} (g : cend → cend) (π π' : gmap cend Y) (φ' : gmap cend Z) :
  renk g π π' → dom φ' = dom π' → ∃ φ, dom φ = dom π ∧ renk g φ φ'.
Proof.
  intros [A B] Hd. exists (map_imap (λ o _, φ' !! g o) π). split.
  - apply set_eq. intros o. rewrite !elem_of_dom, map_lookup_imap.
    destruct (π !! o) as [k|] eqn:E; simpl; [|split; intros []; done].
    split; [intros _; by exists k|]. intros _.
    assert (g o ∈ dom φ') as Hin by (rewrite Hd; eapply elem_of_dom_2; by apply A).
    by apply elem_of_dom in Hin.
  - split.
    + intros o f Ho. rewrite map_lookup_imap in Ho. destruct (π !! o); simpl in Ho; done.
    + intros o' f Ho'. assert (o' ∈ dom π') as [k Hk]%elem_of_dom by (rewrite <-Hd; by eapply elem_of_dom_2).
      destruct (B o' k Hk) as (o & -> & Ho). exists o. split; [done|].
      by rewrite map_lookup_imap, Ho.
Qed.

Lemma renk_fmap {Y Z : Type} (f : Y → Z) (g : cend → cend) (m m' : gmap cend Y) :
  renk g m m' → renk g (f <$> m) (f <$> m').
Proof.
  intros [A B]. split.
  - intros o v Ho. apply lookup_fmap_Some in Ho as (v0 & <- & Ho). rewrite lookup_fmap, (A o v0 Ho). done.
  - intros o' v Ho'. apply lookup_fmap_Some in Ho' as (v0 & <- & Ho').
    destruct (B o' v0 Ho') as (o & -> & Ho). exists o. by rewrite lookup_fmap, Ho.
Qed.

(** ** A fresh renaming by a prefix

    [eprefix s] prepends s to the channel of an end, [eunfix s g] undoes
    it and renames every other end by g. s is longer than every channel
    in sight, so the two agree with g there. *)

Fixpoint unprefix (s c : string) : option string :=
  match s, c with
  | EmptyString, _ => Some c
  | String a s', String b c' => if Ascii.ascii_dec a b then unprefix s' c' else None
  | String _ _, EmptyString => None
  end.

Lemma unprefix_app s c : unprefix s (String.append s c) = Some c.
Proof. induction s as [|a s IH]; simpl; [done|]. by destruct (Ascii.ascii_dec a a). Qed.

Lemma unprefix_short s c : String.length c < String.length s → unprefix s c = None.
Proof.
  revert c. induction s as [|a s IH]; intros [|b c]; simpl; try lia; try done.
  intros H. destruct (Ascii.ascii_dec a b); [apply IH; lia|done].
Qed.

Lemma slen_app a b : String.length (String.append a b) = String.length a + String.length b.
Proof. induction a as [|x a IH]; simpl; [done|]. by rewrite IH. Qed.

Definition slonger (X : gset chan) : string :=
  String.append (foldr String.append "" (elements X)) "x".

Lemma slonger_spec X c : c ∈ X → String.length c < String.length (slonger X).
Proof.
  intros Hc. apply elem_of_elements in Hc. unfold slonger. rewrite slen_app. simpl.
  enough (String.length c ≤ String.length (foldr String.append "" (elements X))) by lia.
  induction (elements X) as [|c' l IH]; simpl; [by apply elem_of_nil in Hc|].
  rewrite slen_app. apply elem_of_cons in Hc as [->|Hc]; [lia|]. specialize (IH Hc). lia.
Qed.

Definition eprefix (s : string) : cend → cend := cmap (String.append s).

Definition eunfix (s : string) (g : cend → cend) (o : cend) : cend :=
  match o with
  | EPos c => match unprefix s c with Some c0 => EPos c0 | None => g o end
  | ENeg c => match unprefix s c with Some c0 => ENeg c0 | None => g o end
  end.

Lemma eunfix_prefix s g o : eunfix s g (eprefix s o) = o.
Proof. destruct o; simpl; by rewrite unprefix_app. Qed.

Lemma eunfix_short s g o : String.length (ech o) < String.length s → eunfix s g o = g o.
Proof. destruct o; simpl; intros H; by rewrite unprefix_short. Qed.

Lemma eprefix_inj s o1 o2 : eprefix s o1 = eprefix s o2 → o1 = o2.
Proof.
  intros H. rewrite <-(eunfix_prefix s id o1), <-(eunfix_prefix s id o2). by rewrite H.
Qed.

Lemma kinj_eprefix {Y : Type} (s : string) (m : gmap cend Y) : kinj (eprefix s) m.
Proof. intros o1 o2 v1 v2 _ _. apply eprefix_inj. Qed.

Lemma eprefix_len s o : String.length s ≤ String.length (ech (eprefix s o)).
Proof. destruct o; simpl; rewrite slen_app; lia. Qed.

Lemma emap_ext_fends (g h : cend → cend) e : (∀ o, o ∈ fends e → g o = h o) → emap g e = emap h e.
Proof. induction e; simpl; intros H; f_equal; auto; set_solver. Qed.

(** ** F5: values under injective renamings *)

Section rename.
  Context (n : Ix).
  Context (IH : ∀ j, olt j n → ∀ N σ Π φ v (g : cend → cend) Π' φ',
    kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
    v ∈ FV^N _ j⟦σ⟧(Π, φ) → emap g v ∈ FV^N _ j⟦σ⟧(Π', φ')).

  (** The closure clause, renamed. The argument is moved out of the way
      of the closure's ends by [eprefix], the body runs there and is
      renamed back by [eunfix]. *)
  Lemma Vty_arr_rename N c a T1 U e (Π : penv) (φ : cenv) (g : cend → cend) (Π' : penv) (φ' : cenv) :
    kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' → dom Π = dom φ →
    (∀ j φ1 Πu φu u, olt j n → dom φ1 = dom φ →
       (∀ o f f', φ !! o = Some f → φ1 !! o = Some f' → f'.2 = f.2 ∧ fle (fsub f.1 a) f'.1) →
       Π ##ₘ Πu → φ1 ##ₘ φu →
       u ∈ FV^N _ j⟦RTy T1⟧(Πu, φu) →
       subst1 u e ∈ F^N _ j⟦RTy U ▷ c⟧(Π ∪ Πu, φ1 ∪ φu)) →
    ∀ j φ1 Πu φu u, olt j n → dom φ1 = dom φ' →
      (∀ o f f', φ' !! o = Some f → φ1 !! o = Some f' → f'.2 = f.2 ∧ fle (fsub f.1 a) f'.1) →
      Π' ##ₘ Πu → φ1 ##ₘ φu →
      u ∈ FV^N _ j⟦RTy T1⟧(Πu, φu) →
      subst1 u (emap g e) ∈ F^N _ j⟦RTy U ▷ c⟧(Π' ∪ Πu, φ1 ∪ φu).
  Proof.
    intros Hk1 Hk2 HΠ Hφ HdΠφ HF j φ1 Πu φu u Hj Hd1 Hh HdΠ Hdφ Hu.
    set (s := slonger (set_map ech (fends e ∪ dom Π ∪ dom φ))).
    assert (Hshort : ∀ o, o ∈ fends e ∪ dom Π ∪ dom φ → String.length (ech o) < String.length s).
    { intros o Ho. apply slonger_spec. apply elem_of_map. by exists o. }
    set (g' := eunfix s g).
    assert (Hg' : ∀ o, o ∈ fends e ∪ dom Π ∪ dom φ → g' o = g o) by (intros; by apply eunfix_short, Hshort).
    destruct (renk_exists (eprefix s) Πu (kinj_eprefix s Πu)) as [Πu0 HΠu].
    destruct (renk_exists (eprefix s) φu (kinj_eprefix s φu)) as [φu0 Hφu].
    destruct (renk_preimage g φ φ' φ1 Hφ Hd1) as (φ0 & Hd0 & Hφ0).
    assert (Hfar : ∀ o, o ∈ dom Π ∪ dom φ → ∀ o', o ≠ eprefix s o').
    { intros o Ho o' ->. assert (Hs := Hshort (eprefix s o') ltac:(set_solver)).
      pose proof (eprefix_len s o'). lia. }
    assert (Hd0u : φ0 ##ₘ φu0).
    { apply map_disjoint_dom. rewrite Hd0, (renk_dom _ _ _ Hφu). intros o Ho Ho'.
      apply elem_of_map in Ho' as (o' & -> & _). by apply (Hfar (eprefix s o') ltac:(set_solver) o'). }
    assert (HdΠu0 : Π ##ₘ Πu0).
    { apply map_disjoint_dom. rewrite (renk_dom _ _ _ HΠu). intros o Ho Ho'.
      apply elem_of_map in Ho' as (o' & -> & _). by apply (Hfar (eprefix s o') ltac:(set_solver) o'). }
    assert (HF0 : subst1 (emap (eprefix s) u) e ∈ F^N _ j⟦RTy U ▷ c⟧(Π ∪ Πu0, φ0 ∪ φu0)).
    { apply HF; try done.
      - intros o f f' Ho Ho'. apply (Hh (g o)); [by apply (proj1 Hφ)|by apply (proj1 Hφ0)].
      - apply (IH j Hj N (RTy T1) Πu φu u); [apply kinj_eprefix|apply kinj_eprefix|done|done|done]. }
    (* rename back *)
    assert (Hinv : ∀ o, g' (eprefix s o) = o) by (intros; apply eunfix_prefix).
    assert (HkΠ : kinj g' (Π ∪ Πu0)).
    { apply kinj_union.
      - apply (kinj_ext g); [intros o Ho; apply Hg'; set_solver|done].
      - intros o1 o2 v1 v2 H1 H2.
        destruct (proj2 HΠu o1 v1 H1) as (p1 & -> & _). destruct (proj2 HΠu o2 v2 H2) as (p2 & -> & _).
        by rewrite !Hinv => ->.
      - intros o1 o2 Ho1 Ho2 Heq. rewrite Hg' in Heq by set_solver.
        rewrite (renk_dom _ _ _ HΠu) in Ho2. apply elem_of_map in Ho2 as (p & -> & Hp).
        rewrite Hinv in Heq. apply map_disjoint_dom in HdΠ. apply (HdΠ p); [|done].
        rewrite (renk_dom _ _ _ HΠ). apply elem_of_map. by exists o1. }
    assert (Hkφ : kinj g' (φ0 ∪ φu0)).
    { apply (kinj_dom g' (Π ∪ Πu0)); [|done].
      rewrite !dom_union_L, Hd0, (renk_dom _ _ _ Hφu), (renk_dom _ _ _ HΠu), HdΠφ, (Vfuel_dom _ _ _ _ _ _ Hu).
      done. }
    assert (HrΠ : renk g' (Π ∪ Πu0) (Π' ∪ Πu)).
    { apply renk_union; [done| |by apply (renk_inv (eprefix s))].
      apply (renk_ext g); [intros o Ho; apply Hg'; set_solver|done]. }
    assert (Hrφ : renk g' (φ0 ∪ φu0) (φ1 ∪ φu)).
    { apply renk_union; [done| |by apply (renk_inv (eprefix s))].
      apply (renk_ext g); [|done]. intros o Ho. apply Hg'. rewrite Hd0 in Ho. set_solver. }
    pose proof (FuelE_rename _ _ _ _ _ _ _ g' _ _ HkΠ Hkφ HrΠ Hrφ HF0) as HR.
    rewrite emap_subst1, emap_emap in HR.
    rewrite (emap_ext (g' ∘ eprefix s) id) in HR by (intros o; apply eunfix_prefix).
    rewrite emap_id in HR.
    rewrite (emap_ext_fends g' g e) in HR; [done|].
    intros o Ho. apply Hg'. set_solver.
  Qed.

  Lemma Vty_rename N T Π φ v (g : cend → cend) Π' φ' :
    kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T Π φ v →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T Π' φ' (emap g v).
  Proof.
    revert Π φ v Π' φ'.
    induction T as [|ub lb c T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c U IHU|s x a mt|lb m C T1 IHT];
      intros Π φ v Π' φ' Hk1 Hk2 HΠ Hφ; simpl.
    - intros (-> & -> & ->). split_and!; [done|by apply (renk_empty g)|by apply (renk_empty g)].
    - intros (e & -> & Hx & Hd & Hf & H). exists (emap g e). split_and!; [done|by rewrite fends_emap, Hx, (renk_dom _ _ _ HΠ)| | |].
      + by rewrite (renk_dom _ _ _ HΠ), (renk_dom _ _ _ Hφ), Hd.
      + intros o' f Ho' Hi. destruct (proj2 Hφ o' f Ho') as (o & -> & Ho). apply (Hf o f Ho).
        intros (S0 & HS0 & HS). apply Hi. exists S0. split; [by apply (proj1 HΠ)|done].
      + intros j φ1 Πu φu u Hj Hd1.
        eapply (Vty_arr_rename N c a T1 U e Π φ g Π' φ'); try done.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & H1 & H2).
      destruct (renk_union_split g Π1 Π2 Π' Hk1 HdΠ HΠ) as (Π1' & Π2' & -> & R1 & R2 & Hd').
      destruct (renk_union_split g φ1 φ2 φ' Hk2 Hdφ Hφ) as (φ1' & φ2' & -> & Q1 & Q2 & Hd'').
      exists (emap g v1), (emap g v2), Π1', Π2', φ1', φ2'. split_and!; try done.
      + apply (IH1 Π1 φ1); try done.
        * apply (kinj_dom g (Π1 ∪ Π2)); [rewrite dom_union_L; set_solver|done].
        * apply (kinj_dom g (φ1 ∪ φ2)); [rewrite dom_union_L; set_solver|done].
      + apply (IH2 Π2 φ2); try done.
        * apply (kinj_dom g (Π1 ∪ Π2)); [rewrite dom_union_L; set_solver|done].
        * apply (kinj_dom g (φ1 ∪ φ2)); [rewrite dom_union_L; set_solver|done].
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists (emap g v'); split; try done;
        [by apply (IH1 Π φ)|by apply (IH2 Π φ)].
    - intros (e & -> & Hx & -> & -> & H). rewrite (renk_empty g Π'), (renk_empty g φ') by done.
      exists (emap g e). split_and!; [done|by rewrite fends_emap, Hx, set_map_empty|done|done|].
      intros j ss Hj Hl Hs. specialize (H j ss Hj Hl Hs).
      pose proof (FuelE_rename _ _ _ _ _ _ _ g ∅ ∅ (kinj_nil g) (kinj_nil g)
        (renk_nil g) (renk_nil g) H) as HR.
      by rewrite emap_subst1 in HR.
    - intros (o & S' & f & -> & -> & -> & Hs & Hf).
      exists (g o), S', f. split_and!; [done|by apply renk_singleton|by apply renk_singleton|done|done].
    - intros H. by apply (IHT Π φ).
  Qed.
End rename.

Lemma Vfuel_rename n : ∀ N σ Π φ v (g : cend → cend) Π' φ',
  kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
  v ∈ FV^N _ n⟦σ⟧(Π, φ) → emap g v ∈ FV^N _ n⟦σ⟧(Π', φ').
Proof.
  induction n as [n IH] using oind.
  intros N σ Π φ v g Π' φ' Hk1 Hk2 HΠ Hφ. rewrite !Vfuel_eq. destruct σ as [T|]; simpl.
  - apply Vty_rename; [exact IH|done..].
  - intros [-> ->]. split; [by apply (renk_empty g)|by apply (renk_empty g)].
Qed.

(** ** F2: values *)

Lemma FuelE_val N n σ d Π φ v :
  is_val v → v ∈ FV^N _ n⟦σ⟧(Π, φ) → v ∈ F^N _ n⟦σ ▷ d⟧(Π, φ).
Proof.
  intros Hv HV.
  apply FuelE_eq. intros g Π' φ' Hk1 Hk2 HΠ Hφ. split.
  - intros _. apply Vfuel_eq. by eapply Vfuel_rename.
  - intros α e' Hst. exfalso. eapply val_no_tstep; [exact Hst|]. by rewrite is_val_emap.
Qed.

(** ** Evaluation contexts *)

Abbreviation ectx := (list frame).

Fixpoint efill (K : ectx) (e : expr) : expr :=
  match K with [] => e | f :: K' => fill_frame f (efill K' e) end.

Definition kemap (g : cend → cend) (K : ectx) : ectx := frame_emap g <$> K.

(** Right-of-value frames hold values. *)
Definition ectx_ok (K : ectx) : Prop := Forall frame_val K.

Lemma emap_efill (g : cend → cend) K e : emap g (efill K e) = efill (kemap g K) (emap g e).
Proof. induction K as [|f K IH]; simpl; [done|]. rewrite <-IH. by destruct f. Qed.

Lemma kemap_kemap (g h : cend → cend) K : kemap g (kemap h K) = kemap (g ∘ h) K.
Proof.
  induction K as [|f K IH]; simpl; [done|]. rewrite IH. f_equal.
  destruct f; simpl; by rewrite ?emap_emap.
Qed.

Lemma ectx_ok_emap (g : cend → cend) K : ectx_ok K → ectx_ok (kemap g K).
Proof.
  induction 1 as [|f K Hf HK IH]; simpl; constructor; [|done].
  destruct f; simpl in *; try done; by rewrite is_val_emap.
Qed.

Lemma efill_not_val K e : ¬ is_val e → ¬ is_val (efill K e).
Proof.
  intros Hv. induction K as [|f K IH]; simpl; [done|].
  destruct f; simpl; first [exact IH | intros [] | intros H; apply andb_True in H as [? ?]; done].
Qed.

Lemma tstep_efill_inv K e α E' :
  ectx_ok K → ¬ is_val e → tstep (efill K e) α E' → ∃ e', tstep e α e' ∧ E' = efill K e'.
Proof.
  intros HK Hv. revert E'. induction HK as [|f K Hf HK IH]; simpl; intros E' Hst; [by exists E'|].
  destruct (tstep_fill_inv f (efill K e) α E' Hf (efill_not_val K e Hv) Hst) as (e'' & Hst' & ->).
  destruct (IH e'' Hst') as (e' & He' & ->). by exists e'.
Qed.

(** ** F3: β-expansion *)

Lemma head_beta_emap (g : cend → cend) e e' :
  head_step e LBeta e' → head_step (emap g e) LBeta (emap g e').
Proof.
  inversion 1; subst; simpl; rewrite ?emap_subst1, ?emap_subst2; simpl;
    constructor; by rewrite ?is_val_emap.
Qed.

(** A head β redex has one step. *)
Lemma head_beta_det e e' α e2 : head_step e LBeta e' → tstep e α e2 → α = LBeta ∧ e2 = e'.
Proof.
  intros Hh Hst. apply tstep_inv in Hst as [Hh2|(f & e0 & e0' & Hf & -> & -> & Hs)].
  - inversion Hh; subst; inversion Hh2; subst; done.
  - exfalso. eapply val_no_tstep; [exact Hs|]. by eapply head_redex_val.
Qed.

Lemma head_not_val e α e' : head_step e α e' → ¬ is_val e.
Proof. intros H Hv. by eapply val_head_step. Qed.

(** A head β step in an evaluation context: FuelE of the successor at
    every level below n gives FuelE of the redex at level n. *)
Lemma FuelE_beta N n σ d Π φ K e e' :
  ectx_ok K → head_step e LBeta e' →
  (∀ j, olt j n → efill K e' ∈ F^N _ j⟦σ ▷ d⟧(Π, φ)) → efill K e ∈ F^N _ n⟦σ ▷ d⟧(Π, φ).
Proof.
  intros HK Hh HF. apply FuelE_eq. intros g Π' φ' Hk1 Hk2 HΠ Hφ.
  pose proof (head_not_val _ _ _ Hh) as Hnv.
  assert (Hnv' : ¬ is_val (emap g e)) by (by rewrite is_val_emap).
  assert (HK' := ectx_ok_emap g K HK).
  pose proof (head_beta_emap g _ _ Hh) as Hh'.
  rewrite emap_efill. split.
  - intros Hv. exfalso. exact (efill_not_val _ _ Hnv' Hv).
  - intros α e2 Hst. destruct (tstep_efill_inv _ _ _ _ HK' Hnv' Hst) as (e3 & Hst3 & ->).
    destruct (head_beta_det _ _ _ _ Hh' Hst3) as [-> ->]. simpl. unfold f_beta.
    rewrite <-emap_efill. intros j Hj. by eapply FuelE_rename; [..|apply HF].
Qed.

(** ** F5: counters and credits *)

(** [fadd (Some 0) a] after [simpl]. *)
Ltac fix0 :=
  repeat match goal with
  | |- context [match ?a with Some n0 => Some n0 | None => None end] =>
      replace (match a with Some n0 => Some n0 | None => None end) with a by (by destruct a)
  | |- context [fadd (Some 0) ?a] => rewrite (fadd_0_l a)
  end.

Section credits.
  Context (El : Ix → epred) (Vl : Ix → vpred).

  (** A type without ends holds no end and reads no counter. *)
  Lemma Vty_tfree N n T : tfree T → ∀ Π φ v,
    Vty N El Vl n T Π φ v → Π = ∅ ∧ φ = ∅ ∧ Vty N El Vl n T ∅ ∅ v.
  Proof.
    induction 1 as [| m k C ub c U|T1 T2 H1 IH1 H2 IH2|T1 T2 H1 IH1 H2 IH2];
      intros Π φ v; simpl.
    - intros (-> & -> & ->). by split_and!.
    - intros (e & -> & Hx & -> & -> & H). split_and!; [done|done|]. exists e. by split_and!.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hv1 & Hv2).
      destruct (IH1 _ _ _ Hv1) as (-> & -> & Hv1'). destruct (IH2 _ _ _ Hv2) as (-> & -> & Hv2').
      rewrite !map_empty_union. split_and!; [done|done|].
      exists v1, v2, ∅, ∅, ∅, ∅. rewrite !map_empty_union.
      split_and!; try done; try apply map_disjoint_empty_l.
    - intros [(v' & -> & Hv)|(v' & -> & Hv)].
      + destruct (IH1 _ _ _ Hv) as (-> & -> & Hv'). split_and!; [done|done|].
        left. exists v'. split; [done|apply Hv'].
      + destruct (IH2 _ _ _ Hv) as (-> & -> & Hv'). split_and!; [done|done|].
        right. exists v'. split; [done|apply Hv'].
  Qed.

  Lemma map_split_dom (φ1 φ2 φ' : cenv) :
    φ1 ##ₘ φ2 → dom φ' = dom (φ1 ∪ φ2) →
    φ' = mres (dom φ1) φ' ∪ mres (dom φ2) φ' ∧ mres (dom φ1) φ' ##ₘ mres (dom φ2) φ' ∧
    dom (mres (dom φ1) φ') = dom φ1 ∧ dom (mres (dom φ2) φ') = dom φ2.
  Proof.
    intros Hd Hdom. rewrite dom_union_L in Hdom. apply map_disjoint_dom in Hd. split_and!.
    - apply map_eq. intros o. rewrite lookup_union, !lookup_mres.
      destruct (φ' !! o) eqn:E.
      + assert (o ∈ dom φ') as Ho by (by apply elem_of_dom_2 in E). rewrite Hdom in Ho.
        repeat case_decide; simpl; try done; set_solver.
      + repeat case_decide; done.
    - apply map_disjoint_dom. rewrite !dom_mres. set_solver.
    - rewrite dom_mres. set_solver.
    - rewrite dom_mres. set_solver.
  Qed.

  Definition fminus (c : fuel) (p : fuel * fuel) : fuel * fuel := (fsub p.1 c, p.2).

  Lemma fle_fsub_mono a f c : fle a f → fle (fsub a c) (fsub f c).
  Proof. destruct a, f, c; simpl; lia. Qed.

  Lemma fle_fsub_add h a c f : fle c a → fle (fadd h a) f → fle (fadd h (fsub a c)) (fsub f c).
  Proof. destruct h, a, c, f; simpl; lia. Qed.

  (** F5, aging Γ − c: every counter of the value loses c units, and the
      aged type of [tage] still holds. An end and a closure pay c from
      their credit, an idle end loses c truncated at 0. *)
  Lemma Vty_age N n c T T' Π φ v :
    tage c T T' → Vty N El Vl n T Π φ v → Vty N El Vl n T' Π (fminus c <$> φ) v.
  Proof.
    intros Ha. revert Π φ v.
    induction Ha as [T Hf|S x a mt Hle|S x a mt Hi|ub lb c0 T U a Hca
                    |T1 T2 T1' T2' H1 IH1 H2 IH2|T1 T2 T1' T2' H1 IH1 H2 IH2|lb m C T T' H1 IH1];
      intros Π φ v; simpl.
    - intros Hv. destruct (Vty_tfree _ _ _ Hf _ _ _ Hv) as (-> & -> & Hv'). by rewrite fmap_empty.
    - intros (o & S' & f & -> & -> & -> & Hs & Hf). exists o, S', (fsub f c).
      split_and!; try done; [by rewrite map_fmap_singleton|by apply fle_fsub_mono].
    - intros (o & S' & f & -> & -> & -> & Hs & Hf). exists o, S', (fsub f c).
      split_and!; try done; [by rewrite map_fmap_singleton|by apply fle_fsub_mono].
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|by rewrite dom_fmap_L| |].
      + intros o f Ho Hi. apply lookup_fmap_Some in Ho as (f0 & <- & Ho).
        apply fle_fsub_mono. by apply (Hf o f0).
      + intros j φ1 Πu φu u Hj Hd1 Hh1. apply H; [done|by rewrite Hd1, dom_fmap_L|].
        intros o f f' Ho Ho'. destruct (Hh1 o (fminus c f) f') as [E Hle]; [by rewrite lookup_fmap, Ho|done|].
        split; [done|]. eapply fle_trans; [by apply fsub_age|exact Hle].
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hv1 & Hv2).
      exists v1, v2, Π1, Π2, (fminus c <$> φ1), (fminus c <$> φ2). split_and!; try done.
      + by apply map_disjoint_fmap.
      + by rewrite map_fmap_union.
      + by apply IH1.
      + by apply IH2.
    - intros [(v' & -> & Hv)|(v' & -> & Hv)]; [left|right]; exists v'; split; try done;
        [by apply IH1|by apply IH2].
    - intros Hv. by apply IH1.
  Qed.
End credits.

Lemma Vfuel_age N n c T T' Π φ v :
  tage c T T' → v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → v ∈ FV^N _ n⟦RTy T'⟧(Π, fminus c <$> φ).
Proof. rewrite !Vfuel_eq. simpl. apply Vty_age. Qed.

(** ** F6: values from their parts *)

Lemma Vfuel_unit N n : EUnit ∈ FV^N _ n⟦RTy TUnit⟧(∅, ∅).
Proof. rewrite Vfuel_eq. simpl. by split_and!. Qed.

Lemma Vfuel_pair N n T1 T2 Π1 Π2 φ1 φ2 u v :
  Π1 ##ₘ Π2 → φ1 ##ₘ φ2 →
  u ∈ FV^N _ n⟦RTy T1⟧(Π1, φ1) → v ∈ FV^N _ n⟦RTy T2⟧(Π2, φ2) →
  Pair u v ∈ FV^N _ n⟦RTy (TProd T1 T2)⟧(Π1 ∪ Π2, φ1 ∪ φ2).
Proof. rewrite !Vfuel_eq. simpl. intros. exists u, v, Π1, Π2, φ1, φ2. by split_and!. Qed.

Lemma Vfuel_inj (i : bool) N n T1 T2 Π φ u :
  u ∈ FV^N _ n⟦RTy (if i then T2 else T1)⟧(Π, φ) →
  Inj i u ∈ FV^N _ n⟦RTy (TSum T1 T2)⟧(Π, φ).
Proof. rewrite !Vfuel_eq. simpl. intros. destruct i; [right|left]; eauto. Qed.

Lemma Vfuel_pack N n lb m C T Π φ v :
  v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → v ∈ FV^N _ n⟦RTy (TEx lb m C T)⟧(Π, φ).
Proof. by rewrite !Vfuel_eq. Qed.

(** ** Result types *)

(** A result type whose values are values of another. *)
Lemma FuelE_res_mono n : ∀ N σ σ' d Π φ e,
  (∀ m Π φ v, ole m n → v ∈ FV^N _ m⟦σ⟧(Π, φ) → v ∈ FV^N _ m⟦σ'⟧(Π, φ)) →
  e ∈ F^N _ n⟦σ ▷ d⟧(Π, φ) → e ∈ F^N _ n⟦σ' ▷ d⟧(Π, φ).
Proof.
  induction n as [n IH] using oind; intros N σ σ' d Π φ e Hσ H.
  apply FuelE_eq. apply FuelE_eq in H. intros g Π' φ' Hk1 Hk2 HΠ Hφ.
  destruct (H g Π' φ' Hk1 Hk2 HΠ Hφ) as [Hv Hs].
  assert (IHj : ∀ j, olt j n → ∀ d Π φ e,
    e ∈ F^N _ j⟦σ ▷ d⟧(Π, φ) → e ∈ F^N _ j⟦σ' ▷ d⟧(Π, φ)).
  { intros j Hj d0 Π0 φ0 e0 He. apply (IH j Hj _ σ); [|done].
    intros m Π1 φ1 v Hm. apply Hσ. exact (ole_trans _ _ _ Hm (olt_ole _ _ Hj)). }
  assert (IHn : ∀ d Π φ e, (∀ j, olt j n → e ∈ F^N _ j⟦σ ▷ d⟧(Π, φ)) →
    ∀ j, olt j n → e ∈ F^N _ j⟦σ' ▷ d⟧(Π, φ)) by (intros; apply IHj; auto).
  split.
  { intros Hval. pose proof (Hv Hval) as HV.
    apply Vfuel_eq. apply Hσ; [apply ole_refl|]. by apply Vfuel_eq. }
  intros α e' Hst. specialize (Hs α e' Hst).
  destruct α as [|ℓ c|κ o c|v|[o w|o w|o|o i|o i|os]]; simpl in Hs |- *;
    unfold f_beta, f_new, f_new_at, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link in *.
  - by apply IHn.
  - intros Hf. destruct (Hs Hf) as [Sn HS]. exists Sn. by apply IHn.
  - destruct Hs as (p & Hp & Hs). exists p. split; [done|].
    intros Hf. destruct (Hs Hf) as [Sn HS]. exists Sn. by apply IHn.
  - destruct Hs as (H1 & H2 & H3 & H4). split_and!; auto.
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3 & H4 & H5 & H6).
    split; [done|]. exists S0, m, T, Sc. split_and!; auto.
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3).
    split; [done|]. exists S0, m, T, Sc. split_and!; [done|done|].
    intros j Πi φi Hj HΠi Hφi Hw.
    apply (IHj j Hj). by apply H3.
  - destruct Hs as (Ha & S0 & H1 & H2 & H3). split; [done|]. exists S0. split_and!; auto.
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|]. exists S0, S1, S2. split_and!; auto.
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|]. exists S0, S1, S2. split_and!; auto.
  - destruct Hs as (H0 & H1 & H2 & H3). split_and!; auto.
Qed.

(** A result of a [tfree] type holds no end, so FuelE at it is FuelE of a thread
    once the frame is dropped. *)
Lemma FuelE_thread N n T d Π φ e :
  tfree T → e ∈ F^N _ n⟦RTy T ▷ d⟧(Π, φ) → FuelT N n Π φ e.
Proof.
  intros Hp H. eapply FuelE_res_mono; [|eapply FuelE_mono; [apply cle_refl|apply fle_inf|exact H]].
  intros m Π0 φ0 v _. rewrite !Vfuel_eq. simpl. intros Hv.
  by destruct (Vty_tfree _ _ _ _ _ Hp _ _ _ Hv) as (-> & -> & _).
Qed.

(** ** Points are not read *)

Lemma pinst_sinst_comm ρ σ T : pinst_ty ρ (sinst_ty σ T) = sinst_ty σ (pinst_ty ρ T).
Proof. induction T in ρ, σ |- *; simpl; f_equal; auto. Qed.

Section pinst.
  Context (n : Ix).
  Context (IH : ∀ j, olt j n → ∀ N ρ T Π φ v,
    v ∈ FV^N _ j⟦RTy (pinst_ty ρ T)⟧(Π, φ) ↔ v ∈ FV^N _ j⟦RTy T⟧(Π, φ)).

  Lemma FuelE_pinst_below j N ρ U c Π φ e : olt j n →
    e ∈ F^N _ j⟦RTy (pinst_ty ρ U) ▷ c⟧(Π, φ) ↔ e ∈ F^N _ j⟦RTy U ▷ c⟧(Π, φ).
  Proof.
    intros Hj. split; apply FuelE_res_mono; intros m Π0 φ0 v Hm; apply IH;
      exact (ole_trans_lt _ _ _ Hm Hj).
  Qed.

  Lemma Vty_pinst N ρ T Π φ v :
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n (pinst_ty ρ T) Π φ v ↔
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T Π φ v.
  Proof.
    revert ρ Π φ v.
    induction T as [|ub lb c T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c U IHU|s x a mt|lb m C T1 IHT];
      intros ρ Π φ v; simpl; try done.
    - split; intros (e & -> & Hx & Hd & Hf & H); exists e; split_and!; try done;
        intros j φ1 Πu φu u Hj Hd1 Hh HΠ Hφ Hu.
      + apply (FuelE_pinst_below j N ρ U); [done|]. apply H; try done.
        by apply (proj2 (IH j Hj N ρ T1 Πu φu u)).
      + apply (FuelE_pinst_below j N ρ U); [done|]. apply H; try done.
        by apply (proj1 (IH j Hj N ρ T1 Πu φu u)).
    - split; intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2);
        exists v1, v2, Π1, Π2, φ1, φ2; split_and!; try done;
        first [by apply IH1|by apply IH2|by apply (IH1 ρ)|by apply (IH2 ρ)].
    - split; intros [(v' & -> & H)|(v' & -> & H)];
        first [left; exists v'; split; [done|]; by apply (IH1 ρ)
              |right; exists v'; split; [done|]; by apply (IH2 ρ)].
    - split; intros (e & -> & Hx & -> & -> & H); exists e; split_and!; try done;
        intros j ss Hj Hl Hs; specialize (H j ss Hj Hl Hs);
        [rewrite <-pinst_sinst_comm in H|rewrite <-pinst_sinst_comm];
        by apply (FuelE_pinst_below j N (pup m ρ)).
  Qed.
End pinst.

(** Vfuel reads no point: an instance of the point variables of a type
    does not change it. *)
Lemma Vfuel_pinst n : ∀ N ρ T Π φ v,
  v ∈ FV^N _ n⟦RTy (pinst_ty ρ T)⟧(Π, φ) ↔ v ∈ FV^N _ n⟦RTy T⟧(Π, φ).
Proof.
  induction n as [n IH] using oind. intros N ρ T Π φ v. rewrite !Vfuel_eq. simpl.
  apply Vty_pinst. exact IH.
Qed.
