(** * The semantic lemmas of the fuel predicate (lock-freedom plan §19.7, stage H3)

    The compatibility lemmas of stage H4 are one lemma per rule of the
    cost judgment. This file gives them their tools.

    - Basics. Renamings of maps of ends ([renk_exists],
      [renk_union_split], [renk_functional]), the cap in every extension
      of the world ([fcap_ext]), and protocols under [wbext]
      ([pfits_wbext], [pfitpt_wbext]).
    - F5. [Vfuel_wbext], [Vfuel_rename] under an injective renaming,
      [Vfuel_sub] along ⊑c, [Vfuel_recount] (counters change to any map
      above a lower bound, [clow]) and [Vfuel_minus] (the counters of a
      value lose i units, its credit pays them).
    - F4. [FuelE_mono]: FuelE is monotone in the result type along ⊑c,
      in the reserve, the tickets and the frame.
    - F2. [FuelE_val]: a value in [Vfuel] satisfies FuelE.
    - F3. [FuelE_beta]: a head β step in an evaluation context lifts
      FuelE one index.
    - F1. [FuelE_bind]: a hole run in an evaluation context whose held
      ends have counters at least the hole's frame, given the
      continuation after any i ≤ frame actions of the hole ([fkont]).
    - F6. Protocol moves: [pfits_node], [pfits_snd], [pfits_rcv],
      [pfits_sel], [pfits_bra], [pfits_sub], and the refilled end
      [Vfuel_refill]. Values from parts: [Vfuel_end], [Vfuel_pair],
      [Vfuel_inj1], [Vfuel_inj2], [Vfuel_unit], [Vfuel_any].

    F1 needed four repairs of the obligations of [Fobl] and one of the
    pair clause of [Vfuel], recorded in plan §19.13. *)

From stdpp Require Import base gmap strings.
From LRGV Require Import lang.Semantics relation.Worlds lockfree.Instr lockfree.TauThread.
From LRGV Require Export lockfree.LFFuel.

(** ** Renamings of maps of ends *)

(** The image of a set of ends under a renaming of channels. *)
Definition kimg (g : chan → chan) (X : gset cend) : gset cend := set_map (λ o : cend, (g o.1, o.2)) X.

Lemma renk_functional {Y : Type} (g : chan → chan) (m m1 m2 : gmap cend Y) : renk g m m1 → renk g m m2 → m1 = m2.
Proof.
  intros [A1 B1] [A2 B2]. apply map_eq. intros o'.
  destruct (m1 !! o') as [v|] eqn:E1.
  - destruct (B1 o' v E1) as (o & -> & Ho). symmetry. by apply A2.
  - destruct (m2 !! o') as [v|] eqn:E2; [|done].
    destruct (B2 o' v E2) as (o & -> & Ho). by rewrite (A1 o v Ho) in E1.
Qed.

Lemma kinj_dom {Y Z : Type} (g : chan → chan) (m : gmap cend Y) (m1 : gmap cend Z) :
  dom m1 ⊆ dom m → kinj g m → kinj g m1.
Proof.
  intros Hd Hk o1 o2 v1 v2 H1 H2 Heq.
  apply elem_of_dom_2 in H1, H2. apply Hd, elem_of_dom in H1 as [w1 W1], H2 as [w2 W2].
  exact (Hk o1 o2 w1 w2 W1 W2 Heq).
Qed.

Lemma kinj_elem {Y : Type} (g : chan → chan) (m : gmap cend Y) o1 o2 :
  kinj g m → o1 ∈ dom m → o2 ∈ dom m → (g o1.1, o1.2) = (g o2.1, o2.2) → o1 = o2.
Proof.
  intros Hk [v1 H1]%elem_of_dom [v2 H2]%elem_of_dom. exact (Hk o1 o2 v1 v2 H1 H2).
Qed.

Lemma renk_exists {Y : Type} (g : chan → chan) (m : gmap cend Y) : kinj g m → ∃ m', renk g m m'.
Proof.
  induction m as [|o v m Hno IH] using map_ind; intros Hk.
  - exists ∅. split; intros ? ?; by rewrite lookup_empty.
  - destruct IH as [m' [A B]].
    { intros o1 o2 v1 v2 H1 H2 Heq. apply (Hk o1 o2 v1 v2); [| |done];
        rewrite lookup_insert_ne; [done| |done|]; intros ->; congruence. }
    exists (<[(g o.1, o.2) := v]> m'). split.
    + intros o1 v1 Ho1. destruct (decide (o1 = o)) as [->|Hne].
      * rewrite lookup_insert_eq in Ho1. simplify_eq. by rewrite lookup_insert_eq.
      * rewrite lookup_insert_ne in Ho1 by done. rewrite lookup_insert_ne; [by apply A|].
        intros Heq. apply Hne. apply (Hk o1 o v1 v); [by rewrite lookup_insert_ne|by rewrite lookup_insert_eq|done].
    + intros o' v' Ho'. destruct (decide ((g o.1, o.2) = o')) as [<-|Hne].
      * rewrite lookup_insert_eq in Ho'. simplify_eq. exists o. split; [done|by rewrite lookup_insert_eq].
      * rewrite lookup_insert_ne in Ho' by done. destruct (B o' v' Ho') as (o1 & -> & Ho1).
        exists o1. split; [done|]. rewrite lookup_insert_ne; [done|]. intros ->. congruence.
Qed.

Lemma renk_dom {Y : Type} (g : chan → chan) (m m' : gmap cend Y) : renk g m m' → dom m' = kimg g (dom m).
Proof.
  intros [A B]. apply set_eq. intros o'. unfold kimg. rewrite elem_of_map. split.
  - intros [v Hv]%elem_of_dom. destruct (B o' v Hv) as (o & -> & Ho). exists o.
    split; [done|]. by eapply elem_of_dom_2.
  - intros (o & -> & [v Hv]%elem_of_dom). eapply elem_of_dom_2. by apply A.
Qed.

Lemma elem_of_kimg (g : chan → chan) X o : o ∈ X → (g o.1, o.2) ∈ kimg g X.
Proof. intros H. unfold kimg. apply elem_of_map. by exists o. Qed.

Lemma renk_empty {Y : Type} (g : chan → chan) (m' : gmap cend Y) : renk g ∅ m' → m' = ∅.
Proof.
  intros H. apply (renk_functional g ∅); [done|]. split; intros ? ?; by rewrite lookup_empty.
Qed.

Lemma renk_nil {Y : Type} (g : chan → chan) : renk (Y := Y) g ∅ ∅.
Proof. split; intros ? ?; by rewrite lookup_empty. Qed.

Lemma kinj_nil {Y : Type} (g : chan → chan) : kinj (Y := Y) g ∅.
Proof. intros ? ? ? ?; by rewrite lookup_empty. Qed.

Lemma renk_singleton {Y : Type} (g : chan → chan) o (v : Y) m' : renk g {[o := v]} m' → m' = {[(g o.1, o.2) := v]}.
Proof.
  intros H. apply (renk_functional g {[o := v]}); [done|]. split.
  - intros o1 v1 H1. apply lookup_singleton_Some in H1 as [<- <-]. by rewrite lookup_singleton_eq.
  - intros o' v' H'. apply lookup_singleton_Some in H' as [<- <-]. exists o.
    split; [done|by rewrite lookup_singleton_eq].
Qed.

Lemma renk_union {Y : Type} (g : chan → chan) (m1 m2 m1' m2' : gmap cend Y) :
  kinj g (m1 ∪ m2) → dom m1 ## dom m2 → renk g m1 m1' → renk g m2 m2' →
  renk g (m1 ∪ m2) (m1' ∪ m2').
Proof.
  intros Hk Hd [A1 B1] [A2 B2]. split.
  - intros o v Ho. apply lookup_union_Some_raw in Ho as [Ho|[Hn Ho]].
    + apply lookup_union_Some_l. by apply A1.
    + apply lookup_union_Some_raw. right. split; [|by apply A2].
      destruct (m1' !! (g o.1, o.2)) as [v1|] eqn:E; [|done].
      destruct (B1 _ _ E) as (o1 & Heq & Ho1). exfalso.
      assert (o1 = o) as ->.
      { apply (Hk o1 o v1 v); [by apply lookup_union_Some_l| |done].
        apply lookup_union_Some_raw. by right. }
      congruence.
  - intros o' v Ho'. apply lookup_union_Some_raw in Ho' as [Ho'|[Hn Ho']].
    + destruct (B1 _ _ Ho') as (o & -> & Ho). exists o. split; [done|]. by apply lookup_union_Some_l.
    + destruct (B2 _ _ Ho') as (o & -> & Ho). exists o. split; [done|].
      apply lookup_union_Some_raw. right. split; [|done].
      apply not_elem_of_dom. intros Hin. apply (Hd o); [done|by eapply elem_of_dom_2].
Qed.

(** A renamed union splits into the renamed parts. *)
Lemma renk_union_split {Y : Type} (g : chan → chan) (m1 m2 m' : gmap cend Y) :
  kinj g (m1 ∪ m2) → dom m1 ## dom m2 → renk g (m1 ∪ m2) m' →
  ∃ m1' m2', m' = m1' ∪ m2' ∧ renk g m1 m1' ∧ renk g m2 m2' ∧ dom m1' ## dom m2'.
Proof.
  intros Hk Hd Hr.
  assert (kinj g m1) as Hk1 by (apply (kinj_dom g (m1 ∪ m2)); [rewrite dom_union_L; set_solver|done]).
  assert (kinj g m2) as Hk2 by (apply (kinj_dom g (m1 ∪ m2)); [rewrite dom_union_L; set_solver|done]).
  destruct (renk_exists g m1 Hk1) as [m1' H1]. destruct (renk_exists g m2 Hk2) as [m2' H2].
  exists m1', m2'. split_and!; [|done|done|].
  - eapply renk_functional; [exact Hr|by apply renk_union].
  - rewrite (renk_dom _ _ _ H1), (renk_dom _ _ _ H2). intros o' Ho1 Ho2. unfold kimg in *.
    apply elem_of_map in Ho1 as (o1 & -> & Ho1). apply elem_of_map in Ho2 as (o2 & Heq & Ho2).
    assert (o1 = o2) as <-.
    { apply (kinj_elem g (m1 ∪ m2)); [done|rewrite dom_union_L; set_solver|rewrite dom_union_L; set_solver|done]. }
    by apply (Hd o1).
Qed.

Lemma renk_fmap {Y Z : Type} (f : Y → Z) (g : chan → chan) (m m' : gmap cend Y) :
  renk g m m' → renk g (f <$> m) (f <$> m').
Proof.
  intros [A B]. split.
  - intros o z Ho. apply lookup_fmap_Some in Ho as (y & <- & Ho). rewrite lookup_fmap, (A o y Ho). done.
  - intros o' z Ho'. apply lookup_fmap_Some in Ho' as (y & <- & Ho'). destruct (B o' y Ho') as (o & -> & Ho).
    exists o. split; [done|]. by rewrite lookup_fmap, Ho.
Qed.

Lemma renk_dom_eq {Y Z : Type} (g : chan → chan) (π π' : gmap cend Y) (φ φ' : gmap cend Z) :
  dom φ = dom π → renk g π π' → renk g φ φ' → dom φ' = dom π'.
Proof. intros Hd Hπ Hφ. by rewrite (renk_dom _ _ _ Hπ), (renk_dom _ _ _ Hφ), Hd. Qed.

(** A renaming that agrees with g on the channels of m. *)
Lemma renk_ext {Y : Type} (g g' : chan → chan) (m m' : gmap cend Y) :
  (∀ o, o ∈ dom m → g' o.1 = g o.1) → renk g m m' → renk g' m m'.
Proof.
  intros He [A B]. split.
  - intros o v Ho. rewrite He by (by eapply elem_of_dom_2). by apply A.
  - intros o' v Ho'. destruct (B o' v Ho') as (o & -> & Ho). exists o.
    rewrite He by (by eapply elem_of_dom_2). done.
Qed.

(** The inverse of an injective renaming h, on the renamed map. *)
Lemma renk_inv {Y : Type} (h g' : chan → chan) (m m0 : gmap cend Y) :
  (∀ c, g' (h c) = c) → renk h m m0 → renk g' m0 m.
Proof.
  intros Hi [A B]. split.
  - intros o0 v Ho0. destruct (B o0 v Ho0) as (o & -> & Ho). simpl. rewrite Hi. by destruct o.
  - intros o v Ho. exists (h o.1, o.2). simpl. rewrite Hi. split; [by destruct o|]. by apply A.
Qed.

(** Counters on the preimage of a renamed map. *)
Lemma renk_preimage {Y Z : Type} (g : chan → chan) (π π' : gmap cend Y) (φ' : gmap cend Z) :
  renk g π π' → dom φ' = dom π' → ∃ φ, dom φ = dom π ∧ renk g φ φ'.
Proof.
  intros [A B] Hd. exists (map_imap (λ o _, φ' !! (g o.1, o.2)) π). split.
  - apply set_eq. intros o. rewrite !elem_of_dom, map_lookup_imap.
    destruct (π !! o) as [k|] eqn:E; simpl; [|split; intros []; done].
    split; [intros _; by exists k|]. intros _.
    assert ((g o.1, o.2) ∈ dom φ') as Hin by (rewrite Hd; eapply elem_of_dom_2; by apply A).
    by apply elem_of_dom in Hin.
  - split.
    + intros o f Ho. rewrite map_lookup_imap in Ho. destruct (π !! o); simpl in Ho; done.
    + intros o' f Ho'. assert (o' ∈ dom π') as [k Hk]%elem_of_dom by (rewrite <-Hd; by eapply elem_of_dom_2).
      destruct (B o' k Hk) as (o & -> & Ho). exists o. split; [done|].
      by rewrite map_lookup_imap, Ho.
Qed.

Lemma kinj_union {Y : Type} (g : chan → chan) (m1 m2 : gmap cend Y) :
  kinj g m1 → kinj g m2 →
  (∀ o1 o2, o1 ∈ dom m1 → o2 ∈ dom m2 → (g o1.1, o1.2) ≠ (g o2.1, o2.2)) →
  kinj g (m1 ∪ m2).
Proof.
  intros H1 H2 Hx o1 o2 v1 v2 Ho1 Ho2 Heq.
  apply lookup_union_Some_raw in Ho1 as [Ho1|[N1 Ho1]], Ho2 as [Ho2|[N2 Ho2]].
  - exact (H1 o1 o2 v1 v2 Ho1 Ho2 Heq).
  - exfalso. apply (Hx o1 o2); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
  - exfalso. apply (Hx o2 o1); [by eapply elem_of_dom_2|by eapply elem_of_dom_2|done].
  - exact (H2 o1 o2 v1 v2 Ho1 Ho2 Heq).
Qed.

(** ** Maps of ends: restriction and removal along unions *)

Lemma mres_union_l {Y : Type} (X : gset cend) (m1 m2 : gmap cend Y) :
  X ## dom m2 → mres X (m1 ∪ m2) = mres X m1.
Proof.
  intros Hd. apply map_eq. intros o. unfold mres. rewrite !map_lookup_filter.
  destruct (decide (o ∈ X)) as [Hx|Hx].
  - assert (m2 !! o = None) as N2 by (apply not_elem_of_dom; set_solver).
    rewrite lookup_union, N2. by destruct (m1 !! o).
  - destruct ((m1 ∪ m2) !! o), (m1 !! o); simpl; try done;
      rewrite ?option_guard_False by done; done.
Qed.

Lemma mrem_union_l {Y : Type} (X : gset cend) (m1 m2 : gmap cend Y) :
  X ## dom m2 → mrem X (m1 ∪ m2) = mrem X m1 ∪ m2.
Proof.
  intros Hd. apply map_eq. intros o. unfold mrem. rewrite lookup_union, !map_lookup_filter, lookup_union.
  destruct (decide (o ∈ X)) as [Hx|Hx].
  - assert (m2 !! o = None) as N2 by (apply not_elem_of_dom; set_solver).
    rewrite N2. destruct (m1 !! o); simpl; [|done]. rewrite option_guard_False by (simpl; auto). done.
  - destruct (m1 !! o), (m2 !! o); simpl; rewrite ?option_guard_True by done; done.
Qed.

Lemma mres_fmap {Y Z : Type} (f : Y → Z) (X : gset cend) (m : gmap cend Y) :
  mres X (f <$> m) = f <$> mres X m.
Proof.
  apply map_eq. intros o. unfold mres. rewrite lookup_fmap, !map_lookup_filter, lookup_fmap.
  destruct (m !! o); simpl; [|done]. by destruct (decide (o ∈ X)); [rewrite !option_guard_True|rewrite !option_guard_False].
Qed.

Lemma dom_mres_sub {Y : Type} (X : gset cend) (m : gmap cend Y) : dom (mres X m) ⊆ X.
Proof. rewrite dom_mres. set_solver. Qed.

(** Restriction of the counters to the renamed part. *)
Lemma renk_mres {Y : Type} (g : chan → chan) (π π1 π1' : gmap cend point) (φ φ' : gmap cend Y) :
  kinj g π → dom φ ⊆ dom π → dom π1 ⊆ dom π → renk g φ φ' → renk g π1 π1' →
  renk g (mres (dom π1) φ) (mres (dom π1') φ').
Proof.
  intros Hk Hdφ Hd1 [A B] H1. split.
  - intros o f Ho. apply lookup_mres_Some in Ho as [Ho Hin]. apply lookup_mres_Some. split; [by apply A|].
    rewrite (renk_dom _ _ _ H1). by apply elem_of_kimg.
  - intros o' f Ho'. apply lookup_mres_Some in Ho' as [Ho' Hin].
    destruct (B o' f Ho') as (o & -> & Ho). exists o. split; [done|]. apply lookup_mres_Some. split; [done|].
    rewrite (renk_dom _ _ _ H1) in Hin. unfold kimg in Hin. apply elem_of_map in Hin as (o1 & Heq & Ho1).
    assert (o = o1) as -> ; [|done].
    apply (kinj_elem g π); [done|apply Hdφ; by eapply elem_of_dom_2|by apply Hd1|done].
Qed.

(** ** The cap in every extension of the world ([fcap_ext], LFFuel.v) *)

Lemma fcap_dom W π φ : fcap W π φ → dom φ ⊆ dom π.
Proof.
  intros H o [f Hf]%elem_of_dom. destruct (H o f Hf) as (k & Hk & _). by eapply elem_of_dom_2.
Qed.

Lemma fcap_ext_wbext W W' π φ : wbext W W' → fcap_ext W π φ → fcap_ext W' π φ.
Proof. intros Hb H W'' Hb'. apply H. by eapply wbext_trans. Qed.

Lemma fcap_ext_here W π φ : fcap_ext W π φ → fcap W π φ.
Proof. intros H. apply H, wbext_refl. Qed.

(** A known point keeps its budget in every extension. *)
Lemma fcap_ext_known W π φ :
  fcap W π φ → (∀ o k, π !! o = Some k → pt_known W k) → fcap_ext W π φ.
Proof.
  intros H Hk W' [_ Hb] o f Hf. destruct (H o f Hf) as (k & Ho & Hle). exists k. split; [done|].
  by rewrite (proj1 (Hb k (Hk o k Ho))).
Qed.

Lemma renk_fcap W (g : chan → chan) π π' φ φ' : fcap W π φ → renk g π π' → renk g φ φ' → fcap W π' φ'.
Proof.
  intros H [A _] [_ B] o' f Hf. destruct (B o' f Hf) as (o & -> & Ho).
  destruct (H o f Ho) as (k & Hk & Hle). exists k. split; [by apply A|done].
Qed.

Lemma fcap_union W π1 φ1 π2 φ2 :
  fcap W π1 φ1 → fcap W π2 φ2 → dom π1 ## dom π2 → fcap W (π1 ∪ π2) (φ1 ∪ φ2).
Proof.
  intros H1 H2 Hd o f Hf. apply lookup_union_Some_raw in Hf as [Hf|[N Hf]].
  - destruct (H1 o f Hf) as (k & Hk & Hle). exists k. split; [by apply lookup_union_Some_l|done].
  - destruct (H2 o f Hf) as (k & Hk & Hle). exists k. split; [|done].
    apply lookup_union_Some_raw. right. split; [|done].
    apply not_elem_of_dom. intros Hin. apply (Hd o); [done|by eapply elem_of_dom_2].
Qed.

Lemma fcap_ext_union W π1 φ1 π2 φ2 :
  fcap_ext W π1 φ1 → fcap_ext W π2 φ2 → dom π1 ## dom π2 → fcap_ext W (π1 ∪ π2) (φ1 ∪ φ2).
Proof. intros H1 H2 Hd W' Hb. apply fcap_union; auto. Qed.

Lemma fcap_ext_rename W (g : chan → chan) π π' φ φ' : fcap_ext W π φ → renk g π π' → renk g φ φ' → fcap_ext W π' φ'.
Proof. intros H Hπ Hφ W' Hb. eapply renk_fcap; [apply H, Hb|done|done]. Qed.

Lemma fcap_ext_fmap W π φ (f : fuel → fuel) :
  (∀ x, fle (f x) x) → fcap_ext W π φ → fcap_ext W π (f <$> φ).
Proof.
  intros Hf H W' Hb o x Hx. apply lookup_fmap_Some in Hx as (x0 & <- & Hx).
  destruct (H W' Hb o x0 Hx) as (k & Hk & Hle). exists k. split; [done|]. by eapply fle_trans.
Qed.

(** FuelE at a positive index gives the cap in every extension. *)
Lemma FuelE_fcap_ext n W σ r π φ tk d e : FuelE (S n) W σ r π φ tk d e → fcap_ext W π φ.
Proof.
  intros H W' Hb. apply FuelE_S in H.
  destruct (H W' id π φ Hb (kinj_id π) (renk_id π) (renk_id φ)) as [Hc _]. done.
Qed.

(** ** Protocols under extensions of the world *)

Lemma pt_known_dual W x : pt_known W (pt_dual x) ↔ pt_known W x.
Proof. done. Qed.

Lemma wbext_known W W' x : wbext W W' → pt_known W x → pt_known W' x.
Proof. intros [Hn _]. unfold pt_known. set_solver. Qed.

Lemma pfits_wbext W W' x P : wbext W W' → pfits W x P → pfits W' x P.
Proof.
  intros Hb. apply pfits_at_mono. intros y Hy.
  destruct Hb as [Hn Hbud]. destruct (Hbud y Hy) as [B1 C1].
  destruct (Hbud (pt_dual y)) as [B2 C2]; [done|].
  split_and!; [unfold pt_known in *; set_solver|done..].
Qed.

Lemma pfitpt_wbext W W' x ρ : wbext W W' → pfitpt W x ρ → pfitpt W' x ρ.
Proof.
  intros Hb. apply pfitpt_at_mono. intros y Hy.
  destruct Hb as [Hn Hbud]. destruct (Hbud y Hy) as [B1 C1].
  destruct (Hbud (pt_dual y)) as [B2 C2]; [done|].
  split_and!; [unfold pt_known in *; set_solver|done..].
Qed.

(** ** F5: values under extensions of the world *)

Lemma farr_wbext (E : nat → epred) (V : nat → vpred) n W W' c t h σ1 σ2 a π φ body :
  wbext W W' → farr E V n W c t h σ1 σ2 a π φ body → farr E V n W' c t h σ1 σ2 a π φ body.
Proof. intros Hb [Hf H]. split; [done|]. intros W'' j φ' v πa φa Hb'. apply H. by eapply wbext_trans. Qed.

Lemma fpts_wbext W W' π : wbext W W' → fpts W π → fpts W' π.
Proof.
  intros Hb H o k Hk. destruct (H o k Hk) as [Hkn Hd]. split; [by apply (wbext_known W)|].
  destruct Hb as [_ Hbud]. by rewrite (proj1 (Hbud (pt_dual k) ltac:(by apply pt_known_dual))).
Qed.

Lemma Vfuel_wbext n W W' σ π φ w : wbext W W' → Vfuel n W σ π φ w → Vfuel n W' σ π φ w.
Proof.
  intros Hb. rewrite !Vfuel_eq.
  induction w in σ, π, φ |- *; destruct σ as [τ a]; destruct τ; simpl; try done;
    try (intros (xx & Hw & Hp & Hk & Hf); exists xx; split_and!;
         [done|done|by apply (wbext_known W W')|by apply (pfitpt_wbext W W')]);
    try (intros (cc & bb & xx & ff & Hw & Hp & Hf & Hc & Ha & Hq); exists cc, bb, xx, ff; split_and!;
         [done|done|by apply (pfits_wbext W W')|done|done|by apply (fpts_wbext W W')]);
    try (intros (Hp & Hq & Hf); split_and!; [done|by apply (fpts_wbext W W')|by apply (farr_wbext _ _ _ W W')]);
    try (intros (π1 & π2 & Hπ & Hd & H1 & H2); exists π1, π2; split_and!; auto; fail);
    auto.
  intros (Hp & Hf & H). split_and!; [done|done|]. intros W'' j r0 tk0 Hb' Hj Hm. apply H; [|done|done].
  by eapply wbext_trans.
Qed.

(** ** Channels of a renamed term *)

Lemma fends_emap (g : chan → chan) e : fends (emap g e) = kimg g (fends e).
Proof.
  unfold kimg. induction e; simpl;
    rewrite ?set_map_union_L, ?set_map_empty, ?set_map_singleton_L; try reflexivity; congruence.
Qed.

Lemma emap_ext_fchans (g h : chan → chan) e : (∀ c, c ∈ fchans e → g c = h c) → emap g e = emap h e.
Proof. induction e; simpl; intros H; f_equal; auto; set_solver. Qed.

(** ** A fresh injective renaming

    [Vfuel_rename] moves the channels of an argument out of the way of
    the closure's own channels: [sprefix s] prepends s, which is longer
    than every channel of the closure, and [sunfix s g] undoes it and
    renames everything else by g. *)

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

Definition slonger (X : gset chan) : string := String.append (foldr String.append "" (elements X)) "x".

Lemma slonger_spec X c : c ∈ X → String.length c < String.length (slonger X).
Proof.
  intros Hc. apply elem_of_elements in Hc. unfold slonger. rewrite slen_app. simpl.
  enough (String.length c ≤ String.length (foldr String.append "" (elements X))) by lia.
  induction (elements X) as [|c' l IH]; simpl; [by apply elem_of_nil in Hc|].
  rewrite slen_app. apply elem_of_cons in Hc as [->|Hc]; [lia|]. specialize (IH Hc). lia.
Qed.

Definition sprefix (s : string) : chan → chan := String.append s.
Definition sunfix (s : string) (g : chan → chan) (c : chan) : chan :=
  match unprefix s c with Some c0 => c0 | None => g c end.

Lemma sunfix_prefix s g c : sunfix s g (sprefix s c) = c.
Proof. unfold sunfix, sprefix. by rewrite unprefix_app. Qed.

Lemma sunfix_short s g c : String.length c < String.length s → sunfix s g c = g c.
Proof. intros H. unfold sunfix. by rewrite unprefix_short. Qed.

Lemma sprefix_inj s c1 c2 : sprefix s c1 = sprefix s c2 → c1 = c2.
Proof.
  intros H. unfold sprefix in H. pose proof (unprefix_app s c1) as H1.
  rewrite H, unprefix_app in H1. by injection H1.
Qed.

Lemma kinj_sprefix {Y : Type} (s : string) (m : gmap cend Y) : kinj (sprefix s) m.
Proof. intros [c1 b1] [c2 b2] v1 v2 _ _ [= Hc ->]. by rewrite (sprefix_inj s c1 c2 Hc). Qed.

(** ** F5: values under injective renamings *)

(** Incoming ends, renamed. *)
Lemma fin_ok_rename W (g : chan → chan) w πa φa πa' φa' :
  kinj g πa → renk g πa πa' → renk g φa φa' → fin_ok W w πa φa → fin_ok W (emap g w) πa' φa'.
Proof.
  intros Hk Hπ Hφ (D1 & D2 & Hc & Hb & Hkn). split_and!.
  - by rewrite (renk_dom _ _ _ Hπ), fends_emap, D1.
  - by rewrite (renk_dom _ _ _ Hφ), fends_emap, D2.
  - by eapply renk_fcap.
  - intros o' k Ho'. destruct (proj2 Hπ o' k Ho') as (o & -> & Ho). by apply (Hb o).
  - intros o' k Ho'. destruct (proj2 Hπ o' k Ho') as (o & -> & Ho). by apply (Hkn o).
Qed.

Lemma fpts_rename W (g : chan → chan) π π' : renk g π π' → fpts W π → fpts W π'.
Proof. intros [_ B] H o' k Hk. destruct (B o' k Hk) as (o & -> & Ho). by apply (H o). Qed.

Section rename.
  (** The closure clause, renamed. The argument is moved out of the way
      of the closure's channels by [sprefix], the body is run there and
      renamed back by [sunfix]. *)
  Lemma farr_rename n W c t h σ1 σ2 a eb π φ (g : chan → chan) π' φ' :
    (∀ j, j < n → ∀ W σ π φ w (g : chan → chan) π' φ',
       kinj g π → dom φ ⊆ dom π → renk g π π' → renk g φ φ' →
       Vfuel j W σ π φ w → Vfuel j W σ π' φ' (emap g w)) →
    dom π = fends (Lam eb) → kinj g π → renk g π π' → renk g φ φ' →
    farr FuelE Vfuel n W c t h σ1 σ2 a π φ (λ v, subst1 v eb) →
    farr FuelE Vfuel n W c t h σ1 σ2 a π' φ' (λ v, subst1 v (emap g eb)).
  Proof.
    intros IH Hdom Hk Hπ Hφ [Hfl HF]. split.
    { intros o' f Ho'. destruct (proj2 Hφ o' f Ho') as (o & -> & Ho). by apply (Hfl o). }
    intros W' j φ'' v πa φa Hb Hj Hd'' Hc'' Hh'' Hdis Hin Hv r tk Hm.
    set (s := slonger (fchans eb)).
    assert (Hshort : ∀ c0, c0 ∈ fchans eb → String.length c0 < String.length s) by (intros; by apply slonger_spec).
    assert (Hchan : ∀ o, o ∈ dom π → o.1 ∈ fchans eb).
    { intros o Ho. rewrite Hdom in Ho. simpl in Ho. rewrite fchans_fends. apply elem_of_map. by exists o. }
    set (g' := sunfix s g).
    assert (Hg' : ∀ o, o ∈ dom π → g' o.1 = g o.1) by (intros o Ho; by apply sunfix_short, Hshort, Hchan).
    pose proof (proj1 (proj2 Hin)) as Hdφa.
    destruct (renk_exists (sprefix s) πa (kinj_sprefix s πa)) as [πa0 Hπa].
    destruct (renk_exists (sprefix s) φa (kinj_sprefix s φa)) as [φa0 Hφa].
    destruct (renk_preimage g π π' φ'' Hπ Hd'') as (φ0 & Hd0 & Hφ0).
    (* the closure's points and the moved argument's points are apart *)
    assert (Hapart : ∀ o1 o2, o1 ∈ dom π → o2 ∈ dom πa0 → o1 ≠ o2).
    { intros o1 o2 Ho1 Ho2 ->. rewrite (renk_dom _ _ _ Hπa) in Ho2. unfold kimg in Ho2.
      apply elem_of_map in Ho2 as (o & -> & _). simpl in Ho1. apply Hchan, Hshort in Ho1. simpl in Ho1.
      unfold sprefix in Ho1. rewrite slen_app in Ho1. lia. }
    assert (Hcap0 : fcap_ext W' π φ0).
    { intros W3 Hb3 o f Ho. pose proof (proj1 Hφ0 o f Ho) as Ho'. destruct (Hc'' W3 Hb3 _ f Ho') as (k & Hk' & Hle).
      assert (o ∈ dom π) as [k0 Hk0]%elem_of_dom by (rewrite <-Hd0; by eapply elem_of_dom_2).
      rewrite (proj1 Hπ o k0 Hk0) in Hk'. injection Hk' as <-. by exists k0. }
    assert (HF0 : FuelE j W' σ2 r (π ∪ πa0) (φ0 ∪ φa0) tk c (subst1 (emap (sprefix s) v) eb)).
    { apply (HF W' j φ0 (emap (sprefix s) v) πa0 φa0 Hb Hj Hd0 Hcap0); [| | | |done].
      - intros o f Ho. apply (Hh'' (g o.1, o.2)). by apply (proj1 Hφ0).
      - intros o Ho1 Ho2. by apply (Hapart o o).
      - split_and!; [by rewrite is_val_emap; apply (proj1 Hin)|exact (renk_dom_eq _ _ _ _ _ Hdφa Hπa Hφa)|].
        exact (fcap_ext_rename _ _ _ _ _ _ (proj2 (proj2 Hin)) Hπa Hφa).
      - apply (IH j Hj W' σ1 πa φa v); [apply kinj_sprefix|by rewrite Hdφa|done|done|done]. }
    (* rename back *)
    assert (Hkg : kinj g' (π ∪ πa0)).
    { apply kinj_union.
      - intros o1 o2 v1 v2 H1 H2. rewrite !Hg' by (by eapply elem_of_dom_2). by apply (Hk o1 o2 v1 v2).
      - intros o1 o2 v1 v2 H1 H2 Heq.
        destruct (proj2 Hπa o1 v1 H1) as (p1 & -> & _). destruct (proj2 Hπa o2 v2 H2) as (p2 & -> & _).
        simpl in Heq. unfold g' in Heq. rewrite !sunfix_prefix in Heq. by injection Heq as -> ->.
      - intros o1 o2 Ho1 Ho2 Heq. rewrite Hg' in Heq by done.
        rewrite (renk_dom _ _ _ Hπa) in Ho2. unfold kimg in Ho2. apply elem_of_map in Ho2 as (p & -> & Hp).
        simpl in Heq. unfold g' in Heq. rewrite sunfix_prefix in Heq. apply (Hdis p).
        + done.
        + rewrite (renk_dom _ _ _ Hπ). destruct p as [pc pb]. simpl in Heq. rewrite <-Heq.
          by apply elem_of_kimg. }
    assert (Hd0a : dom φ0 ## dom φa0).
    { rewrite Hd0, (renk_dom _ _ _ Hφa), Hdφa, <-(renk_dom _ _ _ Hπa).
      intros o Ho1 Ho2. by apply (Hapart o o). }
    assert (Hrπ : renk g' (π ∪ πa0) (π' ∪ πa)).
    { apply renk_union; [done| |by apply (renk_ext g)|by apply (renk_inv (sprefix s)); [apply sunfix_prefix|]].
      intros o Ho1 Ho2. by apply (Hapart o o). }
    assert (Hrφ : renk g' (φ0 ∪ φa0) (φ'' ∪ φa)).
    { apply renk_union; [|done| |by apply (renk_inv (sprefix s)); [apply sunfix_prefix|]].
      - apply (kinj_dom g' (π ∪ πa0)); [|done]. rewrite !dom_union_L, Hd0, (renk_dom _ _ _ Hφa),
          (renk_dom _ _ _ Hπa), Hdφa. done.
      - apply (renk_ext g); [|done]. intros o Ho. apply Hg'. by rewrite <-Hd0. }
    pose proof (FuelE_rename j W' σ2 r (π ∪ πa0) (φ0 ∪ φa0) tk c _ g' _ _ Hkg Hrπ Hrφ HF0) as HR.
    rewrite emap_subst1, emap_emap in HR.
    rewrite (emap_ext (g' ∘ sprefix s) id) in HR by (intros c0; apply sunfix_prefix).
    rewrite emap_id in HR.
    rewrite (emap_ext_fchans g' g eb) in HR; [done|].
    intros c0 Hc0. by apply sunfix_short, Hshort.
  Qed.

  Lemma Vfuel_rename n : ∀ W σ π φ w (g : chan → chan) π' φ',
    kinj g π → dom φ ⊆ dom π → renk g π π' → renk g φ φ' →
    Vfuel n W σ π φ w → Vfuel n W σ π' φ' (emap g w).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros W σ π φ w g π' φ' Hk Hdφ Hπ Hφ. rewrite !Vfuel_eq.
    induction w in σ, π, φ, π', φ', Hk, Hdφ, Hπ, Hφ |- *; destruct σ as [τ a]; destruct τ; simpl; try done.
    all: first
      [ intros [[=] _]; fail
      | intros (xx & [=] & _); fail
      | intros (cc & bb & xx & ff & [=] & _); fail
      | (* the unit *)
        intros [_ ->]; split; [done|by apply (renk_empty g)]
      | (* a point *)
        intros (xx & [= <-] & -> & Hkn & Hf); exists x; split_and!; [done|by apply (renk_empty g)|done|done]
      | (* an end *)
        intros (cc & bb & xx & ff & [= <- <-] & -> & Hp & Hf & Ha & Hq);
        exists (g c), b, xx, ff; split_and!; [done|by apply (renk_singleton g (c, b) xx)|done|by apply (proj1 Hφ (c, b))|done
                                             |by apply (fpts_rename W g {[(c, b) := xx]})]
      | (* a closure *)
        intros (Hd & Hq & Hf); split_and!;
        [by rewrite (renk_dom _ _ _ Hπ), Hd, fends_emap
        |by apply (fpts_rename W g π)
        |by apply (farr_rename n W _ _ _ _ _ _ w π φ g π' φ' IH)]
      | (* a pair *)
        intros (π1 & π2 & -> & Hd & H1 & H2);
        destruct (renk_union_split g π1 π2 π' Hk Hd Hπ) as (π1' & π2' & -> & R1 & R2 & Hd');
        assert (Hk1 : kinj g π1); [apply (kinj_dom g (π1 ∪ π2)); [rewrite dom_union_L; set_solver|done]|];
        assert (Hk2 : kinj g π2); [apply (kinj_dom g (π1 ∪ π2)); [rewrite dom_union_L; set_solver|done]|];
        exists π1', π2'; split_and!; [done|done|apply (IHw1 _ π1 (mres (dom π1) φ))|apply (IHw2 _ π2 (mres (dom π2) φ))];
        try apply dom_mres_sub; try done;
        (apply (renk_mres g (π1 ∪ π2)); [done|done|rewrite dom_union_L; set_solver|done|done])
      | (* an injection *)
        apply IHw; done
      | (* a box *)
        intros (-> & Hfe & H); split; [by apply (renk_empty g)|];
        split; [rewrite fends_emap, Hfe; unfold kimg; by rewrite set_map_empty|];
        intros W' j r0 tk0 Hb Hj Hm; specialize (H W' j r0 tk0 Hb Hj Hm);
        pose proof (FuelE_rename j W' _ r0 ∅ ∅ tk0 c _ g ∅ ∅ (kinj_nil g) (renk_nil g) (renk_nil g) H) as HR;
        by rewrite emap_subst1 in HR ].
  Qed.
End rename.

(** ** F4 and F5: subsumption and monotonicity

    By induction on the index, both at once. The closure clause of
    [Vfuel] reads FuelE below its level, and the value clause of FuelE
    reads [Vfuel] at its own level. *)

Lemma fle_ftick_mono d d' : fle d d' → fle (ftick d) (ftick d').
Proof. destruct d, d'; simpl; lia. Qed.

Lemma fle_None d : fle d None.
Proof. by destruct d. Qed.

Lemma sub_mono n :
  (∀ W σ σ' π φ w, σ ⊑c σ' → Vfuel n W σ π φ w → Vfuel n W σ' π φ w) ∧
  (∀ W σ σ' r r' π φ tk tk' d d' e, σ ⊑c σ' → r' ≤ r → tk ≤ tk' → fle d d' →
     FuelE n W σ r π φ tk d e → FuelE n W σ' r' π φ tk' d' e).
Proof.
  induction n as [n IH] using lt_wf_ind.
  assert (HV : ∀ W σ σ' π φ w, σ ⊑c σ' → Vfuel n W σ π φ w → Vfuel n W σ' π φ w).
  { intros W σ σ' π φ w Hs. rewrite !Vfuel_eq.
    (* the closure clause along subtyping *)
    assert (Harr : ∀ c t h σ1 σ2 a c' t' h' σ1' σ2' a' π φ body,
      fle c c' → tle t t' → h ≤ h' → σ1' ⊑c σ1 → σ2 ⊑c σ2' →
      fle (fadd (Some h') a') (fadd (Some h) a) →
      farr FuelE Vfuel n W c t h σ1 σ2 a π φ body → farr FuelE Vfuel n W c' t' h' σ1' σ2' a' π φ body).
    { intros c t h σ1 σ2 a c' t' h' σ1' σ2' a' π0 φ0 body Hc Ht Hh H1 H2 Ha [Hfl HF]. split.
      - intros o f Ho. eapply fle_trans; [exact Ha|by apply (Hfl o)].
      - intros W' j φ' v πa φa Hb Hj Hd Hcap Hfl' Hdis Hin Hv r tk Hm.
        apply (proj2 (IH j Hj) W' σ2 σ2' r r _ _ tk tk c c'); [done|lia|lia|done|].
        apply (HF W' j φ' v πa φa Hb Hj Hd Hcap); [| |done| |by apply Ht].
        + intros o f Ho. eapply fle_trans; [|by apply (Hfl' o)]. simpl. lia.
        + done.
        + by apply (proj1 (IH j Hj) W' σ1' σ1). }
    induction w in σ, σ', π, φ, Hs |- *; destruct Hs as [τ a τ' a' Ht Hcr];
      destruct Ht as [τ0| |ρ ρ' Hρ|P P' HP|ca ta ha σ1 σ2 ca' ta' ha' σ1' σ2' Hc Ht Hh Hs1 Hs2
                    |ca ta σ0 ca' ta' σ0' Hc Ht Hs0|σ1 σ2 σ1' σ2' Hs1 Hs2|σ1 σ2 σ1' σ2' Hs1 Hs2];
      simpl in *; try done.
    all: first
      [ intros (xx & Hw & Hp & Hk & Hf); exists xx; split_and!; [done|done|done|];
        by apply (pfitpt_at_cst _ _ _ xx ρ)
      | intros (cc & bb & xx & ff & Hw & Hp & Hf & Hl & Ha & Hq); exists cc, bb, xx, ff;
        split_and!; [done|done|by apply (pfits_at_cst _ _ _ xx P)|done|by eapply fle_trans|done]
      | intros (Hp & Hq & Hf); split_and!; [done|done|]; by eapply Harr
      | intros (Hp & Hfe & H); split_and!; [done|done|]; intros W' j r tk Hb Hj Hm;
        apply (proj2 (IH j Hj) W' σ0 σ0' r r ∅ ∅ tk tk ca ca'); [done|lia|lia|done|];
        apply H; [done|done|by apply Ht]
      | intros (π1 & π2 & Hπ & Hd & H1 & H2); exists π1, π2; split_and!; [done|done| |];
        [eapply IHw1|eapply IHw2]; try done; by apply cst_cadd
      | apply IHw; by apply cst_cadd ]. }
  split; [exact HV|].
  intros W σ σ' r r' π φ tk tk' d d' e Hs Hr Htk Hd H.
  destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H. intros W' g π' φ' Hb Hk G1 G2.
  destruct (H W' g π' φ' Hb Hk G1 G2) as (Hc & Hw & Hv & Hst).
  assert (IHE : ∀ j, j ≤ n → ∀ W σ σ' r r' π φ tk tk' d d' e, σ ⊑c σ' → r' ≤ r → tk ≤ tk' → fle d d' →
    FuelE j W σ r π φ tk d e → FuelE j W σ' r' π φ tk' d' e) by (intros j Hj; apply (IH j); lia).
  split_and!; [done|done| |].
  { intros Hval. destruct (Hv Hval) as [Hr0 HV0]. split; [lia|].
    apply Vfuel_eq. apply (HV W' σ σ'); [done|]. by apply Vfuel_eq. }
  intros α e' Hs'. specialize (Hst α e' Hs').
  assert (Htick : ∀ s, (∀ o, sl_end s = Some o → ftick_ok o φ' ∧ fle (Some 1) d) →
    ∀ o, sl_end s = Some o → ftick_ok o φ' ∧ fle (Some 1) d').
  { intros s H1 o Ho. destruct (H1 o Ho). split; [done|by eapply fle_trans]. }
  assert (Hd1 := fle_ftick_mono d d' Hd).
  destruct α as [|[o w|o w|o|cd|o b|o b]|c x|w]; simpl in Hst |- *.
  - by apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ d).
  - destruct Hst as [H1 H2]. split; [exact (Htick (SRecv o w) H1)|].
    intros k j πi φi Hk' Hj Hdj Hin Hv'.
    apply (IHE j Hj _ σ _ r _ _ _ tk _ (ftick d)); [done..|]. by apply (H2 k).
  - destruct Hst as (H1 & H0 & H2 & H3 & H4). split_and!; [exact (Htick (SSend o w) H1)|done|done|done|].
    by apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ (ftick d)).
  - destruct Hst as [H1 H2]. split; [exact (Htick (SClos o) H1)|].
    by apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ (ftick d)).
  - destruct Hst as (H1 & H0 & H2 & H3). split_and!; [exact (Htick (SLink cd) H1)|done|lia|].
    apply (IHE n ltac:(lia) _ σ _ r _ _ _ (tk - 1) _ d); [done|done|lia|done|done].
  - destruct Hst as [H1 H2]. split; [exact (Htick (SSel o b) H1)|]. intros Hso.
    apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ (ftick d)); [done..|]. by apply H2.
  - destruct Hst as [H1 H2]. split; [exact (Htick (SBra o b) H1)|]. intros Hso.
    apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ (ftick d)); [done..|]. by apply H2.
  - intros Hc1 Hc2. apply (IHE n ltac:(lia) _ σ _ r _ _ _ tk _ d); [done..|]. by apply Hst.
  - destruct Hst as (H0 & H1 & H2 & H3). split_and!; [done|done| |].
    + apply (IHE n ltac:(lia) _ cany _ 0 _ _ _ (Nat.div2 (S tk)) _ None); [apply cst_refl|lia| |done|done].
      apply (div2_mono (S tk) (S tk')). lia.
    + apply (IHE n ltac:(lia) _ σ _ r _ _ _ (Nat.div2 tk) _ d); [done|done| |done|done].
      by apply div2_mono.
Qed.

(** F5, subsumption. *)
Lemma Vfuel_sub n W σ σ' π φ w : σ ⊑c σ' → Vfuel n W σ π φ w → Vfuel n W σ' π φ w.
Proof. apply (proj1 (sub_mono n)). Qed.

(** F4: the result type along ⊑c, a smaller reserve, more tickets, a
    larger frame. *)
Lemma FuelE_mono n W σ σ' r r' π φ tk tk' d d' e :
  σ ⊑c σ' → r' ≤ r → tk ≤ tk' → fle d d' →
  FuelE n W σ r π φ tk d e → FuelE n W σ' r' π φ tk' d' e.
Proof. apply (proj2 (sub_mono n)). Qed.

Lemma FuelE_frame_mono n W σ r π φ tk d d' e :
  fle d d' → FuelE n W σ r π φ tk d e → FuelE n W σ r π φ tk d' e.
Proof. intros Hd. apply FuelE_mono; [apply cst_refl|lia|lia|done]. Qed.

Lemma FuelE_reserve_mono n W σ r r' π φ tk d e :
  r' ≤ r → FuelE n W σ r π φ tk d e → FuelE n W σ r' π φ tk d e.
Proof. intros Hr. apply FuelE_mono; [apply cst_refl|done|lia|apply fle_refl]. Qed.

Lemma FuelE_ty_mono n W σ σ' r π φ tk d e :
  σ ⊑c σ' → FuelE n W σ r π φ tk d e → FuelE n W σ' r π φ tk d e.
Proof. intros Hs. apply FuelE_mono; [done|lia|lia|apply fle_refl]. Qed.

(** Every FuelE weakens to the thread level. *)
Lemma FuelE_thread n W σ r π φ tk d e : FuelE n W σ r π φ tk d e → FuelT n W π φ tk e.
Proof. apply FuelE_mono; [apply cst_any|lia|lia|apply fle_None]. Qed.

(** ** F5: counters *)

(** i units less. *)
Definition fminus (i : nat) (f : fuel) : fuel := fsub f (Some i).

Lemma fminus_0 f : fminus 0 f = f.
Proof. destruct f; simpl; [f_equal; lia|done]. Qed.

Lemma fminus_S i f : fminus i (ftick f) = fminus (S i) f.
Proof. destruct f; simpl; [f_equal; lia|done]. Qed.

Lemma fminus_le i f : fle (fminus i f) f.
Proof. destruct f; simpl; lia. Qed.

Lemma ftick_le f : fle (ftick f) f.
Proof. destruct f; simpl; lia. Qed.

Lemma cadd_cadd a b σ : cadd a (cadd b σ) = cadd (fadd a b) σ.
Proof. destruct σ as [τ c]. destruct a, b, c; simpl; try done. f_equal. f_equal. lia. Qed.

(** The counters of a value lose i units, its credit pays them. A send
    and a spawn hand ends on with one unit less (plan §19.7, C-Send,
    C-Spawn). *)
Lemma Vfuel_minus n W i σ π φ w :
  Vfuel n W (cadd (Some i) σ) π φ w → Vfuel n W σ π (fminus i <$> φ) w.
Proof.
  rewrite !Vfuel_eq.
  induction w in σ, π, φ |- *; destruct σ as [τ a]; destruct τ; simpl; try done.
  all: first
    [ intros H; exact H
    | intros (cc & bb & xx & ff & Hw & Hp & Hf & Hl & Ha & Hq); exists cc, bb, xx, (fminus i ff);
      split_and!; [done|done|done|by rewrite lookup_fmap, Hl| |done];
      destruct a, ff; simpl in *; lia
    | intros (Hp & Hq & Hfl & HF); split; [done|]; split; [done|]; split; [|exact HF];
      intros o f Ho; apply lookup_fmap_Some in Ho as (f0 & <- & Ho); specialize (Hfl o f0 Ho);
      destruct a, f0; simpl in *; lia
    | intros (π1 & π2 & Hπ & Hd & H1 & H2); exists π1, π2; split_and!; [done|done| |];
      rewrite mres_fmap; [apply IHw1|apply IHw2]; by rewrite cadd_cadd
    | intros H; apply IHw; by rewrite cadd_cadd ].
Qed.

(** [clow m σ σ']: σ′ is σ restated at current lower bound m. An end
    needs counter m, a closure with floor h ≤ m credit m − h, a type
    without ends nothing. The arrow and box clauses keep their
    meaning. This is the restating Θ^h of C-Abs (plan §19.4). *)
Inductive clow (m : nat) : cta → cta → Prop :=
  | ClFree τ a a' : cfree τ → clow m (CTa τ a) (CTa τ a')
  | ClAny a a' : clow m (CTa CAny a) (CTa CAny a')
  | ClEnd P a : clow m (CTa (CEnd P) a) (CTa (CEnd P) (Some m))
  | ClArr c t h σ1 σ2 a : h ≤ m → clow m (CTa (CArr c t h σ1 σ2) a) (CTa (CArr c t h σ1 σ2) (Some (m - h)))
  | ClProd σ1 σ2 σ1' σ2' a :
      clow m σ1 σ1' → clow m σ2 σ2' → clow m (CTa (CProd σ1 σ2) a) (CTa (CProd σ1' σ2') (Some 0))
  | ClSum σ1 σ2 σ1' σ2' a :
      clow m σ1 σ1' → clow m σ2 σ2' → clow m (CTa (CSum σ1 σ2) a) (CTa (CSum σ1' σ2') (Some 0)).

Lemma clow_cadd m a σ σ' : clow m σ σ' → clow m (cadd a σ) σ'.
Proof. destruct 1; simpl; by constructor. Qed.

(** A type without ends holds no points and reads neither its credit
    nor the counters. *)
Lemma Vfdef_cfree (E : nat → epred) (V : nat → vpred) n W τ :
  cfree τ → ∀ w a π φ, Vfdef E V n W (CTa τ a) π φ w → π = ∅ ∧ ∀ a' φ', Vfdef E V n W (CTa τ a') π φ' w.
Proof.
  induction 1 as [| |c t σ|τ1 a1 τ2 a2 H1 IH1 H2 IH2|τ1 a1 τ2 a2 H1 IH1 H2 IH2];
    intros w a π φ; destruct w; simpl; try (intros []; fail).
  all: first
    [ intros [Hw ->]; split; [done|intros; by split]
    | intros (xx & Hw & -> & Hk & Hf); split; [done|intros; by exists xx]
    | intros [-> H]; split; [done|intros; by split]
    | intros (π1 & π2 & -> & Hd & Hu & Hv);
      destruct (IH1 _ _ _ _ Hu) as [-> Hu']; destruct (IH2 _ _ _ _ Hv) as [-> Hv'];
      rewrite map_empty_union; split; [done|]; intros a' φ'; exists ∅, ∅;
      split_and!; [by rewrite map_empty_union|set_solver|apply Hu'|apply Hv']
    | intros Hu; destruct (IH1 _ _ _ _ Hu) as [-> Hu']; split; [done|]; intros; apply Hu'
    | intros Hu; destruct (IH2 _ _ _ _ Hu) as [-> Hu']; split; [done|]; intros; apply Hu' ].
Qed.

(** F5, recount. The counters of a value change to any map at or above
    m on its points, and its type is restated at lower bound m. Only
    the end clause and the floor check read the counters. *)
Lemma Vfuel_recount n W m σ σ' π φ φ' w :
  clow m σ σ' → (∀ o f, φ' !! o = Some f → fle (Some m) f) → dom π ⊆ dom φ' →
  Vfuel n W σ π φ w → Vfuel n W σ' π φ' w.
Proof.
  rewrite !Vfuel_eq. intros Hl. revert π φ φ'.
  induction w in σ, σ', Hl |- *; intros π φ φ' Hm Hd;
    destruct Hl as [τ a a' Hf|a a'|P a|ca ta ha σ1 σ2 a Hh|σ1 σ2 σ1' σ2' a H1 H2|σ1 σ2 σ1' σ2' a H1 H2];
    try (intros H; by destruct (Vfdef_cfree _ _ _ _ τ Hf _ _ _ _ H) as [_ H']);
    simpl; try done.
  all: first
    [ intros (cc & bb & xx & ff & [=] & _); fail
    | intros (cc & bb & xx & ff & Hw & Hp & Hf & Hl & Ha & Hq); simplify_eq;
      assert ((cc, bb) ∈ dom φ') as [f' Hf']%elem_of_dom by (apply Hd; set_solver);
      exists cc, bb, xx, f'; split_and!; [done|done|done|done|by apply (Hm (cc, bb))|done]
    | intros (Hp & Hq & Hfl & HF); split; [done|]; split; [done|]; split; [|exact HF];
      intros o f Ho; specialize (Hm o f Ho); destruct f; simpl in *; lia
    | intros (π1 & π2 & -> & Hd' & Hu & Hv); exists π1, π2; split_and!; [done|done| |];
      [eapply IHw1; [rewrite cadd_0; by apply clow_cadd| | |exact Hu]
      |eapply IHw2; [rewrite cadd_0; by apply clow_cadd| | |exact Hv]];
      [intros o f Ho; apply lookup_mres_Some in Ho as [Ho _]; by apply (Hm o)
      |rewrite dom_mres; rewrite dom_union_L in Hd; set_solver
      |intros o f Ho; apply lookup_mres_Some in Ho as [Ho _]; by apply (Hm o)
      |rewrite dom_mres; rewrite dom_union_L in Hd; set_solver]
    | intros Hu; eapply IHw; [rewrite cadd_0; by apply clow_cadd|done|done|exact Hu] ].
Qed.

(** ** The clauses of FuelE at index n + 1, at the identity *)

Lemma fuel_core n W σ r π φ tk d e :
  FuelE (S n) W σ r π φ tk d e →
  fcap W π φ ∧ fwait W π e ∧
  (is_val e = true → r ≤ tk ∧ Vfdef FuelE Vfuel (S n) W σ π φ e) ∧
  ∀ α e', tstep e α e' → Fobl FuelE Vfuel n W σ r π φ tk d α e'.
Proof.
  intros H. apply FuelE_S in H.
  pose proof (H W id π φ (wbext_refl W) (kinj_id π) (renk_id π) (renk_id φ)) as H'.
  by rewrite emap_id in H'.
Qed.

(** ** F2: values *)

Lemma FuelE_val n W σ r π φ tk d v :
  is_val v = true → r ≤ tk → fcap_ext W π φ → Vfuel n W σ π φ v → FuelE n W σ r π φ tk d v.
Proof.
  destruct n as [|n]; [intros; apply FuelE_0|]. intros Hv Hr Hc HV.
  apply FuelE_S. intros W' g π' φ' Hb Hk G1 G2.
  assert (dom φ ⊆ dom π) as Hd by (apply (fcap_dom W), fcap_ext_here, Hc).
  assert (Hnst : ∀ α e', ¬ tstep (emap g v) α e').
  { intros α e' Hst. eapply val_no_tstep; [exact Hst|by rewrite is_val_emap, Hv]. }
  split_and!.
  - eapply renk_fcap; [apply Hc, Hb|done|done].
  - intros s e' o Hst. by destruct (Hnst _ _ Hst).
  - intros _. split; [done|]. apply Vfuel_eq.
    apply (Vfuel_rename (S n) W' σ π φ v g π' φ' Hk Hd G1 G2). by apply (Vfuel_wbext _ W).
  - intros α e' Hst. by destruct (Hnst _ _ Hst).
Qed.

(** ** Evaluation contexts *)

Abbreviation ectx := (list frame).

Fixpoint efill (K : ectx) (e : expr) : expr :=
  match K with [] => e | f :: K' => fill_frame f (efill K' e) end.

Definition frame_emap (g : chan → chan) (f : frame) : frame :=
  match f with
  | FAppL e2 => FAppL (emap g e2)
  | FAppR v1 => FAppR (emap g v1)
  | FPairL e2 => FPairL (emap g e2)
  | FPairR v1 => FPairR (emap g v1)
  | FLetU e2 => FLetU (emap g e2)
  | FLetP e2 => FLetP (emap g e2)
  | FInj1 => FInj1
  | FInj2 => FInj2
  | FCase e1 e2 => FCase (emap g e1) (emap g e2)
  end.

Definition kemap (g : chan → chan) (K : ectx) : ectx := frame_emap g <$> K.

(** Right-of-value frames hold values. *)
Definition ectx_ok (K : ectx) : Prop := Forall frame_val K.

Lemma emap_efill (g : chan → chan) K e : emap g (efill K e) = efill (kemap g K) (emap g e).
Proof. induction K as [|f K IH]; simpl; [done|]. rewrite <-IH. by destruct f. Qed.

Lemma kemap_kemap (g h : chan → chan) K : kemap g (kemap h K) = kemap (g ∘ h) K.
Proof. induction K as [|f K IH]; simpl; [done|]. rewrite IH. f_equal. destruct f; simpl; by rewrite ?emap_emap. Qed.

Lemma ectx_ok_emap (g : chan → chan) K : ectx_ok K → ectx_ok (kemap g K).
Proof.
  induction 1 as [|f K Hf HK IH]; simpl; constructor; [|done].
  destruct f; simpl in *; try done; by rewrite is_val_emap.
Qed.

Lemma efill_not_val K e : is_val e = false → is_val (efill K e) = false.
Proof.
  intros Hv. induction K as [|f K IH]; simpl; [done|].
  destruct f; simpl; rewrite ?IH; try done. apply andb_false_r.
Qed.

Lemma tstep_efill K e α e' : ectx_ok K → tstep e α e' → tstep (efill K e) α (efill K e').
Proof. induction 1 as [|f K Hf HK IH]; simpl; [done|]. intros Hst. apply tstep_fill; auto. Qed.

Lemma tstep_efill_inv K e α E' :
  ectx_ok K → is_val e = false → tstep (efill K e) α E' → ∃ e', tstep e α e' ∧ E' = efill K e'.
Proof.
  intros HK Hv. revert E'. induction HK as [|f K Hf HK IH]; simpl; intros E' Hst; [by exists E'|].
  assert (Hnv : ¬ is_val (efill K e)) by (intros Hc; by rewrite (efill_not_val K e Hv) in Hc).
  destruct (tstep_fill_inv f (efill K e) α E' Hf Hnv Hst) as (e'' & Hst' & ->).
  destruct (IH e'' Hst') as (e' & He' & ->). by exists e'.
Qed.

(** ** F3: β-expansion *)

Lemma val_emap_no_step (g : chan → chan) v α e' : is_val v → tstep (emap g v) α e' → False.
Proof. intros Hv Hst. eapply val_no_tstep; [exact Hst|by rewrite is_val_emap]. Qed.

(** A head β redex has one step, under every renaming. *)
Lemma head_beta_det (g : chan → chan) e e' α e2 :
  head_step e LBeta e' → tstep (emap g e) α e2 → α = LBeta ∧ e2 = emap g e'.
Proof.
  intros Hh Hst. inversion Hh; subst; simpl in Hst.
  - apply tstep_app_inv in Hst as [(e1' & H1 & _)|[(_ & e2' & H2 & _)|(_ & _ & Hh2)]].
    + by apply val_no_tstep in H1.
    + by destruct (val_emap_no_step g v _ _ H H2).
    + inversion Hh2; subst. by rewrite emap_subst1.
  - apply tstep_letu_inv in Hst as [(e1' & H1 & _)|(_ & -> & ->)]; [by apply val_no_tstep in H1|done].
  - apply tstep_letp_inv in Hst as [(e1' & H1 & _)|(u' & v' & [= <- <-] & _ & _ & -> & ->)].
    + exfalso. eapply (val_emap_no_step g (Pair u v)); [simpl; by apply andb_True|exact H1].
    + by rewrite emap_subst2.
  - apply tstep_app_inv in Hst as [(e1' & H1 & _)|[(_ & e2' & H2 & _)|(_ & _ & Hh2)]].
    + by apply val_no_tstep in H1.
    + by apply val_no_tstep in H2.
    + by inversion Hh2.
  - apply tstep_app_inv in Hst as [(e1' & H1 & _)|[(_ & e2' & H2 & _)|(_ & _ & Hh2)]].
    + by apply val_no_tstep in H1.
    + by apply val_no_tstep in H2.
    + by inversion Hh2.
  - apply tstep_case_inv in Hst as [(e'' & H1 & _)|[(v' & [= <-] & _ & -> & ->)|(v' & [=] & _)]].
    + exfalso. by apply (val_emap_no_step g (Inj1 v) _ _ H H1).
    + by rewrite emap_subst1.
  - apply tstep_case_inv in Hst as [(e'' & H1 & _)|[(v' & [=] & _)|(v' & [= <-] & _ & -> & ->)]].
    + exfalso. by apply (val_emap_no_step g (Inj2 v) _ _ H H1).
    + by rewrite emap_subst1.
  - apply tstep_app_inv in Hst as [(e1' & H1 & _)|[(_ & e2' & H2 & _)|(_ & _ & Hh2)]].
    + by apply val_no_tstep in H1.
    + by apply val_no_tstep in H2.
    + inversion Hh2; subst. by rewrite emap_subst1.
Qed.

Lemma head_not_val e α e' : head_step e α e' → is_val e = false.
Proof. intros H. destruct (is_val e) eqn:E; [|done]. exfalso. eapply val_head_step; [exact H|by rewrite E]. Qed.

(** A head β step in an evaluation context: FuelE of the successor at
    n gives FuelE of the redex at n + 1. *)
Lemma FuelE_beta n W σ r π φ tk d K e e' :
  ectx_ok K → head_step e LBeta e' → fcap_ext W π φ →
  FuelE n W σ r π φ tk d (efill K e') → FuelE (S n) W σ r π φ tk d (efill K e).
Proof.
  intros HK Hh Hc HF. apply FuelE_S. intros W' g π' φ' Hb Hk G1 G2.
  pose proof (head_not_val _ _ _ Hh) as Hnv.
  assert (Hnv' : is_val (emap g e) = false) by by rewrite is_val_emap.
  assert (HK' := ectx_ok_emap g K HK).
  rewrite emap_efill. split_and!.
  - eapply renk_fcap; [apply Hc, Hb|done|done].
  - intros s e2 o Hst. destruct (tstep_efill_inv _ _ _ _ HK' Hnv' Hst) as (e3 & Hst3 & ->).
    by destruct (head_beta_det g e e' _ _ Hh Hst3).
  - intros Hv. by rewrite efill_not_val in Hv.
  - intros α e2 Hst. destruct (tstep_efill_inv _ _ _ _ HK' Hnv' Hst) as (e3 & Hst3 & ->).
    destruct (head_beta_det g e e' _ _ Hh Hst3) as [-> ->]. simpl.
    rewrite <-emap_efill. apply (FuelE_rename n W' σ r π φ tk d _ g); [done|done|done|].
    by apply (FuelE_wbext n W).
Qed.

(** ** F1: bind

    A hole e runs in an evaluation context K. The hole holds π1, φ1,
    the context πK, φK, disjoint from the hole. The hole has frame c1:
    it acts at most c1 times before it returns. Each action ticks the
    context's counters ([kupd]) and spends a unit of the composite's
    frame d, so the context's counters must be at least c1 ([fabove]).
    The continuation [fkont] holds after any i ≤ c1 actions, for every
    value the hole returns at its result type σ1 with reserve r1, and
    for every renaming of the context, because FuelE quantifies over
    renamings. Tickets flow unchanged, a spawn's child is the hole's
    child, a receive adds ends to the hole. *)

(** The counters of the context: each at least c. *)
Definition fabove (c : fuel) (φ : gmap cend fuel) : Prop := ∀ o f, φ !! o = Some f → fle c f.

(** The context's counters after a step of the hole: an action ticks them. *)
Definition kupd (α : tlabel) (φ : gmap cend fuel) : gmap cend fuel :=
  match α with
  | LSess s => match sl_end s with Some _ => ftick <$> φ | None => φ end
  | _ => φ
  end.

(** A step of the hole leaves the context's ends alone: it acts on an
    end of the hole, hands on ends of the hole, and creates or moves to
    ends the context does not hold. *)
Definition fsep (π1 πK : gmap cend point) (α : tlabel) : Prop :=
  match α with
  | LBeta => True
  | LNew c _ => ((c, true) ∉ dom πK) ∧ ((c, false) ∉ dom πK)
  | LSpawn w => fends w ## dom πK
  | LSess s =>
      sl_out s ## dom πK ∧
      ∀ o, sl_end s = Some o →
        o ∈ dom π1 ∧ (o ∉ sl_out s) ∧ ∀ k o' k', sl_next s k = Some (o', k') → o' ∉ dom πK
  end.

Lemma fupd_union W π1 φ1 πK φK α :
  dom φK = dom πK → dom π1 ## dom πK → fsep π1 πK α →
  fupd W (π1 ∪ πK) (φ1 ∪ φK) α = ((fupd W π1 φ1 α).1 ∪ πK, (fupd W π1 φ1 α).2 ∪ kupd α φK).
Proof.
  intros HdK Hd Hs. destruct α as [|s|c x|w]; simpl in *.
  - done.
  - destruct Hs as [Hout Ho].
    rewrite (mrem_union_l _ π1 πK) by done. rewrite (mrem_union_l _ φ1 φK) by (by rewrite HdK).
    unfold fact. destruct (sl_end s) as [o|] eqn:E; [|done].
    destruct (Ho o eq_refl) as (Ho1 & Hno & Hnext).
    assert (o ∈ dom (mrem (sl_out s) π1)) as [k Hk]%elem_of_dom by (rewrite dom_mrem; set_solver).
    erewrite lookup_union_Some_l by exact Hk. rewrite Hk.
    assert (πK !! o = None) as N1 by (apply not_elem_of_dom; set_solver).
    assert (φK !! o = None) as N2 by (apply not_elem_of_dom; rewrite HdK; set_solver).
    destruct (sl_next s k) as [[o' k']|]; simpl;
      rewrite !delete_union, (delete_id πK), (delete_id φK) by done;
      by rewrite ?map_fmap_union, ?insert_union_l.
  - by rewrite !insert_union_l.
  - rewrite (mrem_union_l _ π1 πK) by done. rewrite (mrem_union_l _ φ1 φK) by (by rewrite HdK). done.
Qed.

Lemma fupd_disj W π1 φ1 πK α :
  dom π1 ## dom πK → fsep π1 πK α → dom (fupd W π1 φ1 α).1 ## dom πK.
Proof.
  intros Hd Hs. destruct α as [|s|c x|w]; simpl in *.
  - done.
  - destruct Hs as [Hout Ho]. unfold fact. destruct (sl_end s) as [o|] eqn:E; [|simpl; rewrite dom_mrem; set_solver].
    destruct (mrem (sl_out s) π1 !! o) as [k|]; [|simpl; rewrite dom_mrem; set_solver].
    destruct (Ho o eq_refl) as (_ & _ & Hn).
    destruct (sl_next s k) as [[o' k']|] eqn:En; simpl.
    + specialize (Hn k o' k' En). rewrite dom_insert_L, dom_delete_L, dom_mrem. set_solver.
    + rewrite dom_delete_L, dom_mrem. set_solver.
  - destruct Hs as [H1 H2]. rewrite !dom_insert_L. destruct (pt_pol x); simpl; set_solver.
  - rewrite dom_mrem. set_solver.
Qed.

Lemma fupd_dom_eq W π φ α : dom φ = dom π → dom (fupd W π φ α).2 = dom (fupd W π φ α).1.
Proof.
  intros H. destruct α as [|s|c x|w]; simpl.
  - done.
  - unfold fact. destruct (sl_end s) as [o|]; simpl; [|by rewrite !dom_mrem, H].
    destruct (mrem (sl_out s) π !! o) as [k|]; simpl; [|by rewrite !dom_mrem, H].
    destruct (sl_next s k) as [[o' k']|]; simpl;
      by rewrite ?dom_insert_L, dom_fmap_L, !dom_delete_L, !dom_mrem, H.
  - by rewrite !dom_insert_L, H.
  - by rewrite !dom_mrem, H.
Qed.

Lemma dom_kupd α φ : dom (kupd α φ) = dom φ.
Proof. destruct α as [|s| |]; simpl; try done. destruct (sl_end s); [apply dom_fmap_L|done]. Qed.

Lemma fcap_ext_kupd W π φ α : fcap_ext W π φ → fcap_ext W π (kupd α φ).
Proof.
  intros H. destruct α as [|s| |]; simpl; try done.
  destruct (sl_end s); [|done]. apply fcap_ext_fmap; [apply ftick_le|done].
Qed.

Lemma fabove_kupd c φ α : fabove c φ → fabove (dupd c α) (kupd α φ).
Proof.
  intros H. destruct α as [|s| |]; simpl; try done. destruct (sl_end s); [|done].
  intros o f Ho. apply lookup_fmap_Some in Ho as (f0 & <- & Ho). by apply fle_ftick_mono, (H o).
Qed.

Lemma fle_dupd c d α : fle c d → fle (dupd c α) (dupd d α).
Proof. intros H. destruct α as [|s| |]; simpl; try done. destruct (sl_end s); [by apply fle_ftick_mono|done]. Qed.

Lemma fchild_union π1 φ1 πK φK w :
  fends w ## dom πK → dom φK = dom πK → fchild (π1 ∪ πK) (φ1 ∪ φK) w = fchild π1 φ1 w.
Proof. intros H HdK. unfold fchild. rewrite !mres_union_l; [done| |done]. by rewrite HdK. Qed.

Lemma union_swap {Y : Type} (m1 m2 m3 : gmap cend Y) : dom m2 ## dom m3 → (m1 ∪ m2) ∪ m3 = (m1 ∪ m3) ∪ m2.
Proof.
  intros Hd. rewrite <-!(assoc_L (∪)). f_equal. apply map_union_comm. by apply map_disjoint_dom.
Qed.

Lemma fmap_fminus_0 (m : gmap cend fuel) : fminus 0 <$> m = m.
Proof.
  rewrite <-(map_fmap_id m) at 2. apply map_fmap_ext. intros o f _. apply fminus_0.
Qed.

(** The continuation: after i ≤ c1 actions of the hole, for every value
    v the hole returns at σ1 with points π1 and counters φ1 under the
    cap, at every index j ≤ n and every ticket count meeting r1, in
    every extension of the world and under every injective renaming of
    the context. *)
Definition fkont (n : nat) (W : world) (σ1 : cta) (r1 : nat) (σ : cta) (r : nat) (c1 d : fuel)
    (πK : gmap cend point) (φK : gmap cend fuel) (K : ectx) : Prop :=
  ∀ W' (g : chan → chan) πK' φK' i j v π1 φ1 tk,
    wbext W W' → kinj g πK → renk g πK πK' → renk g φK φK' →
    fle (Some i) c1 → j ≤ n → is_val v = true → r1 ≤ tk →
    dom π1 ## dom πK' → dom φ1 = dom π1 → fcap_ext W' π1 φ1 →
    Vfuel j W' σ1 π1 φ1 v →
    FuelE j W' σ r (π1 ∪ πK') (φ1 ∪ (fminus i <$> φK')) tk (fminus i d) (efill (kemap g K) v).

Lemma fkont_down m n W σ1 r1 σ r c1 d πK φK K :
  m ≤ n → fkont n W σ1 r1 σ r c1 d πK φK K → fkont m W σ1 r1 σ r c1 d πK φK K.
Proof. intros Hmn H W' g πK' φK' i j v π1 φ1 tk Hb Hk H1 H2 Hi Hj. apply H; try done. lia. Qed.

Lemma fkont_rename n W σ1 r1 σ r c1 d πK φK K W0 (g : chan → chan) πK0 φK0 :
  wbext W W0 → kinj g πK → renk g πK πK0 → renk g φK φK0 →
  fkont n W σ1 r1 σ r c1 d πK φK K → fkont n W0 σ1 r1 σ r c1 d πK0 φK0 (kemap g K).
Proof.
  intros Hb Hk Hπ Hφ H W' g' πK' φK' i j v π1 φ1 tk Hb' Hk' Hπ' Hφ'.
  rewrite kemap_kemap. apply (H W' (g' ∘ g) πK' φK').
  - by eapply wbext_trans.
  - by apply (kinj_compose g' g πK πK0).
  - by apply (renk_compose g' g πK πK0 πK').
  - by apply (renk_compose g' g φK φK0 φK').
Qed.

Lemma fkont_tick n W σ1 r1 σ r c1 d πK φK K :
  fle (Some 1) c1 → dom φK = dom πK →
  fkont n W σ1 r1 σ r c1 d πK φK K → fkont n W σ1 r1 σ r (ftick c1) (ftick d) πK (ftick <$> φK) K.
Proof.
  intros H1 Hd H W' g πK' φK'' i j v π1 φ1 tk Hb Hk Hπ Hφ Hi.
  assert (kinj g φK) as HkK by (apply (kinj_dom g πK); [by rewrite Hd|done]).
  destruct (renk_exists g φK HkK) as [φK' HφK].
  assert (φK'' = ftick <$> φK') as -> by (eapply renk_functional; [exact Hφ|by apply renk_fmap]).
  assert (Heq : fminus i <$> (ftick <$> φK') = fminus (S i) <$> φK').
  { rewrite <-map_fmap_compose. apply map_fmap_ext. intros o f _. apply fminus_S. }
  rewrite Heq, fminus_S. apply (H W' g πK' φK' (S i)); try done.
  destruct c1; simpl in *; lia.
Qed.

Lemma fkont_upd n W σ1 r1 σ r c1 d πK φK K α :
  (∀ s o, α = LSess s → sl_end s = Some o → fle (Some 1) c1) → dom φK = dom πK →
  fkont n W σ1 r1 σ r c1 d πK φK K → fkont n W σ1 r1 σ r (dupd c1 α) (dupd d α) πK (kupd α φK) K.
Proof.
  intros H1 Hd H. destruct α as [|s| |]; simpl; try done.
  destruct (sl_end s) as [o|] eqn:E; [|done]. by apply fkont_tick; [apply (H1 s o)| |].
Qed.

(** One step of the hole is one step of the composite. *)
Lemma Fobl_bind n W σ1 r1 σ r π1 φ1 πK φK tk c1 d K α e3 :
  dom φ1 = dom π1 → dom φK = dom πK → dom π1 ## dom πK → fabove c1 φK → fle c1 d →
  (∀ s o, α = LSess s → sl_end s = Some o → o ∈ dom π1) →
  (∀ j tk' πh φh, j ≤ n → dom πh ## dom πK → dom φh = dom πh →
     (∀ s o, α = LSess s → sl_end s = Some o → fle (Some 1) c1) →
     FuelE j W σ1 r1 πh φh tk' (dupd c1 α) e3 →
     FuelE j W σ r (πh ∪ πK) (φh ∪ kupd α φK) tk' (dupd d α) (efill K e3)) →
  Fobl FuelE Vfuel n W σ1 r1 π1 φ1 tk c1 α e3 →
  Fobl FuelE Vfuel n W σ r (π1 ∪ πK) (φ1 ∪ φK) tk d α (efill K e3).
Proof.
  intros Hd1 HdK Hd Hab Hcd Hact Hcont Hob.
  assert (Hlinv : ∀ o k, o ∈ dom π1 → (π1 ∪ πK) !! o = Some k → π1 !! o = Some k).
  { intros o k [k' Hk']%elem_of_dom H. erewrite lookup_union_Some_l in H by exact Hk'. congruence. }
  assert (Htick : ∀ s, (∀ o, sl_end s = Some o → ftick_ok o φ1 ∧ fle (Some 1) c1) →
     ∀ o, sl_end s = Some o → ftick_ok o (φ1 ∪ φK) ∧ fle (Some 1) d).
  { intros s H o Ho. destruct (H o Ho) as [Ht H1]. split; [|by eapply fle_trans].
    intros o' m Hne Hm. apply lookup_union_Some_raw in Hm as [Hm|[_ Hm]]; [by apply (Ht o')|].
    specialize (Hab o' _ Hm). destruct c1; simpl in *; lia. }
  assert (Hgo : ∀ tk', fsep π1 πK α → (∀ s o, α = LSess s → sl_end s = Some o → fle (Some 1) c1) →
     FuelE n W σ1 r1 (fupd W π1 φ1 α).1 (fupd W π1 φ1 α).2 tk' (dupd c1 α) e3 →
     FuelE n W σ r (fupd W (π1 ∪ πK) (φ1 ∪ φK) α).1 (fupd W (π1 ∪ πK) (φ1 ∪ φK) α).2 tk'
       (dupd d α) (efill K e3)).
  { intros tk' Hs H1 H. rewrite fupd_union by done. cbn [fst snd].
    apply Hcont; [lia|by apply fupd_disj|by apply fupd_dom_eq|done|done]. }
  assert (Hsolo : ∀ o, fsolo (π1 ∪ πK) o → fsolo π1 o).
  { intros o H b' Hb'. apply H. rewrite dom_union_L. set_solver. }
  assert (Hsucc : ∀ o b', o ∈ dom π1 → fsolo (π1 ∪ πK) o → (o.1, b') ∉ dom πK).
  { intros o b' Ho H Hin. assert ((o.1, b') = o) as Heq by (apply H; rewrite dom_union_L; set_solver).
    rewrite Heq in Hin. by apply (Hd o). }
  destruct α as [|s|c x|w].
  - exact (Hgo tk I ltac:(by intros ? ? [=]) Hob).
  - assert (Ho1 : ∀ o, sl_end s = Some o → o ∈ dom π1) by (intros o; by apply (Hact s o)).
    assert (Hno : ∀ o, sl_end s = Some o → o ∉ dom πK) by (intros o Ho; specialize (Ho1 o Ho); set_solver).
    destruct s as [o w|o w|o|cd|o b|o b]; unfold Fobl in Hob |- *; cbv beta iota in Hob |- *.
    + (* receive *)
      destruct Hob as [H1 H2]. split; [exact (Htick (SRecv o w) H1)|].
      assert (Hs : fsep π1 πK (LSess (SRecv o w))).
      { split; [simpl; set_solver|]. intros o0 [= <-]. split_and!; [by apply Ho1|set_solver|].
        intros k o' k' [= <- _]. by apply Hno. }
      intros k j πi φi Hk Hj Hdi Hin Hv.
      rewrite fupd_union in Hdi |- * by done. cbn [fst snd] in Hdi |- *. rewrite dom_union_L in Hdi.
      specialize (H2 k j πi φi (Hlinv o k (Ho1 o eq_refl) Hk) Hj ltac:(set_solver) Hin Hv).
      destruct Hin as (Dπ & Dφ & _).
      rewrite (union_swap _ πK πi) by set_solver.
      rewrite (union_swap _ (kupd _ φK) φi) by (rewrite dom_kupd, HdK, Dφ, <-Dπ; set_solver).
      apply (Hcont j tk); [lia| | |by intros ? ? [= <-]; destruct (H1 o eq_refl)|exact H2].
      * rewrite dom_union_L. pose proof (fupd_disj W π1 φ1 πK _ Hd Hs). set_solver.
      * rewrite !dom_union_L, fupd_dom_eq, Dφ, Dπ by done. done.
    + (* send *)
      destruct Hob as (H1 & Hheld & Htr & HV & HE).
      assert (Hs : fsep π1 πK (LSess (SSend o w))).
      { split; [simpl; set_solver|]. intros o0 [= <-]. split_and!; [by apply Ho1|simpl; set_solver|].
        intros k o' k' [= <- _]. by apply Hno. }
      split_and!.
      * exact (Htick (SSend o w) H1).
      * rewrite dom_union_L. set_solver.
      * intros o2 k Ho2 Hk. apply (Htr o2 k Ho2), Hlinv; [set_solver|done].
      * intros k Hk. rewrite !mres_union_l by (rewrite ?HdK; set_solver).
        apply HV, Hlinv; [by apply Ho1|done].
      * apply (Hgo tk Hs); [by intros ? ? [= <-]; destruct (H1 o eq_refl)|exact HE].
    + (* close *)
      destruct Hob as [H1 HE]. split; [exact (Htick (SClos o) H1)|].
      apply (Hgo tk); [|by intros ? ? [= <-]; destruct (H1 o eq_refl)|exact HE].
      split; [simpl; set_solver|]. intros o0 [= <-]. split_and!; [by apply Ho1|set_solver|done].
    + (* link *)
      destruct Hob as (H1 & Hcd0 & Htk & HE). split_and!; [exact (Htick (SLink cd) H1)|rewrite dom_union_L; set_solver|done|].
      apply (Hgo (tk - 1)); [|by intros ? ? [= <-]|exact HE].
      split; [simpl; set_solver|done].
    + (* select *)
      destruct Hob as [H1 HE]. split; [exact (Htick (SSel o b) H1)|]. intros Hso.
      apply (Hgo tk); [|by intros ? ? [= <-]; destruct (H1 o eq_refl)|by apply HE, Hsolo].
      split; [simpl; set_solver|]. intros o0 [= <-]. split_and!; [by apply Ho1|set_solver|].
      intros k o' k' [= <- _]. apply Hsucc; [by apply Ho1|done].
    + (* branch *)
      destruct Hob as [H1 HE]. split; [exact (Htick (SBra o b) H1)|]. intros Hso.
      apply (Hgo tk); [|by intros ? ? [= <-]; destruct (H1 o eq_refl)|by apply HE, Hsolo].
      split; [simpl; set_solver|]. intros o0 [= <-]. split_and!; [by apply Ho1|set_solver|].
      intros k o' k' [= <- _]. apply Hsucc; [by apply Ho1|done].
  - (* new *)
    intros Hc1 Hc2. rewrite dom_union_L in Hc1, Hc2.
    apply (Hgo tk); [simpl; set_solver|by intros ? ? [=]|]. apply Hob; set_solver.
  - (* spawn *)
    unfold Fobl in Hob |- *; cbv beta iota in Hob |- *.
    destruct Hob as (Hw & Hh & Hch & Hpar). split_and!.
    + rewrite dom_union_L. set_solver.
    + intros o m Ho Hm. apply lookup_union_Some_raw in Hm as [Hm|[Hn Hm]]; [by apply (Hh o)|].
      exfalso. apply not_elem_of_dom in Hn. apply Hn. rewrite Hd1. set_solver.
    + rewrite fchild_union; [exact Hch|set_solver|done].
    + apply (Hgo (Nat.div2 tk)); [simpl; set_solver|by intros ? ? [=]|exact Hpar].
Qed.

(** F1. *)
Lemma FuelE_bind n : ∀ W σ1 r1 σ r π1 φ1 πK φK tk c1 d K e,
  ectx_ok K → dom φ1 = dom π1 → dom φK = dom πK → dom π1 ## dom πK →
  fcap_ext W πK φK → fabove c1 φK → fle c1 d →
  fkont n W σ1 r1 σ r c1 d πK φK K →
  FuelE n W σ1 r1 π1 φ1 tk c1 e →
  FuelE n W σ r (π1 ∪ πK) (φ1 ∪ φK) tk d (efill K e).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros W σ1 r1 σ r π1 φ1 πK φK tk c1 d K e HK Hd1 HdK Hd HcK Hab Hcd Hkont HF.
  destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. intros W' g π' φ' Hb Hk Gπ Gφ.
  (* the renamed maps split into the hole's and the context's *)
  destruct (renk_union_split g π1 πK π' Hk Hd Gπ) as (π1' & πK' & -> & Rπ1 & RπK & Hd').
  assert (Hkφ : kinj g (φ1 ∪ φK)) by (apply (kinj_dom g (π1 ∪ πK)); [by rewrite !dom_union_L, Hd1, HdK|done]).
  destruct (renk_union_split g φ1 φK φ' Hkφ ltac:(by rewrite Hd1, HdK) Gφ) as (φ1' & φK' & -> & Rφ1 & RφK & _).
  assert (Hk1 : kinj g π1) by (apply (kinj_dom g (π1 ∪ πK)); [rewrite dom_union_L; set_solver|done]).
  assert (HkK : kinj g πK) by (apply (kinj_dom g (π1 ∪ πK)); [rewrite dom_union_L; set_solver|done]).
  assert (Hd1' : dom φ1' = dom π1') by (eapply renk_dom_eq; [exact Hd1|exact Rπ1|exact Rφ1]).
  assert (HdK' : dom φK' = dom πK') by (eapply renk_dom_eq; [exact HdK|exact RπK|exact RφK]).
  assert (HcK' : fcap_ext W' πK' φK') by (apply (fcap_ext_wbext W); [done|]; eapply fcap_ext_rename; eauto).
  assert (Hab' : fabove c1 φK').
  { intros o' f Ho'. destruct (proj2 RφK o' f Ho') as (o & -> & Ho). by apply (Hab o). }
  assert (Hkont' : fkont (S n) W' σ1 r1 σ r c1 d πK' φK' (kemap g K)) by (eapply fkont_rename; eauto).
  assert (HK' : ectx_ok (kemap g K)) by (by apply ectx_ok_emap).
  (* the hole, renamed *)
  apply FuelE_S in HF. destruct (HF W' g π1' φ1' Hb Hk1 Rπ1 Rφ1) as (Hc1 & Hw1 & Hv1 & Hs1).
  rewrite emap_efill.
  destruct (is_val (emap g e)) eqn:Hve.
  - (* the hole returned: the continuation after no action *)
    destruct (Hv1 eq_refl) as [Hr1 HV1].
    assert (Hc1e : fcap_ext W' π1' φ1').
    { intros W3 Hb3. destruct (HF W3 g π1' φ1' ltac:(by eapply wbext_trans) Hk1 Rπ1 Rφ1) as [Hc3 _]. exact Hc3. }
    pose proof (Hkont W' g πK' φK' 0 (S n) (emap g e) π1' φ1' tk Hb HkK RπK RφK
      ltac:(destruct c1; simpl; lia) ltac:(lia) Hve Hr1 Hd' Hd1' Hc1e ltac:(by apply Vfuel_eq)) as HC.
    rewrite fmap_fminus_0, fminus_0 in HC. by apply fuel_core.
  - split_and!.
    + apply fcap_union; [done|by apply fcap_ext_here|done].
    + intros s e2 o Hst Ho. destruct (tstep_efill_inv _ _ _ _ HK' Hve Hst) as (e3 & Hst3 & ->).
      destruct (Hw1 s e3 o Hst3 Ho) as (k & Hk1' & Hbud). exists k. split; [by apply lookup_union_Some_l|done].
    + intros Hv. by rewrite efill_not_val in Hv.
    + intros α e2 Hst. destruct (tstep_efill_inv _ _ _ _ HK' Hve Hst) as (e3 & Hst3 & ->).
      apply (Fobl_bind n W' σ1 r1 σ r π1' φ1' πK' φK' tk c1 d (kemap g K) α e3); try done.
      * intros s o -> Ho. destruct (Hw1 s e3 o Hst3 Ho) as (k & Hk' & _). by eapply elem_of_dom_2.
      * intros j tk' πh φh Hj Hdh Hdeq H1 Hh.
        apply (IH j ltac:(lia) W' σ1 r1 σ r πh φh πK' (kupd α φK') tk' (dupd c1 α) (dupd d α) (kemap g K) e3);
          try done.
        -- by rewrite dom_kupd.
        -- by apply fcap_ext_kupd.
        -- by apply fabove_kupd.
        -- by apply fle_dupd.
        -- apply (fkont_down j (S n)); [lia|]. by apply fkont_upd.
      * by apply Hs1.
Qed.

(** ** F6: protocol moves *)

Lemma pfits_node W x n b :
  pfits W x (PNode n b) →
  pt_known W x ∧ fle (Some n) (w_bud W x) ∧ (∃ m, w_bud W (pt_dual x) = Some m) ∧
  pfits_body (pt_known W) (w_bud W) (w_pc W) x b.
Proof.
  unfold pfits. intros H. inversion H as [|? ? ? Hk Hn Hd Hb]; subst. split_and!; [done|done| |done].
  destruct (w_bud W (pt_dual x)) as [m|]; [by exists m|done].
Qed.

(** A send node: the payload lies below the carrier's payload cost type,
    the successor fits at x + 1. *)
Lemma pfits_snd W x n σ P :
  pfits W x (PNode n (PSnd σ P)) → σ ⊑c w_pc W x ∧ pfits W (pt_shift 1 x) P.
Proof. intros H. destruct (pfits_node _ _ _ _ H) as (_ & _ & _ & Hb). by inversion Hb. Qed.

(** A receive node: the payload is read at the sender's point. *)
Lemma pfits_rcv W x n σ P :
  pfits W x (PNode n (PRcv σ P)) → w_pc W (pt_dual x) ⊑c σ ∧ pfits W (pt_shift 1 x) P.
Proof. intros H. destruct (pfits_node _ _ _ _ H) as (_ & _ & _ & Hb). by inversion Hb. Qed.

(** A select node: branch i continues at (x[i])‾. *)
Lemma pfits_sel W x n P1 P2 (i : bool) :
  pfits W x (PNode n (PSel P1 P2)) → pfits W (sel_pt x i) (if i then P2 else P1).
Proof. intros H. destruct (pfits_node _ _ _ _ H) as (_ & _ & _ & Hb). inversion Hb; subst. by destruct i. Qed.

(** A branch node: branch i continues at x[i]. *)
Lemma pfits_bra W x n P1 P2 (i : bool) :
  pfits W x (PNode n (PBra P1 P2)) → pfits W (bra_pt x i) (if i then P2 else P1).
Proof. intros H. destruct (pfits_node _ _ _ _ H) as (_ & _ & _ & Hb). inversion Hb; subst. by destruct i. Qed.

(** Protocol subsumption at a point (C-Sub on ends). *)
Lemma pfits_sub W x P P' : pfits W x P → cst_pro P P' → pfits W x P'.
Proof. apply pfits_at_cst. Qed.

(** An end that fits its protocol at a known point with a partner of
    finite budget, with a counter at least its credit. *)
Lemma Vfuel_end n W P a c b x φ f :
  pfits W x P → pt_known W x → w_bud W (pt_dual x) ≠ None → φ !! (c, b) = Some f → fle a f →
  Vfuel n W (CTa (CEnd P) a) {[(c, b) := x]} φ (Chan c b).
Proof.
  intros Hp Hk Hd Hf Ha. apply Vfuel_eq. simpl. exists c, b, x, f. split_and!; try done.
  intros o k Ho. apply lookup_singleton_Some in Ho as [_ <-]. done.
Qed.

(** The refill at a node meets its bound: an end refilled to the budget
    of its point is in [Vfuel] at credit n. *)
Lemma Vfuel_refill j W n bd c b x φ :
  pfits W x (PNode n bd) → φ !! (c, b) = Some (w_bud W x) →
  Vfuel j W (CTa (CEnd (PNode n bd)) (Some n)) {[(c, b) := x]} φ (Chan c b).
Proof.
  intros Hp Hf. destruct (pfits_node _ _ _ _ Hp) as (Hk & Hn & [m Hm] & _).
  apply (Vfuel_end _ _ _ _ _ _ _ _ _ Hp Hk ltac:(by rewrite Hm) Hf Hn).
Qed.

(** ** Values built from parts *)

Lemma Vfuel_pair n W σ1 σ2 a π1 π2 φ1 φ2 u v :
  dom π1 ## dom π2 → dom φ1 = dom π1 → dom φ2 = dom π2 →
  Vfuel n W (cadd a σ1) π1 φ1 u → Vfuel n W (cadd a σ2) π2 φ2 v →
  Vfuel n W (CTa (CProd σ1 σ2) a) (π1 ∪ π2) (φ1 ∪ φ2) (Pair u v).
Proof.
  intros Hd D1 D2 Hu Hv. rewrite Vfuel_eq in Hu, Hv |- *. simpl. exists π1, π2.
  assert (mres (dom π1) (φ1 ∪ φ2) = φ1) as ->.
  { rewrite mres_union_l by (rewrite D2; set_solver). apply map_eq. intros o. unfold mres.
    rewrite map_lookup_filter. destruct (φ1 !! o) eqn:E; simpl; [|done].
    rewrite option_guard_True; [done|]. rewrite <-D1. by eapply elem_of_dom_2. }
  assert (mres (dom π2) (φ1 ∪ φ2) = φ2) as ->.
  { apply map_eq. intros o. unfold mres. rewrite map_lookup_filter.
    destruct (decide (o ∈ dom π2)) as [Ho|Ho].
    - rewrite lookup_union_r; [|apply not_elem_of_dom; rewrite D1; set_solver].
      destruct (φ2 !! o); simpl; [by rewrite option_guard_True|done].
    - assert (φ2 !! o = None) as -> by (apply not_elem_of_dom; by rewrite D2).
      destruct ((φ1 ∪ φ2) !! o); simpl; [by rewrite option_guard_False|done]. }
  done.
Qed.

Lemma Vfuel_inj1 n W σ1 σ2 a π φ u :
  Vfuel n W (cadd a σ1) π φ u → Vfuel n W (CTa (CSum σ1 σ2) a) π φ (Inj1 u).
Proof. rewrite !Vfuel_eq. done. Qed.

Lemma Vfuel_inj2 n W σ1 σ2 a π φ u :
  Vfuel n W (cadd a σ2) π φ u → Vfuel n W (CTa (CSum σ1 σ2) a) π φ (Inj2 u).
Proof. rewrite !Vfuel_eq. done. Qed.

Lemma Vfuel_unit n W a φ : Vfuel n W (CTa CVal a) ∅ φ EUnit.
Proof. by apply Vfuel_eq. Qed.

Lemma Vfuel_any n W a π φ w : Vfuel n W (CTa CAny a) π φ w.
Proof. rewrite Vfuel_eq. destruct w; done. Qed.
