(** * The fundamental theorem of the cost judgment (lock-freedom plan §19.7, stage H4)

    [csem W Θ Γ e σ c t] is the semantic cost judgment. For every index
    n, every extension W′ of W, every renaming g of the channels of e
    that is injective on the ends of Θ, every substitution γ of values
    for Γ, and points and counters for the ends of Θ and γ that fit
    their cost types ([thsem], [gsem]), FuelE holds of the instance
    [subst γ (emap g e)] at result σ, frame c and every reserve and
    ticket count that meet t. The judgment reads cost types, the world,
    the values of γ and the channels the renaming hits. It reads no
    term beyond those values.

    One compatibility lemma per rule of static/CostTyping.v ([c_unit_sem]
    to [c_contract_sem]) and [ctyped_csem] by induction. [ctyped_fsem]
    turns a closed thread into [fsem], the form [LFP_term] needs. The
    examples sync and the callback server get their [fsem] this way.

    Three lemmas carry the sequencing. [sem_bind0] runs a hole that
    holds the whole environment in a context that holds nothing.
    [sem_bind1] runs a hole beside the rest of the environment, which
    ages by the hole's cost. [sem_bind2] runs a hole beside a value that
    an earlier hole returned. Each is F1 ([FuelE_bind]) with the
    environment renamed, moved to the later world and aged.

    The rules C-Abs, C-Box and C-SpawnLam build a closure or a box,
    whose map must be the ends of the value. Their lemmas take the
    syntactic facts [cfacts] of the term, which every derivation gives
    ([ctyped_cfacts]). Plan §19.14 records where this stage changed
    the definitions of H1 to H3. *)

From stdpp Require Import base gmap.
From LRGV Require Import lang.Semantics relation.Worlds lockfree.Instr lockfree.TauThread.
From LRGV Require Export lockfree.LFFuelBind static.CostTyping.

Implicit Types (W : world) (π : gmap cend point) (φ : gmap cend fuel) (n m i j r tk : nat)
  (Γ : cenv) (Θ : cthe) (σ : cta) (τ : cty) (γ : nat → expr) (c d : fuel) (t : tix) (o : cend).

(** ** The semantic judgment *)

(** The values of Γ, one disjoint part of the points per entry. The
    counters of an entry are those of its points. *)
Fixpoint gsem (n : nat) (W : world) (Γ : cenv) (γ : nat → expr)
    (π : gmap cend point) (φ : gmap cend fuel) : Prop :=
  match Γ with
  | [] => π = ∅
  | None :: Γ' => gsem n W Γ' (λ x, γ (S x)) π φ
  | Some σ :: Γ' =>
      ∃ π1 π2, π = π1 ∪ π2 ∧ dom π1 ## dom π2 ∧ is_val (γ 0) = true ∧
        Vfuel n W σ π1 (mres (dom π1) φ) (γ 0) ∧ gsem n W Γ' (λ x, γ (S x)) π2 φ
  end.

(** An end renamed by g. *)
Definition tkey (g : chan → chan) (o : cend) : cend := (g o.1, o.2).

(** The ends of Θ, renamed injectively by g, each at one point. *)
Definition thsem (n : nat) (W : world) (Θ : cthe) (g : chan → chan)
    (π : gmap cend point) (φ : gmap cend fuel) : Prop :=
  (∀ o1 o2, o1 ∈ dom Θ → o2 ∈ dom Θ → tkey g o1 = tkey g o2 → o1 = o2) ∧
  dom π = kimg g (dom Θ) ∧
  ∀ o σ, Θ !! o = Some σ → ∃ x, π !! tkey g o = Some x ∧
    Vfuel n W σ {[tkey g o := x]} (mres {[tkey g o]} φ) (Chan (g o.1) o.2).

(** Θ; Γ ⊨_W e : σ ▷ c ; t. *)
Definition csem (W0 : world) (Θ : cthe) (Γ : cenv) (e : expr) (σ : cta) (c : fuel) (t : tix) : Prop :=
  ∀ n W g γ πΘ πΓ φ, wbext W0 W →
    thsem n W Θ g πΘ φ → gsem n W Γ γ πΓ φ → dom πΘ ## dom πΓ →
    dom φ = dom (πΘ ∪ πΓ) → fcap_ext W (πΘ ∪ πΓ) φ →
    ∀ r tk, meets t r tk → FuelE n W σ r (πΘ ∪ πΓ) φ tk c (subst γ (emap g e)).

(** ** Arithmetic of counters, transformers and maps *)

Lemma meets_mono t r tk tk' : tk ≤ tk' → meets t r tk → meets t r tk'.
Proof. unfold meets. destruct (tapp t r); lia. Qed.

Lemma meets_ge t r tk : meets t r tk → r ≤ tk.
Proof.
  unfold meets, tapp. destruct t as [[s|] b].
  - pose proof (Nat.pow_le_mono_r 2 0 s ltac:(lia) ltac:(lia)). simpl in *. nia.
  - destruct (Nat.eqb r 0) eqn:E; [apply Nat.eqb_eq in E; lia|done].
Qed.

Lemma meets_tid r tk : meets tid r tk ↔ r ≤ tk.
Proof. unfold meets, tid, tapp. simpl. lia. Qed.

Lemma meets_zero t tk : meets t 0 tk ↔ snd t ≤ tk.
Proof. destruct t as [[s|] b]; unfold meets, tapp; simpl; [lia|done]. Qed.

Lemma meets_tmax t1 t2 r tk : meets (tmax t1 t2) r tk → meets t1 r tk ∧ meets t2 r tk.
Proof.
  destruct t1 as [[s1|] b1], t2 as [[s2|] b2]; unfold meets, tmax, tapp; simpl;
    try (destruct (Nat.eqb r 0) eqn:E; [apply Nat.eqb_eq in E as ->|done]); simpl.
  - intros H. pose proof (Nat.pow_le_mono_r 2 s1 (Nat.max s1 s2) ltac:(lia) ltac:(lia)).
    pose proof (Nat.pow_le_mono_r 2 s2 (Nat.max s1 s2) ltac:(lia) ltac:(lia)). nia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma tseq_split t1 t2 r tk : tok t1 t2 → meets (tseq t1 t2) r tk → ∃ r', meets t1 r' tk ∧ meets t2 r r'.
Proof. intros Hok. apply seq_sound. unfold tok in Hok. tauto. Qed.

Lemma fle_fadd_l a b : fle a (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fle_fadd_r a b : fle b (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fle_fminus_fadd i a b : fle (Some i) a → fle b (fminus i (fadd a b)).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fle_fmax_l a b : fle a (fmax a b).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fle_fmax_r a b : fle b (fmax a b).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fminus_fminus (i j : nat) (f : fuel) : fminus i (fminus j f) = fminus (j + i) f.
Proof. destruct f; simpl; [f_equal; lia|done]. Qed.

Lemma ftick_fminus f : ftick f = fminus 1 f.
Proof. destruct f; simpl; [f_equal; lia|done]. Qed.

Lemma fmap_fminus_fminus (i j : nat) (m : gmap cend fuel) : fminus i <$> (fminus j <$> m) = fminus (j + i) <$> m.
Proof. rewrite <-map_fmap_compose. apply map_fmap_ext. intros. apply fminus_fminus. Qed.

Lemma fle_some_zero f : fle (Some 0) f.
Proof. destruct f; simpl; lia. Qed.

Lemma mres_dom {Y : Type} (m : gmap cend Y) : mres (dom m) m = m.
Proof. apply map_eq. intros o. destruct (m !! o) eqn:E.
  - apply lookup_mres_Some. split; [done|by eapply elem_of_dom_2].
  - destruct (mres (dom m) m !! o) eqn:E'; [|done]. apply lookup_mres_Some in E' as [? _]. congruence.
Qed.

Lemma mres_dom_eq {Y Z : Type} (π : gmap cend Z) (m : gmap cend Y) : dom m = dom π → mres (dom π) m = m.
Proof. intros <-. apply mres_dom. Qed.

Lemma mres_mres {Y : Type} (X Z : gset cend) (m : gmap cend Y) : X ⊆ Z → mres X (mres Z m) = mres X m.
Proof.
  intros H. apply map_eq. intros o. destruct (mres X m !! o) eqn:E.
  - apply lookup_mres_Some in E as [E1 E2]. apply lookup_mres_Some. split; [|done].
    apply lookup_mres_Some. split; [done|set_solver].
  - destruct (mres X (mres Z m) !! o) eqn:E'; [|done].
    apply lookup_mres_Some in E' as [E' Hx]. apply lookup_mres_Some in E' as [E' _].
    assert (mres X m !! o = Some y) by (by apply lookup_mres_Some). congruence.
Qed.

Lemma mres_agree {Y : Type} (X : gset cend) (m m' : gmap cend Y) :
  (∀ o, o ∈ X → m' !! o = m !! o) → mres X m' = mres X m.
Proof.
  intros H. apply map_eq. intros o. destruct (decide (o ∈ X)) as [Hx|Hx].
  - destruct (mres X m !! o) eqn:E.
    + apply lookup_mres_Some in E as [E _]. apply lookup_mres_Some. by rewrite H.
    + destruct (mres X m' !! o) eqn:E'; [|done]. apply lookup_mres_Some in E' as [E' _].
      rewrite H in E' by done. assert (mres X m !! o = Some y) by (by apply lookup_mres_Some). congruence.
  - destruct (mres X m !! o) eqn:E; [apply lookup_mres_Some in E as [_ ?]; done|].
    destruct (mres X m' !! o) eqn:E'; [apply lookup_mres_Some in E' as [_ ?]; done|done].
Qed.

Lemma mres_union_split {Y : Type} (X1 X2 : gset cend) (m : gmap cend Y) :
  dom m ⊆ X1 ∪ X2 → m = mres X1 m ∪ mres X2 m.
Proof.
  intros Hd. apply map_eq. intros o. destruct (m !! o) eqn:E.
  - assert (o ∈ X1 ∪ X2) as Ho by (apply Hd; by eapply elem_of_dom_2).
    destruct (decide (o ∈ X1)).
    + symmetry. apply lookup_union_Some_l. by apply lookup_mres_Some.
    + symmetry. apply lookup_union_Some_raw. right. split.
      * destruct (mres X1 m !! o) eqn:E1; [|done]. apply lookup_mres_Some in E1 as [_ ?]. done.
      * apply lookup_mres_Some. split; [done|set_solver].
  - symmetry. apply lookup_union_None. split.
    + destruct (mres X1 m !! o) eqn:E1; [|done]. apply lookup_mres_Some in E1 as [? _]. congruence.
    + destruct (mres X2 m !! o) eqn:E1; [|done]. apply lookup_mres_Some in E1 as [? _]. congruence.
Qed.

Lemma lookup_mres_in {Y : Type} (X : gset cend) (m : gmap cend Y) o : o ∈ X → mres X m !! o = m !! o.
Proof.
  intros Hx. destruct (m !! o) eqn:E.
  - by apply lookup_mres_Some.
  - destruct (mres X m !! o) eqn:E'; [|done]. apply lookup_mres_Some in E' as [? _]. congruence.
Qed.

Lemma fcap_ext_mres W (X : gset cend) π φ : fcap_ext W π φ → fcap_ext W (mres X π) (mres X φ).
Proof. intros H W' Hb. apply fcap_mres, H, Hb. Qed.

Lemma fcap_ext_empty W : fcap_ext W ∅ ∅.
Proof. intros W' _ o f. by rewrite lookup_empty. Qed.

Lemma union_dom_disj {Y Z : Type} (π1 π2 : gmap cend Z) (m : gmap cend Y) :
  dom m = dom (π1 ∪ π2) → m = mres (dom π1) m ∪ mres (dom π2) m.
Proof. intros Hd. apply mres_union_split. rewrite Hd, dom_union_L. done. Qed.

Lemma union_comm_d {Y : Type} (m1 m2 : gmap cend Y) : dom m1 ## dom m2 → m1 ∪ m2 = m2 ∪ m1.
Proof. intros H. apply map_union_comm. by apply map_disjoint_dom. Qed.

Lemma kimg_compose (g h : chan → chan) (X : gset cend) : kimg g (kimg h X) = kimg (g ∘ h) X.
Proof. unfold kimg. apply set_eq. intros o. rewrite !elem_of_map. split.
  - intros (o1 & -> & Ho1). apply elem_of_map in Ho1 as (o2 & -> & H). by exists o2.
  - intros (o2 & -> & H). exists (h o2.1, o2.2). split; [done|]. apply elem_of_map. by exists o2.
Qed.

Lemma renk_singleton_ex {Y : Type} (g : chan → chan) o (v : Y) : renk g {[o := v]} {[(g o.1, o.2) := v]}.
Proof.
  split.
  - intros o1 v1 H1. apply lookup_singleton_Some in H1 as [<- <-]. by rewrite lookup_singleton_eq.
  - intros o' v' H'. apply lookup_singleton_Some in H' as [<- <-]. exists o.
    split; [done|by rewrite lookup_singleton_eq].
Qed.

(** ** Values that hold ends *)

Lemma cfree_cheld τ : cfree τ → cheld τ.
Proof. induction 1; constructor; done. Qed.

Lemma Vfuel_cfree n W τ a π φ w :
  cfree τ → Vfuel n W (CTa τ a) π φ w → π = ∅ ∧ ∀ a' φ', Vfuel n W (CTa τ a') π φ' w.
Proof.
  intros Hf HV. rewrite Vfuel_eq in HV. destruct (Vfdef_cfree _ _ _ _ τ Hf _ _ _ _ HV) as [-> H].
  split; [done|]. intros a' φ'. apply Vfuel_eq, H.
Qed.

(** A value whose type has no [CAny] at its top holds exactly its ends,
    at known points with partners of finite budget, and its counters
    lie at or above its credit. *)
Lemma Vfuel_held n W τ a π φ w :
  cheld τ → Vfuel n W (CTa τ a) π φ w →
  dom π = fends w ∧ fpts W π ∧ ∀ o f, o ∈ dom π → φ !! o = Some f → fle a f.
Proof.
  rewrite Vfuel_eq. intros Hh. revert a π φ w.
  assert (Hnil : ∀ (w : expr), fends w = ∅ → dom (∅ : gmap cend point) = fends w ∧ fpts W ∅ ∧
    ∀ (a : fuel) (φ : gmap cend fuel) o f, o ∈ dom (∅ : gmap cend point) → φ !! o = Some f → fle a f).
  { intros w Hw. rewrite dom_empty_L, Hw. split_and!; [done|intros o k; by rewrite lookup_empty|set_solver]. }
  induction Hh as [|ρ|P|c t h σ1 σ2|c t σ|τ1 a1 τ2 a2 H1 IH1 H2 IH2|τ1 a1 τ2 a2 H1 IH1 H2 IH2];
    intros a π φ w HV; destruct w; simpl in HV.
  all: try (destruct HV as [Hw _]; discriminate Hw).
  all: try (destruct HV as (y & Hw & _); discriminate Hw).
  all: try (destruct HV as (c' & b' & y & f & Hw & _); discriminate Hw).
  all: try done.
  - destruct HV as [_ ->]. destruct (Hnil EUnit) as (A & B & C); [done|]. split_and!; [done|done|apply C].
  - destruct HV as (y & [= <-] & -> & _). destruct (Hnil (EPt x)) as (A & B & C); [done|]. split_and!; [done|done|apply C].
  - destruct HV as (c' & b' & x & f & [= <- <-] & -> & Hp & Hf & Ha & Hq). split_and!.
    + by rewrite dom_singleton_L.
    + done.
    + intros o f' Ho Hf'. rewrite dom_singleton_L in Ho. apply elem_of_singleton in Ho as ->.
      rewrite Hf in Hf'. by injection Hf' as <-.
  - destruct HV as (Hd & Hq & Hfl & _). split_and!; [done|done|].
    intros o f _ Hf. eapply fle_trans; [|exact (Hfl o f Hf)]. apply fle_fadd_r.
  - destruct HV as (-> & Hfe & _). destruct (Hnil (EBox w)) as (A & B & C); [done|].
    split_and!; [done|done|apply C].
  - destruct HV as (π1 & π2 & -> & Hd & Hu & Hv).
    destruct (IH1 _ _ _ _ Hu) as (D1 & P1 & C1). destruct (IH2 _ _ _ _ Hv) as (D2 & P2 & C2).
    split_and!.
    + rewrite dom_union_L, D1, D2. done.
    + intros o k Ho. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [by apply (P1 o)|by apply (P2 o)].
    + intros o f Ho Hf. rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho].
      * eapply fle_trans; [apply fle_fadd_l|]. apply (C1 o f Ho). by rewrite lookup_mres_in.
      * eapply fle_trans; [apply fle_fadd_l|]. apply (C2 o f Ho). by rewrite lookup_mres_in.
  - destruct (IH1 _ _ _ _ HV) as (D & P & C). split_and!; [done|done|].
    intros o f Ho Hf. eapply fle_trans; [apply fle_fadd_l|]. by apply (C o f).
  - destruct (IH2 _ _ _ _ HV) as (D & P & C). split_and!; [done|done|].
    intros o f Ho Hf. eapply fle_trans; [apply fle_fadd_l|]. by apply (C o f).
Qed.

(** Aging a value by c: after i ≤ c ticks of its counters it is in
    [Vfuel] at the aged type. *)
Lemma Vfuel_age n W c i σ σ' π φ w :
  cagex c σ σ' → fle (Some i) c → Vfuel n W σ π φ w → Vfuel n W σ' π (fminus i <$> φ) w.
Proof.
  intros [Hc _] Hi HV. destruct Hc as [τ a Hf|τ a Ha].
  - by destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [_ H'].
  - assert (CTa τ a = cadd (Some i) (CTa τ (fminus i a))) as Eq.
    { simpl. destruct a as [a|], c as [c|]; simpl in *; try done. f_equal. f_equal. lia. }
    rewrite Eq in HV. apply Vfuel_minus in HV. eapply Vfuel_sub; [|exact HV].
    constructor; [apply cst_ty_refl|].
    destruct τ; simpl; destruct a as [a|], c as [c|]; simpl in *; try lia; done.
Qed.

(** An aged value has counters at least the age, unless it ages by 0. *)
Lemma Vfuel_age_above n W c σ σ' π φ w :
  cagex c σ σ' → Vfuel n W σ π φ w → ∀ o f, o ∈ dom π → φ !! o = Some f → fle c f.
Proof.
  intros [Hc [->|Hh]] HV o f Ho Hf; [apply fle_some_zero|].
  destruct σ as [τ a]. simpl in Hh. destruct (Vfuel_held _ _ _ _ _ _ _ Hh HV) as (_ & _ & C).
  inversion Hc as [? ? Hfr|? ? Ha]; subst.
  - destruct (Vfuel_cfree _ _ _ _ _ _ _ Hfr HV) as [-> _]. by rewrite dom_empty_L in Ho.
  - eapply fle_trans; [exact Ha|exact (C o f Ho Hf)].
Qed.

Lemma cagex_cheld c σ σ' : cagex c σ σ' → c ≠ Some 0 → cheld (cta_ty σ).
Proof. intros [_ [->|H]] Hc; [done|exact H]. Qed.

(** ** Capture *)

Lemma ccap_cheld h a σ σ' : ccap h a σ σ' → cheld (cta_ty σ).
Proof.
  induction 1 as [τ a0 Hf|P a0 _|c t h0 σ1 σ2 a0 _ _|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2];
    simpl; [by apply cfree_cheld|constructor|constructor| |];
    destruct σ1, σ2; constructor; done.
Qed.

Lemma ccap_cfree h a σ σ' : ccap h a σ σ' → cfree (cta_ty σ') → cfree (cta_ty σ).
Proof.
  induction 1 as [τ a0 Hf|P a0 _|c t h0 σ1 σ2 a0 _ _|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2];
    simpl; intros H; try done; try (inversion H; fail).
  - destruct σ1', σ2'. inversion H; subst. destruct σ1, σ2. constructor; [apply IH1|apply IH2]; done.
  - destruct σ1', σ2'. inversion H; subst. destruct σ1, σ2. constructor; [apply IH1|apply IH2]; done.
Qed.

Lemma ccap_clow h a σ σ' : ccap h a σ σ' → ∀ a', clow h (CTa (cta_ty σ) a') σ'.
Proof.
  induction 1 as [τ a0 Hf|P a0 _|c t h0 σ1 σ2 a0 Hh _|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2|σ1 σ2 σ1' σ2' a0 _ IH1 _ IH2];
    intros a'; simpl.
  - by apply ClFree.
  - apply ClEnd.
  - by apply ClArr.
  - destruct σ1 as [τ1 b1], σ2 as [τ2 b2]. apply ClProd; [apply (IH1 b1)|apply (IH2 b2)].
  - destruct σ1 as [τ1 b1], σ2 as [τ2 b2]. apply ClSum; [apply (IH1 b1)|apply (IH2 b2)].
Qed.

Lemma Vfuel_ccap n W h a σ σ' π φ φ' w :
  ccap h a σ σ' → (∀ o f, φ' !! o = Some f → fle (Some h) f) → dom π ⊆ dom φ' →
  Vfuel n W σ π φ w → Vfuel n W σ' π φ' w.
Proof. intros Hc. destruct σ as [τ a0]. apply Vfuel_recount. exact (ccap_clow _ _ _ _ Hc a0). Qed.

Lemma Vfuel_ccap_above n W h a σ σ' π φ w :
  ccap h a σ σ' → Vfuel n W σ π φ w → ∀ o f, o ∈ dom π → φ !! o = Some f → fle (fadd (Some h) a) f.
Proof.
  intros Hc. revert π φ w.
  induction Hc as [τ a0 Hf|P a0 Hle|c t h0 σ1 σ2 a0 Hh Hle|σ1 σ2 σ1' σ2' a0 H1 IH1 H2 IH2|σ1 σ2 σ1' σ2' a0 H1 IH1 H2 IH2];
    intros π φ w HV o f Ho Hof.
  - destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _]. by rewrite dom_empty_L in Ho.
  - destruct (Vfuel_held _ _ _ _ _ _ _ (HdEnd P) HV) as (_ & _ & C).
    eapply fle_trans; [exact Hle|exact (C o f Ho Hof)].
  - rewrite Vfuel_eq in HV. destruct w; simpl in HV; try done. destruct HV as (_ & _ & Hfl & _).
    eapply fle_trans; [exact Hle|exact (Hfl o f Hof)].
  - rewrite Vfuel_eq in HV. destruct w; simpl in HV; try done. destruct HV as (π1 & π2 & -> & Hd & Hu & Hv).
    rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho].
    + apply (IH1 π1 (mres (dom π1) φ) w1 ltac:(by apply Vfuel_eq) o f Ho). by rewrite lookup_mres_in.
    + apply (IH2 π2 (mres (dom π2) φ) w2 ltac:(by apply Vfuel_eq) o f Ho). by rewrite lookup_mres_in.
  - rewrite Vfuel_eq in HV. destruct w; simpl in HV; try done.
    + exact (IH1 π φ w ltac:(by apply Vfuel_eq) o f Ho Hof).
    + exact (IH2 π φ w ltac:(by apply Vfuel_eq) o f Ho Hof).
Qed.
