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
  (Γ : cenv) (Θ : cthe) (σ : cta) (τ : cty) (γ : nat → expr) (c d : fuel) (t : tix) (o : cend)
  (a : fuel) (h : nat) (e v w : expr).

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

(** ** The values of Γ *)

Lemma gsem_local n W Γ γ π φ φ' :
  (∀ o, o ∈ dom π → φ' !! o = φ !! o) → gsem n W Γ γ π φ → gsem n W Γ γ π φ'.
Proof.
  revert γ π. induction Γ as [|[σ|] Γ IH]; intros γ π Hag; simpl; [done| |by apply IH].
  intros (π1 & π2 & -> & Hd & Hv & HV & HG). exists π1, π2. split_and!; [done|done|done| |].
  - rewrite (mres_agree (dom π1) φ φ'); [done|]. intros o Ho. apply Hag. rewrite dom_union_L. set_solver.
  - apply IH; [|done]. intros o Ho. apply Hag. rewrite dom_union_L. set_solver.
Qed.

Lemma gsem_mono m n W W' Γ γ π φ : m ≤ n → wbext W W' → gsem n W Γ γ π φ → gsem m W' Γ γ π φ.
Proof.
  intros Hm Hb. revert γ π. induction Γ as [|[σ|] Γ IH]; intros γ π; simpl; [done| |by apply IH].
  intros (π1 & π2 & -> & Hd & Hv & HV & HG). exists π1, π2. split_and!; [done|done|done| |by apply IH].
  apply (Vfuel_wbext _ W); [done|]. by apply (Vfuel_down _ n).
Qed.

Lemma gsem_rename n W Γ γ (g : chan → chan) (P : gmap cend point) π π' φ φ' :
  kinj g P → dom φ ⊆ dom P → dom π ⊆ dom P → renk g π π' → renk g φ φ' →
  gsem n W Γ γ π φ → gsem n W Γ (λ x, emap g (γ x)) π' φ'.
Proof.
  revert γ π π'. induction Γ as [|[σ|] Γ IH]; intros γ π π' Hk Hdφ Hdπ Hπ Hφ; simpl.
  - intros ->. by apply (renk_empty g).
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG). rewrite dom_union_L in Hdπ.
    assert (Hk12 : kinj g (π1 ∪ π2)) by (apply (kinj_dom g P); [by rewrite dom_union_L|done]).
    destruct (renk_union_split g π1 π2 π' Hk12 Hd Hπ) as (π1' & π2' & -> & R1 & R2 & Hd').
    exists π1', π2'. split_and!; [done|done|by rewrite is_val_emap| |].
    + apply (Vfuel_rename n W σ π1 (mres (dom π1) φ) (γ 0) g);
        [apply (kinj_dom g P); [set_solver|done]|apply dom_mres_sub|done| |done].
      apply (renk_mres g P); [done|done|set_solver|done|done].
    + apply (IH _ π2); [done|done|set_solver|done|done|done].
  - by apply IH.
Qed.

Lemma gsem_age n W c i Γ Γ' γ π φ :
  cage_env c Γ Γ' → fle (Some i) c → gsem n W Γ γ π φ → gsem n W Γ' γ π (fminus i <$> φ).
Proof.
  intros Ha Hi. revert γ π. induction Ha as [|Γ Γ' Ha IH|σ σ' Γ Γ' Hs Ha IH]; intros γ π; simpl; [done|apply IH|].
  intros (π1 & π2 & -> & Hd & Hv & HV & HG). exists π1, π2. split_and!; try done; [|by apply IH].
  rewrite mres_fmap. by apply (Vfuel_age n W c i σ σ').
Qed.

Lemma gsem_above n W c Γ Γ' γ π φ :
  cage_env c Γ Γ' → gsem n W Γ γ π φ → ∀ o f, o ∈ dom π → φ !! o = Some f → fle c f.
Proof.
  intros Ha. revert γ π. induction Ha as [|Γ Γ' Ha IH|σ σ' Γ Γ' Hs Ha IH]; intros γ π; simpl.
  - intros -> o f Ho. by rewrite dom_empty_L in Ho.
  - apply IH.
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG) o f Ho Hf. rewrite dom_union_L in Ho.
    apply elem_of_union in Ho as [Ho|Ho]; [|exact (IH _ π2 HG o f Ho Hf)].
    apply (Vfuel_age_above n W c σ σ' π1 (mres (dom π1) φ) (γ 0) Hs HV o f Ho). by rewrite lookup_mres_in.
Qed.

Lemma gsem_split n W Γ Γ1 Γ2 γ π φ :
  csplit Γ Γ1 Γ2 → gsem n W Γ γ π φ →
  ∃ π1 π2, π = π1 ∪ π2 ∧ dom π1 ## dom π2 ∧ gsem n W Γ1 γ π1 φ ∧ gsem n W Γ2 γ π2 φ.
Proof.
  intros Hs. revert γ π.
  induction Hs as [|Γ Γ1 Γ2 Hs IH|σ Γ Γ1 Γ2 Hs IH|σ Γ Γ1 Γ2 Hs IH|σ Γ Γ1 Γ2 Hf Hs IH]; intros γ π; simpl.
  - intros ->. exists ∅, ∅. split_and!; [by rewrite map_empty_union|set_solver|done|done].
  - apply IH.
  - intros (πa & πb & -> & Hd & Hv & HV & HG). destruct (IH _ _ HG) as (π1 & π2 & -> & Hd12 & G1 & G2).
    rewrite dom_union_L in Hd. exists (πa ∪ π1), π2. split_and!.
    + by rewrite map_union_assoc.
    + rewrite dom_union_L. set_solver.
    + exists πa, π1. split_and!; [done|set_solver|done|done|done].
    + done.
  - intros (πa & πb & -> & Hd & Hv & HV & HG). destruct (IH _ _ HG) as (π1 & π2 & -> & Hd12 & G1 & G2).
    rewrite dom_union_L in Hd. exists π1, (πa ∪ π2). split_and!.
    + rewrite map_union_assoc, (union_comm_d πa π1) by set_solver. by rewrite <-map_union_assoc.
    + rewrite dom_union_L. set_solver.
    + done.
    + exists πa, π2. split_and!; [done|set_solver|done|done|done].
  - intros (πa & πb & -> & Hd & Hv & HV & HG). destruct σ as [τ a]. simpl in Hf.
    destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _].
    destruct (IH _ _ HG) as (π1 & π2 & -> & Hd12 & G1 & G2).
    exists π1, π2. rewrite map_empty_union. split_and!; [done|done| |].
    + exists ∅, π1. rewrite map_empty_union. split_and!; [done|set_solver|done|done|done].
    + exists ∅, π2. rewrite map_empty_union. split_and!; [done|set_solver|done|done|done].
Qed.

Lemma gsem_unl n W Γ γ π φ : cunlenv Γ → gsem n W Γ γ π φ → π = ∅.
Proof.
  revert γ π. induction Γ as [|[σ|] Γ IH]; intros γ π; simpl; [by intros _ ->| |intros [_ H]; by apply IH].
  intros [Hf HΓ] (π1 & π2 & -> & Hd & Hv & HV & HG). destruct σ as [τ a]. simpl in Hf.
  destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _]. rewrite (IH _ _ HΓ HG). by rewrite map_empty_union.
Qed.

Lemma gsem_unl_intro n W Γ γ φ :
  (∀ x σ, Γ !! x = Some (Some σ) → is_val (γ x) = true ∧ cfree (cta_ty σ) ∧ Vfuel n W σ ∅ ∅ (γ x)) →
  gsem n W Γ γ ∅ φ.
Proof.
  revert γ. induction Γ as [|[σ|] Γ IH]; intros γ H; simpl; [done| |].
  - destruct (H 0 σ eq_refl) as (Hv & Hf & HV). exists ∅, ∅. rewrite map_empty_union.
    split_and!; [done|set_solver|done| |].
    + destruct σ. simpl in Hf. destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [_ H']. rewrite dom_empty_L. apply H'.
    + apply IH. intros x σ' Hx. apply (H (S x) σ' Hx).
  - apply IH. intros x σ' Hx. apply (H (S x) σ' Hx).
Qed.

Lemma gsem_conly n W Γ x σ γ π φ :
  conly Γ x σ → gsem n W Γ γ π φ → is_val (γ x) = true ∧ Vfuel n W σ π (mres (dom π) φ) (γ x).
Proof.
  intros [Hx Hu]. revert x γ π Hx Hu. induction Γ as [|[σ0|] Γ IH]; intros [|x] γ π Hx Hu; simpl in *; try done.
  - injection Hx as ->. destruct Hu as [_ Hu]. intros (π1 & π2 & -> & Hd & Hv & HV & HG).
    rewrite (gsem_unl _ _ _ _ _ _ Hu HG), map_union_empty. done.
  - destruct Hu as [Hf Hu]. intros (π1 & π2 & -> & Hd & Hv & HV & HG). destruct σ0 as [τ a]. simpl in Hf.
    destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _]. rewrite map_empty_union. exact (IH x (λ x, γ (S x)) π2 Hx Hu HG).
  - destruct Hu as [_ Hu]. exact (IH x (λ x, γ (S x)) π Hx Hu).
Qed.

Lemma gsem_ccap n W h a Γ Γh γ π φ φ' :
  ccap_env h a Γ Γh → (∀ o f, o ∈ dom π → φ' !! o = Some f → fle (Some h) f) → dom π ⊆ dom φ' →
  gsem n W Γ γ π φ → gsem n W Γh γ π φ'.
Proof.
  intros Hc. revert γ π. induction Hc as [|Γ Γ' Hc IH|σ σ' Γ Γ' Hs Hc IH]; intros γ π Hm Hd; simpl;
    [done|by apply IH|].
  intros (π1 & π2 & -> & Hd12 & Hv & HV & HG). rewrite dom_union_L in Hd.
  exists π1, π2. split_and!; [done|done|done| |].
  - apply (Vfuel_ccap n W h a σ σ' π1 (mres (dom π1) φ)); [done| |rewrite dom_mres; set_solver|done].
    intros o f Ho. apply lookup_mres_Some in Ho as [Ho Hin]. apply (Hm o f); [rewrite dom_union_L; set_solver|done].
  - apply IH; [|set_solver|done]. intros o f Ho. apply Hm. rewrite dom_union_L. set_solver.
Qed.

Lemma gsem_ccap_above n W h a Γ Γh γ π φ :
  ccap_env h a Γ Γh → gsem n W Γ γ π φ → ∀ o f, o ∈ dom π → φ !! o = Some f → fle (fadd (Some h) a) f.
Proof.
  intros Hc. revert γ π. induction Hc as [|Γ Γ' Hc IH|σ σ' Γ Γ' Hs Hc IH]; intros γ π; simpl.
  - intros -> o f Ho. by rewrite dom_empty_L in Ho.
  - apply IH.
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG) o f Ho Hf. rewrite dom_union_L in Ho.
    apply elem_of_union in Ho as [Ho|Ho]; [|exact (IH _ π2 HG o f Ho Hf)].
    apply (Vfuel_ccap_above n W h a σ σ' π1 (mres (dom π1) φ) (γ 0) Hs HV o f Ho). by rewrite lookup_mres_in.
Qed.

Lemma gsem_wk n W Γ' Γ γ π φ : cwk Γ' Γ → gsem n W Γ γ π φ → gsem n W Γ' γ π φ.
Proof.
  intros Hw. revert γ π. induction Hw as [|[σ|] Γ' Γ Hw IH|σ Γ' Γ Hf Hw IH]; intros γ π; simpl.
  - done.
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG). exists π1, π2. split_and!; try done. by apply IH.
  - apply IH.
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG). destruct σ as [τ a]. simpl in Hf.
    destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _]. rewrite map_empty_union. by apply IH.
Qed.

Lemma gsem_contract n W σ Γ γ π φ :
  cfree (cta_ty σ) → gsem n W (Some σ :: Γ) γ π φ → gsem n W (Some σ :: Some σ :: Γ) (λ x, γ (pred x)) π φ.
Proof.
  intros Hf (π1 & π2 & -> & Hd & Hv & HV & HG). destruct σ as [τ a]. simpl in Hf.
  destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> H']. rewrite map_empty_union.
  exists ∅, π2. rewrite map_empty_union. split_and!; [done|set_solver|done|apply H'|].
  exists ∅, π2. rewrite map_empty_union. split_and!; [done|set_solver|done|apply H'|exact HG].
Qed.

(** The values of the entries hold their ends. *)
Lemma gsem_ends n W Γ γ π φ :
  (∀ x σ, Γ !! x = Some (Some σ) → cheld (cta_ty σ)) → gsem n W Γ γ π φ →
  (∀ x σ, Γ !! x = Some (Some σ) → fends (γ x) ⊆ dom π) ∧
  (∀ o, o ∈ dom π → ∃ x σ, Γ !! x = Some (Some σ) ∧ ¬ cfree (cta_ty σ) ∧ o ∈ fends (γ x)) ∧
  fpts W π.
Proof.
  revert γ π. induction Γ as [|[σ|] Γ IH]; intros γ π Hh; simpl.
  - intros ->. split_and!; [intros [] ?; done|intros o Ho; by rewrite dom_empty_L in Ho|intros o k; by rewrite lookup_empty].
  - intros (π1 & π2 & -> & Hd & Hv & HV & HG).
    destruct (IH (λ x, γ (S x)) π2 (λ x σ0 Hx, Hh (S x) σ0 Hx) HG) as (A & B & C).
    destruct σ as [τ a]. destruct (Vfuel_held _ _ _ _ _ _ _ (Hh 0 _ eq_refl) HV) as (D & P & _).
    split_and!.
    + intros [|x] σ0 Hx; simpl in Hx; rewrite dom_union_L.
      * injection Hx as <-. rewrite <-D. set_solver.
      * specialize (A x σ0 Hx). set_solver.
    + intros o Ho. rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho].
      * exists 0, (CTa τ a). split_and!; [done| |by rewrite <-D].
        intros Hf. destruct (Vfuel_cfree _ _ _ _ _ _ _ Hf HV) as [-> _]. by rewrite dom_empty_L in Ho.
      * destruct (B o Ho) as (x & σ0 & Hx & Hn & Ho'). by exists (S x), σ0.
    + intros o k Ho. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [by apply (P o)|by apply (C o)].
  - intros HG. destruct (IH (λ x, γ (S x)) π (λ x σ0 Hx, Hh (S x) σ0 Hx) HG) as (A & B & C).
    split_and!; [intros [|x] σ0 Hx; [done|exact (A x σ0 Hx)]| |done].
    intros o Ho. destruct (B o Ho) as (x & σ0 & Hx & Hn & Ho'). by exists (S x), σ0.
Qed.

Lemma ccap_env_lookup h a Γ Γh x σ : ccap_env h a Γ Γh → Γ !! x = Some (Some σ) → ∃ σ', Γh !! x = Some (Some σ') ∧ ccap h a σ σ'.
Proof.
  intros Hc. revert x. induction Hc as [|Γ Γ' Hc IH|σ0 σ' Γ Γ' Hs Hc IH]; intros [|x] Hx; simpl in *; try done.
  - by apply IH.
  - injection Hx as <-. by exists σ'.
  - by apply IH.
Qed.

Lemma cage_env_lookup c Γ Γ' x σ : cage_env c Γ Γ' → Γ !! x = Some (Some σ) → ∃ σ', Γ' !! x = Some (Some σ') ∧ cagex c σ σ'.
Proof.
  intros Hc. revert x. induction Hc as [|Γ Γ'' Hc IH|σ0 σ' Γ Γ'' Hs Hc IH]; intros [|x] Hx; simpl in *; try done.
  - by apply IH.
  - injection Hx as <-. by exists σ'.
  - by apply IH.
Qed.

(** ** The ends of Θ *)

Lemma elem_of_kimg_inv (g : chan → chan) (X : gset cend) o' : o' ∈ kimg g X → ∃ o, o' = tkey g o ∧ o ∈ X.
Proof. unfold kimg. intros (o & -> & Ho)%elem_of_map. by exists o. Qed.

Lemma thsem_dom n W Θ g π φ : thsem n W Θ g π φ → dom π = kimg g (dom Θ).
Proof. by intros (_ & H & _). Qed.

Lemma thsem_local n W Θ g π φ φ' :
  (∀ o, o ∈ dom π → φ' !! o = φ !! o) → thsem n W Θ g π φ → thsem n W Θ g π φ'.
Proof.
  intros Hag (Hinj & Hdom & HV). split_and!; [done|done|]. intros o σ Ho.
  destruct (HV o σ Ho) as (x & Hx & HVo). exists x. split; [done|].
  rewrite (mres_agree _ φ φ'); [done|]. intros o' ->%elem_of_singleton. apply Hag. by eapply elem_of_dom_2.
Qed.

Lemma thsem_mono m n W W' Θ g π φ : m ≤ n → wbext W W' → thsem n W Θ g π φ → thsem m W' Θ g π φ.
Proof.
  intros Hm Hb (Hinj & Hdom & HV). split_and!; [done|done|]. intros o σ Ho.
  destruct (HV o σ Ho) as (x & Hx & HVo). exists x. split; [done|].
  apply (Vfuel_wbext _ W); [done|]. by apply (Vfuel_down _ n).
Qed.

Lemma thsem_rename n W Θ (g g' : chan → chan) (P : gmap cend point) π π' φ φ' :
  kinj g' P → dom φ ⊆ dom P → dom π ⊆ dom P → renk g' π π' → renk g' φ φ' →
  thsem n W Θ g π φ → thsem n W Θ (g' ∘ g) π' φ'.
Proof.
  intros Hk Hdφ Hdπ Hπ Hφ (Hinj & Hdom & HV).
  assert (HinP : ∀ o, o ∈ dom Θ → tkey g o ∈ dom P).
  { intros o Ho. apply Hdπ. rewrite Hdom. by apply elem_of_kimg. }
  split_and!.
  - intros o1 o2 H1 H2 Heq. apply Hinj; [done|done|].
    apply (kinj_elem g' P); [done|by apply HinP|by apply HinP|exact Heq].
  - rewrite (renk_dom _ _ _ Hπ), Hdom. apply kimg_compose.
  - intros o σ Ho. destruct (HV o σ Ho) as (x & Hx & HVo). exists x. split.
    + exact (proj1 Hπ (tkey g o) x Hx).
    + assert (Ho' : o ∈ dom Θ) by (by eapply elem_of_dom_2).
      assert (E1 : mres {[tkey g o]} φ = mres (dom {[tkey g o := x]}) φ) by (by rewrite dom_singleton_L).
      assert (E2 : mres {[tkey (g' ∘ g) o]} φ' = mres (dom {[tkey (g' ∘ g) o := x]}) φ') by (by rewrite dom_singleton_L).
      rewrite E1 in HVo. rewrite E2.
      assert (Hks : kinj g' ({[tkey g o := x]} : gmap cend point)).
      { apply (kinj_dom g' P); [|done]. rewrite dom_singleton_L. intros ? ->%elem_of_singleton. by apply HinP. }
      apply (Vfuel_rename n W σ {[tkey g o := x]} (mres (dom ({[tkey g o := x]} : gmap cend point)) φ)
        (Chan (g o.1) o.2) g' _ _ Hks ltac:(apply dom_mres_sub) (renk_singleton_ex g' (tkey g o) x)); [|exact HVo].
      apply (renk_mres g' P); [done|done| |done|apply (renk_singleton_ex g' (tkey g o) x)].
      rewrite dom_singleton_L. intros ? ->%elem_of_singleton. by apply HinP.
Qed.

Lemma cage_th_lookup c Θ Θ' o σ : cage_th c Θ Θ' → Θ !! o = Some σ → ∃ σ', Θ' !! o = Some σ' ∧ cagex c σ σ'.
Proof. intros H Ho. specialize (H o). rewrite Ho in H. destruct (Θ' !! o); [by eexists|done]. Qed.

Lemma cage_th_lookup_r c Θ Θ' o σ' : cage_th c Θ Θ' → Θ' !! o = Some σ' → ∃ σ, Θ !! o = Some σ ∧ cagex c σ σ'.
Proof. intros H Ho. specialize (H o). rewrite Ho in H. destruct (Θ !! o); [by eexists|done]. Qed.

Lemma cage_th_dom c Θ Θ' : cage_th c Θ Θ' → dom Θ' = dom Θ.
Proof.
  intros H. apply set_eq. intros o. rewrite !elem_of_dom. specialize (H o).
  destruct (Θ !! o), (Θ' !! o); split; intros [? ?]; try done; eauto.
Qed.

Lemma ccap_th_lookup h a Θ Θ' o σ : ccap_th h a Θ Θ' → Θ !! o = Some σ → ∃ σ', Θ' !! o = Some σ' ∧ ccap h a σ σ'.
Proof. intros H Ho. specialize (H o). rewrite Ho in H. destruct (Θ' !! o); [by eexists|done]. Qed.

Lemma ccap_th_lookup_r h a Θ Θ' o σ' : ccap_th h a Θ Θ' → Θ' !! o = Some σ' → ∃ σ, Θ !! o = Some σ ∧ ccap h a σ σ'.
Proof. intros H Ho. specialize (H o). rewrite Ho in H. destruct (Θ !! o); [by eexists|done]. Qed.

Lemma ccap_th_dom h a Θ Θ' : ccap_th h a Θ Θ' → dom Θ' = dom Θ.
Proof.
  intros H. apply set_eq. intros o. rewrite !elem_of_dom. specialize (H o).
  destruct (Θ !! o), (Θ' !! o); split; intros [? ?]; try done; eauto.
Qed.

Lemma thsem_age n W c i Θ Θ' g π φ :
  cage_th c Θ Θ' → fle (Some i) c → thsem n W Θ g π φ → thsem n W Θ' g π (fminus i <$> φ).
Proof.
  intros Ha Hi (Hinj & Hdom & HV). rewrite <-(cage_th_dom _ _ _ Ha) in Hinj, Hdom. split_and!; [done|done|].
  intros o σ' Ho. destruct (cage_th_lookup_r _ _ _ _ _ Ha Ho) as (σ & Ho0 & Hs).
  destruct (HV o σ Ho0) as (x & Hx & HVo). exists x. split; [done|].
  rewrite mres_fmap. by apply (Vfuel_age n W c i σ σ').
Qed.

Lemma thsem_point n W Θ g π φ o' :
  thsem n W Θ g π φ → o' ∈ dom π →
  ∃ o σ x, o' = tkey g o ∧ Θ !! o = Some σ ∧ π !! o' = Some x ∧
    Vfuel n W σ {[o' := x]} (mres {[o']} φ) (Chan (g o.1) o.2).
Proof.
  intros (Hinj & Hdom & HV) Ho'. rewrite Hdom in Ho'. destruct (elem_of_kimg_inv _ _ _ Ho') as (o & -> & Ho).
  apply elem_of_dom in Ho as [σ Hσ]. destruct (HV o σ Hσ) as (x & Hx & HVo). by exists o, σ, x.
Qed.

Lemma thsem_above n W c Θ Θ' g π φ :
  cage_th c Θ Θ' → thsem n W Θ g π φ → ∀ o f, o ∈ dom π → φ !! o = Some f → fle c f.
Proof.
  intros Ha HT o' f Ho' Hf. destruct (thsem_point _ _ _ _ _ _ _ HT Ho') as (o & σ & x & -> & Hσ & Hx & HVo).
  destruct (cage_th_lookup _ _ _ _ _ Ha Hσ) as (σ' & _ & Hs).
  apply (Vfuel_age_above n W c σ σ' _ _ _ Hs HVo (tkey g o)); [by rewrite dom_singleton_L; set_solver|].
  rewrite lookup_mres_in; [done|set_solver].
Qed.

Lemma thsem_ccap n W h a Θ Θh g π φ φ' :
  ccap_th h a Θ Θh → (∀ o f, o ∈ dom π → φ' !! o = Some f → fle (Some h) f) → dom π ⊆ dom φ' →
  thsem n W Θ g π φ → thsem n W Θh g π φ'.
Proof.
  intros Hc Hm Hd (Hinj & Hdom & HV). rewrite <-(ccap_th_dom _ _ _ _ Hc) in Hinj, Hdom. split_and!; [done|done|].
  intros o σ' Ho. destruct (ccap_th_lookup_r _ _ _ _ _ _ Hc Ho) as (σ & Ho0 & Hs).
  destruct (HV o σ Ho0) as (x & Hx & HVo). exists x. split; [done|].
  apply (Vfuel_ccap n W h a σ σ' _ (mres {[tkey g o]} φ)); [done| | |done].
  - intros o1 f Ho1. apply lookup_mres_Some in Ho1 as [Ho1 Hin]. apply elem_of_singleton in Hin as ->.
    apply (Hm (tkey g o) f); [by eapply elem_of_dom_2|done].
  - rewrite dom_singleton_L, dom_mres. assert (tkey g o ∈ dom φ') by (apply Hd; by eapply elem_of_dom_2). set_solver.
Qed.

Lemma thsem_ccap_above n W h a Θ Θh g π φ :
  ccap_th h a Θ Θh → thsem n W Θ g π φ → ∀ o f, o ∈ dom π → φ !! o = Some f → fle (fadd (Some h) a) f.
Proof.
  intros Hc HT o' f Ho' Hf. destruct (thsem_point _ _ _ _ _ _ _ HT Ho') as (o & σ & x & -> & Hσ & Hx & HVo).
  destruct (ccap_th_lookup _ _ _ _ _ _ Hc Hσ) as (σ' & _ & Hs).
  apply (Vfuel_ccap_above n W h a σ σ' _ _ _ Hs HVo (tkey g o)); [by rewrite dom_singleton_L; set_solver|].
  rewrite lookup_mres_in; [done|set_solver].
Qed.

Lemma thsem_split n W Θ Θ1 Θ2 g π φ :
  thsplit Θ Θ1 Θ2 → thsem n W Θ g π φ →
  ∃ π1 π2, π = π1 ∪ π2 ∧ dom π1 ## dom π2 ∧ thsem n W Θ1 g π1 φ ∧ thsem n W Θ2 g π2 φ.
Proof.
  intros [Hdisj ->] (Hinj & Hdom & HV). rewrite dom_union_L in Hinj, Hdom.
  assert (Hd12 : dom Θ1 ## dom Θ2) by by apply map_disjoint_dom.
  assert (Hpart : ∀ (Θi : cthe), (∀ o σ, Θi !! o = Some σ → (Θ1 ∪ Θ2) !! o = Some σ) → dom Θi ⊆ dom Θ1 ∪ dom Θ2 →
      thsem n W Θi g (mres (kimg g (dom Θi)) π) φ).
  { intros Θi Hsub Hdi. split_and!.
    - intros o1 o2 H1 H2. apply Hinj; set_solver.
    - rewrite dom_mres, Hdom. apply set_eq. intros o'. rewrite elem_of_intersection. split; [by intros [_ H]|].
      intros H. split; [|done]. destruct (elem_of_kimg_inv _ _ _ H) as (o & -> & Ho). apply elem_of_kimg. set_solver.
    - intros o σ Ho. destruct (HV o σ (Hsub o σ Ho)) as (x & Hx & HVo). exists x. split; [|done].
      rewrite lookup_mres_in; [done|]. apply elem_of_kimg. by eapply elem_of_dom_2. }
  exists (mres (kimg g (dom Θ1)) π), (mres (kimg g (dom Θ2)) π). split_and!.
  - apply mres_union_split. rewrite Hdom. unfold kimg. by rewrite set_map_union_L.
  - rewrite !dom_mres. intros o' [_ H1]%elem_of_intersection [_ H2]%elem_of_intersection.
    destruct (elem_of_kimg_inv _ _ _ H1) as (o1 & -> & Ho1). destruct (elem_of_kimg_inv _ _ _ H2) as (o2 & Heq & Ho2).
    assert (o1 = o2) as <- by (apply Hinj; set_solver). set_solver.
  - apply Hpart; [|set_solver]. intros o σ Ho. by apply lookup_union_Some_l.
  - apply Hpart; [|set_solver]. intros o σ Ho. apply lookup_union_Some_raw. right. split; [|done].
    apply not_elem_of_dom. intros Hin. apply (Hd12 o); [done|by eapply elem_of_dom_2].
Qed.

Lemma thsem_nil n W g φ : thsem n W ∅ g ∅ φ.
Proof.
  split_and!.
  - intros o1 o2 H. by rewrite dom_empty_L in H.
  - rewrite !dom_empty_L. unfold kimg. by rewrite set_map_empty.
  - intros o σ. by rewrite lookup_empty.
Qed.

Lemma thsem_empty n W g π φ : thsem n W ∅ g π φ → π = ∅.
Proof.
  intros (_ & Hdom & _). rewrite dom_empty_L in Hdom. unfold kimg in Hdom. rewrite set_map_empty in Hdom.
  by apply dom_empty_inv_L.
Qed.

Lemma thsem_single n W (c : chan) (b : bool) σ g π φ :
  thsem n W {[(c, b) := σ]} g π φ →
  ∃ x, π = {[(g c, b) := x]} ∧ Vfuel n W σ π (mres {[(g c, b)]} φ) (Chan (g c) b).
Proof.
  intros (Hinj & Hdom & HV). destruct (HV (c, b) σ ltac:(by rewrite lookup_singleton_eq)) as (x & Hx & HVo).
  exists x. assert (π = {[(g c, b) := x]}) as ->; [|done].
  apply map_eq. intros o'. destruct (decide (o' = (g c, b))) as [->|Hne].
  - by rewrite lookup_singleton_eq.
  - rewrite lookup_singleton_ne by done. apply not_elem_of_dom. rewrite Hdom, dom_singleton_L.
    unfold kimg. rewrite set_map_singleton_L. set_solver.
Qed.

(** ** Sequencing: F1 over the environment *)

Lemma mres_disj_l {Y Z : Type} (m1 m2 : gmap cend Y) (π : gmap cend Z) :
  dom m1 = dom π → dom m2 ## dom π → mres (dom π) (m1 ∪ m2) = m1.
Proof.
  intros H1 H2. apply map_eq. intros o. destruct (decide (o ∈ dom π)) as [Ho|Ho].
  - rewrite lookup_mres_in by done. rewrite <-H1 in Ho. apply elem_of_dom in Ho as [y Hy].
    rewrite Hy. by apply lookup_union_Some_l.
  - destruct (mres (dom π) (m1 ∪ m2) !! o) eqn:E; [apply lookup_mres_Some in E as [_ ?]; done|].
    symmetry. apply not_elem_of_dom. by rewrite H1.
Qed.

Lemma mres_disj_r {Y Z : Type} (m1 m2 : gmap cend Y) (π : gmap cend Z) :
  dom m2 = dom π → dom m1 ## dom π → mres (dom π) (m1 ∪ m2) = m2.
Proof.
  intros H1 H2. rewrite union_comm_d by (rewrite H1; set_solver). by apply mres_disj_l.
Qed.

Lemma dom_mres_of {Y Z : Type} (m : gmap cend Y) (π1 π2 : gmap cend Z) :
  dom m = dom (π1 ∪ π2) → dom (mres (dom π1) m) = dom π1.
Proof. intros H. rewrite dom_mres, H, dom_union_L. set_solver. Qed.

Lemma dom_mres_of_r {Y Z : Type} (m : gmap cend Y) (π1 π2 : gmap cend Z) :
  dom m = dom (π1 ∪ π2) → dom (mres (dom π2) m) = dom π2.
Proof. intros H. rewrite dom_mres, H, dom_union_L. set_solver. Qed.

Lemma fcap_ext_part W π1 π2 φ : dom π1 ## dom π2 → fcap_ext W (π1 ∪ π2) φ → fcap_ext W π1 (mres (dom π1) φ).
Proof.
  intros Hd H. rewrite <-(mres_disj_l π1 π2 π1) at 1 by (done||set_solver). by apply fcap_ext_mres.
Qed.

Lemma fcap_ext_part_r W π1 π2 φ : dom π1 ## dom π2 → fcap_ext W (π1 ∪ π2) φ → fcap_ext W π2 (mres (dom π2) φ).
Proof.
  intros Hd H. rewrite <-(mres_disj_r π1 π2 π2) at 1 by (done||set_solver). by apply fcap_ext_mres.
Qed.

(** The continuation's environment: the context renamed by g′, moved to
    W′ and aged by i. *)
Lemma env_cont n j W W' Θ Θ' Γ Γ' c i g g' γ πΘ πΓ πK' φK φK' φ' :
  j ≤ n → wbext W W' → cage_th c Θ Θ' → cage_env c Γ Γ' → fle (Some i) c →
  thsem n W Θ g πΘ φK → gsem n W Γ γ πΓ φK → dom πΘ ## dom πΓ → dom φK = dom (πΘ ∪ πΓ) →
  kinj g' (πΘ ∪ πΓ) → renk g' (πΘ ∪ πΓ) πK' → renk g' φK φK' →
  (∀ o, o ∈ dom πK' → φ' !! o = (fminus i <$> φK') !! o) →
  ∃ πΘ' πΓ', πK' = πΘ' ∪ πΓ' ∧ dom πΘ' ## dom πΓ' ∧
    thsem j W' Θ' (g' ∘ g) πΘ' φ' ∧ gsem j W' Γ' (λ x, emap g' (γ x)) πΓ' φ'.
Proof.
  intros Hj Hb HaT HaG Hi HT HG Hd HdK Hk Rπ Rφ Hag.
  destruct (renk_union_split g' πΘ πΓ πK' Hk Hd Rπ) as (πΘ' & πΓ' & -> & R1 & R2 & Hd').
  exists πΘ', πΓ'. split_and!; [done|done| |].
  - apply (thsem_local _ _ _ _ _ (fminus i <$> φK')); [intros o Ho; apply Hag; rewrite dom_union_L; set_solver|].
    apply (thsem_mono j n W W'); [done|done|]. apply (thsem_age n W c i Θ); [done|done|].
    apply (thsem_rename n W Θ g g' (πΘ ∪ πΓ) πΘ πΘ' φK φK'); [done|rewrite HdK; done|rewrite dom_union_L; set_solver|done|done|done].
  - apply (gsem_local _ _ _ _ _ (fminus i <$> φK')); [intros o Ho; apply Hag; rewrite dom_union_L; set_solver|].
    apply (gsem_mono j n W W'); [done|done|]. apply (gsem_age n W c i Γ); [done|done|].
    apply (gsem_rename n W Γ γ g' (πΘ ∪ πΓ) πΓ πΓ' φK φK'); [done|rewrite HdK; done|rewrite dom_union_L; set_solver|done|done|done].
Qed.

(** A hole that holds the whole environment, in a context that holds
    nothing. *)
Lemma sem_bind0 W0 Θ Γ e σ1 c1 t1 (K : ectx) σ r d n W g γ πΘ πΓ φ tk r1 :
  ectx_ok K → (∀ g' : chan → chan, kemap g' K = K) → csem W0 Θ Γ e σ1 c1 t1 → fle c1 d → wbext W0 W →
  thsem n W Θ g πΘ φ → gsem n W Γ γ πΓ φ → dom πΘ ## dom πΓ →
  dom φ = dom (πΘ ∪ πΓ) → fcap_ext W (πΘ ∪ πΓ) φ → meets t1 r1 tk →
  (∀ j W' i v πv φv tk', j ≤ n → wbext W0 W' → fle (Some i) c1 → is_val v = true → r1 ≤ tk' →
     dom φv = dom πv → fcap_ext W' πv φv → Vfuel j W' σ1 πv φv v →
     FuelE j W' σ r πv φv tk' (fminus i d) (efill K v)) →
  FuelE n W σ r (πΘ ∪ πΓ) φ tk d (efill K (subst γ (emap g e))).
Proof.
  intros HK HKe Hcs Hcd Hb HT HG Hd Hdφ Hc Hm Hk.
  rewrite <-(map_union_empty (πΘ ∪ πΓ)), <-(map_union_empty φ).
  apply (FuelE_bind n W σ1 r1 σ r (πΘ ∪ πΓ) φ ∅ ∅ tk c1 d K);
    [done|done|by rewrite !dom_empty_L|rewrite dom_empty_L; set_solver|apply fcap_ext_empty
    |intros o f; by rewrite lookup_empty|done| |].
  - intros W' g' πK' φK' i j v π1 φ1 tk' Hb' Hk' R1 R2 Hi Hj Hv Hr Hdis Hd1 Hc1 HV.
    rewrite (renk_empty g' πK' R1), (renk_empty g' φK' R2), fmap_empty, !map_union_empty, HKe.
    apply Hk; try done. by eapply wbext_trans.
  - apply Hcs; try done.
Qed.

(** A hole beside the rest of the environment, which ages by the
    hole's cost. *)
Lemma sem_bind1 W0 Θ1 Γ1 e1 σ1 c1 t1 Θ2 Θ2' Γ2 Γ2' (fr : (nat → expr) → (chan → chan) → frame)
    σ r d n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1 :
  (∀ (g' : chan → chan) γ (g : chan → chan), frame_emap g' (fr γ g) = fr (λ x, emap g' (γ x)) (g' ∘ g)) →
  (∀ γ (g : chan → chan), frame_val (fr γ g)) →
  csem W0 Θ1 Γ1 e1 σ1 c1 t1 → cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' → fle c1 d → wbext W0 W →
  thsem n W Θ1 g πΘ1 φ → gsem n W Γ1 γ πΓ1 φ → thsem n W Θ2 g πΘ2 φ → gsem n W Γ2 γ πΓ2 φ →
  dom πΘ1 ## dom πΓ1 → dom πΘ2 ## dom πΓ2 → dom (πΘ1 ∪ πΓ1) ## dom (πΘ2 ∪ πΓ2) →
  dom φ = dom ((πΘ1 ∪ πΓ1) ∪ (πΘ2 ∪ πΓ2)) → fcap_ext W ((πΘ1 ∪ πΓ1) ∪ (πΘ2 ∪ πΓ2)) φ → meets t1 r1 tk →
  (∀ j W' (g' : chan → chan) γ' πΘ' πΓ' φ' i v πv tk', j ≤ n → wbext W0 W' → fle (Some i) c1 →
     is_val v = true → r1 ≤ tk' →
     thsem j W' Θ2' g' πΘ' φ' → gsem j W' Γ2' γ' πΓ' φ' → Vfuel j W' σ1 πv (mres (dom πv) φ') v →
     dom πΘ' ## dom πΓ' → dom πv ## dom (πΘ' ∪ πΓ') →
     dom φ' = dom (πv ∪ (πΘ' ∪ πΓ')) → fcap_ext W' (πv ∪ (πΘ' ∪ πΓ')) φ' →
     FuelE j W' σ r (πv ∪ (πΘ' ∪ πΓ')) φ' tk' (fminus i d) (fill_frame (fr γ' g') v)) →
  FuelE n W σ r ((πΘ1 ∪ πΓ1) ∪ (πΘ2 ∪ πΓ2)) φ tk d (fill_frame (fr γ g) (subst γ (emap g e1))).
Proof.
  intros Hfe Hfv Hcs HaT HaG Hcd Hb HT1 HG1 HT2 HG2 Hd1 Hd2 Hd Hdφ Hc Hm Hk.
  set (π1 := πΘ1 ∪ πΓ1). set (πK := πΘ2 ∪ πΓ2).
  rewrite (union_dom_disj π1 πK φ Hdφ).
  change (fill_frame (fr γ g) (subst γ (emap g e1))) with (efill [fr γ g] (subst γ (emap g e1))).
  assert (Hdφ1 : dom (mres (dom π1) φ) = dom π1) by (by eapply dom_mres_of).
  assert (HdφK : dom (mres (dom πK) φ) = dom πK) by (by eapply dom_mres_of_r).
  apply (FuelE_bind n W σ1 r1 σ r π1 (mres (dom π1) φ) πK (mres (dom πK) φ) tk c1 d [fr γ g]);
    [|done|done|done| | |done| |].
  - constructor; [apply Hfv|constructor].
  - by apply (fcap_ext_part_r W π1 πK φ).
  - intros o f Hf. apply lookup_mres_Some in Hf as [Hf Ho]. unfold πK in Ho. rewrite dom_union_L in Ho.
    apply elem_of_union in Ho as [Ho|Ho]; [exact (thsem_above _ _ _ _ _ _ _ _ HaT HT2 o f Ho Hf)
                                          |exact (gsem_above _ _ _ _ _ _ _ _ HaG HG2 o f Ho Hf)].
  - intros W' g' πK' φK' i j v πv φv tk' Hb' Hk' Rπ Rφ Hi Hj Hv Hr Hdis Hdv Hcv HV. simpl. rewrite Hfe.
    destruct (env_cont n j W W' Θ2 Θ2' Γ2 Γ2' c1 i g g' γ πΘ2 πΓ2 πK' (mres (dom πK) φ) φK' (φv ∪ (fminus i <$> φK'))
      Hj Hb' HaT HaG Hi) as (πΘ' & πΓ' & -> & Hd' & HT' & HG').
    { apply (thsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold πK. rewrite dom_union_L. set_solver. }
    { apply (gsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold πK. rewrite dom_union_L. set_solver. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { intros o Ho. apply lookup_union_r. apply not_elem_of_dom. rewrite Hdv. set_solver. }
    assert (HdK' : dom φK' = dom (πΘ' ∪ πΓ')) by (eapply renk_dom_eq; [exact HdφK|exact Rπ|exact Rφ]).
    apply (Hk j W' (g' ∘ g) (λ x, emap g' (γ x)) πΘ' πΓ' (φv ∪ (fminus i <$> φK')) i v πv tk');
      [done|by eapply wbext_trans|done|done|done|done|done| |done|done| |].
    + rewrite (mres_disj_l φv (fminus i <$> φK') πv); [done|done|]. rewrite dom_fmap_L, HdK'. done.
    + rewrite !dom_union_L, dom_fmap_L, HdK', Hdv, dom_union_L. done.
    + apply fcap_ext_union; [done| |done]. apply (fcap_ext_fmap W' _ _ (fminus i)); [apply fminus_le|].
      apply (fcap_ext_wbext W); [done|]. eapply fcap_ext_rename; [|exact Rπ|exact Rφ]. by apply (fcap_ext_part_r W π1 πK φ).
  - apply Hcs; try done.
    + apply (thsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold π1. rewrite dom_union_L. set_solver.
    + apply (gsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold π1. rewrite dom_union_L. set_solver.
    + by apply (fcap_ext_part W π1 πK φ).
Qed.

(** A hole beside a value an earlier hole returned. The value ages by
    the hole's cost. *)
Lemma sem_bind2 W0 Θ Γ e σ2 c2 t2 σv σv' (fr : expr → frame) σ r d n W g γ πΘ πΓ v πv φ tk r2 :
  (∀ (g' : chan → chan) v, frame_emap g' (fr v) = fr (emap g' v)) → (∀ v, is_val v = true → frame_val (fr v)) →
  csem W0 Θ Γ e σ2 c2 t2 → cagex c2 σv σv' → fle c2 d → wbext W0 W → is_val v = true →
  thsem n W Θ g πΘ φ → gsem n W Γ γ πΓ φ → Vfuel n W σv πv (mres (dom πv) φ) v →
  dom πΘ ## dom πΓ → dom (πΘ ∪ πΓ) ## dom πv →
  dom φ = dom ((πΘ ∪ πΓ) ∪ πv) → fcap_ext W ((πΘ ∪ πΓ) ∪ πv) φ → meets t2 r2 tk →
  (∀ j W' v' πv' v2 π2 φ' i tk', j ≤ n → wbext W0 W' → fle (Some i) c2 → is_val v2 = true → r2 ≤ tk' →
     is_val v' = true →
     Vfuel j W' σv' πv' (mres (dom πv') φ') v' → Vfuel j W' σ2 π2 (mres (dom π2) φ') v2 →
     dom π2 ## dom πv' → dom φ' = dom (π2 ∪ πv') → fcap_ext W' (π2 ∪ πv') φ' →
     FuelE j W' σ r (π2 ∪ πv') φ' tk' (fminus i d) (fill_frame (fr v') v2)) →
  FuelE n W σ r ((πΘ ∪ πΓ) ∪ πv) φ tk d (fill_frame (fr v) (subst γ (emap g e))).
Proof.
  intros Hfe Hfv Hcs Hs Hcd Hb Hvv HT HG HV Hd1 Hd Hdφ Hc Hm Hk.
  set (π1 := πΘ ∪ πΓ).
  rewrite (union_dom_disj π1 πv φ Hdφ).
  change (fill_frame (fr v) (subst γ (emap g e))) with (efill [fr v] (subst γ (emap g e))).
  assert (Hdφ1 : dom (mres (dom π1) φ) = dom π1) by (by eapply dom_mres_of).
  assert (HdφK : dom (mres (dom πv) φ) = dom πv) by (by eapply dom_mres_of_r).
  apply (FuelE_bind n W σ2 r2 σ r π1 (mres (dom π1) φ) πv (mres (dom πv) φ) tk c2 d [fr v]);
    [|done|done|done| | |done| |].
  - constructor; [by apply Hfv|constructor].
  - by apply (fcap_ext_part_r W π1 πv φ).
  - intros o f Hf. pose proof Hf as Hf'. apply lookup_mres_Some in Hf' as [_ Ho].
    exact (Vfuel_age_above n W c2 σv σv' πv _ v Hs HV o f Ho Hf).
  - intros W' g' πK' φK' i j v2 π2 φ2 tk' Hb' Hk' Rπ Rφ Hi Hj Hv Hr Hdis Hd2 Hc2 HV2. simpl. rewrite Hfe.
    assert (HdK' : dom φK' = dom πK') by (eapply renk_dom_eq; [exact HdφK|exact Rπ|exact Rφ]).
    apply (Hk j W' (emap g' v) πK' v2 π2 (φ2 ∪ (fminus i <$> φK')) i tk');
      [done|by eapply wbext_trans|done|done|done|by rewrite is_val_emap| | |done| |].
    + rewrite (mres_disj_r φ2 (fminus i <$> φK') πK'); [|by rewrite dom_fmap_L|by rewrite Hd2].
      apply (Vfuel_age j W' c2 i σv σv'); [done|done|].
      apply (Vfuel_wbext _ W); [done|]. apply (Vfuel_down _ n); [lia|].
      apply (Vfuel_rename n W σv πv (mres (dom πv) φ) v g'); [done|apply dom_mres_sub|done|done|done].
    + rewrite (mres_disj_l φ2 (fminus i <$> φK') π2); [done|done|]. rewrite dom_fmap_L, HdK'. done.
    + rewrite !dom_union_L, dom_fmap_L, HdK', Hd2. done.
    + apply fcap_ext_union; [done| |done]. apply (fcap_ext_fmap W' _ _ (fminus i)); [apply fminus_le|].
      apply (fcap_ext_wbext W); [done|]. eapply fcap_ext_rename; [|exact Rπ|exact Rφ]. by apply (fcap_ext_part_r W π1 πv φ).
  - apply Hcs; try done.
    + apply (thsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold π1. rewrite dom_union_L. set_solver.
    + apply (gsem_local _ _ _ _ _ φ); [|done]. intros o Ho. apply lookup_mres_in. unfold π1. rewrite dom_union_L. set_solver.
    + by apply (fcap_ext_part W π1 πv φ).
Qed.

(** ** Helpers for redexes *)

Lemma mrem_none {Y : Type} (X : gset cend) (m : gmap cend Y) : dom m ## X → mrem X m = m.
Proof.
  intros H. apply map_eq. intros o. destruct (m !! o) eqn:E.
  - apply lookup_mrem_Some. split; [done|]. intros Hx. apply (H o); [by eapply elem_of_dom_2|done].
  - destruct (mrem X m !! o) eqn:E'; [|done]. apply lookup_mrem_Some in E' as [? _]. congruence.
Qed.

Lemma mrem_all {Y : Type} (X : gset cend) (m : gmap cend Y) : dom m ⊆ X → mrem X m = ∅.
Proof.
  intros H. apply map_eq. intros o. rewrite lookup_empty. destruct (mrem X m !! o) eqn:E; [|done].
  apply lookup_mrem_Some in E as [E Hx]. exfalso. apply Hx, H. by eapply elem_of_dom_2.
Qed.

Lemma mrem_disj_l {Y Z : Type} (m1 m2 : gmap cend Y) (π : gmap cend Z) :
  dom m1 = dom π → dom m2 ## dom π → mrem (dom π) (m1 ∪ m2) = m2.
Proof.
  intros H1 H2. apply map_eq. intros o. destruct (decide (o ∈ dom π)) as [Ho|Ho].
  - destruct (mrem (dom π) (m1 ∪ m2) !! o) eqn:E; [apply lookup_mrem_Some in E as [_ ?]; done|].
    symmetry. apply not_elem_of_dom. intros Hin. by apply (H2 o).
  - destruct (m2 !! o) eqn:E.
    + apply lookup_mrem_Some. split; [|done]. apply lookup_union_Some_raw. right. split; [|done].
      apply not_elem_of_dom. by rewrite H1.
    + destruct (mrem (dom π) (m1 ∪ m2) !! o) eqn:E'; [|done]. apply lookup_mrem_Some in E' as [E' _].
      apply lookup_union_Some_raw in E' as [E'|[_ E']]; [|congruence].
      exfalso. apply Ho. rewrite <-H1. by eapply elem_of_dom_2.
Qed.

Lemma dom_single_inv {Y : Type} (m : gmap cend Y) o : dom m = {[o]} → ∃ y, m = {[o := y]}.
Proof.
  intros H. assert (o ∈ dom m) as [y Hy]%elem_of_dom by set_solver. exists y.
  apply map_eq. intros o'. destruct (decide (o' = o)) as [->|Hne]; [by rewrite lookup_singleton_eq|].
  rewrite lookup_singleton_ne by done. apply not_elem_of_dom. set_solver.
Qed.

(** An action on the only end held: the end moves to its next point and
    refills, or goes. *)
Lemma fact_single W (s : slabel) o (x : point) (φ1 : gmap cend fuel) :
  sl_end s = Some o → dom φ1 = {[o]} →
  fact W s {[o := x]} φ1 =
    match sl_next s x with
    | Some (o', k') => ({[o' := k']}, {[o' := w_bud W k']})
    | None => (∅, ∅)
    end.
Proof.
  intros He Hd. destruct (dom_single_inv φ1 o Hd) as [y ->]. unfold fact. rewrite He, lookup_singleton_eq.
  destruct (sl_next s x) as [[o' k']|]; rewrite !delete_singleton, !decide_True, fmap_empty by done; [|done].
  by rewrite !insert_empty.
Qed.

Lemma fcap_ext_single W o (x : point) : pt_known W x → fcap_ext W {[o := x]} {[o := w_bud W x]}.
Proof.
  intros Hk. apply fcap_ext_known.
  - intros o' f Hf. apply lookup_singleton_Some in Hf as [<- <-]. exists x. rewrite lookup_singleton_eq. split; [done|apply fle_refl].
  - intros o' k Hk'. by apply lookup_singleton_Some in Hk' as [_ <-].
Qed.

Lemma pt_known_shift W (x : point) n : pt_known W (pt_shift n x) ↔ pt_known W x.
Proof. done. Qed.

Lemma pt_known_payload W (x : point) i : pt_known W (pt_payload x i) ↔ pt_known W x.
Proof. done. Qed.

Lemma tstep_app_val v1 v2 α e' : is_val v1 = true → is_val v2 = true → tstep (App v1 v2) α e' → head_step (App v1 v2) α e'.
Proof.
  intros H1 H2 Hst. apply tstep_app_inv in Hst as [(e1' & S1 & _)|[(_ & e2' & S2 & _)|(_ & _ & Hh)]].
  - exfalso. eapply val_no_tstep; [exact S1|by rewrite H1].
  - exfalso. eapply val_no_tstep; [exact S2|by rewrite H2].
  - done.
Qed.

Lemma Vfuel_move n W W' σ π φ v (g : chan → chan) π' φ' :
  wbext W W' → kinj g π → dom φ ⊆ dom π → renk g π π' → renk g φ φ' →
  Vfuel n W σ π φ v → Vfuel n W' σ π' φ' (emap g v).
Proof. intros Hb Hk Hd R1 R2 HV. apply (Vfuel_wbext _ W); [done|]. by apply (Vfuel_rename n W σ π φ v g). Qed.

(** FuelE of a term that is no value, from its clauses under every
    renaming and extension. *)
Lemma FuelE_redex n W σ r π φ tk d e :
  is_val e = false → fcap_ext W π φ →
  (∀ W' (g : chan → chan) π' φ', wbext W W' → kinj g π → renk g π π' → renk g φ φ' →
     fwait W' π' (emap g e) ∧ ∀ α e', tstep (emap g e) α e' → Fobl FuelE Vfuel n W' σ r π' φ' tk d α e') →
  FuelE (S n) W σ r π φ tk d e.
Proof.
  intros Hv Hc H. apply FuelE_S. intros W' g π' φ' Hb Hk R1 R2.
  destruct (H W' g π' φ' Hb Hk R1 R2) as [Hw Hs]. split_and!; [eapply renk_fcap; [apply Hc, Hb|done|done]|done| |done].
  intros Hv'. by rewrite is_val_emap, Hv in Hv'.
Qed.

Lemma sem_val n W σ r π φ tk d v :
  is_val v = true → meets tid r tk → fcap_ext W π φ → Vfuel n W σ π φ v → FuelE n W σ r π φ tk d v.
Proof. intros Hv Hm. apply FuelE_val; [done|by apply meets_tid]. Qed.

(** ** Leaves and structure *)

Lemma c_unit_sem W0 Γ : cunlenv Γ → csem W0 ∅ Γ EUnit (CTa CVal None) (Some 0) tid.
Proof.
  intros Hu n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  rewrite (thsem_empty _ _ _ _ _ HT), (gsem_unl _ _ _ _ _ _ Hu HG), map_empty_union in *. simpl.
  apply sem_val; [done|done|done|apply Vfuel_unit].
Qed.

Lemma c_pt_sem W0 Γ x ρ :
  cunlenv Γ → pt_known W0 x → cpfitpt W0 x ρ → csem W0 ∅ Γ (EPt x) (CTa (CPt ρ) None) (Some 0) tid.
Proof.
  intros Hu Hk Hf n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  rewrite (thsem_empty _ _ _ _ _ HT), (gsem_unl _ _ _ _ _ _ Hu HG), map_empty_union in *. simpl.
  apply sem_val; [done|done|done|]. apply Vfuel_eq. simpl. exists x. split_and!; [done|done| |].
  - by apply (wbext_known W0).
  - by apply (pfitpt_wbext W0).
Qed.

Lemma c_var_sem W0 Γ x σ : conly Γ x σ → csem W0 ∅ Γ (Var x) σ (Some 0) tid.
Proof.
  intros Ho n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  rewrite (thsem_empty _ _ _ _ _ HT), map_empty_union in *. simpl.
  destruct (gsem_conly _ _ _ _ _ _ _ _ Ho HG) as [Hv HV]. rewrite (mres_dom_eq πΓ φ Hdφ) in HV.
  by apply sem_val.
Qed.

Lemma c_ch_sem W0 Γ (c : chan) (b : bool) σ : cunlenv Γ → csem W0 {[(c, b) := σ]} Γ (Chan c b) σ (Some 0) tid.
Proof.
  intros Hu n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  rewrite (gsem_unl _ _ _ _ _ _ Hu HG), map_union_empty in *. simpl.
  destruct (thsem_single _ _ _ _ _ _ _ _ HT) as (x & -> & HV).
  rewrite <-(dom_singleton_L (g c, b) x), (mres_dom_eq _ φ Hdφ) in HV.
  by apply sem_val.
Qed.

Lemma c_sub_sem W0 Θ Γ e σ σ' c c' t t' :
  csem W0 Θ Γ e σ c t → σ ⊑c σ' → fle c c' → tle t t' → csem W0 Θ Γ e σ' c' t'.
Proof.
  intros Hcs Hs Hc Ht n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hcap r tk Hm.
  apply (FuelE_mono n W σ σ' r r _ _ tk tk c c'); [done|lia|lia|done|]. apply Hcs; try done. by apply Ht.
Qed.

Lemma c_weak_sem W0 Θ Γ' Γ e σ c t : cwk Γ' Γ → csem W0 Θ Γ' e σ c t → csem W0 Θ Γ e σ c t.
Proof.
  intros Hw Hcs n W g γ πΘ πΓ φ Hb HT HG. apply Hcs; [done|done|]. by apply (gsem_wk _ _ _ Γ).
Qed.

Lemma c_contract_sem W0 Θ Γ σ e σ' c t :
  cfree (cta_ty σ) → csem W0 Θ (Some σ :: Some σ :: Γ) e σ' c t → csem W0 Θ (Some σ :: Γ) (rename pred e) σ' c t.
Proof.
  intros Hf Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  rewrite emap_rename, subst_rename. apply (Hcs n W g (λ x, γ (pred x))); try done.
  by apply gsem_contract.
Qed.

(** ** Redexes of the primitive constants *)

Lemma Vfuel_end_inv n W P a π φ v :
  Vfuel n W (CTa (CEnd P) a) π φ v →
  ∃ (c : chan) (b : bool) (x : point) f, v = Chan c b ∧ π = {[(c, b) := x]} ∧ pfits W x P ∧
    φ !! (c, b) = Some f ∧ fle a f ∧ fpts W π.
Proof. rewrite Vfuel_eq. destruct v; simpl; try done; intros (?&?&?&?&H&_); discriminate H. Qed.

Lemma pnode_inv P n bd : pnode P = Some (n, bd) → P = PNode n bd.
Proof. destruct P; simpl; [by intros [= -> ->]|done]. Qed.

(** An end, renamed and moved to a later world. *)
Lemma end_setup j W W' P a π φ (c : chan) (b : bool) (g : chan → chan) π' φ' :
  Vfuel j W (CTa (CEnd P) a) π φ (Chan c b) → dom φ = dom π → wbext W W' → renk g π π' → renk g φ φ' →
  ∃ x, π = {[(c, b) := x]} ∧ π' = {[(g c, b) := x]} ∧ dom φ' = {[(g c, b)]} ∧ pfits W' x P.
Proof.
  intros HV Hd Hb R1 R2. destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV) as (c' & b' & x & f & [= <- <-] & -> & Hp & _).
  exists x. pose proof (renk_singleton g (c, b) x π' R1) as ->. split_and!; [done|done| |by apply (pfits_wbext W)].
  rewrite (renk_dom_eq g _ _ _ _ Hd R1 R2). by rewrite dom_singleton_L.
Qed.

Lemma ftick_ok_single o (φ : gmap cend fuel) : dom φ = {[o]} → ftick_ok o φ.
Proof. intros Hd o' m Hne Hm. apply elem_of_dom_2 in Hm. rewrite Hd in Hm. set_solver. Qed.

Lemma partner_fin W x n bd : pfits W x (PNode n bd) → w_bud W (pt_dual x) ≠ None.
Proof. intros Hp. destruct (pfits_node _ _ _ _ Hp) as (_ & _ & [m Hm] & _). by rewrite Hm. Qed.

Lemma close_redex j W P a n π φ tk d r v :
  pnode P = Some (n, PCls) → Vfuel j W (CTa (CEnd P) a) π φ v → dom φ = dom π → fcap_ext W π φ →
  fle (Some 1) d → r ≤ tk → FuelE j W (CTa CVal None) r π φ tk d (App EClos v).
Proof.
  intros HP HV Hd Hc H1 Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV) as (c & b & x & f & -> & _). apply pnode_inv in HP as ->.
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2.
  destruct (end_setup _ _ _ _ _ _ _ _ _ _ _ _ HV Hd Hb R1 R2) as (x' & -> & -> & Hdφ' & Hp). cbn [emap].
  split.
  - intros s e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst. simpl in Ho.
    injection Ho as <-. exists x'. rewrite lookup_singleton_eq. split; [done|by eapply partner_fin].
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst.
    unfold Fobl; cbv beta iota. split; [intros o [= <-]; split; [by apply ftick_ok_single|done]|].
    assert (Hf : fupd W' {[(g c, b) := x']} φ' (LSess (SClos (g c, b))) = (∅, ∅)).
    { unfold fupd. cbn [sl_out]. rewrite !mrem_none by set_solver. by rewrite fact_single. }
    rewrite Hf. cbn [fst snd]. apply sem_val; [done|by apply meets_tid|apply fcap_ext_empty|apply Vfuel_unit].
Qed.

Lemma recv_redex j W P a n σ P' n' b' π φ tk d r v :
  pnode P = Some (n, PRcv σ P') → pnode P' = Some (n', b') →
  Vfuel j W (CTa (CEnd P) a) π φ v → dom φ = dom π → fcap_ext W π φ →
  fle (Some 1) d → r ≤ tk → FuelE j W (CTa (CProd σ (CTa (CEnd P') (Some n'))) (Some 0)) r π φ tk d (App ERecv v).
Proof.
  intros HP HP' HV Hd Hc H1 Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV) as (c & b & x & f & -> & _).
  apply pnode_inv in HP as ->. apply pnode_inv in HP' as ->.
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2.
  destruct (end_setup _ _ _ _ _ _ _ _ _ _ _ _ HV Hd Hb R1 R2) as (x' & -> & -> & Hdφ' & Hp). cbn [emap].
  destruct (pfits_rcv _ _ _ _ _ Hp) as [Hpc Hp1].
  split.
  - intros s e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst. simpl in Ho.
    injection Ho as <-. exists x'. rewrite lookup_singleton_eq. split; [done|by eapply partner_fin].
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done].
    pose proof (head_step_label_val _ _ _ Hst) as Hlv. inversion Hst; subst. simpl in Hlv.
    unfold Fobl; cbv beta iota. split; [intros o [= <-]; split; [by apply ftick_ok_single|done]|].
    assert (Hf : fupd W' {[(g c, b) := x']} φ' (LSess (SRecv (g c, b) v)) =
                 ({[(g c, b) := pt_shift 1 x']}, {[(g c, b) := w_bud W' (pt_shift 1 x')]})).
    { unfold fupd. cbn [sl_out]. rewrite !mrem_none by set_solver. by rewrite fact_single. }
    rewrite Hf. cbn [fst snd]. intros k j' πi φi Hk' Hj' Hdi Hin HVi.
    rewrite lookup_singleton_eq in Hk'. injection Hk' as <-.
    destruct Hin as (Dπ & Dφ & Hci & Hfin & Hkn).
    assert (Hdisj : dom πi ## dom ({[(g c, b) := pt_shift 1 x']} : gmap cend point)) by done.
    rewrite (union_comm_d {[(g c, b) := pt_shift 1 x']} πi) by set_solver.
    rewrite (union_comm_d {[(g c, b) := w_bud W' (pt_shift 1 x')]} φi)
      by (rewrite Dφ, <-Dπ, dom_singleton_L; rewrite dom_singleton_L in Hdisj; set_solver).
    apply sem_val; [simpl; destruct (is_val v); done|by apply meets_tid| |].
    + apply fcap_ext_union; [|apply fcap_ext_single; by apply pt_known_shift, (pfits_node _ _ _ _ Hp)|set_solver].
      by apply fcap_ext_known.
    + apply Vfuel_pair; [set_solver|by rewrite Dφ, Dπ|by rewrite !dom_singleton_L| |].
      * rewrite cadd_0. by apply (Vfuel_sub _ _ (w_pc W' (pt_dual x'))).
      * apply (Vfuel_refill j' W' n' b' (g c) b (pt_shift 1 x')); [done|by rewrite lookup_singleton_eq].
Qed.

Lemma sel_redex j W (s : bool) P a n P1 P2 n' b' π φ tk d r v :
  pnode P = Some (n, PSel P1 P2) → pnode (if s then P2 else P1) = Some (n', b') →
  Vfuel j W (CTa (CEnd P) a) π φ v → dom φ = dom π → fcap_ext W π φ →
  fle (Some 1) d → r ≤ tk →
  FuelE j W (CTa (CEnd (if s then P2 else P1)) (Some n')) r π φ tk d (App (Konst (ksel s)) v).
Proof.
  intros HP HP' HV Hd Hc H1 Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV) as (c & b & x & f & -> & _). apply pnode_inv in HP as ->.
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2.
  destruct (end_setup _ _ _ _ _ _ _ _ _ _ _ _ HV Hd Hb R1 R2) as (x' & -> & -> & Hdφ' & Hp). cbn [emap].
  pose proof (pfits_sel _ _ _ _ _ s Hp) as Hps. rewrite (pnode_inv _ _ _ HP') in Hps |- *.
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. destruct s; inversion Hst; subst; simpl in Ho;
      injection Ho as <-; exists x'; rewrite lookup_singleton_eq; (split; [done|by eapply partner_fin]).
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done].
    assert (∃ s', α = LSess (SSel (g c, b) s') ∧ e' = Chan (g c) false ∧ s' = s) as (s' & -> & -> & ->)
      by (destruct s; inversion Hst; subst; eauto).
    unfold Fobl; cbv beta iota. split; [intros o [= <-]; split; [by apply ftick_ok_single|done]|]. intros _.
    assert (Hf : fupd W' {[(g c, b) := x']} φ' (LSess (SSel (g c, b) s)) =
                 ({[(g c, false) := sel_pt x' s]}, {[(g c, false) := w_bud W' (sel_pt x' s)]})).
    { unfold fupd. cbn [sl_out]. rewrite !mrem_none by set_solver. by rewrite fact_single. }
    rewrite Hf. cbn [fst snd]. apply sem_val; [done|by apply meets_tid| |].
    + apply fcap_ext_single. by apply (pfits_node _ _ _ _ Hps).
    + apply (Vfuel_refill j W' n' b' (g c) false (sel_pt x' s)); [done|by rewrite lookup_singleton_eq].
Qed.

Lemma bra_redex j W P a n P1 P2 n1 b1 n2 b2 π φ tk d r v :
  pnode P = Some (n, PBra P1 P2) → pnode P1 = Some (n1, b1) → pnode P2 = Some (n2, b2) →
  Vfuel j W (CTa (CEnd P) a) π φ v → dom φ = dom π → fcap_ext W π φ →
  fle (Some 1) d → r ≤ tk →
  FuelE j W (CTa (CSum (CTa (CEnd P1) (Some n1)) (CTa (CEnd P2) (Some n2))) (Some 0)) r π φ tk d (App EBra v).
Proof.
  intros HP HP1 HP2 HV Hd Hc H1 Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV) as (c & b & x & f & -> & _). apply pnode_inv in HP as ->.
  apply pnode_inv in HP1 as ->. apply pnode_inv in HP2 as ->.
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2.
  destruct (end_setup _ _ _ _ _ _ _ _ _ _ _ _ HV Hd Hb R1 R2) as (x' & -> & -> & Hdφ' & Hp). cbn [emap].
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst; simpl in Ho.
    injection Ho as <-. exists x'. rewrite lookup_singleton_eq. split; [done|by eapply partner_fin].
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done].
    assert (∃ s, α = LSess (SBra (g c, b) s) ∧ e' = inj_of s (Chan (g c) true)) as (s & -> & ->)
      by (inversion Hst; subst; eauto).
    unfold Fobl; cbv beta iota. split; [intros o [= <-]; split; [by apply ftick_ok_single|done]|]. intros _.
    pose proof (pfits_bra _ _ _ _ _ s Hp) as Hps.
    assert (Hf : fupd W' {[(g c, b) := x']} φ' (LSess (SBra (g c, b) s)) =
                 ({[(g c, true) := bra_pt x' s]}, {[(g c, true) := w_bud W' (bra_pt x' s)]})).
    { unfold fupd. cbn [sl_out]. rewrite !mrem_none by set_solver. by rewrite fact_single. }
    rewrite Hf. cbn [fst snd].
    apply sem_val; [by destruct s|by apply meets_tid|apply fcap_ext_single; destruct s; by apply (pfits_node _ _ _ _ Hps)|].
    destruct s; simpl.
    + apply Vfuel_inj2. rewrite cadd_0. apply (Vfuel_refill j W' n2 b2 (g c) true (bra_pt x' true)); [done|by rewrite lookup_singleton_eq].
    + apply Vfuel_inj1. rewrite cadd_0. apply (Vfuel_refill j W' n1 b1 (g c) true (bra_pt x' false)); [done|by rewrite lookup_singleton_eq].
Qed.

Lemma Vfuel_pair_inv n W σ1 σ2 a π φ v :
  Vfuel n W (CTa (CProd σ1 σ2) a) π φ v →
  ∃ u w π1 π2, v = Pair u w ∧ π = π1 ∪ π2 ∧ dom π1 ## dom π2 ∧
    Vfuel n W (cadd a σ1) π1 (mres (dom π1) φ) u ∧ Vfuel n W (cadd a σ2) π2 (mres (dom π2) φ) w.
Proof.
  rewrite Vfuel_eq. destruct v; simpl; try done. intros (π1 & π2 & -> & Hd & H1 & H2).
  exists v1, v2, π1, π2. rewrite !Vfuel_eq. done.
Qed.

Lemma Vfuel_pt_inv n W ρ a π φ v :
  Vfuel n W (CTa (CPt ρ) a) π φ v → ∃ x, v = EPt x ∧ π = ∅ ∧ pt_known W x ∧ pfitpt W x ρ.
Proof. rewrite Vfuel_eq. destruct v; simpl; try done; intros (?&H&_); discriminate H. Qed.

Lemma Vfuel_arr_inv n W c t h σ1 σ2 a π φ v :
  Vfuel n W (CTa (CArr c t h σ1 σ2) a) π φ v →
  ∃ eb, v = Lam eb ∧ dom π = fends v ∧ fpts W π ∧ farr FuelE Vfuel n W c t h σ1 σ2 a π φ (λ u, subst1 u eb).
Proof. rewrite Vfuel_eq. destruct v; simpl; try done. intros H. by exists v. Qed.

Lemma Vfuel_box_inv n W c t σ a π φ v :
  Vfuel n W (CTa (CBox c t σ) a) π φ v →
  ∃ eb, v = EBox eb ∧ π = ∅ ∧ fends eb = ∅ ∧
    ∀ W' j r tk, wbext W W' → j < n → meets t r tk → FuelE j W' σ r ∅ ∅ tk c (subst1 (EBox eb) eb).
Proof. rewrite Vfuel_eq. destruct v; simpl; try done. intros H. by exists v. Qed.

Lemma dom_empty_map {Y Z : Type} (m : gmap cend Y) (π : gmap cend Z) : dom m = dom π → π = ∅ → m = ∅.
Proof. intros H ->. rewrite dom_empty_L in H. by apply dom_empty_inv_L. Qed.

Lemma send_redex j W σp σp' a a0 P n σ P' n' b' π φ tk d r v :
  pnode P = Some (n, PSnd σ P') → pnode P' = Some (n', b') →
  cagex (Some 1) (cadd a0 σp) σp' → σp' ⊑c σ → is_val v = true →
  Vfuel j W (CTa (CProd σp (CTa (CEnd P) a)) a0) π φ v → dom φ = dom π → fcap_ext W π φ →
  fle (Some 1) d → r ≤ tk → FuelE j W (CTa (CEnd P') (Some n')) r π φ tk d (App ESend v).
Proof.
  intros HP HP' Hs Hσ Hv HV Hd Hc H1 Hr. destruct j as [|j]; [apply FuelE_0|].
  apply pnode_inv in HP as ->. apply pnode_inv in HP' as ->.
  assert (Hh : cheld (cta_ty (cadd a0 σp))) by exact (cagex_cheld _ _ _ Hs ltac:(done)).
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2. cbn [emap].
  assert (Hdφ' : dom φ' = dom π') by (eapply renk_dom_eq; [exact Hd|exact R1|exact R2]).
  pose proof (Vfuel_move _ _ _ _ _ _ _ g π' φ' Hb Hk ltac:(by rewrite Hd) R1 R2 HV) as HV'.
  assert (Hv' : is_val (emap g v) = true) by by rewrite is_val_emap.
  destruct (Vfuel_pair_inv _ _ _ _ _ _ _ _ HV') as (w & e2 & πw & πe & Heq & -> & Hdwe & HVw & HVe).
  rewrite Heq in Hv' |- *. simpl in HVe.
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HVe) as (c & b & x & f & -> & -> & Hp & _).
  destruct σp as [τp ap]. simpl in Hh.
  destruct (Vfuel_held _ _ _ _ _ _ _ Hh HVw) as (Dw & Pw & _).
  assert (Habove := Vfuel_age_above _ _ _ _ _ _ _ _ Hs HVw).
  destruct (pfits_snd _ _ _ _ _ Hp) as [Hpc Hp1].
  assert (Hcx : (c, b) ∉ dom πw) by (rewrite dom_singleton_L in Hdwe; set_solver).
  assert (Hπx : (πw ∪ {[(c, b) := x]}) !! (c, b) = Some x).
  { apply lookup_union_Some_raw. right. split; [by apply not_elem_of_dom|by rewrite lookup_singleton_eq]. }
  assert (Hvw : is_val w = true) by (simpl in Hv'; destruct (is_val w); done).
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst. simpl in Ho.
    injection Ho as <-. exists x. split; [done|by eapply partner_fin].
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst.
    unfold Fobl; cbv beta iota. split_and!.
    + intros o [= <-]. split; [|done]. intros o' m Hne Hm. assert (Ho' : o' ∈ dom πw).
      { apply elem_of_dom_2 in Hm. rewrite Hdφ', dom_union_L, dom_singleton_L in Hm. set_solver. }
      apply (Habove o' (Some m) Ho'). by rewrite lookup_mres_in.
    + rewrite <-Dw, dom_union_L, dom_singleton_L. set_solver.
    + intros o k Ho Hk'. rewrite <-Dw in Ho. apply elem_of_dom in Ho as [k0 Hk0].
      rewrite (lookup_union_Some_l _ _ _ _ Hk0) in Hk'. injection Hk' as <-. by apply (Pw o).
    + intros k Hk'. rewrite Hπx in Hk'. injection Hk' as <-.
      rewrite <-Dw, (mres_disj_l πw {[(c, b) := x]} πw) by (done || set_solver).
      rewrite (map_fmap_ext ftick (fminus 1)) by (intros; apply ftick_fminus).
      apply (Vfuel_down _ (S j)); [lia|]. eapply Vfuel_sub; [eapply cst_trans; [exact Hσ|exact Hpc]|].
      apply (Vfuel_age _ _ (Some 1) 1 _ _ _ _ _ Hs); [apply fle_refl|exact HVw].
    + assert (Hf : fupd W' (πw ∪ {[(c, b) := x]}) φ' (LSess (SSend (c, b) w)) =
                   ({[(c, b) := pt_shift 1 x]}, {[(c, b) := w_bud W' (pt_shift 1 x)]})).
      { unfold fupd. cbn [sl_out]. rewrite <-Dw, (mrem_disj_l πw {[(c, b) := x]} πw) by (done || set_solver).
        apply fact_single; [done|]. rewrite dom_mrem, Hdφ', dom_union_L, dom_singleton_L. set_solver. }
      rewrite Hf. cbn [fst snd]. apply sem_val; [done|by apply meets_tid| |].
      * apply fcap_ext_single. by apply pt_known_shift, (pfits_node _ _ _ _ Hp).
      * apply (Vfuel_refill j W' n' b' c b (pt_shift 1 x)); [done|by rewrite lookup_singleton_eq].
Qed.

Lemma link_redex j W P1 a1 P2 a2 a0 π φ tk d r v :
  is_val v = true → Vfuel j W (CTa (CProd (CTa (CEnd P1) a1) (CTa (CEnd P2) a2)) a0) π φ v →
  dom φ = dom π → fcap_ext W π φ → meets (tlink tid) r tk →
  FuelE j W (CTa CVal None) r π φ tk d (App ELink v).
Proof.
  intros Hv HV Hd Hc Hm. destruct j as [|j]; [apply FuelE_0|].
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2. cbn [emap].
  assert (Hdφ' : dom φ' = dom π') by (eapply renk_dom_eq; [exact Hd|exact R1|exact R2]).
  pose proof (Vfuel_move _ _ _ _ _ _ _ g π' φ' Hb Hk ltac:(by rewrite Hd) R1 R2 HV) as HV'.
  assert (Hv' : is_val (emap g v) = true) by by rewrite is_val_emap.
  destruct (Vfuel_pair_inv _ _ _ _ _ _ _ _ HV') as (u & w & π1 & π2 & Heq & -> & Hd12 & HV1 & HV2).
  simpl in HV1, HV2.
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV1) as (c1 & b1 & x1 & f1 & -> & -> & _).
  destruct (Vfuel_end_inv _ _ _ _ _ _ _ HV2) as (c2 & b2 & x2 & f2 & -> & -> & _).
  rewrite Heq. destruct (link_split _ _ _ Hm) as [Htk Hm'].
  assert (Hdπ : dom ({[(c1, b1) := x1]} ∪ {[(c2, b2) := x2]} : gmap cend point) = {[(c1, b1); (c2, b2)]}).
  { rewrite dom_union_L, !dom_singleton_L. done. }
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst. done.
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst.
    unfold Fobl; cbv beta iota. split_and!; [intros o [=]|by rewrite Hdπ|done|].
    unfold fupd, fact. cbn [sl_out sl_end fst snd].
    rewrite (mrem_all _ ({[(c1, b1) := x1]} ∪ {[(c2, b2) := x2]})) by (by rewrite Hdπ).
    rewrite (mrem_all _ φ') by (by rewrite Hdφ', Hdπ).
    apply sem_val; [done|done|apply fcap_ext_empty|apply Vfuel_unit].
Qed.

Lemma new_redex j W ρ a P Q n b n' b' π φ tk d r v :
  pprof ρ = Some (P, Q) → pnode P = Some (n, b) → pnode Q = Some (n', b') →
  Vfuel j W (CTa (CPt ρ) a) π φ v → dom φ = dom π → r ≤ tk →
  FuelE j W (CTa (CProd (CTa (CEnd P) (Some n)) (CTa (CEnd Q) (Some n'))) (Some 0)) r π φ tk d (App ENew v).
Proof.
  intros Hρ HP HQ HV Hd Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_pt_inv _ _ _ _ _ _ _ HV) as (x & -> & -> & Hkx & Hfx).
  pose proof (dom_empty_map φ ∅ Hd eq_refl) as ->.
  destruct ρ as [P0 Q0 fl sc|]; [|done]. simpl in Hρ. injection Hρ as <- <-.
  apply pnode_inv in HP as ->. apply pnode_inv in HQ as ->.
  apply FuelE_redex; [done|apply fcap_ext_empty|]. intros W' g π' φ' Hb Hk R1 R2.
  rewrite (renk_empty g π' R1), (renk_empty g φ' R2). cbn [emap].
  assert (Hf' : pfitpt W' x (Prof (PNode n b) (PNode n' b') fl sc)) by (by apply (pfitpt_wbext W)).
  inversion Hf' as [|? ? ? ? ? HpP HpQ _ _]; subst.
  destruct (pfits_node _ _ _ _ HpP) as (Hk1 & Hn1 & [m1 Hm1] & _).
  destruct (pfits_node _ _ _ _ HpQ) as (Hk2 & Hn2 & [m2 Hm2] & _). rewrite pt_dual_dual in Hm2.
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst.
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst.
    unfold Fobl; cbv beta iota. intros _ _. cbn [fupd fst snd].
    set (o1 := (c, pt_pol x)). set (o2 := (c, negb (pt_pol x))).
    assert (Hne : o1 ≠ o2) by (unfold o1, o2; destruct (pt_pol x); done).
    rewrite !insert_empty, !insert_union_singleton_l.
    apply sem_val; [done|by apply meets_tid| |].
    + apply fcap_ext_union; [apply fcap_ext_single; done|apply fcap_ext_single; done|].
      rewrite !dom_singleton_L. set_solver.
    + apply Vfuel_pair; [rewrite !dom_singleton_L; set_solver|by rewrite !dom_singleton_L|by rewrite !dom_singleton_L| |];
        rewrite cadd_0.
      * apply (Vfuel_end _ _ _ _ _ _ _ _ (w_bud W' x)); [done|done|by rewrite Hm1|by rewrite lookup_singleton_eq|done].
      * apply (Vfuel_end _ _ _ _ _ _ _ _ (w_bud W' (pt_dual x))); [done|done|by rewrite pt_dual_dual, Hm2|by rewrite lookup_singleton_eq|done].
Qed.

Lemma pfitpt_fld W x ρ i : pfitpt W x ρ → pfitpt W (pt_payload x i) (pfld ρ i).
Proof. intros H. destruct ρ; simpl; [|constructor]. inversion H as [|? ? ? ? ? _ _ Hf _]; subst. exact (Hf i). Qed.

Lemma pfitpt_suc W x ρ : pfitpt W x ρ → pfitpt W (pt_shift 1 x) (psuc ρ).
Proof. intros H. destruct ρ; simpl; [|constructor]. inversion H as [|? ? ? ? ? _ _ _ Hs]; subst. exact Hs. Qed.

Lemma pay_redex j W ρ a i π φ tk d r v :
  Vfuel j W (CTa (CPt ρ) a) π φ v → dom φ = dom π → r ≤ tk →
  FuelE j W (CTa (CPt (pfld ρ i)) None) r π φ tk d (App (Konst (KPay i)) v).
Proof.
  intros HV Hd Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_pt_inv _ _ _ _ _ _ _ HV) as (x & -> & -> & Hkx & Hfx).
  pose proof (dom_empty_map φ ∅ Hd eq_refl) as ->.
  apply (FuelE_beta j W _ r ∅ ∅ tk d [] _ (EPt (pt_payload x i))); [by apply Forall_nil|constructor|apply fcap_ext_empty|].
  apply sem_val; [done|by apply meets_tid|apply fcap_ext_empty|]. apply Vfuel_eq. simpl.
  exists (pt_payload x i). split_and!; [done|done|done|by apply pfitpt_fld].
Qed.

Lemma succ_redex j W ρ a π φ tk d r v :
  Vfuel j W (CTa (CPt ρ) a) π φ v → dom φ = dom π → r ≤ tk →
  FuelE j W (CTa (CPt (psuc ρ)) None) r π φ tk d (App (Konst KSucc) v).
Proof.
  intros HV Hd Hr. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_pt_inv _ _ _ _ _ _ _ HV) as (x & -> & -> & Hkx & Hfx).
  pose proof (dom_empty_map φ ∅ Hd eq_refl) as ->.
  apply (FuelE_beta j W _ r ∅ ∅ tk d [] _ (EPt (pt_shift 1 x))); [by apply Forall_nil|constructor|apply fcap_ext_empty|].
  apply sem_val; [done|by apply meets_tid|apply fcap_ext_empty|]. apply Vfuel_eq. simpl.
  exists (pt_shift 1 x). split_and!; [done|done|done|by apply pfitpt_suc].
Qed.

Lemma force_redex j W c t σ a π φ tk d r v :
  Vfuel j W (CTa (CBox c t σ) a) π φ v → dom φ = dom π → meets t r tk → fle c d →
  FuelE j W σ r π φ tk d (App EForce v).
Proof.
  intros HV Hd Hm Hcd. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_box_inv _ _ _ _ _ _ _ _ _ HV) as (eb & -> & -> & _ & HB).
  pose proof (dom_empty_map φ ∅ Hd eq_refl) as ->.
  apply (FuelE_beta j W _ r ∅ ∅ tk d [] _ (subst1 (EBox eb) eb)); [by apply Forall_nil|constructor|apply fcap_ext_empty|].
  apply (FuelE_frame_mono _ _ _ _ _ _ _ c); [done|]. apply HB; [apply wbext_refl|lia|done].
Qed.

Lemma app_redex j W c t h σ1 σ2 a π1 φ1 π2 φ2 tk d r v1 v2 :
  Vfuel j W (CTa (CArr c t h σ1 σ2) a) π1 φ1 v1 → Vfuel j W σ1 π2 φ2 v2 → is_val v2 = true →
  dom π1 ## dom π2 → dom φ1 = dom π1 → dom φ2 = dom π2 → fcap_ext W π1 φ1 → fcap_ext W π2 φ2 →
  meets t r tk → fle c d → FuelE j W σ2 r (π2 ∪ π1) (φ2 ∪ φ1) tk d (App v1 v2).
Proof.
  intros HV1 HV2 Hv Hd H1 H2 Hc1 Hc2 Hm Hcd. destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_arr_inv _ _ _ _ _ _ _ _ _ _ _ HV1) as (eb & -> & _ & _ & Hfl & HF).
  apply (FuelE_beta j W _ r _ _ tk d [] _ (subst1 v2 eb)); [by apply Forall_nil|apply HeadApp; by rewrite Hv|by apply fcap_ext_union|].
  rewrite (union_comm_d π2 π1), (union_comm_d φ2 φ1) by (rewrite ?H1, ?H2; set_solver).
  apply (FuelE_frame_mono _ _ _ _ _ _ _ c); [done|].
  apply (HF W j φ1 v2 π2 φ2); [apply wbext_refl|lia|done|done| |set_solver| |apply (Vfuel_down _ (S j)); [lia|done]|done].
  - intros o f Ho. eapply fle_trans; [apply fle_fadd_l|exact (Hfl o f Ho)].
  - split_and!; done.
Qed.

Lemma spawn_redex j W c' t' h a1 σ' a π φ tk d r v :
  Vfuel j W (CTa (CArr c' t' h (CTa CVal a1) σ') a) π φ v → fle (Some 1) a →
  dom φ = dom π → fcap_ext W π φ → meets (tspawn (snd t') tid) r tk →
  FuelE j W (CTa CVal None) r π φ tk d (App ESpawn v).
Proof.
  intros HV Ha Hd Hc Hm. destruct j as [|j]; [apply FuelE_0|].
  destruct (spawn_split _ _ _ _ Hm) as [Hch Hpar].
  destruct (Vfuel_arr_inv _ _ _ _ _ _ _ _ _ _ _ HV) as (eb & -> & _ & _ & _ & _).
  apply FuelE_redex; [done|done|]. intros W' g π' φ' Hb Hk R1 R2. cbn [emap].
  assert (Hdφ' : dom φ' = dom π') by (eapply renk_dom_eq; [exact Hd|exact R1|exact R2]).
  assert (Hc' : fcap_ext W' π' φ') by (apply (fcap_ext_wbext W); [done|]; eapply fcap_ext_rename; eauto).
  pose proof (Vfuel_move _ _ _ _ _ _ _ g π' φ' Hb Hk ltac:(by rewrite Hd) R1 R2 HV) as HV'.
  destruct (Vfuel_arr_inv _ _ _ _ _ _ _ _ _ _ _ HV') as (eb' & Heq & Hdom' & _ & Hfl' & HF').
  cbn [emap] in Heq, Hdom'. rewrite Heq in Hdom' |- *. clear Heq.
  assert (Hab : ∀ o f, φ' !! o = Some f → fle (Some (S h)) f).
  { intros o f Ho. eapply fle_trans; [|exact (Hfl' o f Ho)]. destruct a as [a|]; simpl in *; lia. }
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst.
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done]. inversion Hst; subst.
    unfold Fobl; cbv beta iota. split_and!.
    + by rewrite <-Hdom'.
    + intros o m _ Hom. specialize (Hab o _ Hom). simpl in Hab. lia.
    + unfold fchild. cbn [fst snd]. rewrite <-Hdom', mres_dom, (mres_dom_eq π' φ' Hdφ').
      destruct j as [|j0]; [apply FuelE_0|].
      apply (FuelE_beta j0 W' _ 0 π' (ftick <$> φ') (Nat.div2 (S tk)) None [] _ (subst1 EUnit eb')); [by apply Forall_nil|by apply HeadApp| |].
      { apply (fcap_ext_fmap _ _ _ ftick); [apply ftick_le|done]. }
      apply (FuelE_mono _ _ σ' cany 0 0 _ _ (Nat.div2 (S tk)) (Nat.div2 (S tk)) c' None); [apply cst_any|lia|lia|apply fle_None|].
      rewrite <-(map_union_empty π'), <-(map_union_empty (ftick <$> φ')).
      apply (HF' W' j0 (ftick <$> φ') EUnit ∅ ∅); [apply wbext_refl|lia|by rewrite dom_fmap_L| | |set_solver| |apply Vfuel_unit|].
      * apply (fcap_ext_fmap _ _ _ ftick); [apply ftick_le|done].
      * intros o f Ho. apply lookup_fmap_Some in Ho as (f0 & <- & Ho). specialize (Hab o f0 Ho).
        destruct f0; simpl in *; lia.
      * split_and!; [done|done|apply fcap_ext_empty].
      * apply meets_zero. done.
    + unfold fupd. cbn [fst snd]. rewrite (mrem_all _ π') by (by rewrite Hdom').
      rewrite (mrem_all _ φ') by (by rewrite Hdφ', Hdom').
      apply sem_val; [done|done|apply fcap_ext_empty|apply Vfuel_unit].
Qed.

(** ** Rules over one subterm *)

Lemma ectx_ok_konst (k : konst) : ectx_ok [FAppR (Konst k)].
Proof. constructor; [done|by apply Forall_nil]. Qed.

Ltac bind0 K r1 :=
  lazymatch goal with
  | Hcs : csem ?W0 ?Θ ?Γ ?e ?s1 ?c1 ?t1, Hb : wbext ?W0 ?W, HT : thsem ?n ?W ?Θ ?g ?πΘ ?φ, HG : gsem ?n ?W ?Γ ?γ ?πΓ ?φ
    |- FuelE _ _ ?σ ?r _ _ ?tk ?d _ =>
      apply (sem_bind0 W0 Θ Γ e s1 c1 t1 K σ r d n W g γ πΘ πΓ φ tk r1);
        [first [apply ectx_ok_konst|constructor; [done|by apply Forall_nil]]|intros ?; reflexivity|exact Hcs| |done|done|done|done|done|done| |];
        [|done|intros j W' i v πv φv tk' Hj Hb' Hi Hv Hr Hdv Hcv HV]
  end.

Lemma c_inj1_sem W0 Θ Γ e σ1 σ2 c t :
  csem W0 Θ Γ e σ1 c t → csem W0 Θ Γ (Inj1 e) (CTa (CSum σ1 σ2) (Some 0)) c t.
Proof.
  intros Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FInj1] r; [apply fle_refl|]. simpl.
  apply FuelE_val; [done|done|done|]. apply Vfuel_inj1. by rewrite cadd_0.
Qed.

Lemma c_inj2_sem W0 Θ Γ e σ1 σ2 c t :
  csem W0 Θ Γ e σ2 c t → csem W0 Θ Γ (Inj2 e) (CTa (CSum σ1 σ2) (Some 0)) c t.
Proof.
  intros Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FInj2] r; [apply fle_refl|]. simpl.
  apply FuelE_val; [done|done|done|]. apply Vfuel_inj2. by rewrite cadd_0.
Qed.

Lemma c_force_sem W0 Θ Γ e c t σ a c0 t0 :
  csem W0 Θ Γ e (CTa (CBox c t σ) a) c0 t0 → tok t0 t →
  csem W0 Θ Γ (App EForce e) σ (fadd c0 c) (tseq t0 t).
Proof.
  intros Hcs Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r' & Hm1 & Hm2).
  bind0 [FAppR EForce] r'; [apply fle_fadd_l|]. simpl.
  apply (force_redex _ _ _ _ _ _ _ _ _ _ _ _ HV Hdv); [by apply (meets_mono _ _ r')|by apply fle_fminus_fadd].
Qed.

Lemma c_new_sem W0 Θ Γ e ρ a c0 t0 P Q n b n' b' :
  csem W0 Θ Γ e (CTa (CPt ρ) a) c0 t0 →
  pprof ρ = Some (P, Q) → pnode P = Some (n, b) → pnode Q = Some (n', b') →
  csem W0 Θ Γ (App ENew e) (CTa (CProd (CTa (CEnd P) (Some n)) (CTa (CEnd Q) (Some n'))) (Some 0)) c0 t0.
Proof.
  intros Hcs Hρ HP HQ n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR ENew] r; [apply fle_refl|]. simpl.
  by apply (new_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hρ HP HQ HV Hdv).
Qed.

Lemma c_pay_sem W0 Θ Γ e (ip : nat) ρ a c0 t0 :
  csem W0 Θ Γ e (CTa (CPt ρ) a) c0 t0 →
  csem W0 Θ Γ (App (Konst (KPay ip)) e) (CTa (CPt (pfld ρ ip)) None) c0 t0.
Proof.
  intros Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR (Konst (KPay ip))] r; [apply fle_refl|]. simpl.
  by apply (pay_redex _ _ _ _ _ _ _ _ _ _ _ HV Hdv).
Qed.

Lemma c_succ_sem W0 Θ Γ e ρ a c0 t0 :
  csem W0 Θ Γ e (CTa (CPt ρ) a) c0 t0 →
  csem W0 Θ Γ (App (Konst KSucc) e) (CTa (CPt (psuc ρ)) None) c0 t0.
Proof.
  intros Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR (Konst KSucc)] r; [apply fle_refl|]. simpl.
  by apply (succ_redex _ _ _ _ _ _ _ _ _ _ HV Hdv).
Qed.

Lemma c_send_sem W0 Θ Γ e σp σp' a a0 P n σ P' n' b' c0 t0 :
  csem W0 Θ Γ e (CTa (CProd σp (CTa (CEnd P) a)) a0) c0 t0 →
  pnode P = Some (n, PSnd σ P') → pnode P' = Some (n', b') →
  cagex (Some 1) (cadd a0 σp) σp' → σp' ⊑c σ →
  csem W0 Θ Γ (App ESend e) (CTa (CEnd P') (Some n')) (fadd c0 (Some 1)) t0.
Proof.
  intros Hcs HP HP' Hs Hσ n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR ESend] r; [apply fle_fadd_l|]. simpl.
  apply (send_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HP' Hs Hσ Hv HV Hdv Hcv); [by apply fle_fminus_fadd|done].
Qed.

Lemma c_recv_sem W0 Θ Γ e a P n σ P' n' b' c0 t0 :
  csem W0 Θ Γ e (CTa (CEnd P) a) c0 t0 → pnode P = Some (n, PRcv σ P') → pnode P' = Some (n', b') →
  csem W0 Θ Γ (App ERecv e) (CTa (CProd σ (CTa (CEnd P') (Some n'))) (Some 0)) (fadd c0 (Some 1)) t0.
Proof.
  intros Hcs HP HP' n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR ERecv] r; [apply fle_fadd_l|]. simpl.
  apply (recv_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HP' HV Hdv Hcv); [by apply fle_fminus_fadd|done].
Qed.

Lemma c_close_sem W0 Θ Γ e a P n c0 t0 :
  csem W0 Θ Γ e (CTa (CEnd P) a) c0 t0 → pnode P = Some (n, PCls) →
  csem W0 Θ Γ (App EClos e) (CTa CVal None) (fadd c0 (Some 1)) t0.
Proof.
  intros Hcs HP n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR EClos] r; [apply fle_fadd_l|]. simpl.
  apply (close_redex _ _ _ _ _ _ _ _ _ _ _ HP HV Hdv Hcv); [by apply fle_fminus_fadd|done].
Qed.

Lemma c_sel_sem W0 (s : bool) Θ Γ e a P n P1 P2 n' b' c0 t0 :
  csem W0 Θ Γ e (CTa (CEnd P) a) c0 t0 →
  pnode P = Some (n, PSel P1 P2) → pnode (if s then P2 else P1) = Some (n', b') →
  csem W0 Θ Γ (App (Konst (ksel s)) e) (CTa (CEnd (if s then P2 else P1)) (Some n')) (fadd c0 (Some 1)) t0.
Proof.
  intros Hcs HP HP' n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR (Konst (ksel s))] r; [apply fle_fadd_l|]. simpl.
  apply (sel_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HP' HV Hdv Hcv); [by apply fle_fminus_fadd|done].
Qed.

Lemma c_bra_sem W0 Θ Γ e a P n P1 P2 n1 b1 n2 b2 c0 t0 :
  csem W0 Θ Γ e (CTa (CEnd P) a) c0 t0 →
  pnode P = Some (n, PBra P1 P2) → pnode P1 = Some (n1, b1) → pnode P2 = Some (n2, b2) →
  csem W0 Θ Γ (App EBra e) (CTa (CSum (CTa (CEnd P1) (Some n1)) (CTa (CEnd P2) (Some n2))) (Some 0))
    (fadd c0 (Some 1)) t0.
Proof.
  intros Hcs HP HP1 HP2 n0 W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  bind0 [FAppR EBra] r; [apply fle_fadd_l|]. simpl.
  apply (bra_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HP1 HP2 HV Hdv Hcv); [by apply fle_fminus_fadd|done].
Qed.

Lemma c_link_sem W0 Θ Γ e P1 a1 P2 a2 a0 c0 t0 :
  csem W0 Θ Γ e (CTa (CProd (CTa (CEnd P1) a1) (CTa (CEnd P2) a2)) a0) c0 t0 → tok t0 (tlink tid) →
  csem W0 Θ Γ (App ELink e) (CTa CVal None) c0 (tseq t0 (tlink tid)).
Proof.
  intros Hcs Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r' & Hm1 & Hm2).
  bind0 [FAppR ELink] r'; [apply fle_refl|]. simpl.
  apply (link_redex _ _ _ _ _ _ _ _ _ _ _ _ _ Hv HV Hdv Hcv). by apply (meets_mono _ _ r').
Qed.

Lemma c_spawn_sem W0 Θ Γ e c' t' h a1 σ' a c0 t0 :
  csem W0 Θ Γ e (CTa (CArr c' t' h (CTa CVal a1) σ') a) c0 t0 →
  fle (Some 1) a → tok t0 (tspawn (snd t') tid) →
  csem W0 Θ Γ (App ESpawn e) (CTa CVal None) c0 (tseq t0 (tspawn (snd t') tid)).
Proof.
  intros Hcs Ha Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r' & Hm1 & Hm2).
  bind0 [FAppR ESpawn] r'; [apply fle_refl|]. simpl.
  apply (spawn_redex _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV Ha Hdv Hcv). by apply (meets_mono _ _ r').
Qed.

(** ** Rules that sequence two subterms *)

Lemma union_swap4 {Y : Type} (m1 m2 m3 m4 : gmap cend Y) :
  dom m2 ## dom m3 → (m1 ∪ m2) ∪ (m3 ∪ m4) = (m1 ∪ m3) ∪ (m2 ∪ m4).
Proof.
  intros H. rewrite <-!map_union_assoc. f_equal. rewrite !map_union_assoc. f_equal. by apply union_comm_d.
Qed.

Lemma union_lcomm {Y : Type} (m1 m2 m3 : gmap cend Y) : dom m1 ## dom m2 → m1 ∪ (m2 ∪ m3) = m2 ∪ (m1 ∪ m3).
Proof. intros H. rewrite !map_union_assoc. f_equal. by apply union_comm_d. Qed.

Lemma fle_frame3 i i2 c1 c2 c : fle (Some i) c1 → fle (Some i2) c2 → fle c (fminus i2 (fminus i (fadd c1 (fadd c2 c)))).
Proof. destruct c1, c2, c; simpl; lia. Qed.

Lemma fle_frame_max i c0 c1 c2 : fle (Some i) c0 → fle c1 (fminus i (fadd c0 (fmax c1 c2))) ∧ fle c2 (fminus i (fadd c0 (fmax c1 c2))).
Proof. destruct c0, c1, c2; simpl; lia. Qed.

Lemma emap_subst_up (g : chan → chan) γ e : emap g (subst (up γ) e) = subst (up (λ x, emap g (γ x))) (emap g e).
Proof. rewrite emap_subst. apply subst_ext. intros x. apply emap_up. Qed.

Lemma emap_subst_up2 (g : chan → chan) γ e :
  emap g (subst (up (up γ)) e) = subst (up (up (λ x, emap g (γ x)))) (emap g e).
Proof.
  rewrite emap_subst. apply subst_ext. intros x. rewrite emap_up. apply up_ext. intros y. apply emap_up.
Qed.

Lemma Vfuel_sum_inv n W σ1 σ2 a π φ v :
  Vfuel n W (CTa (CSum σ1 σ2) a) π φ v →
  (∃ u, v = Inj1 u ∧ Vfuel n W (cadd a σ1) π φ u) ∨ (∃ u, v = Inj2 u ∧ Vfuel n W (cadd a σ2) π φ u).
Proof. rewrite Vfuel_eq. destruct v; simpl; try done; intros H; [left|right]; exists v; by rewrite Vfuel_eq. Qed.

Lemma Vfuel_unit_inv n W a π φ v : Vfuel n W (CTa CVal a) π φ v → v = EUnit ∧ π = ∅.
Proof. rewrite Vfuel_eq. destruct v; simpl; intros [H1 H2]; done. Qed.

(** The split of the environment for a rule over two subterms. *)
Ltac split_env :=
  lazymatch goal with
  | HsT : thsplit ?Θ _ _, HT : thsem _ _ ?Θ _ _ _, HsG : csplit ?Γ _ _, HG : gsem _ _ ?Γ _ _ _ |- _ =>
      destruct (thsem_split _ _ _ _ _ _ _ _ HsT HT) as (πΘ1 & πΘ2 & -> & HdT & HT1 & HT2);
      destruct (gsem_split _ _ _ _ _ _ _ _ HsG HG) as (πΓ1 & πΓ2 & -> & HdG & HG1 & HG2);
      rewrite union_swap4 in * by (rewrite !dom_union_L in *; set_solver)
  end.

Lemma c_app_sem W0 Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 c t h σ1 σ2 a1 c1 t1 c2 t2 :
  thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
  csem W0 Θ1 Γ1 e1 (CTa (CArr c t h σ1 σ2) a1) c1 t1 →
  cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
  csem W0 Θ2' Γ2' e2 σ1 c2 t2 →
  fle c2 a1 → tok t2 t → tok t1 (tseq t2 t) →
  csem W0 Θ Γ (App e1 e2) σ2 (fadd c1 (fadd c2 c)) (tseq t1 (tseq t2 t)).
Proof.
  intros HsT HsG Hc1 HaT HaG Hc2 Ha Hok2 Hok1 n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok1 Hm) as (r1 & Hm1 & Hm2).
  destruct (tseq_split _ _ _ _ Hok2 Hm2) as (r2 & Hm21 & Hm22).
  split_env.
  change (subst γ (emap g (App e1 e2))) with (fill_frame ((λ γ g, FAppL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  apply (sem_bind1 W0 Θ1 Γ1 e1 (CTa (CArr c t h σ1 σ2) a1) c1 t1 Θ2 Θ2' Γ2 Γ2' (λ γ g, FAppL (subst γ (emap g e2))) σ2 r _ n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst, emap_emap|done|done|done|done|apply fle_fadd_l|done|done|done|done|done
    |rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver
    |done|done|done|].
  intros j W' g' γ' πΘ' πΓ' φ' i v πv tk' Hj Hb' Hi Hv Hr HT' HG' HV Hd' Hdv Hdφ' Hc'. simpl.
  rewrite (union_comm_d πv) in Hdφ', Hc' |- * by done.
  change (App v (subst γ' (emap g' e2))) with (fill_frame (FAppR v) (subst γ' (emap g' e2))).
  apply (sem_bind2 W0 Θ2' Γ2' e2 σ1 c2 t2 (CTa (CArr c t h σ1 σ2) a1) (CTa (CArr c t h σ1 σ2) (fsub a1 c2)) FAppR σ2 r (fminus i (fadd c1 (fadd c2 c))) j W' g' γ' πΘ' πΓ' v πv φ' tk' r2);
    [done|intros v0 Hv0; simpl; by rewrite Hv0|done| | |done|done|done|done|done|done|set_solver|done|done|by apply (meets_mono _ _ r1)|].
  { split; [by constructor|right; constructor]. }
  { eapply fle_trans; [apply (fle_fadd_l c2 c)|by apply fle_fminus_fadd]. }
  intros j2 W2 v' πv' v2 π2 φ2 i2 tk2 Hj2 Hb2 Hi2 Hv2 Hr2 Hvv' HV' HV2 Hd2 Hdφ2 Hc2'. simpl.
  rewrite (union_dom_disj π2 πv' φ2 Hdφ2).
  apply (app_redex j2 W2 c t h σ1 σ2 (fsub a1 c2)); [done|done|done|set_solver|by eapply dom_mres_of_r|by eapply dom_mres_of
    |by apply (fcap_ext_part_r W2 π2)|by apply (fcap_ext_part W2 π2 πv')|by apply (meets_mono _ _ r2)|].
  rewrite fminus_fminus. pose proof (fle_frame3 i i2 c1 c2 c Hi Hi2) as H. by rewrite fminus_fminus in H.
Qed.

Lemma c_pair_sem W0 Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 σ1 σ1' σ2 c1 t1 c2 t2 :
  thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
  csem W0 Θ1 Γ1 e1 σ1 c1 t1 →
  cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
  csem W0 Θ2' Γ2' e2 σ2 c2 t2 →
  cagex c2 σ1 σ1' → tok t1 t2 →
  csem W0 Θ Γ (Pair e1 e2) (CTa (CProd σ1' σ2) (Some 0)) (fadd c1 c2) (tseq t1 t2).
Proof.
  intros HsT HsG Hc1 HaT HaG Hc2 Hs Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  split_env.
  change (subst γ (emap g (Pair e1 e2))) with (fill_frame ((λ γ g, FPairL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  apply (sem_bind1 W0 Θ1 Γ1 e1 σ1 c1 t1 Θ2 Θ2' Γ2 Γ2' (λ γ g, FPairL (subst γ (emap g e2))) _ r _ n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst, emap_emap|done|done|done|done|apply fle_fadd_l|done|done|done|done|done
    |rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver
    |done|done|done|].
  intros j W' g' γ' πΘ' πΓ' φ' i v πv tk' Hj Hb' Hi Hv Hr HT' HG' HV Hd' Hdv Hdφ' Hc'. simpl.
  rewrite (union_comm_d πv) in Hdφ', Hc' |- * by done.
  change (Pair v (subst γ' (emap g' e2))) with (fill_frame (FPairR v) (subst γ' (emap g' e2))).
  apply (sem_bind2 W0 Θ2' Γ2' e2 σ2 c2 t2 σ1 σ1' FPairR (CTa (CProd σ1' σ2) (Some 0)) r (fminus i (fadd c1 c2)) j W' g' γ' πΘ' πΓ' v πv φ' tk' r);
    [done|intros v0 Hv0; simpl; by rewrite Hv0|done|done| |done|done|done|done|done|done|set_solver|done|done
    |by apply (meets_mono _ _ r1)|].
  { by apply fle_fminus_fadd. }
  intros j2 W2 v' πv' v2 π2 φ2 i2 tk2 Hj2 Hb2 Hi2 Hv2 Hr2 Hvv' HV' HV2 Hd2 Hdφ2 Hc2'. simpl.
  rewrite (union_comm_d π2 πv') in Hc2' |- * by done.
  apply FuelE_val; [simpl; by rewrite Hvv', Hv2|done|done|].
  rewrite (union_dom_disj πv' π2 φ2) by (rewrite Hdφ2, !dom_union_L; set_solver).
  apply Vfuel_pair; [set_solver|by apply (dom_mres_of φ2 πv' π2); rewrite Hdφ2, !dom_union_L; set_solver
    |by apply (dom_mres_of_r φ2 πv' π2); rewrite Hdφ2, !dom_union_L; set_solver|by rewrite cadd_0|by rewrite cadd_0].
Qed.

Lemma c_letu_sem W0 Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 a σ c1 t1 c2 t2 :
  thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
  csem W0 Θ1 Γ1 e1 (CTa CVal a) c1 t1 →
  cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
  csem W0 Θ2' Γ2' e2 σ c2 t2 →
  tok t1 t2 →
  csem W0 Θ Γ (LetU e1 e2) σ (fadd c1 c2) (tseq t1 t2).
Proof.
  intros HsT HsG Hc1 HaT HaG Hc2 Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  split_env.
  change (subst γ (emap g (LetU e1 e2))) with (fill_frame ((λ γ g, FLetU (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  apply (sem_bind1 W0 Θ1 Γ1 e1 (CTa CVal a) c1 t1 Θ2 Θ2' Γ2 Γ2' (λ γ g, FLetU (subst γ (emap g e2))) σ r _ n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst, emap_emap|done|done|done|done|apply fle_fadd_l|done|done|done|done|done
    |rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver
    |done|done|done|].
  intros j W' g' γ' πΘ' πΓ' φ' i v πv tk' Hj Hb' Hi Hv Hr HT' HG' HV Hd' Hdv Hdφ' Hc'. simpl.
  destruct (Vfuel_unit_inv _ _ _ _ _ _ HV) as [-> ->]. rewrite map_empty_union in Hdφ', Hc' |- *.
  destruct j as [|j]; [apply FuelE_0|].
  apply (FuelE_beta j W' σ r _ φ' tk' _ [] _ (subst γ' (emap g' e2))); [by apply Forall_nil|constructor|done|].
  apply (FuelE_frame_mono _ _ _ _ _ _ _ c2); [by apply fle_fminus_fadd|].
  apply Hc2; [done|apply (thsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]|apply (gsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]|done|done|done|].
  by apply (meets_mono _ _ r1).
Qed.

Lemma c_letp_sem W0 Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 σa σb a σ c1 t1 c2 t2 :
  thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
  csem W0 Θ1 Γ1 e1 (CTa (CProd σa σb) a) c1 t1 →
  cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
  csem W0 Θ2' (Some (cadd a σb) :: Some (cadd a σa) :: Γ2') e2 σ c2 t2 →
  tok t1 t2 →
  csem W0 Θ Γ (LetP e1 e2) σ (fadd c1 c2) (tseq t1 t2).
Proof.
  intros HsT HsG Hc1 HaT HaG Hc2 Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  split_env.
  change (subst γ (emap g (LetP e1 e2))) with
    (fill_frame ((λ γ g, FLetP (subst (up (up γ)) (emap g e2))) γ g) (subst γ (emap g e1))).
  apply (sem_bind1 W0 Θ1 Γ1 e1 (CTa (CProd σa σb) a) c1 t1 Θ2 Θ2' Γ2 Γ2' (λ γ g, FLetP (subst (up (up γ)) (emap g e2))) σ r _ n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_up2, emap_emap|done|done|done|done|apply fle_fadd_l|done|done|done|done|done
    |rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver
    |done|done|done|].
  intros j W' g' γ' πΘ' πΓ' φ' i v πv tk' Hj Hb' Hi Hv Hr HT' HG' HV Hd' Hdv Hdφ' Hc'. simpl.
  destruct (Vfuel_pair_inv _ _ _ _ _ _ _ _ HV) as (u & w & πu & πw & -> & -> & Huw & HVu & HVw).
  simpl in Hv. assert (is_val u = true ∧ is_val w = true) as [Hu Hw] by (destruct (is_val u), (is_val w); done).
  destruct j as [|j]; [apply FuelE_0|].
  apply (FuelE_beta j W' σ r _ φ' tk' _ [] _ (subst2 u w (subst (up (up γ')) (emap g' e2))));
    [by apply Forall_nil|constructor; by rewrite ?Hu, ?Hw|done|].
  rewrite subst2_subst. rewrite dom_union_L in Hdv.
  assert (Heq : (πu ∪ πw) ∪ (πΘ' ∪ πΓ') = πΘ' ∪ (πw ∪ (πu ∪ πΓ'))).
  { rewrite (union_lcomm (πu ∪ πw) πΘ') by (rewrite dom_union_L; set_solver). f_equal.
    rewrite (union_comm_d πu πw) by done. by rewrite map_union_assoc. }
  rewrite Heq in Hdφ', Hc' |- *.
  apply (FuelE_frame_mono _ _ _ _ _ _ _ c2); [by apply fle_fminus_fadd|].
  apply Hc2; [done|apply (thsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]| |rewrite !dom_union_L; set_solver|done|done|by apply (meets_mono _ _ r1)].
  exists πw, (πu ∪ πΓ'). split_and!; [done|rewrite dom_union_L; set_solver|done| |].
  - apply (Vfuel_down _ (S j)); [lia|]. rewrite (mres_mres (dom πw) (dom (πu ∪ πw))) in HVw by (rewrite dom_union_L; set_solver).
    done.
  - exists πu, πΓ'. split_and!; [done|set_solver|done| |apply (gsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]].
    apply (Vfuel_down _ (S j)); [lia|]. rewrite (mres_mres (dom πu) (dom (πu ∪ πw))) in HVu by (rewrite dom_union_L; set_solver).
    done.
Qed.

Lemma c_case_sem W0 Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e e1 e2 σa σb a σ c0 t0 c1 t1 c2 t2 :
  thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
  csem W0 Θ1 Γ1 e (CTa (CSum σa σb) a) c0 t0 →
  cage_th c0 Θ2 Θ2' → cage_env c0 Γ2 Γ2' →
  csem W0 Θ2' (Some (cadd a σa) :: Γ2') e1 σ c1 t1 →
  csem W0 Θ2' (Some (cadd a σb) :: Γ2') e2 σ c2 t2 →
  tok t0 (tmax t1 t2) →
  csem W0 Θ Γ (Case e e1 e2) σ (fadd c0 (fmax c1 c2)) (tseq t0 (tmax t1 t2)).
Proof.
  intros HsT HsG Hc0 HaT HaG Hc1 Hc2 Hok n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (tseq_split _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2). destruct (meets_tmax _ _ _ _ Hm2) as [Hm21 Hm22].
  split_env.
  change (subst γ (emap g (Case e e1 e2))) with
    (fill_frame ((λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) γ g) (subst γ (emap g e))).
  apply (sem_bind1 W0 Θ1 Γ1 e (CTa (CSum σa σb) a) c0 t0 Θ2 Θ2' Γ2 Γ2' (λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) σ r _ n W g γ πΘ1 πΓ1 πΘ2 πΓ2 φ tk r1);
    [intros g' γ0 g0; simpl; by rewrite !emap_subst_up, !emap_emap|done|done|done|done|apply fle_fadd_l|done|done|done|done|done
    |rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver|rewrite !dom_union_L in *; set_solver
    |done|done|done|].
  intros j W' g' γ' πΘ' πΓ' φ' i v πv tk' Hj Hb' Hi Hv Hr HT' HG' HV Hd' Hdv Hdφ' Hc'. simpl.
  destruct (fle_frame_max i c0 c1 c2 Hi) as [Hf1 Hf2].
  destruct j as [|j]; [apply FuelE_0|].
  rewrite (union_lcomm πv πΘ') in Hdφ', Hc' |- * by (rewrite dom_union_L in Hdv; set_solver).
  assert (Hgs : ∀ σ0 u, is_val u = true → Vfuel (S j) W' σ0 πv (mres (dom πv) φ') u →
     gsem j W' (Some σ0 :: Γ2') (u .: γ') (πv ∪ πΓ') φ').
  { intros σ0 u Hu HVu. exists πv, πΓ'. split_and!; [done|rewrite dom_union_L in Hdv; set_solver|done| |apply (gsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]].
    apply (Vfuel_down _ (S j)); [lia|done]. }
  destruct (Vfuel_sum_inv _ _ _ _ _ _ _ _ HV) as [(u & -> & HVu)|(u & -> & HVu)]; simpl in Hv.
  - apply (FuelE_beta j W' σ r _ φ' tk' _ [] _ (subst1 u (subst (up γ') (emap g' e1)))); [by apply Forall_nil|apply HeadCase1; by rewrite Hv|done|].
    rewrite subst1_subst. apply (FuelE_frame_mono _ _ _ _ _ _ _ c1); [done|].
    apply Hc1; [done|apply (thsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]|by apply Hgs|rewrite dom_union_L in *; set_solver|done|done
               |by apply (meets_mono _ _ r1)].
  - apply (FuelE_beta j W' σ r _ φ' tk' _ [] _ (subst1 u (subst (up γ') (emap g' e2)))); [by apply Forall_nil|apply HeadCase2; by rewrite Hv|done|].
    rewrite subst1_subst. apply (FuelE_frame_mono _ _ _ _ _ _ _ c2); [done|].
    apply Hc2; [done|apply (thsem_mono _ (S j) W' W'); [lia|apply wbext_refl|done]|by apply Hgs|rewrite dom_union_L in *; set_solver|done|done
               |by apply (meets_mono _ _ r1)].
Qed.

(** ** Closures and boxes: the map of the value is its ends *)

(** The syntactic facts a derivation gives about its term: its ends are
    those of Θ, its free variables have entries, and every entry that
    may hold an end occurs. *)
Definition cfacts (Θ : cthe) (Γ : cenv) (e : expr) : Prop :=
  fends e = dom Θ ∧ (∀ x, freevar x e → ∃ σ, Γ !! x = Some (Some σ)) ∧
  (∀ x σ, Γ !! x = Some (Some σ) → ¬ cfree (cta_ty σ) → freevar x e).

Lemma freevar_emap (g : chan → chan) e : ∀ x, freevar x (emap g e) ↔ freevar x e.
Proof. induction e; intros y; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; done. Qed.

Lemma upP_of (P Q : nat → Prop) : (∀ x, Q (S x) → P x) → ∀ x, Q x → upP P x.
Proof. intros H [|x] Hx; simpl; auto. Qed.

Lemma allfv_of_freevar e : ∀ (P : nat → Prop), (∀ x, freevar x e → P x) → allfv P e.
Proof.
  induction e; intros P H; simpl in *.
  - by apply H.
  - done.
  - done.
  - done.
  - done.
  - apply IHe. apply (upP_of _ (λ y, freevar y e)). intros x Hx. by apply H.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1; intros x Hx; apply H; tauto|].
    apply IHe2. apply (upP_of _ (λ y, freevar y e2)). apply (upP_of _ (λ y, freevar (S y) e2)).
    intros x Hx. apply H. tauto.
  - by apply IHe.
  - by apply IHe.
  - split_and!; [apply IHe1; intros x Hx; apply H; tauto| |].
    + apply IHe2. apply (upP_of _ (λ y, freevar y e2)). intros x Hx. apply H. tauto.
    + apply IHe3. apply (upP_of _ (λ y, freevar y e3)). intros x Hx. apply H. tauto.
  - apply IHe. apply (upP_of _ (λ y, freevar y e)). intros x Hx. by apply H.
Qed.

Lemma fends_subst_eq e γ (D : gset cend) :
  (∀ x, freevar x e → fends (γ x) ⊆ D) → (∀ o, o ∈ D → ∃ x, freevar x e ∧ o ∈ fends (γ x)) →
  fends (subst γ e) = fends e ∪ D.
Proof.
  intros H1 H2. apply set_eq. intros o. split.
  - intros Ho. by apply (fends_subst e γ D (allfv_of_freevar e _ H1)).
  - intros [Ho|Ho]%elem_of_union; [by apply fends_subst_super|].
    destruct (H2 o Ho) as (x & Hx & Ho'). by apply (fends_subst_free e x γ).
Qed.

Lemma csem_dom n W Θ Γ e (g : chan → chan) γ πΘ πΓ φ :
  cfacts Θ Γ e → (∀ x σ, Γ !! x = Some (Some σ) → cheld (cta_ty σ)) →
  thsem n W Θ g πΘ φ → gsem n W Γ γ πΓ φ → fends (subst γ (emap g e)) = dom (πΘ ∪ πΓ).
Proof.
  intros (Hf & Hfv & Hnf) Hh HT HG. destruct (gsem_ends _ _ _ _ _ _ Hh HG) as (A & B & _).
  rewrite dom_union_L, (thsem_dom _ _ _ _ _ _ HT), <-Hf, <-fends_emap.
  apply fends_subst_eq.
  - intros x Hx. apply freevar_emap in Hx. destruct (Hfv x Hx) as [σ Hσ]. exact (A x σ Hσ).
  - intros o Ho. destruct (B o Ho) as (x & σ & Hx & Hn & Ho'). exists x. split; [|done].
    apply freevar_emap. by apply (Hnf x σ).
Qed.

(** The ends of Θ, all of them held by values of types without [CAny]. *)
Lemma thsem_fpts n W Θ (g : chan → chan) π φ :
  (∀ o σ, Θ !! o = Some σ → cheld (cta_ty σ)) → thsem n W Θ g π φ → fpts W π.
Proof.
  intros Hh HT o' k Hk. destruct (thsem_point _ _ _ _ _ _ _ HT ltac:(by eapply elem_of_dom_2)) as (o & σ & x & -> & Hσ & Hx & HV).
  rewrite Hk in Hx. injection Hx as <-. destruct σ as [τ a].
  destruct (Vfuel_held _ _ _ _ _ _ _ (Hh o _ Hσ) HV) as (_ & P & _). apply (P (tkey g o)). by rewrite lookup_singleton_eq.
Qed.

Lemma fpts_union W π1 π2 : fpts W π1 → fpts W π2 → fpts W (π1 ∪ π2).
Proof. intros H1 H2 o k Ho. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [by apply (H1 o)|by apply (H2 o)]. Qed.

Lemma Vfuel_lam_intro n W c t h σ1 σ2 a π φ eb :
  dom π = fends (Lam eb) → fpts W π → farr FuelE Vfuel n W c t h σ1 σ2 a π φ (λ v, subst1 v eb) →
  Vfuel n W (CTa (CArr c t h σ1 σ2) a) π φ (Lam eb).
Proof. intros H1 H2 H3. apply Vfuel_eq. simpl. by split_and!. Qed.

Lemma c_abs_sem W0 Θ Θh Γ Γh e c t h a σ1 σ2 :
  cfacts Θ Γ (Lam e) → ccap_th h a Θ Θh → ccap_env h a Γ Γh →
  csem W0 Θh (Some σ1 :: Γh) e σ2 c t →
  csem W0 Θ Γ (Lam e) (CTa (CArr c t h σ1 σ2) a) (Some 0) tid.
Proof.
  intros Hcf HcT HcG Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  assert (HhG : ∀ x σ, Γ !! x = Some (Some σ) → cheld (cta_ty σ)).
  { intros x σ Hx. destruct (ccap_env_lookup _ _ _ _ _ _ HcG Hx) as (σ' & _ & Hs). exact (ccap_cheld _ _ _ _ Hs). }
  assert (HhT : ∀ o σ, Θ !! o = Some σ → cheld (cta_ty σ)).
  { intros o σ Ho. destruct (ccap_th_lookup _ _ _ _ _ _ HcT Ho) as (σ' & _ & Hs). exact (ccap_cheld _ _ _ _ Hs). }
  apply sem_val; [done|done|done|]. cbn [emap subst].
  apply Vfuel_lam_intro.
  - symmetry. exact (csem_dom n W Θ Γ (Lam e) g γ πΘ πΓ φ Hcf HhG HT HG).
  - apply fpts_union; [exact (thsem_fpts n W Θ g πΘ φ HhT HT)|exact (proj2 (proj2 (gsem_ends _ _ _ _ _ _ HhG HG)))].
  - split.
    + intros o f Hf. assert (Ho : o ∈ dom (πΘ ∪ πΓ)) by (rewrite <-Hdφ; by eapply elem_of_dom_2).
      rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho];
        [exact (thsem_ccap_above _ _ _ _ _ _ _ _ _ HcT HT o f Ho Hf)|exact (gsem_ccap_above _ _ _ _ _ _ _ _ _ HcG HG o f Ho Hf)].
    + intros W' j φ' v πa φa Hb' Hj Hdφ' Hc' Hh' Hda (Hva & Hdfa & Hcfa) HVa r0 tk0 Hm0.
      rewrite subst1_subst.
      rewrite dom_union_L in Hda.
      assert (Heq : (πΘ ∪ πΓ) ∪ πa = πΘ ∪ (πa ∪ πΓ)).
      { rewrite <-map_union_assoc. f_equal. apply union_comm_d. set_solver. }
      rewrite Heq.
      assert (Hag : ∀ o, o ∈ dom (πΘ ∪ πΓ) → (φ' ∪ φa) !! o = φ' !! o).
      { intros o Ho. apply lookup_union_l. apply not_elem_of_dom. rewrite Hdfa. rewrite dom_union_L in Ho. set_solver. }
      assert (Hhm : ∀ o f, o ∈ dom (πΘ ∪ πΓ) → (φ' ∪ φa) !! o = Some f → fle (Some h) f).
      { intros o f Ho Hf. rewrite Hag in Hf by done. by apply (Hh' o). }
      apply Hcs; [by eapply wbext_trans| | |rewrite dom_union_L; set_solver| | |done].
      * apply (thsem_ccap _ _ h a Θ _ _ _ φ); [done| |rewrite dom_union_L, Hdφ', dom_union_L; set_solver|].
        { intros o f Ho. apply Hhm. rewrite dom_union_L. set_solver. }
        apply (thsem_mono _ n W W'); [lia|done|done].
      * exists πa, πΓ. split_and!; [done|set_solver|done| |].
        { rewrite (mres_disj_r φ' φa πa) by (done || (rewrite Hdφ', dom_union_L; set_solver)). done. }
        apply (gsem_ccap _ _ h a Γ _ _ _ φ); [done| |rewrite dom_union_L, Hdφ', dom_union_L; set_solver|].
        { intros o f Ho. apply Hhm. rewrite dom_union_L. set_solver. }
        apply (gsem_mono _ n W W'); [lia|done|done].
      * rewrite !dom_union_L, Hdφ', Hdfa, dom_union_L. set_solver.
      * rewrite <-Heq. apply fcap_ext_union; [done|done|rewrite dom_union_L; set_solver].
Qed.

Lemma c_box_sem W0 Γ e c t σ :
  cfacts ∅ Γ (EBox e) → cunlenv Γ → csem W0 ∅ (Some (CTa (CBox c t σ) None) :: Γ) e σ c t →
  csem W0 ∅ Γ (EBox e) (CTa (CBox c t σ) None) (Some 0) tid.
Proof.
  intros Hcf Hu Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  assert (HhG : ∀ x σ0, Γ !! x = Some (Some σ0) → cheld (cta_ty σ0)).
  { intros x σ0 Hx. apply cfree_cheld. clear -Hu Hx. revert x Hx. induction Γ as [|[σ1|] Γ IH]; intros [|x] Hx; simpl in *; try done.
    - injection Hx as <-. apply Hu. - apply (IH (proj2 Hu) x Hx). - apply (IH (proj2 Hu) x Hx). }
  pose proof (csem_dom n W ∅ Γ (EBox e) g γ πΘ πΓ φ Hcf HhG HT HG) as Hfe.
  pose proof (thsem_empty _ _ _ _ _ HT) as ->. pose proof (gsem_unl _ _ _ _ _ _ Hu HG) as ->.
  rewrite map_empty_union, dom_empty_L in *.
  apply dom_empty_inv_L in Hdφ as ->. cbn [emap subst] in Hfe |- *.
  set (eb := subst (up γ) (emap g e)). fold eb in Hfe.
  apply sem_val; [done|done|done|].
  assert (Hlob : ∀ m, m ≤ n → ∀ W', wbext W W' → Vfuel m W' (CTa (CBox c t σ) None) ∅ ∅ (EBox eb)).
  { induction m as [m IH] using lt_wf_ind. intros Hmn W' Hb'. apply Vfuel_eq. simpl. split_and!; [done|done|].
    intros W'' j r0 tk0 Hb'' Hj Hm0. unfold eb. rewrite subst1_subst.
    rewrite <-(map_empty_union (∅ : gmap cend point)).
    apply Hcs; [by do 2 (eapply wbext_trans)|apply thsem_nil| |set_solver|by rewrite map_empty_union|
                rewrite map_empty_union; apply fcap_ext_empty|done].
    exists ∅, ∅. rewrite map_empty_union. split_and!; [done|set_solver|done| |].
    - rewrite dom_empty_L. apply (IH j); [done|lia|]. by eapply wbext_trans.
    - apply (gsem_mono _ n W W''); [lia|by eapply wbext_trans|done]. }
  apply (Hlob n); [done|apply wbext_refl].
Qed.

Lemma c_spawnlam_sem W0 Θ Θ' Γ Γ' e a1 σ' c' t' :
  cfacts Θ Γ (Lam e) → cage_th (Some 1) Θ Θ' → cage_env (Some 1) Γ Γ' →
  csem W0 Θ' (Some (CTa CVal a1) :: Γ') e σ' c' t' →
  csem W0 Θ Γ (App ESpawn (Lam e)) (CTa CVal None) (Some 0) (tspawn (snd t') tid).
Proof.
  intros Hcf HaT HaG Hcs n W g γ πΘ πΓ φ Hb HT HG Hd Hdφ Hc r tk Hm.
  destruct (spawn_split _ _ _ _ Hm) as [Hch Hpar].
  assert (HhG : ∀ x σ, Γ !! x = Some (Some σ) → cheld (cta_ty σ)).
  { intros x σ Hx. destruct (cage_env_lookup _ _ _ _ _ HaG Hx) as (σ0 & _ & Hs). exact (cagex_cheld _ _ _ Hs ltac:(done)). }
  pose proof (csem_dom n W Θ Γ (Lam e) g γ πΘ πΓ φ Hcf HhG HT HG) as Hdom. cbn [emap subst] in Hdom.
  assert (Hab : ∀ o f, φ !! o = Some f → fle (Some 1) f).
  { intros o f Hf. assert (Ho : o ∈ dom (πΘ ∪ πΓ)) by (rewrite <-Hdφ; by eapply elem_of_dom_2).
    rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho];
      [exact (thsem_above _ _ _ _ _ _ _ _ HaT HT o f Ho Hf)|exact (gsem_above _ _ _ _ _ _ _ _ HaG HG o f Ho Hf)]. }
  destruct n as [|n]; [apply FuelE_0|]. cbn [emap subst].
  apply FuelE_redex; [done|done|]. intros W' g' π' φ' Hb' Hk R1 R2.
  assert (Hdφ' : dom φ' = dom π') by (eapply renk_dom_eq; [exact Hdφ|exact R1|exact R2]).
  assert (Hc' : fcap_ext W' π' φ') by (apply (fcap_ext_wbext W); [done|]; eapply fcap_ext_rename; eauto).
  assert (Hdom' : fends (emap g' (Lam (subst (up γ) (emap g e)))) = dom π').
  { rewrite fends_emap, Hdom. symmetry. apply (renk_dom _ _ _ R1). }
  cbn [emap] in Hdom' |- *. rewrite emap_subst_up, emap_emap in Hdom' |- *.
  set (w := Lam (subst (up (λ x, emap g' (γ x))) (emap (g' ∘ g) e))). fold w in Hdom'.
  destruct (renk_union_split g' πΘ πΓ π' Hk Hd R1) as (πΘ' & πΓ' & Hπ' & R1T & R1G & Hd').
  split.
  - intros s0 e' o Hst Ho. apply tstep_app_val in Hst; [|done|done]. inversion Hst.
  - intros α e' Hst. apply tstep_app_val in Hst; [|done|done].
    assert (α = LSpawn w ∧ e' = EUnit) as [-> ->] by (inversion Hst; done).
    unfold Fobl; cbv beta iota. split_and!.
    + by rewrite Hdom'.
    + intros o m _ Hom. destruct (proj2 R2 o _ Hom) as (o0 & -> & Ho0). specialize (Hab o0 _ Ho0). simpl in Hab. lia.
    + unfold fchild. cbn [fst snd]. rewrite Hdom', mres_dom, (mres_dom_eq π' φ' Hdφ').
      destruct n as [|n0]; [apply FuelE_0|].
      apply (FuelE_beta n0 W' _ 0 π' (ftick <$> φ') (Nat.div2 (S tk)) None [] _
        (subst1 EUnit (subst (up (λ x, emap g' (γ x))) (emap (g' ∘ g) e)))); [by apply Forall_nil|by apply HeadApp| |].
      { apply (fcap_ext_fmap _ _ _ ftick); [apply ftick_le|done]. }
      rewrite subst1_subst.
      apply (FuelE_mono _ _ σ' cany 0 0 _ _ (Nat.div2 (S tk)) (Nat.div2 (S tk)) c' None); [apply cst_any|lia|lia|apply fle_None|].
      assert (Hφt : ftick <$> φ' = fminus 1 <$> φ') by (apply map_fmap_ext; intros; apply ftick_fminus).
      rewrite Hπ' in Hdφ', Hc' |- *. rewrite Hφt.
      apply Hcs; [by eapply wbext_trans| | |done|by rewrite dom_fmap_L|apply (fcap_ext_fmap _ _ _ (fminus 1)); [apply fminus_le|done]|by apply meets_zero].
      * apply (thsem_mono _ (S (S n0)) W' W'); [lia|apply wbext_refl|].
        apply (thsem_age _ _ (Some 1) 1 Θ); [done|apply fle_refl|].
        apply (thsem_mono _ (S (S n0)) W W'); [lia|done|].
        apply (thsem_rename _ _ Θ g g' (πΘ ∪ πΓ) πΘ πΘ' φ φ'); [done|by rewrite Hdφ|rewrite dom_union_L; set_solver|done|done|done].
      * exists ∅, πΓ'. rewrite map_empty_union. split_and!; [done|set_solver|done|rewrite dom_empty_L; apply Vfuel_unit|].
        apply (gsem_mono _ (S (S n0)) W' W'); [lia|apply wbext_refl|].
        apply (gsem_age _ _ (Some 1) 1 Γ); [done|apply fle_refl|].
        apply (gsem_mono _ (S (S n0)) W W'); [lia|done|].
        apply (gsem_rename _ _ Γ γ g' (πΘ ∪ πΓ) πΓ πΓ' φ φ'); [done|by rewrite Hdφ|rewrite dom_union_L; set_solver|done|done|done].
    + unfold fupd. cbn [fst snd]. rewrite (mrem_all _ π') by (by rewrite Hdom').
      rewrite (mrem_all _ φ') by (by rewrite Hdφ', Hdom').
      apply sem_val; [done|done|apply fcap_ext_empty|apply Vfuel_unit].
Qed.
