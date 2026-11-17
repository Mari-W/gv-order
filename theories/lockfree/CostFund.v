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
