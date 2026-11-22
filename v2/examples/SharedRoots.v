(** * Shared constants and hiding

    Two components composed at their whole worlds share every constant
    both worlds hold, S = [swshared W1 W2]. Repair (a) of the open item
    in docs/redesign/pending.md asked whether S ⊆ the roots of the
    points of the cut Σ_C in every derivation. It fails, and dropping
    constants no derivation needs does not save it. The hidden judgment
    [ptyped] (repair (b)) makes S irrelevant.

    Each component closes two channels of its own in one order,

      P(c, d) = (cl c⁺; cl d⁺) ∥ (cl c⁻; cl d⁻),   c at 0, d at 0·0.

    The first close of each thread waits on the other channel, so E-Close
    asks 0 ≺ (0·0)‾ and 0‾ ≺ 0·0. Both are facts of the world W0 with the
    one constant 0, and any well-formed world that derives the first
    fact holds 0 ([fact_needs_zero]). So the whole worlds of P(c, d) and
    P(e, f) share 0 although the empty cut between them has no point.

    With hiding the thread worlds restrict to the interface constant 0,
    and P-Connect over the cut at 0 hides 0. So P(c, d) types over the
    empty interface at a world with no constant and no fact
    ([hcomp_typed]), and P(c, d) ∥ P(e, f) composes because the two
    interface worlds are well-founded together ([shared_hidden]).

    P'(e, f) closes f first and orders 0 oppositely. The whole worlds of
    P(c, d) and P'(e, f) hold a cycle at 0 ([opposite_clash]), and with
    hiding the two compose ([opposite_compose]) to a deadlock-free
    process ([opposite_df]). *)

From Stdlib Require Import Wf_nat.
From GV Require Import static.FundamentalProc.

(** ** Well-foundedness by a measure *)

Definition pdepth (p : pname) : nat := match p with NField _ _ _ => 1 | _ => 0 end.
Definition pmeas (x : point) : nat := 2 * pt_off x + pdepth (pt_name x).

Lemma swf_meas W : (∀ x y, sw_facts W (FLt x y) → pmeas x < pmeas y) → swf W.
Proof.
  intros Hf. apply swf_iff.
  assert (∀ x y, W ⊢ₛ x ≺ y → pmeas x < pmeas y) as Hm.
  { assert (∀ x y, swstep W x y → pmeas x < pmeas y) as Hs.
    { intros x y [x' y' H|x'|x']; [by apply Hf|unfold pmeas; simpl; lia|unfold pmeas; simpl; lia]. }
    intros x y H. induction H as [x y H|x y z H _ IH]; [by apply Hs|]. specialize (Hs _ _ H). lia. }
  apply (wf_sub (ltof point pmeas)); [exact Hm|]. apply well_founded_ltof.
Qed.

(** ** The world W0 *)

Definition p0 : point := MkPt (NConst 0) true 0.

Definition W0 : sworld :=
  SWorld {[0]} (λ g, g = FLt p0 (p0·0)‾ ∨ g = FLt p0‾ (p0·0)).

Lemma W0_wf : sworld_wf W0.
Proof.
  split. intros x y [E|E]; injection E as -> ->; split; exists 0; split; try done; set_solver.
Qed.

Lemma W0_facts x y : sw_facts W0 (FLt x y) → pmeas x < pmeas y.
Proof. intros [E|E]; injection E as -> ->; unfold pmeas; simpl; lia. Qed.

Lemma W0_ok : sworld_wf W0 ∧ swf W0.
Proof. split; [apply W0_wf|apply swf_meas, W0_facts]. Qed.

Lemma W00_ok : sworld_wf (W0 ⊔ W0) ∧ swf (W0 ⊔ W0).
Proof.
  split; [by apply swjoin_wf; apply W0_wf|]. apply swf_meas. intros x y [H|H]; by apply W0_facts.
Qed.

(** ** One thread closes two ends in order *)

Definition cl2 (o1 o2 : cend) : expr := LetU (EClose (Chan o1)) (EClose (Chan o2)).

Definition tenv2 (o1 o2 : cend) (x y : point) : tenv :=
  {[o1 := TE SEnd x None None]} ∪ {[o2 := TE SEnd y None None]}.

Lemma cl2_typed W o1 o2 x y :
  o1 ≠ o2 → sw_facts W (FLt x y‾) →
  typed W None (tenv2 o1 o2 x y) hc_empty [] (∅, None) (cl2 o1 o2) TUnit
    (fadd (fadd (Some 0) (Some 1)) (fadd (Some 0) (Some 1))).
Proof.
  intros Hne Hf. unfold cl2, tenv2.
  eapply (e_letu W None _ {[o1 := TE SEnd x None None]} {[o2 := TE SEnd y None None]}
            {[o2 := TE SEnd y None None]} _ [] [] []).
  - split; [by apply map_disjoint_singleton_l, lookup_singleton_ne|done].
  - apply lsplit_nil.
  - eapply (e_close _ _ _ _ _ _ _ SEnd); [reflexivity| |].
    + simpl. split_and!; [|done]. intros z Hz.
      rewrite (left_id_L ∅ (∪)), (right_id_L ∅ (∪)) in Hz.
      apply elem_of_tenv_heads in Hz as (o & e & Ho & ->).
      apply lookup_singleton_Some in Ho as [_ <-]. simpl. by apply sl_w, sw_lt_fact.
    + apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
  - intros o. destruct (decide (o = o2)) as [->|Ho].
    + rewrite lookup_singleton_eq. split_and!; done.
    + by rewrite lookup_singleton_ne.
  - apply lage_nil.
  - eapply (e_close _ _ _ _ _ _ _ SEnd); [reflexivity|simpl; split_and!; [set_solver|done]|].
    apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
Qed.

Definition senv2 (o1 o2 : cend) (x y : point) : senv :=
  {[o1 := (SEnd, x)]} ∪ {[o2 := (SEnd, y)]}.

Lemma senv2_contr o1 o2 x y : ∀ o e, senv2 o1 o2 x y !! o = Some e → scontr e.1.
Proof.
  intros o e. unfold senv2. rewrite lookup_union_Some_raw, !lookup_singleton_Some.
  intros [[_ <-]|[_ [_ <-]]]; cbn; exact I.
Qed.

(** The premises of P-Term for one thread [cl2], in both judgments. *)
Lemma cl2_prem W o1 o2 x y :
  o1 ≠ o2 → (o1‾)%cend ≠ o2 → sw_facts W (FLt x y‾) →
  tfree TUnit ∧ (∀ o, o ∈ dom (∅ : tenv) ↔ ech o ∈ (∅ : gset chan)) ∧ chans_of (senv2 o1 o2 x y) ## ∅ ∧
  pfree (senv2 o1 o2 x y) ∧ (∀ o e, senv2 o1 o2 x y !! o = Some e → scontr e.1) ∧
  (∀ c, c ∈ (∅ : gset chan) → ∃ S x m m', tsum_ok None m m' ∧ scontr S ∧
     (∅ : tenv) !! (c⁺)%cend = Some (TE S x m m) ∧ (∅ : tenv) !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) ∧
  typed W None (tenv_of (fhalf None) (senv2 o1 o2 x y) ∪ ∅) hc_empty [] (∅, None) (cl2 o1 o2) TUnit
    (fadd (fadd (Some 0) (Some 1)) (fadd (Some 0) (Some 1))).
Proof.
  intros Hne Hd Hf. split_and!.
  - constructor.
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - intros o. unfold senv2. rewrite dom_union_L, !dom_singleton_L, !elem_of_union, !elem_of_singleton.
    assert (∀ o', (o'‾)%cend ≠ o') as Hn by (intros []; discriminate).
    intros [->| ->] [E|E].
    + by apply (Hn o1).
    + by apply Hd.
    + apply Hd. rewrite <-E. apply edual_edual.
    + by apply (Hn o2).
  - apply senv2_contr.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of, senv2. rewrite map_fmap_union, !map_fmap_singleton.
    by apply cl2_typed.
Qed.

(** ** One component P(c, d), over the empty interface *)

Definition comp (c d : chan) : gmultiset expr :=
  {[+ cl2 (c⁺)%cend (d⁺)%cend +]} ⊎ {[+ cl2 (c⁻)%cend (d⁻)%cend +]}.

Lemma chans_of_empty : chans_of ∅ = ∅.
Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

(** ** The constant is used

    The first close of [cl2 c⁺ d⁺] asks p0 ≺ (p0·0)‾ under the empty
    hypotheses. Every well-formed world that derives it holds 0, so no
    restriction of a component's world to the constants it uses removes
    0 from either side. *)

Lemma po_name x y : po x y → pt_name x = pt_name y.
Proof. induction 1 as [x y [->| ->]|x y z [->| ->] _ IH]; done. Qed.

Lemma fl_empty W x y : slt W hc_empty x y → W ⊢ₛ x ≺ y.
Proof.
  induction 1 as [x y H|x y (C & xs & Hin & _)|x y z _ IH1 _ IH2].
  - done.
  - simpl in Hin. set_solver.
  - by eapply sw_lt_trans.
Qed.

Theorem fact_needs_zero W : sworld_wf W → slt W hc_empty p0 (p0·0)‾ → 0 ∈ sw_consts W.
Proof.
  intros Hwf H. apply fl_empty in H. destruct (lt_zone W _ _ Hwf H) as [Hp|[[a [Ha Hin]] _]].
  - apply po_name in Hp. discriminate.
  - simpl in Ha. by injection Ha as ->.
Qed.

(** ** With hiding the two components share no constant

    Each thread hides its world to the constants of its interface, here
    {0}, and P-Connect over the cut at 0 hides 0 as well. So P(c, d)
    types over the empty interface at a world with no constant and no
    fact ([hcomp_typed]), and P(c, d) ∥ P(e, f) composes because the two
    interface worlds, both empty, are well-founded together
    ([shared_hidden]). *)

Lemma iface_empty_unit : iface ∅ TUnit = ∅.
Proof. unfold iface, senv_consts. rewrite map_to_list_empty. simpl. set_solver. Qed.

Lemma swrestrict_empty_facts W g : ¬ sw_facts (swrestrict W ∅) g.
Proof. destruct g as [x y]. simpl. intros (_ & (a & _ & Ha) & _). set_solver. Qed.

Lemma swrestrict_empty_ok W : sworld_wf (swrestrict W ∅) ∧ swf (swrestrict W ∅).
Proof. split; [apply swrestrict_wf|apply swf_bare, swrestrict_empty_facts]. Qed.

Lemma cl2_hterm W o1 o2 x y :
  sworld_wf W ∧ swf W → o1 ≠ o2 → (o1‾)%cend ≠ o2 → sw_facts W (FLt x y‾) →
  ptyped None (swrestrict W (iface (senv2 o1 o2 x y) TUnit)) (senv2 o1 o2 x y) (∅, {[+ cl2 o1 o2 +]}) TUnit.
Proof.
  intros HW Hne Hd Hf. destruct (cl2_prem W o1 o2 x y Hne Hd Hf) as (H1 & H2 & H3 & H4 & H4c & H5 & H6).
  apply (swf_ok_wok None) in HW. by eapply p_term.
Qed.

(** One component over its own cut ΣC, its two threads at worlds W and
    W' that order the cut. The hidden world has no constant. *)
Lemma hcomp_gen W W' (ΣC : senv) (u1 u2 : expr) Σa Σb :
  ptyped None W Σa (∅, {[+ u1 +]}) TUnit → ptyped None W' Σb (∅, {[+ u2 +]}) TUnit →
  Σa = ∅ ∪ ΣC → Σb = ∅ ∪ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  swf (W ⊔ W') →
  ptyped None (swrestrict (W ⊔ W') ∅) ∅ (chans_of ΣC, {[+ u1 +]} ⊎ {[+ u2 +]}) TUnit.
Proof.
  intros H1 H2 -> -> Hf HS. apply (swf_wok None) in HS.
  pose proof (p_connect None W W' ∅ ∅ ΣC ∅ ∅ {[+ u1 +]} {[+ u2 +]} TUnit H1 H2) as H.
  rewrite chans_of_empty, !(left_id_L ∅ (∪)), iface_empty_unit in H. apply H; clear H; try done.
  all: first [apply map_disjoint_empty_l|set_solver].
Qed.

Lemma senv_dual_senv2 o1 o2 x y : senv_dual (senv2 o1 o2 x y) = senv2 (o1‾)%cend (o2‾)%cend x‾ y‾.
Proof.
  unfold senv_dual, senv2. rewrite map_fmap_union, !map_fmap_singleton, kmap_union, !kmap_singleton. done.
  typeclasses eauto.
Qed.

Lemma hcomp_typed c d :
  c ≠ d → ∃ W, ptyped None W ∅ (({[c]} ∪ {[d]}), comp c d) TUnit ∧ sw_consts W = ∅ ∧ ∀ g, ¬ sw_facts W g.
Proof.
  intros Hcd. set (ΣC := senv2 (c⁺)%cend (d⁺)%cend p0 (p0·0)).
  assert (chans_of ΣC = ({[c]} ∪ {[d]})) as Ec.
  { unfold chans_of, ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, set_map_union_L, !set_map_singleton_L.
    done. }
  eexists. split; [|split; [|apply swrestrict_empty_facts]]; [rewrite <-Ec|simpl; apply (right_absorb_L ∅ (∩))]. unfold comp. eapply (hcomp_gen _ _ ΣC).
  - apply (cl2_hterm W0 _ _ p0 (p0·0)); [apply W0_ok|congruence|cbn; congruence|by left].
  - apply (cl2_hterm W0 _ _ p0‾ (p0·0)‾); [apply W0_ok|congruence|cbn; congruence|].
    right. by rewrite pt_dual_dual.
  - by rewrite (left_id_L ∅ (∪)).
  - rewrite (left_id_L ∅ (∪)). unfold ΣC. by rewrite senv_dual_senv2.
  - intros o. unfold ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, !elem_of_union, !elem_of_singleton.
    intros [->| ->] [E|E]; discriminate.
  - eapply swf_sub; [|apply W00_ok]. intros a b. apply join_sub; intros u v; apply swrestrict_lt.
Qed.

Theorem shared_hidden :
  ∃ W, ptyped None W ∅ (({["c"]} ∪ {["d"]}) ∪ ({["e"]} ∪ {["f"]}) ∪ chans_of ∅, comp "c" "d" ⊎ comp "e" "f") TUnit.
Proof.
  destruct (hcomp_typed "c" "d") as (W1 & H1 & _ & F1); [done|].
  destruct (hcomp_typed "e" "f") as (W2 & H2 & _ & F2); [done|].
  eexists. pose proof (p_connect None W1 W2 ∅ ∅ ∅ ({["c"]} ∪ {["d"]}) ({["e"]} ∪ {["f"]})
                (comp "c" "d") (comp "e" "f") TUnit) as H.
  assert (senv_dual ∅ = ∅) as Ed by (unfold senv_dual; by rewrite fmap_empty, kmap_empty).
  rewrite Ed, !(left_id_L ∅ (∪)) in H. apply H; clear H; try done; try set_solver.
  all: first [apply map_disjoint_empty_l|apply swf_wok, swf_bare; intros g [Hg|Hg]; [by apply (F1 g)|by apply (F2 g)]].
Qed.

(** ** Two components that order the same private constant oppositely

    P'(e, f) = (cl f⁺; cl e⁺) ∥ (cl f⁻; cl e⁻), e at 0 and f at 0·0,
    closes f first, so its world Wop holds 0·0 ≺ 0‾ and (0·0)‾ ≺ 0. The
    whole worlds of P(c, d) and P'(e, f) together hold the cycle
    0 ≺ (0·0)‾ ≺ 0 ([opposite_clash]), so the full P-Connect at these
    worlds fails. With hiding both components type at worlds with no
    constant, and P(c, d) ∥ P'(e, f) composes ([opposite_compose]) and
    is deadlock free ([opposite_df]). *)

Definition Wop : sworld :=
  SWorld {[0]} (λ g, g = FLt (p0·0) p0‾ ∨ g = FLt (p0·0)‾ p0).

Definition pmeas' (x : point) : nat := 2 * pt_off x + (1 - pdepth (pt_name x)).

Lemma swf_meas' W : (∀ x y, sw_facts W (FLt x y) → pmeas' x < pmeas' y) → swf W.
Proof.
  intros Hf. apply swf_iff.
  assert (∀ x y, W ⊢ₛ x ≺ y → pmeas' x < pmeas' y) as Hm.
  { assert (∀ x y, swstep W x y → pmeas' x < pmeas' y) as Hs.
    { intros x y [x' y' H|x'|x']; [by apply Hf|unfold pmeas'; simpl; lia|unfold pmeas'; simpl; lia]. }
    intros x y H. induction H as [x y H|x y z H _ IH]; [by apply Hs|]. specialize (Hs _ _ H). lia. }
  apply (wf_sub (ltof point pmeas')); [exact Hm|]. apply well_founded_ltof.
Qed.

Lemma Wop_ok : sworld_wf Wop ∧ swf Wop.
Proof.
  split.
  - split. intros x y [E|E]; injection E as -> ->; split; exists 0; split; try done; set_solver.
  - apply swf_meas'. intros x y [E|E]; injection E as -> ->; unfold pmeas'; simpl; lia.
Qed.

Definition comp' (e f : chan) : gmultiset expr :=
  {[+ cl2 (f⁺)%cend (e⁺)%cend +]} ⊎ {[+ cl2 (f⁻)%cend (e⁻)%cend +]}.

Lemma hcomp'_typed e f :
  e ≠ f → ∃ W, ptyped None W ∅ (({[f]} ∪ {[e]}), comp' e f) TUnit ∧ sw_consts W = ∅ ∧ ∀ g, ¬ sw_facts W g.
Proof.
  intros Hef. set (ΣC := senv2 (f⁺)%cend (e⁺)%cend (p0·0) p0).
  assert (chans_of ΣC = ({[f]} ∪ {[e]})) as Ec.
  { unfold chans_of, ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, set_map_union_L, !set_map_singleton_L.
    done. }
  eexists. split; [|split; [|apply swrestrict_empty_facts]]; [rewrite <-Ec|simpl; apply (right_absorb_L ∅ (∩))]. unfold comp'. eapply (hcomp_gen _ _ ΣC).
  - apply (cl2_hterm Wop _ _ (p0·0) p0); [apply Wop_ok|congruence|cbn; congruence|by left].
  - apply (cl2_hterm Wop _ _ (p0·0)‾ p0‾); [apply Wop_ok|congruence|cbn; congruence|].
    right. by rewrite pt_dual_dual.
  - by rewrite (left_id_L ∅ (∪)).
  - rewrite (left_id_L ∅ (∪)). unfold ΣC. by rewrite senv_dual_senv2.
  - intros o. unfold ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, !elem_of_union, !elem_of_singleton.
    intros [->| ->] [E|E]; discriminate.
  - eapply swf_sub; [|apply (swf_sub _ Wop); [|apply Wop_ok]].
    + intros a b. apply join_sub; intros u v; apply swrestrict_lt.
    + intros a b H. eapply sw_lt_facts; [|exact H]. by intros g [Hg|Hg].
Qed.

Theorem opposite_clash : ¬ sacyc ((W0 ⊔ W0) ⊔ (Wop ⊔ Wop)).
Proof.
  intros HS. apply (HS p0). eapply sw_lt_trans; apply sw_lt_fact.
  - left. left. by left.
  - right. left. by right.
Qed.

Theorem opposite_compose :
  ∃ W, ptyped None W ∅ (({["c"]} ∪ {["d"]}) ∪ ({["f"]} ∪ {["e"]}) ∪ chans_of ∅, comp "c" "d" ⊎ comp' "e" "f") TUnit.
Proof.
  destruct (hcomp_typed "c" "d") as (Wa & H1 & _ & F1); [done|].
  destruct (hcomp'_typed "e" "f") as (Wb & H2 & _ & F2); [done|].
  eexists. pose proof (p_connect None Wa Wb ∅ ∅ ∅ ({["c"]} ∪ {["d"]}) ({["f"]} ∪ {["e"]})
                (comp "c" "d") (comp' "e" "f") TUnit) as H.
  assert (senv_dual ∅ = ∅) as Ed by (unfold senv_dual; by rewrite fmap_empty, kmap_empty).
  rewrite Ed, !(left_id_L ∅ (∪)) in H. apply H; clear H; try done; try set_solver.
  all: first [apply map_disjoint_empty_l|apply swf_wok, swf_bare; intros g [Hg|Hg]; [by apply (F1 g)|by apply (F2 g)]].
Qed.

Theorem opposite_df : deadlock_free (({["c"]} ∪ {["d"]}) ∪ ({["f"]} ∪ {["e"]}) ∪ chans_of ∅, comp "c" "d" ⊎ comp' "e" "f").
Proof. destruct opposite_compose as (W & H). exact (soundness_h W _ TUnit H). Qed.
