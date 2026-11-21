(** * The shared constants of P-Connect are not the roots of the cut

    P-Connect asks [swf (W1|S ⊔ W2|S)] at S = [swshared W1 W2], the
    constants both worlds hold. The repair (a) of the open item in
    docs/redesign/pending.md asked whether S ⊆ the roots of the points of
    the cut Σ_C in every derivation. It fails, and dropping constants no
    derivation needs does not save it.

    Each component closes two channels of its own in one order,

      P(c, d) = (cl c⁺; cl d⁺) ∥ (cl c⁻; cl d⁻),   c at 0, d at 0·0.

    The first close of each thread waits on the other channel, so E-Close
    asks 0 ≺ (0·0)‾ and 0‾ ≺ 0·0. Both are facts of the world W0 with the
    one constant 0. [comp_typed] types P(c, d) over the empty interface at
    W0 ⊔ W0. Then P(c, d) ∥ P(e, f) types by P-Connect over the empty cut
    ([shared_not_cut]), and 0 is a shared constant although the cut has no
    point. Any well-formed world that derives the first fact holds 0
    ([fact_needs_zero]), so the constant is private to each component and
    used by each. Two components may pick the same private constant,
    because nothing in [ptyped] keeps them apart. *)

From Stdlib Require Import Wf_nat.
From GV Require Import static.Typing.

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

Lemma cl2_typed o1 o2 x y :
  o1 ≠ o2 → sw_facts W0 (FLt x y‾) →
  typed W0 None (tenv2 o1 o2 x y) hc_empty [] (∅, None) (cl2 o1 o2) TUnit
    (fadd (fadd (Some 0) (Some 1)) (fadd (Some 0) (Some 1))).
Proof.
  intros Hne Hf. unfold cl2, tenv2.
  eapply (e_letu W0 None _ {[o1 := TE SEnd x None None]} {[o2 := TE SEnd y None None]}
            {[o2 := TE SEnd y None None]} _ [] [] []).
  - split; [by apply map_disjoint_singleton_l, lookup_singleton_ne|done].
  - apply lsplit_nil.
  - eapply (e_close _ _ _ _ _ _ _ SEnd); [reflexivity| |].
    + simpl. split_and!; [|done|done]. intros z Hz.
      rewrite (left_id_L ∅ (∪)), (right_id_L ∅ (∪)) in Hz.
      apply elem_of_tenv_heads in Hz as (o & e & Ho & ->).
      apply lookup_singleton_Some in Ho as [_ <-]. simpl. by apply sl_w, sw_lt_fact.
    + apply e_chan. intros ? Hin. inversion Hin.
  - intros o. destruct (decide (o = o2)) as [->|Ho].
    + rewrite lookup_singleton_eq. split_and!; done.
    + by rewrite lookup_singleton_ne.
  - apply lage_nil.
  - eapply (e_close _ _ _ _ _ _ _ SEnd); [reflexivity|simpl; split_and!; [set_solver|done|done]|].
    apply e_chan. intros ? Hin. inversion Hin.
Qed.

Definition senv2 (o1 o2 : cend) (x y : point) : senv :=
  {[o1 := (SEnd, x)]} ∪ {[o2 := (SEnd, y)]}.

Lemma cl2_term o1 o2 x y :
  o1 ≠ o2 → (o1‾)%cend ≠ o2 → sw_facts W0 (FLt x y‾) →
  ptyped None W0 (senv2 o1 o2 x y) (∅, {[+ cl2 o1 o2 +]}) TUnit.
Proof.
  intros Hne Hd Hf.
  apply (p_term None W0 _ ∅ ∅ _ TUnit (fadd (fadd (Some 0) (Some 1)) (fadd (Some 0) (Some 1)))).
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
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of, senv2. rewrite map_fmap_union, !map_fmap_singleton.
    by apply cl2_typed.
  - apply W0_ok.
Qed.

(** ** One component P(c, d), over the empty interface *)

Definition comp (c d : chan) : gmultiset expr :=
  {[+ cl2 (c⁺)%cend (d⁺)%cend +]} ⊎ {[+ cl2 (c⁻)%cend (d⁻)%cend +]}.

Lemma chans_of_empty : chans_of ∅ = ∅.
Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

Lemma comp_typed c d :
  c ≠ d → ptyped None (W0 ⊔ W0) ∅ (({[c]} ∪ {[d]}), comp c d) TUnit.
Proof.
  intros Hcd.
  set (ΣC := senv2 (c⁺)%cend (d⁺)%cend p0 (p0·0)).
  assert (senv_dual ΣC = senv2 (c⁻)%cend (d⁻)%cend p0‾ (p0·0)‾) as Ed.
  { unfold senv_dual, ΣC, senv2. rewrite map_fmap_union, !map_fmap_singleton, kmap_union, !kmap_singleton.
    done. typeclasses eauto. }
  assert (chans_of ΣC = ({[c]} ∪ {[d]})) as Ec.
  { unfold chans_of, ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, set_map_union_L, !set_map_singleton_L.
    done. }
  pose proof (p_connect_join None W0 W0 ∅ ∅ ΣC ∅ ∅ {[+ cl2 (c⁺)%cend (d⁺)%cend +]}
                {[+ cl2 (c⁻)%cend (d⁻)%cend +]} TUnit) as H.
  rewrite Ec, chans_of_empty, !(left_id_L ∅ (∪)), Ed in H. unfold comp. apply H; clear H.
  - apply cl2_term; [congruence|cbn; congruence|]. by left.
  - apply cl2_term; [congruence|cbn; congruence|]. right. by rewrite pt_dual_dual.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - intros o. unfold ΣC, senv2. rewrite dom_union_L, !dom_singleton_L, !elem_of_union, !elem_of_singleton.
    intros [->| ->] [E|E]; discriminate.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply W0_wf.
  - apply W0_wf.
  - apply W00_ok.
Qed.

(** ** Two components over the empty cut share the constant 0 *)

Theorem shared_not_cut :
  ptyped None ((W0 ⊔ W0) ⊔ (W0 ⊔ W0)) ∅
    (({["c"]} ∪ {["d"]}) ∪ ({["e"]} ∪ {["f"]}) ∪ chans_of ∅, comp "c" "d" ⊎ comp "e" "f") TUnit ∧
  0 ∈ swshared (W0 ⊔ W0) (W0 ⊔ W0) ∧
  (∀ x, x ∈ dom (∅ : senv) → False).
Proof.
  split_and!; [|unfold swshared; simpl; set_solver|intros x; rewrite dom_empty_L; set_solver].
  pose proof (p_connect_join None (W0 ⊔ W0) (W0 ⊔ W0) ∅ ∅ ∅ ({["c"]} ∪ {["d"]}) ({["e"]} ∪ {["f"]})
                (comp "c" "d") (comp "e" "f") TUnit) as H.
  assert (senv_dual ∅ = ∅) as Ed by (unfold senv_dual; by rewrite fmap_empty, kmap_empty).
  rewrite Ed, chans_of_empty, !(left_id_L ∅ (∪)) in H. rewrite chans_of_empty.
  apply H; clear H.
  - by apply comp_typed.
  - by apply comp_typed.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply W00_ok.
  - apply W00_ok.
  - apply swf_meas. intros x y [[H|H]|[H|H]]; by apply W0_facts.
Qed.

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
