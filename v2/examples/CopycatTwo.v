(** * Two-sided identity expansion of the forwarder (fx-open, 2026-11-22)

    P ∥ Q types by P-Connect at a cut a, where P holds a⁻ : S(p)‾@x‾ and
    Q holds a⁺ : S(p)@x, x the point of constant 0. Then
    P ∥ (fwd ∥ Q') types ([fwdp_expand2]). The forwarder holds a⁺ at x
    and b⁻ : S(p)‾ at y‾, y the point of constant 1, and Q' is Q with
    the channel a renamed to b ([fptyped_cren], static/ChanRen.v) and
    the constants 0 and 1 swapped ([fptyped_ren], static/Hiding.v), so
    Q' holds b⁺ : S(p)@y. The cut on a moves to the cuts on a and b.

    The forwarder's facts at x and y‾ relate the two roots. Read with the
    constant 1 sent back to 0, each fact is an equality x_k = x_k or
    program order. A cycle of the new world then maps to a cycle of the
    old one, which is P ∥ Q's world, because no two equalities follow
    each other ([J_acyc]). So the new world is acyclic whenever the old
    one is, with no further condition on P and Q than that their worlds
    do not know the constant 1.

    The protocols are the first-order ones of examples/Copycat.v.
    [fwdp_expand2_N] holds at every bound N, given the forwarder typed
    at N. At N = ∞ that is [fwdq_term], and [fwdp_expand2] is the
    deadlock-freedom instance. At a finite N the collapse carries
    well-foundedness ([collapse_swf]), and examples/CopycatTwoN.v types
    the forwarder at every N ≥ 4. *)

From GV Require Export examples.Copycat static.ChanRen.

(** ** The forwarder at x and y‾ *)

Definition ob : cend := ENeg "b".
Definition pyn : point := py‾.

Definition W_q (p : proto) : sworld := SWorld ({[0]} ∪ {[1]}) (ffacts p px pyn).

Lemma W_q_wf p : sworld_wf (W_q p).
Proof.
  split; simpl. intros u v H. apply ffacts_roots in H as [Hu Hv].
  unfold croot_in. split.
  - destruct Hu as [Hu|Hu]; [exists 0|exists 1]; rewrite Hu; split; [done|set_solver|done|set_solver].
  - destruct Hv as [Hv|Hv]; [exists 0|exists 1]; rewrite Hv; split; [done|set_solver|done|set_solver].
Qed.

(** *** Collapsing the constant 1 onto 0 *)

Definition f01 (a : nat) : nat := if decide (a = 1) then 0 else a.
Definition φ (u : point) : point := pt_ren f01 u.

(** The forwarder's facts that collapse to an equality. *)
Definition idf (u v : point) : Prop :=
  (∃ k, u = MkPt (NConst 0) true k ∧ v = MkPt (NConst 1) true k) ∨
  (∃ k, u = MkPt (NConst 1) false k ∧ v = MkPt (NConst 0) false k).

Lemma idf_φ u v : idf u v → φ u = φ v.
Proof. intros [(k & -> & ->)|(k & -> & ->)]; reflexivity. Qed.

Lemma idf_chain u w v : idf u w → idf w v → False.
Proof. intros [(k & -> & ->)|(k & -> & ->)] [(k' & E & ->)|(k' & E & ->)]; discriminate. Qed.

Lemma idf_irrefl u : idf u u → False.
Proof. intros [(k & -> & E)|(k & -> & E)]; discriminate. Qed.

Definition XN (k : nat) : point := MkPt (NConst 0) true k.
Definition YN (k : nat) : point := MkPt (NConst 1) false k.

Lemma ffacts_collapse p : ∀ k u v, ffacts p (XN k) (YN k) (FLt u v) → idf u v ∨ po (φ u) (φ v).
Proof.
  induction p as [|p IH|p IH]; intros k u v H; cbn [ffacts] in H.
  - injection H as -> ->. left. left. by exists k.
  - destruct H as [H|[H|H]].
    + injection H as -> ->. left. left. by exists k.
    + injection H as -> ->. right. apply tc_once. left. reflexivity.
    + apply (IH (k + 1)). exact H.
  - destruct H as [H|[H|H]].
    + injection H as -> ->. left. right. by exists k.
    + injection H as -> ->. right. apply tc_once. left. reflexivity.
    + apply (IH (k + 1)). exact H.
Qed.

Lemma φ_shift u : φ u⁺ = (φ u)⁺.
Proof. apply pt_ren_shift. Qed.
Lemma φ_dual u : φ u‾ = (φ u)‾.
Proof. apply pt_ren_dual. Qed.

(** A world J whose steps collapse into strict steps of O or into
    equalities is acyclic when O is. *)
Section collapse.
  Context (J O : sworld).
  Context (Hstep : ∀ u v, swstep J u v → O ⊢ₛ φ u ≺ φ v ∨ idf u v).

  Lemma collapse_path u v : J ⊢ₛ u ≺ v → O ⊢ₛ φ u ≺ φ v ∨ idf u v.
  Proof.
    induction 1 as [u v H|u w v H _ IH]; [by apply Hstep|].
    destruct (Hstep _ _ H) as [H1|H1], IH as [H2|H2].
    - left. by eapply sw_lt_trans.
    - left. by rewrite <-(idf_φ _ _ H2).
    - left. by rewrite (idf_φ _ _ H1).
    - exfalso. exact (idf_chain _ _ _ H1 H2).
  Qed.

  Lemma collapse_acyc : sacyc O → sacyc J.
  Proof.
    intros HO u Hu. destruct (collapse_path _ _ Hu) as [H|H]; [exact (HO _ H)|exact (idf_irrefl _ H)].
  Qed.

  (** At a finite N the same collapse carries well-foundedness. A point
      reached by an equality step lies below its target only through a
      strict step of O, because two equalities never follow each
      other. *)
  Lemma collapse_swf : swf O → swf J.
  Proof.
    intros HO. apply wf_iff_wellfounded. apply wf_iff_wellfounded in HO.
    assert (∀ a, Acc (sw_lt O) a → ∀ x, φ x = a → Acc (sw_lt J) x) as Hacc.
    { intros a Ha. induction Ha as [a _ IH]. intros x <-. constructor. intros y Hy.
      destruct (collapse_path _ _ Hy) as [H|H]; [by apply (IH (φ y) H)|].
      constructor. intros z Hz. destruct (collapse_path _ _ Hz) as [H'|H'].
      - apply (IH (φ z)); [|done]. by rewrite <-(idf_φ _ _ H).
      - exfalso. exact (idf_chain _ _ _ H' H). }
    intros x. exact (Hacc (φ x) (HO (φ x)) x eq_refl).
  Qed.

  Lemma collapse_wok N : wok N O → wok N J.
  Proof. destruct N; [apply collapse_swf|apply collapse_acyc]. Qed.
End collapse.

Lemma W_q_step O p u v : swstep (W_q p) u v → O ⊢ₛ φ u ≺ φ v ∨ idf u v.
Proof.
  destruct 1 as [u v H|u|u].
  - simpl in H. destruct (ffacts_collapse p 0 u v H) as [?|Hp]; [by right|left]. by apply po_slt.
  - left. rewrite φ_shift. apply sw_lt_po.
  - left. rewrite φ_shift, φ_dual. apply sw_lt_dpo.
Qed.

Lemma W_q_acyc p : sacyc (W_q p).
Proof. apply (collapse_acyc _ sw_empty); [apply W_q_step|apply sw_empty_acyc]. Qed.

Lemma W_q_wok N p : wok N (W_q p).
Proof. apply (collapse_wok _ sw_empty); [apply W_q_step|apply sw_empty_wok]. Qed.

(** *** The forwarder as a thread *)

Lemma o1_ob : o1 ≠ ob.
Proof. discriminate. Qed.

Definition Σq (p : proto) : senv := {[o1 := (pS p, px)]} ∪ {[ob := (pS (pdual p), pyn)]}.

Lemma Σq_pfree p : pfree (Σq p).
Proof.
  intros o Ho Hn. unfold Σq in Ho, Hn. rewrite dom_union_L, !dom_singleton_L in Ho, Hn.
  set_unfold in Ho; set_unfold in Hn. destruct Ho as [->| ->]; simpl in Hn; destruct Hn; discriminate.
Qed.

Lemma W_q_facts p : ffp (W_q p) hc_empty p px pyn.
Proof. apply ffacts_ffp. intros g Hg. exact Hg. Qed.

Definition fwdq_t (p : proto) : expr := fwdp_t p o1 ob.

Theorem fwdq_term p : fptyped None (W_q p) (Σq p) (∅, {[+ fwdq_t p +]}) TUnit.
Proof.
  apply (fp_term None (W_q p) (Σq p) ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σq_pfree.
  - intros o e He. unfold Σq in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; apply pS_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None (Σq p) ∪ ∅ =
      tenv_df ({[o1 := TE (pS p) px None None]} ∪ {[ob := TE (pS (pdual p)) pyn None None]})) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df, Σq. rewrite !map_fmap_union, !map_fmap_singleton.
      unfold tentry_df. cbn [te_sty te_pt fst snd]. by rewrite !sty_df_pS. }
    exact (fwdp_dftyped _ _ p o1 ob px pyn o1_ob (W_q_facts p)).
  - split; [apply W_q_wf|apply W_q_acyc].
Qed.

(** ** The joined world is acyclic when P ∥ Q's world is

    J = W1 ⊔ (W_q ⊔ W2'), with W2' the world of Q with 0 and 1 swapped.
    A fact of W1 or of W2 has no root 1, so φ fixes it, and φ undoes the
    swap on W2'. *)

Definition sw01 : cbij := cb_swap 0 1.

Lemma f01_fix (a : nat) : a ≠ 1 → f01 a = a.
Proof. intros H. unfold f01. by case_decide. Qed.

Lemma φ_fix S u : 1 ∉ S → croot_in S u → φ u = u.
Proof.
  intros H1 (a & Ha & HaS). apply pt_ren_fix. rewrite (pt_consts_root _ _ Ha).
  intros b ->%elem_of_singleton. apply f01_fix. intros ->. done.
Qed.

Lemma φ_swap S u : 1 ∉ S → croot_in S (pt_ren (cswap 0 1) u) → φ u = pt_ren (cswap 0 1) u.
Proof.
  intros H1 (a & Ha & HaS).
  rewrite <-(pt_ren_inv (cswap 0 1) (cswap 0 1) u (cswap_inv 0 1)) at 1.
  unfold φ. rewrite pt_ren_comp. apply pt_ren_fix. rewrite (pt_consts_root _ _ Ha).
  intros b ->%elem_of_singleton. assert (a ≠ 1) by (intros ->; done).
  unfold compose, cswap, f01. repeat case_decide; subst; try lia; done.
Qed.

Lemma J_step p W1 W2 u v : sworld_wf W1 → sworld_wf W2 → 1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  swstep (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)) u v → (W1 ⊔ W2) ⊢ₛ φ u ≺ φ v ∨ idf u v.
Proof.
  intros Hw1 Hw2 H1 H2 Hs. apply swstep_join_inv in Hs as [Hs|Hs].
  - left. destruct Hs as [u v Hf|u|u].
    + destruct (wf_facts _ Hw1 u v Hf) as [Hu Hv].
      rewrite (φ_fix _ u H1 Hu), (φ_fix _ v H1 Hv). apply sw_lt_fact. by left.
    + rewrite φ_shift. apply sw_lt_po.
    + rewrite φ_shift, φ_dual. apply sw_lt_dpo.
  - apply swstep_join_inv in Hs as [Hs|Hs]; [by apply (W_q_step _ p)|left].
    destruct Hs as [u v Hf|u|u].
    + simpl in Hf. destruct (wf_facts _ Hw2 _ _ Hf) as [Hu Hv].
      rewrite (φ_swap _ u H2 Hu), (φ_swap _ v H2 Hv). apply sw_lt_fact. by right.
    + rewrite φ_shift. apply sw_lt_po.
    + rewrite φ_shift, φ_dual. apply sw_lt_dpo.
Qed.

Lemma J_acyc p W1 W2 : sworld_wf W1 → sworld_wf W2 → 1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  sacyc (W1 ⊔ W2) → sacyc (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)).
Proof. intros Hw1 Hw2 H1 H2. apply collapse_acyc. intros u v. by apply J_step. Qed.

Lemma J_wok N p W1 W2 : sworld_wf W1 → sworld_wf W2 → 1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  wok N (W1 ⊔ W2) → wok N (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)).
Proof. intros Hw1 Hw2 H1 H2. apply collapse_wok. intros u v. by apply J_step. Qed.

(** The order of a join of restrictions is inside the order of the join. *)
Lemma rjoin_lt A B S x y : (swrestrict A S ⊔ swrestrict B S) ⊢ₛ x ≺ y → (A ⊔ B) ⊢ₛ x ≺ y.
Proof.
  assert (∀ u v, swstep (swrestrict A S ⊔ swrestrict B S) u v → (A ⊔ B) ⊢ₛ u ≺ v) as Hs.
  { intros u v Hs. apply swstep_join_inv in Hs as [Hs|Hs].
    - eapply sw_lt_mono; [apply swext_join_l|]. apply (swrestrict_lt A S). by apply tc_once.
    - eapply sw_lt_mono; [apply swext_join_r|]. apply (swrestrict_lt B S). by apply tc_once. }
  induction 1 as [u v H|u v w H _ IH]; [by apply Hs|].
  eapply sw_lt_trans; [by apply Hs|exact IH].
Qed.

(** ** Renaming the partner *)

Definition sswap (a b c : chan) : chan := if decide (c = a) then b else if decide (c = b) then a else c.

Lemma sswap_inv a b c : sswap a b (sswap a b c) = c.
Proof. unfold sswap. repeat case_decide; subst; congruence. Qed.

Global Instance sswap_inj a b : base.Inj eq eq (sswap a b).
Proof. intros c c' E. by rewrite <-(sswap_inv a b c), E, sswap_inv. Qed.

Lemma kmap_cmap_fix h `{!base.Inj eq eq h} (Σ : senv) :
  (∀ c, c ∈ chans_of Σ → h c = c) → kmap (cmap h) Σ = Σ.
Proof.
  intros Hf. apply map_eq. intros o.
  assert (∀ o', o' ∈ dom Σ → cmap h o' = o') as Hc.
  { intros o' Ho'. pose proof (Hf _ (elem_of_chans_of' _ _ Ho')) as E.
    destruct o'; simpl in *; by rewrite E. }
  destruct (Σ !! o) as [v|] eqn:E.
  - rewrite <-(Hc o) at 1 by (by apply elem_of_dom_2 in E). by rewrite (lookup_kmap (cmap h)).
  - apply (lookup_kmap_None (cmap h)). intros i ->. destruct (Σ !! i) as [v|] eqn:Ei; [|done].
    rewrite (Hc i) in E by (by apply elem_of_dom_2 in Ei). congruence.
Qed.

Lemma set_map_fix (h : chan → chan) (C : gset chan) : (∀ c, c ∈ C → h c = c) → set_map h C = C.
Proof.
  intros Hf. apply set_eq. intros c. rewrite elem_of_map. split.
  - intros (c' & -> & Hc'). by rewrite Hf.
  - intros Hc. exists c. by rewrite Hf.
Qed.

Lemma sty_ren_pS f p : sty_ren f (pS p) = pS p.
Proof. induction p as [|p IH|p IH]; simpl; rewrite ?IH; done. Qed.

Definition ΣCb (p : proto) : senv := {[ob := (pS (pdual p), pyn)]}.

Lemma ΣCb_dual p : senv_dual (ΣCb p) = {[EPos "b" := (pS p, py)]}.
Proof.
  unfold senv_dual, ΣCb. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
  by rewrite pS_dual, pdual_pdual.
Qed.

Lemma chans_Σxp p : chans_of (Σxp p) = {["a"]}.
Proof. unfold Σxp. by rewrite chans_single. Qed.
Lemma chans_ΣCb p : chans_of (ΣCb p) = {["b"]}.
Proof. unfold ΣCb. by rewrite chans_single. Qed.

Lemma not_in_dom_chans (Σ : senv) o : ech o ∉ chans_of Σ → o ∉ dom Σ.
Proof. intros H Ho. apply H. by apply elem_of_chans_of'. Qed.

Lemma disj_single_chans (Σ : senv) o v : ech o ∉ chans_of Σ → Σ ##ₘ {[o := v]}.
Proof.
  intros H. apply map_disjoint_singleton_r_2. apply not_elem_of_dom. by apply not_in_dom_chans.
Qed.

(** ** Two-sided identity expansion

    At any bound N, given the forwarder typed at N. At N = ∞ it is
    [fwdq_term]. The world premise carries over by [J_wok], acyclicity
    at N = ∞ and well-foundedness at a finite N. *)

Theorem fwdp_expand2_N N p W1 W2 Σ1 Σ2 C1 C2 E1 E2 T :
  fptyped N (W_q p) (Σq p) (∅, {[+ fwdq_t p +]}) TUnit →
  fptyped N W1 (Σ1 ∪ Σxp p) (C1, E1) T →
  fptyped N W2 (Σ2 ∪ senv_dual (Σxp p)) (C2, E2) TUnit →
  Σ1 ##ₘ Σxp p → Σ2 ##ₘ senv_dual (Σxp p) →
  chans_of Σ1 ## chans_of Σ2 → "a" ∉ chans_of Σ1 → "a" ∉ chans_of Σ2 →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ {["a"]} → C2 ## chans_of Σ1 ∪ {["a"]} →
  wok N (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)) →
  "b" ∉ chans_of Σ1 → "b" ∉ chans_of Σ2 → "b" ∉ C1 → "b" ∉ C2 →
  1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  fptyped N (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)) (Σ1 ∪ senv_ren (cswap 0 1) Σ2)
    (C1 ∪ (∅ ∪ C2 ∪ {["b"]}) ∪ {["a"]},
     E1 ⊎ ({[+ fwdq_t p +]} ⊎ emapE (cmap (sswap "a" "b")) E2)) T.
Proof.
  intros Hfwd HP HQ HD1 HD2 H12 Ha1 Ha2 HC HC1 HC2 HS Hb1 Hb2 HbC1 HbC2 H01 H02.
  set (h := sswap "a" "b"). set (Σ2' := senv_ren (cswap 0 1) Σ2).
  destruct (fptyped_wf _ _ _ _ _ HP) as [Hw1 Hk1]. destruct (fptyped_wf _ _ _ _ _ HQ) as [Hw2 Hk2].
  assert (wok N (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2))) as HJ.
  { apply J_wok; [done|done|done|done|].
    apply (wok_join_iff N W1 W2 Hw1 Hw2). by split_and!. }
  assert (chans_of Σ2' = chans_of Σ2) as EΣ2 by apply chans_of_ren.
  (* The partner Q', renamed. *)
  assert (fptyped N (sw_ren sw01 W2) (Σ2' ∪ {[EPos "b" := (pS p, py)]}) (C2, emapE (cmap h) E2) TUnit) as HQ'.
  { pose proof (fptyped_ren sw01 _ _ _ _ _ HQ) as H. simpl in H.
    change (cb_f sw01) with (cswap 0 1) in H.
    rewrite senv_ren_union, Σxp_dual in H. unfold senv_ren at 2 in H. rewrite map_fmap_singleton in H.
    cbn [fst snd] in H. rewrite sty_ren_pS in H.
    replace (pt_ren (cswap 0 1) px) with py in H by reflexivity.
    pose proof (fptyped_cren h _ _ _ _ _ _ H) as H'. cbn [fst snd] in H'.
    rewrite (kmap_union (cmap h)), (kmap_singleton (cmap h)) in H'.
    fold Σ2' in H'. rewrite (kmap_cmap_fix h Σ2') in H'.
    2:{ intros c Hc. rewrite EΣ2 in Hc. unfold h, sswap. repeat case_decide; subst; set_solver. }
    rewrite (set_map_fix h C2) in H'.
    2:{ intros c Hc. unfold h, sswap. repeat case_decide; subst; set_solver. }
    exact H'. }
  (* fwd ∥ Q', cut on b. *)
  assert (fptyped N (W_q p ⊔ sw_ren sw01 W2) ({[o1 := (pS p, px)]} ∪ Σ2')
            (∅ ∪ C2 ∪ chans_of (ΣCb p), {[+ fwdq_t p +]} ⊎ emapE (cmap h) E2) TUnit) as HFQ.
  { apply fp_connect.
    - exact Hfwd.
    - by rewrite ΣCb_dual.
    - rewrite chans_single, EΣ2. set_solver.
    - rewrite chans_single, chans_ΣCb. set_solver.
    - rewrite chans_ΣCb, EΣ2. set_solver.
    - set_solver.
    - rewrite chans_ΣCb, EΣ2. set_solver.
    - rewrite chans_single, chans_ΣCb. set_solver.
    - eapply wok_sub; [|exact HJ]. intros x y Hxy. eapply sw_lt_mono; [apply swext_join_r|].
      by eapply rjoin_lt. }
  rewrite chans_ΣCb in HFQ.
  (* P ∥ (fwd ∥ Q'), cut on a. *)
  rewrite <-(chans_Σxp p).
  apply fp_connect.
  - exact HP.
  - rewrite Σxp_dual. rewrite map_union_comm; [exact HFQ|].
    apply disj_single_chans. simpl. by rewrite EΣ2.
  - by rewrite EΣ2.
  - rewrite chans_Σxp. set_solver.
  - rewrite chans_Σxp, EΣ2. set_solver.
  - set_solver.
  - rewrite chans_Σxp, EΣ2. set_solver.
  - rewrite chans_Σxp. set_solver.
  - eapply wok_sub; [|exact HJ]. intros x y Hxy. by eapply rjoin_lt.
Qed.

Theorem fwdp_expand2 p W1 W2 Σ1 Σ2 C1 C2 E1 E2 T :
  fptyped None W1 (Σ1 ∪ Σxp p) (C1, E1) T →
  fptyped None W2 (Σ2 ∪ senv_dual (Σxp p)) (C2, E2) TUnit →
  Σ1 ##ₘ Σxp p → Σ2 ##ₘ senv_dual (Σxp p) →
  chans_of Σ1 ## chans_of Σ2 → "a" ∉ chans_of Σ1 → "a" ∉ chans_of Σ2 →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ {["a"]} → C2 ## chans_of Σ1 ∪ {["a"]} →
  wok None (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)) →
  "b" ∉ chans_of Σ1 → "b" ∉ chans_of Σ2 → "b" ∉ C1 → "b" ∉ C2 →
  1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  fptyped None (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)) (Σ1 ∪ senv_ren (cswap 0 1) Σ2)
    (C1 ∪ (∅ ∪ C2 ∪ {["b"]}) ∪ {["a"]},
     E1 ⊎ ({[+ fwdq_t p +]} ⊎ emapE (cmap (sswap "a" "b")) E2)) T.
Proof. apply fwdp_expand2_N, fwdq_term. Qed.

(** A closed P ∥ Q stays deadlock free with the forwarder in the cut. *)
Corollary fwdp_expand2_df p W1 W2 C1 C2 E1 E2 T :
  fptyped None W1 (∅ ∪ Σxp p) (C1, E1) T →
  fptyped None W2 (∅ ∪ senv_dual (Σxp p)) (C2, E2) TUnit →
  C1 ## C2 → "a" ∉ C1 → "a" ∉ C2 →
  wok None (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)) →
  "b" ∉ C1 → "b" ∉ C2 → 1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  deadlock_free (C1 ∪ (∅ ∪ C2 ∪ {["b"]}) ∪ {["a"]},
                 E1 ⊎ ({[+ fwdq_t p +]} ⊎ emapE (cmap (sswap "a" "b")) E2)).
Proof.
  intros HP HQ HC Ha1 Ha2 HS Hb1 Hb2 H01 H02.
  pose proof (fwdp_expand2 p W1 W2 ∅ ∅ C1 C2 E1 E2 T HP HQ) as H.
  assert (chans_of (∅ : senv) = ∅) as E0 by apply chans_empty.
  rewrite E0 in H. unfold senv_ren in H. rewrite fmap_empty, map_union_empty in H.
  eapply soundness, H; try done; try apply map_disjoint_empty_l; set_solver.
Qed.

(** ** An instance: the partners of examples/Copycat.v

    p1 holds a⁻ : (?∗.!∗.Close)‾@x‾ and p2 holds a⁺ : ?∗.!∗.Close@x.
    With the forwarder in their cut, p2 renamed to b⁺ at y, the
    configuration is typed and deadlock free. *)

Definition p0 : proto := PRcv (PSnd PEnd).

Lemma Σxp_p0 : Σxp p0 = Σx.
Proof. reflexivity. Qed.

Lemma p2_term_x : fptyped None sw_empty (∅ ∪ senv_dual (Σxp p0)) (∅, {[+ p2_t o1 +]}) TUnit.
Proof.
  rewrite (left_id_L ∅ (∪)), Σxp_dual.
  apply (fp_term None sw_empty _ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o e He. apply lookup_singleton_Some in He as [_ <-]. apply S1_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None {[o1 := (pS p0, px)]} ∪ ∅ = tenv_df {[o1 := TE S1 px None None]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df. by rewrite !map_fmap_singleton. }
    apply (p2_dftyped sw_empty hc_empty).
  - apply sw_empty_wok.
Qed.

Example fwdp_expand2_example :
  deadlock_free (∅ ∪ (∅ ∪ ∅ ∪ {["b"]}) ∪ {["a"]},
                 {[+ p1_t (edual o1) +]} ⊎ ({[+ fwdq_t p0 +]} ⊎ emapE (cmap (sswap "a" "b")) {[+ p2_t o1 +]})).
Proof.
  apply (fwdp_expand2_df p0 sw_empty sw_empty ∅ ∅ _ _ TUnit).
  - rewrite (left_id_L ∅ (∪)), Σxp_p0. apply p1_term.
  - apply p2_term_x.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply swf_wok, swf_bare. intros [u v] [Hf|Hf]; simpl in Hf; destruct Hf as (_ & (a & _ & Ha) & _);
      unfold swshared in Ha; simpl in Ha; set_solver.
  - set_solver.
  - set_solver.
  - simpl. set_solver.
  - simpl. set_solver.
Qed.
