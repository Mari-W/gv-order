(** * Tools for the closed examples with top-level creation constraints

    Each file *Fresh.v next to an example types the same program with
    its top-level channels as point variables of the hypotheses
    ([created]) and applies [soundness_created_s]
    (docs/extensions/fresh-points.md, sharp edges 172). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** [sf_pinst_none], [fhyps_pinst_empty], [skn_inst] and [fresh_clean]
    moved to examples/ExampleTools.v, because the base examples use
    them too (sharp edges 105). *)

(** The empty world. *)
Lemma Wpo_nil_strict : strict (Wpo []).
Proof. apply Wpo_strict. Qed.

(** ** E-NewFresh with polarities (end points)

    The two ends of a fresh channel sit at ι and ῑ. A gate fact against
    a held end at ι is a fact against its partner ῑ, so a creation
    constraint names both points. [freshp_bcs L H] has the facts
    l ≺ ι^b for (l, b) ∈ L and ι^b ≺ h for (h, b) ∈ H, where ι^true = ι
    and ι^false = ῑ. Betweenness compares facts of one polarity only. *)
Definition freshp_facts (L H : list (point * bool)) (f : fact) : Prop :=
  (∃ i l b, L !! i = Some (l, b) ∧ f = FLt (pvar (S i)) (pt_polar b (pvar 0))) ∨
  (∃ j h b, H !! j = Some (h, b) ∧ f = FLt (pt_polar b (pvar 0)) (pvar (S (length L + j)))).

Definition freshp_bcs (L H : list (point * bool)) : bcs :=
  BCs (L.*1 ++ H.*1) (freshp_facts L H).

Lemma pt_root_polar0 b : pt_root (pt_polar b (pvar 0)) = NVar 0.
Proof. by destruct b. Qed.

Lemma pt_inst_polar σ b x : pt_inst σ (pt_polar b x) = pt_polar b (pt_inst σ x).
Proof. destruct b; simpl; [done|apply pt_inst_dual]. Qed.

Lemma ple_polar0 b b' : ple (pt_polar b (pvar 0)) (pt_polar b' (pvar 0)) → b = b'.
Proof.
  intros [E|Hp].
  - destruct b, b'; done.
  - apply ppo_size in Hp. destruct b, b'; unfold pt_size in Hp; simpl in Hp; lia.
Qed.

Lemma created_p W Ψ L H :
  created W Ψ → Forall (skn W Ψ) (L.*1 ++ H.*1) →
  (∀ l h b, (l, b) ∈ L → (h, b) ∈ H → slt W Ψ l h) →
  created W (hyps_inst (pshift 1) Ψ ++ [(bcs_inst (pshift 1) (freshp_bcs L H), ids 1)]).
Proof.
  intros HΨ HK Hbt.
  apply (created_fresh W Ψ (freshp_bcs L H)); [done| |done|].
  - intros f Hf Hs. destruct Hf as [(i & l & b & Hi & ->)|(j & h & b & Hj & ->)].
    + left. eexists _, _. split; [done|]. split_and!; [left; by exists i, l, b|done|apply pt_root_polar0|done].
    + right. eexists _, _. split; [done|]. split_and!; [right; by exists j, h, b|done|apply pt_root_polar0|done].
  - intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) Hpq.
    destruct Hf as [(i & l & b & Hi & E)|(j & h & b & Hj & E)]; injection E as -> ->;
      [|by rewrite pt_root_polar0 in Hu].
    destruct Hf' as [(i' & l' & b' & Hi' & E)|(j & h & b' & Hj & E)]; injection E as -> ->;
      [by rewrite pt_root_polar0 in Hv|].
    apply ple_polar0 in Hpq as <-.
    unfold fresh_outer. rewrite !pt_inst_pvar_at. unfold plist. simpl.
    assert ((L.*1) !! i = Some l) as Hl by (rewrite list_lookup_fmap, Hi; done).
    assert ((H.*1) !! j = Some h) as Hh by (rewrite list_lookup_fmap, Hj; done).
    rewrite (lookup_app_l_Some _ _ _ _ Hl).
    rewrite lookup_app_r by (rewrite length_fmap; lia).
    rewrite length_fmap. replace (length L + j - length L) with j by lia. rewrite Hh.
    apply (Hbt l h b); by eapply list_elem_of_lookup_2.
Qed.

(** The facts of the hypothesis, read at the instance x. *)
Lemma slt_freshp_l W Ψ σ L H x l b :
  (bcs_inst σ (freshp_bcs L H), [x]) ∈ Ψ → (l, b) ∈ L → slt W Ψ (pt_inst σ l) (pt_polar b x).
Proof.
  intros Hg Hl. apply sl_h. exists (bcs_inst σ (freshp_bcs L H)), [x]. split; [done|].
  apply list_elem_of_lookup_1 in Hl as [i Hi].
  set (env := pt_inst σ <$> (L.*1 ++ H.*1)).
  assert (env !! i = Some (pt_inst σ l)) as He.
  { unfold env. rewrite list_lookup_fmap. rewrite (lookup_app_l_Some _ _ i l); [done|].
    by rewrite list_lookup_fmap, Hi. }
  exists (FLt (pt_inst (pup 1 (plist env)) (pvar (S i)))
              (pt_inst (pup 1 (plist env)) (pt_polar b (pvar 0)))). split.
  - exists (FLt (pvar (S i)) (pt_polar b (pvar 0))). split_and!.
    + left. by exists i, l, b.
    + pose proof (lookup_lt_Some _ _ _ He). unfold env in *. rewrite length_fmap, length_app, !length_fmap in *.
      destruct b; cbn; rewrite ?length_fmap, ?length_app, ?length_fmap; lia.
    + done.
  - cbn [fact_map]. rewrite !pt_inst_polar, pt_inst_open1_0, (pt_inst_open1 x env i _ He). done.
Qed.

Lemma slt_freshp_r W Ψ σ L H x h b :
  (bcs_inst σ (freshp_bcs L H), [x]) ∈ Ψ → (h, b) ∈ H → slt W Ψ (pt_polar b x) (pt_inst σ h).
Proof.
  intros Hg Hh. apply sl_h. exists (bcs_inst σ (freshp_bcs L H)), [x]. split; [done|].
  apply list_elem_of_lookup_1 in Hh as [j Hj].
  set (env := pt_inst σ <$> (L.*1 ++ H.*1)).
  assert (env !! (length L + j) = Some (pt_inst σ h)) as He.
  { unfold env. rewrite list_lookup_fmap. rewrite lookup_app_r by (rewrite length_fmap; lia).
    rewrite length_fmap. replace (length L + j - length L) with j by lia.
    by rewrite list_lookup_fmap, Hj. }
  exists (FLt (pt_inst (pup 1 (plist env)) (pt_polar b (pvar 0)))
              (pt_inst (pup 1 (plist env)) (pvar (S (length L + j))))). split.
  - exists (FLt (pt_polar b (pvar 0)) (pvar (S (length L + j)))). split_and!.
    + right. by exists j, h, b.
    + pose proof (lookup_lt_Some _ _ _ He). unfold env in *. rewrite length_fmap, length_app, !length_fmap in *.
      destruct b; cbn; rewrite ?length_fmap, ?length_app, ?length_fmap; lia.
    + done.
  - cbn [fact_map]. rewrite !pt_inst_polar, pt_inst_open1_0, (pt_inst_open1 x env _ _ He). done.
Qed.

(** ** The two ends of one channel in order

    A closure that captures both ends of a channel, or two aliased
    channels, at ι and ῑ needs a lower point below both partners. The
    creation constraint {ι ≺ ῑ} gives ι. The rank 2·k for ι+k and
    2·k+1 for ῑ+k orders it with program order. *)
Definition ccd_P (g : fact) : Prop := g = FLt (pvar 0) (pt_dual (pvar 0)).
Definition ccd_C : bcs := BCs [] ccd_P.

Definition pol_rank (x : point) : nat := 2 * pt_off x + (if pt_pol x then 0 else 1).

Lemma ccd_ok peq plt : cc_ok peq plt ccd_C.
Proof.
  apply (cc_ok_inner peq plt ccd_P (λ x y, pol_rank x < pol_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold pol_rank, pt_shift. simpl. lia.
  - intros g -> _. eexists _, _. split; [done|]. unfold pol_rank. cbn. lia.
  - intros [n [] o] _; unfold pol_rank, pt_shift, pt_dual; simpl; lia.
Qed.

Lemma slt_ccd W Ψ x : (ccd_C, [x]) ∈ Ψ → slt W Ψ x (pt_dual x).
Proof.
  intros Hg. eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (pvar 0))); [exact Hg|done|cbn; lia| |].
  - by rewrite pt_inst_pvar_at.
  - by rewrite pt_inst_dual, pt_inst_pvar_at.
Qed.
