(** * Composition of the lock-free judgment (lock-freedom plan §17.4)

    [LFP_term] is P-Term for [LFP]. The live part is [LPrel_term]. The
    soup has one thread, thread 0, whose environment is the one of the
    typing, [tenv_of Σ ∪ ΘB]. Its points are a map π on exactly the
    ends of that environment, and its counters start full ([fsem]). *)

From stdpp Require Import base gmap.
From LRGV Require Export lockfree.LFSoup.
From LRGV Require Import lockfree.LFFuel.

Set Default Proof Using "Type".

Lemma soup_singleton_map (t : expr) : soup {[0 := t]} = {[+ t +]}.
Proof.
  rewrite <-insert_empty, soup_insert by apply lookup_empty.
  by rewrite soup_empty, (left_id_L ∅ (⊎)).
Qed.

(** P-Term (§11) for the lock-free judgment. Over [LPrel_term] it asks
    the points π of the held ends and full counters at them. *)
Theorem LFP_term (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr) (T : ty)
    (π : gmap cend point) :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  lsem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  dom π = tenv_ends (tenv_of Σ ∪ ΘB) →
  (∀ o x, tenv_end (tenv_of Σ ∪ ΘB) o = Some x → π !! o = Some x.2) →
  fsem W π t →
  LFP W Σ T (C0, {[+ t +]}).
Proof.
  intros HT HW Hd Hdj Hb Hdu Ht Hdπ Hπ Hf. split.
  { by apply (LPrel_term W Σ ΘB C0 t T). }
  set (Θ := tenv_of Σ ∪ ΘB).
  (* a channel of Θ is a channel of Σ, with one entry, or of ΘB, with two *)
  assert (HΘ : ∀ c, Θ !! c = (One <$> Σ !! c) ∨ (Σ !! c = None ∧ Θ !! c = ΘB !! c)).
  { intros c. unfold Θ. rewrite lookup_union, lookup_tenv_of.
    destruct (Σ !! c) eqn:Hs; simpl.
    - left. assert (ΘB !! c = None) as ->; [|done].
      apply not_elem_of_dom. rewrite Hd. intros Hc. apply (Hdj c); [|done].
      by apply elem_of_dom.
    - right. split; [done|]. by destruct (ΘB !! c). }
  assert (Hbip : tenv_bipol Θ).
  { intros c e1 e2 Hc. destruct (HΘ c) as [H|[_ H]]; rewrite H in Hc.
    - by destruct (Σ !! c).
    - destruct (Hdu c e1 e2 Hc) as [He _]. rewrite He, pt_pol_dual. by destruct (pt_pol e2.2). }
  exists (C0, {[0 := t]}), π, (λ _, π), (λ _, w_bud W <$> π). split.
  { unfold erase. simpl. by rewrite soup_singleton_map. }
  intros n. exists (λ _, Θ), (λ _, T). simpl. split; [split|]; simpl.
  - done.
  - intros s e Hs. apply lookup_singleton_Some in Hs as [_ <-].
    pose proof (Ht n W ∅ _ Var (wext_refl W HW) (tenv_comp_empty_r _ _) eq_refl) as H.
    by rewrite subst_ids in H.
  - done.
  - by left.
  - intros s e o x _ Hx. by apply Hπ.
  - intros s s' e e' Hne Hs Hs'.
    apply lookup_singleton_Some in Hs as [<- _]. apply lookup_singleton_Some in Hs' as [<- _].
    done.
  - intros s e o x Hs Hx Ho. exists 0, t.
    destruct o as [c b]. simpl in Ho.
    assert (Σ !! c = None) as HΣ by (by apply not_elem_of_dom).
    unfold tenv_end in Hx |- *. simpl in Hx |- *.
    destruct (HΘ c) as [H|[_ H]]; rewrite H in Hx |- *; [by rewrite HΣ in Hx|].
    destruct (ΘB !! c) as [oc|] eqn:Hc; [|done].
    destruct (Hb c oc Hc) as (e1 & e2 & ->).
    destruct (Hdu c e1 e2 Hc) as [He Hs12].
    assert (pt_pol e1.2 ≠ pt_pol e2.2) as Hp
      by (rewrite He, pt_pol_dual; by destruct (pt_pol e2.2)).
    rewrite lookup_singleton_eq. unfold cdual. simpl.
    case_bool_decide as H1.
    + injection Hx as <-. subst b. exists e2.
      rewrite (bool_decide_false (pt_pol e1.2 = negb (pt_pol e1.2)))
        by (by destruct (pt_pol e1.2)).
      rewrite bool_decide_true by (destruct (pt_pol e1.2), (pt_pol e2.2); done).
      split_and!; try done. by apply eq_dual_sym.
    + case_bool_decide as H2; [|done]. injection Hx as <-. subst b.
      exists e1. rewrite bool_decide_true by (destruct (pt_pol e1.2), (pt_pol e2.2); done).
      split_and!; try done. by apply sdual_sym.
  - intros s e _. unfold Θ. rewrite dom_union_L. unfold tenv_of. rewrite dom_fmap_L, Hd.
    set_solver.
  - intros s e Hs. simpl in Hs. apply lookup_singleton_Some in Hs as [_ <-].
    split_and!; [by apply fsem_FuelE|done|by rewrite dom_fmap_L|done].
Qed.
