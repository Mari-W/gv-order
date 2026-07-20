From Coq Require Import Classical.
From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Compositionality.

(** Solve only set-level side goals (membership, disjointness,
    inclusion), after normalizing domains; fail cleanly on any other
    goal shape so proof-term side goals are never fed to set_solver. *)
Ltac set_side :=
  lazymatch goal with
  | |- _ ∈ _ => idtac
  | |- _ ∉ _ => idtac
  | |- _ ## _ => idtac
  | |- _ ⊆ _ => idtac
  end;
  rewrite ?dom_insert_L, ?dom_delete_L, ?dom_union_L, ?dom_fmap_L,
    ?dom_singleton_L, ?dom_empty_L;
  set_solver.

Lemma Powners_graft_timed n (IHc : connect_at n) σ Σw Tw Cw Ew :
  Powners (Prel n) σ Σw Tw (Cw, Ew) →
  ∀ c sc Σg Tg Cg Eg Tt,
    Σw !! c = Some sc →
    Prel n (<[c := dual sc]> Σg) Tg (Cg, Eg) →
    ty_one_of Tw Tg Tt → prim Tt →
    Σg ##ₘ Σw → dom σ ## dom Σg → dom σ ## Cg → c ∉ dom Σg → c ∉ Cg →
    Cw ## Cg → Cw ## dom Σg → Cg ## dom Σw → Cw ## dom Σw → Cg ## dom Σg →
    Powners (Prel n) σ (delete c Σw ∪ Σg) Tt (Cw ∪ Cg ∪ {[c]}, Ew ⊎ Eg).
Proof.
  intros HPo. remember (Cw, Ew) as pw eqn:Hpw. revert Cw Ew Hpw.
  induction HPo as [|σ' d sd Σd Σrest Td Trest Tw' Cd Ed Crest Erest
                     Hσd Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10
                     HPd HPrest IHrest Hty'];
    intros Cw Ew Hpw; simplify_eq;
    intros c sc Σg Tg Cg Eg Tt Hlk HPg Hty Hprim Hgw Hσg Hσcg Hcg Hccg
      Hwcg Hwdg Hcgw Hsw Hsg.
  - rewrite lookup_empty in Hlk. done.
  - assert (Σd ##ₘ Σg) as Hdg1.
    { apply map_disjoint_dom_2. apply map_disjoint_dom in Hgw.
      rewrite dom_union_L in Hgw. set_solver. }
    assert (Σrest ##ₘ Σg) as Hdg2.
    { apply map_disjoint_dom_2. apply map_disjoint_dom in Hgw.
      rewrite dom_union_L in Hgw. set_solver. }
    rewrite dom_insert_L in Hσg, Hσcg.
    destruct (decide (c ∈ dom Σd)) as [Hin|Hnin].
    + (* the head piece owns c: connect the graft into it *)
      pose proof Hin as [sc' Hsc']%elem_of_dom.
      assert (sc' = sc) as ->.
      { rewrite (lookup_union_Some_l _ _ _ _ Hsc') in Hlk. congruence. }
      assert (c ≠ d) as Hcd.
      { intros ->. apply not_elem_of_dom in Hd1. congruence. }
      assert (c ∉ dom Σrest) as Hcrest.
      { apply map_disjoint_dom in Hd7. set_solver. }
      assert (<[d:=sd]> Σd = <[c := sc]> (<[d:=sd]> (delete c Σd))) as Heqp.
      { rewrite insert_insert_ne; [|done]. f_equal. by rewrite insert_delete_id. }
      assert (d ∉ dom Σg) as Hdng by set_solver.
      assert (c ∉ dom (<[d:=sd]> (delete c Σd))) as Hcout.
      { rewrite dom_insert_L, dom_delete_L. set_solver. }
      assert (delete c Σd ##ₘ Σrest) as Hx1.
      { apply map_disjoint_dom_2. rewrite dom_delete_L.
        apply map_disjoint_dom in Hd7. set_solver. }
      assert (delete c Σd ##ₘ Σg) as Hx2.
      { apply map_disjoint_dom_2. rewrite dom_delete_L.
        apply map_disjoint_dom in Hdg1. set_solver. }
      assert (∀ T2, ty_one_of T2 Trest Tt →
        Prel n (<[d:=sd]> (delete c Σd) ∪ Σg) T2 (Cd ∪ Cg ∪ {[c]}, Ed ⊎ Eg) →
        Powners (Prel n) (<[d:=sd]> σ') (delete c (Σd ∪ Σrest) ∪ Σg) Tt
          (Cd ∪ Crest ∪ Cg ∪ {[c]}, (Ed ⊎ Erest) ⊎ Eg)) as Hcons.
      { intros T2 Hty2 HP2.
        rewrite delete_union, (delete_id Σrest c);
          [|by apply not_elem_of_dom].
        replace (delete c Σd ∪ Σrest ∪ Σg)
          with ((delete c Σd ∪ Σg) ∪ Σrest) by senv_perm.
        replace (Cd ∪ Crest ∪ Cg ∪ {[c]})
          with ((Cd ∪ Cg ∪ {[c]}) ∪ Crest) by set_solver.
        replace ((Ed ⊎ Erest) ⊎ Eg) with ((Ed ⊎ Eg) ⊎ Erest)
          by multiset_solver.
        eapply Powners_cons with (Td := T2); try done;
          try (by senv_disj); try set_side.
        replace (<[d:=sd]> (delete c Σd ∪ Σg))
          with (<[d:=sd]> (delete c Σd) ∪ Σg) by (by rewrite insert_union_l).
        done. }
      destruct Hty as [[-> ->]|[-> ->]].
      * (* the graft is a unit piece *)
        eapply Hcons; [exact Hty'|].
        rewrite Heqp in HPd.
        eapply (IHc _ _ c sc); try done; try (by senv_disj);
          try set_side.
        destruct (ty_one_of_prim _ _ _ Hty' Hprim). done.
      * (* the graft carries the type *)
        apply ty_one_of_unit_inv in Hty' as [-> ->].
        eapply Hcons; [by left|].
        rewrite Heqp in HPd.
        replace (<[d:=sd]> (delete c Σd) ∪ Σg)
          with (Σg ∪ <[d:=sd]> (delete c Σd))
          by (apply map_union_comm; senv_disj).
        replace (Cd ∪ Cg ∪ {[c]}) with (Cg ∪ Cd ∪ {[c]}) by set_solver.
        replace (Ed ⊎ Eg) with (Eg ⊎ Ed) by multiset_solver.
        eapply (IHc _ _ c (dual sc)); try done; try (by senv_disj);
          try set_side.
        rewrite dual_involutive. done.
    + (* c is owned by the rest of the family *)
      assert (Σrest !! c = Some sc) as Hlk2.
      { rewrite lookup_union_r in Hlk; [done|by apply not_elem_of_dom]. }
      assert (c ∈ dom Σrest) as Hcrest by (apply elem_of_dom; eauto).
      assert (Σd ##ₘ delete c Σrest) as Hx1.
      { apply map_disjoint_dom_2. rewrite dom_delete_L.
        apply map_disjoint_dom in Hd7. set_solver. }
      assert (∀ T3, ty_one_of Td T3 Tt →
        Powners (Prel n) σ' (delete c Σrest ∪ Σg) T3
          (Crest ∪ Cg ∪ {[c]}, Erest ⊎ Eg) →
        Powners (Prel n) (<[d:=sd]> σ') (delete c (Σd ∪ Σrest) ∪ Σg) Tt
          (Cd ∪ Crest ∪ Cg ∪ {[c]}, (Ed ⊎ Erest) ⊎ Eg)) as Hcons.
      { intros T3 Hty3 HPrest'.
        rewrite delete_union, (delete_id Σd c);
          [|by apply not_elem_of_dom].
        replace (Σd ∪ delete c Σrest ∪ Σg)
          with (Σd ∪ (delete c Σrest ∪ Σg)) by (by rewrite (assoc_L (∪))).
        replace (Cd ∪ Crest ∪ Cg ∪ {[c]})
          with (Cd ∪ (Crest ∪ Cg ∪ {[c]})) by set_solver.
        replace ((Ed ⊎ Erest) ⊎ Eg) with (Ed ⊎ (Erest ⊎ Eg))
          by multiset_solver.
        eapply Powners_cons with (Td := Td); try done;
          try (by senv_disj); try set_side. }
      assert (∀ T3, prim T3 → ty_one_of Trest Tg T3 →
        Powners (Prel n) σ' (delete c Σrest ∪ Σg) T3
          (Crest ∪ Cg ∪ {[c]}, Erest ⊎ Eg)) as Hrec.
      { intros T3 Hp3 Hty3.
        apply (IHrest Crest Erest eq_refl c sc Σg Tg Cg Eg T3 Hlk2 HPg);
          try done; try (by senv_disj); try set_side. }
      destruct Hty as [[-> ->]|[-> ->]].
      * destruct Hty' as [[-> ->]|[-> ->]].
        -- apply (Hcons TUnit); [by left|].
           apply Hrec; [constructor|by left].
        -- apply (Hcons Tt); [by right|]. apply Hrec; [done|by left].
      * apply ty_one_of_unit_inv in Hty' as [-> ->].
        apply (Hcons Tt); [by right|]. apply Hrec; [done|by right].
Qed.
