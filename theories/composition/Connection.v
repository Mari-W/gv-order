(** * CONNECT (Lemma 3.10)

    Two components that agree on a single channel c, at dual types,
    compose over it. This is the linear-logic cut, and it is where
    almost all the work of the development sits. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Composition.

(** ** CONNECT (Lemma 3.10) *)

Lemma gsingleton_inj (a b : chan) : ({[a]} : gset chan) = {[b]} → a = b.
Proof.
  intros H. assert (a ∈ ({[b]} : gset chan)) as Ha
    by (rewrite <-H; clear; set_solver).
  by apply elem_of_singleton in Ha.
Qed.

(** A transition on the distinguished channel c reveals the polarity
    of c's session type. A forwarding cannot occur here at all: its
    label carries two subjects, so [subjs σ = {[c]}] forces the two
    ends to coincide, and the forwarding clause demands them
    distinct. *)
Lemma Prel_cstep_shape n Σ T C E c s σ p' :
  Prel (S n) (<[c := s]> Σ) T (C, E) → c ∉ dom Σ →
  proc_step (C, E) (PSess σ) p' → subjs σ = {[c]} →
  match σ with
  | SRecv _ _ => ∃ U u, unfoldS s = SRcv U u
  | SSend _ _ => ∃ U u, unfoldS s = SSnd U u
  | SClos _ => unfoldS s = SEnd
  | SLink _ => False
  end.
Proof.
  intros HP Hcd Hst Hsubj.
  pose proof (Prel_S_step _ _ _ _ _ _ HP Hst) as Hc.
  destruct σ as [c' w|c' w|c'|cd]; simpl in Hsubj, Hc.
  - apply gsingleton_inj in Hsubj as ->.
    destruct Hc as (Σ' & U & u & Hhd & Hc' & _).
    apply senv_hd_insert_inv in Hhd as [Hu _]; eauto.
  - apply gsingleton_inj in Hsubj as ->.
    destruct Hc as (Σ0 & Σv & U & u & σe & Σw & ? & ? & ? & ? & ? & ? &
                    Hhd & ? & ? & ? & Hb0 & Hbv & Hbw & _).
    apply senv_hd_insert_inv in Hhd as [Hu _]; [eauto|done|senv_dom].
  - apply gsingleton_inj in Hsubj as ->.
    destruct Hc as (Σ' & Hhd & Hc' & _).
    apply senv_hd_insert_inv in Hhd as [Hu _]; eauto.
  - destruct Hc as (c1 & d1 & Σ1 & sc & sd & -> & Hne & _). apply Hne.
    assert (c1 ∈ ({[c]} : gset chan)) as H1
      by (rewrite <-Hsubj; clear; set_solver).
    assert (d1 ∈ ({[c]} : gset chan)) as H2
      by (rewrite <-Hsubj; clear; set_solver).
    apply elem_of_singleton in H1. apply elem_of_singleton in H2.
    congruence.
Qed.

(** Iterated CONNECT: a process holding the dual ends of a family of
    channels can be connected to the family's owner pieces one by one.
    The receiver's environment grows by each owner's environment as
    the connections are performed. *)
Lemma connect_owners n (IHc : connect_at n) σ Σw Tw Cw Ew :
  Owners (Prel n) σ Σw Tw (Cw, Ew) →
  ∀ Σr Tr Cr Er Tt,
    Prel n (Σr ∪ (dual <$> σ)) Tr (Cr, Er) →
    ty_one_of Tr Tw Tt → prim Tt →
    dom σ ## dom Σr → dom σ ## Cr →
    Σw ##ₘ Σr → Cw ## Cr → Cw ## dom Σr → Cr ## dom Σw →
    Cr ## dom Σr → Cw ## dom Σw →
    Prel n (Σr ∪ Σw) Tt (Cr ∪ Cw ∪ dom σ, Er ⊎ Ew).
Proof.
  intros HPo. remember (Cw, Ew) as pw eqn:Hpw.
  revert Cw Ew Hpw.
  induction HPo as [|σ' d sd Σd Σrest Td Trest Tw' Cd Ed Crest Erest
                     Hσd Hdd1 Hdd2 Hdd3 Hdd4 Hdd5 Hdd6 Hdd7 Hdd8 Hdd9
                     Hdd10 HPd HPrest IHrest Hty'];
    intros Cw Ew Hpw; simplify_eq;
    intros Σr Tr Cr Er Tt HPr Hty Hprim Hdσr Hdσc Hdw Hcwcr Hcwdr Hcrdw
      Hsr Hsw.
  - (* empty family *)
    assert (Tt = Tr) as -> by (destruct Hty as [[-> _]|[-> <-]]; done).
    rewrite fmap_empty, (right_id ∅ (∪)) in HPr.
    replace (Σr ∪ ∅) with Σr by (by rewrite (right_id ∅ (∪))).
    replace (Cr ∪ ∅ ∪ dom (∅ : gmap chan sty)) with Cr
      by (rewrite dom_empty_L; set_solver).
    by replace (Er ⊎ ∅) with Er by multiset_solver.
  - (* connect the head owner over d, then recurse *)
    rewrite fmap_insert in HPr.
    assert (d ∉ dom (dual <$> σ')) as Hdfσ.
    { rewrite dom_fmap_L. by apply not_elem_of_dom. }
    assert (Σr ##ₘ (dual <$> σ')) as Hdrσ.
    { apply map_disjoint_dom_2. rewrite dom_fmap_L.
      rewrite dom_insert_L in Hdσr. set_solver. }
    assert (Σd ##ₘ (dual <$> σ')) as Hddσ.
    { apply map_disjoint_dom_2. rewrite dom_fmap_L. done. }
    replace (Σr ∪ <[d:=dual sd]> (dual <$> σ'))
      with (<[d:=dual sd]> (Σr ∪ (dual <$> σ')) ) in HPr by senv_perm.
    rewrite dom_insert_L in Hdσr, Hdσc.
    (* facts used by every orientation *)
    assert (d ∉ dom (Σr ∪ (dual <$> σ'))) as Hdnr.
    { rewrite dom_union_L, dom_fmap_L. apply not_elem_of_dom in Hσd.
      set_solver. }
    apply not_elem_of_dom in Hσd.
    rewrite dom_fmap_L in Hdfσ.
    (* recurse over the remaining owners *)
    assert (∀ T2, ty_one_of T2 Trest Tt →
             Prel n ((Σr ∪ Σd) ∪ (dual <$> σ')) T2
               (Cr ∪ Cd ∪ {[d]}, Er ⊎ Ed) →
             Prel n (Σr ∪ (Σd ∪ Σrest)) Tt
               (Cr ∪ (Cd ∪ Crest) ∪ dom (<[d:=sd]> σ'), Er ⊎ (Ed ⊎ Erest)))
      as Hrec.
    { intros T2 Hty2 HP2'.
      replace (Σr ∪ (Σd ∪ Σrest)) with ((Σr ∪ Σd) ∪ Σrest) by senv_perm.
      replace (Cr ∪ (Cd ∪ Crest) ∪ dom (<[d:=sd]> σ'))
        with ((Cr ∪ Cd ∪ {[d]}) ∪ Crest ∪ dom σ')
        by (rewrite dom_insert_L; set_solver).
      replace (Er ⊎ (Ed ⊎ Erest)) with ((Er ⊎ Ed) ⊎ Erest)
        by multiset_solver.
      eapply (IHrest Crest Erest eq_refl);
        [ exact HP2' | exact Hty2 | exact Hprim
        | first [ by senv_disj | by set_solver ] .. ]. }
    destruct Hty as [[-> HTw']|[-> HTw']].
    + (* the receiver carries the type *)
      subst Tw'. apply ty_one_of_unit_inv in Hty' as [-> ->].
      eapply Hrec; [by left|].
      replace ((Σr ∪ Σd) ∪ (dual <$> σ'))
        with ((Σr ∪ (dual <$> σ')) ∪ Σd) by senv_perm.
      apply (IHc (Σr ∪ (dual <$> σ')) Σd d (dual sd) Cr Er Cd Ed Tt
               Hprim);
        [ senv_disj | done | done
        | set_solver | set_solver | set_solver | set_solver
        | set_solver | set_solver | set_solver
        | exact HPr | ].
      rewrite dual_involutive. exact HPd.
    + (* the family carries the type *)
      subst Tw'. destruct Hty' as [[-> ->]|[-> ->]].
      * (* ... the head owner does *)
        eapply Hrec; [by left|].
        replace ((Σr ∪ Σd) ∪ (dual <$> σ'))
          with (Σd ∪ (Σr ∪ (dual <$> σ'))) by senv_perm.
        replace (Cr ∪ Cd ∪ {[d]}) with (Cd ∪ Cr ∪ {[d]}) by set_solver.
        replace (Er ⊎ Ed) with (Ed ⊎ Er) by multiset_solver.
        apply (IHc Σd (Σr ∪ (dual <$> σ')) d sd Cd Ed Cr Er Tt Hprim);
          [ senv_disj | done | done
          | set_solver | set_solver | set_solver | set_solver
          | set_solver | set_solver | set_solver
          | exact HPd | exact HPr ].
      * (* ... an owner in the tail does *)
        eapply Hrec; [by right|].
        replace ((Σr ∪ Σd) ∪ (dual <$> σ'))
          with ((Σr ∪ (dual <$> σ')) ∪ Σd) by senv_perm.
        apply (IHc (Σr ∪ (dual <$> σ')) Σd d (dual sd) Cr Er Cd Ed TUnit
                 prim_unit);
          [ senv_disj | done | done
          | set_solver | set_solver | set_solver | set_solver
          | set_solver | set_solver | set_solver
          | exact HPr | ].
      rewrite dual_involutive. exact HPd.
Qed.

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

(** Connecting an external piece into the (unique) owner piece whose
    environment contains a given channel c ∈ dom Σw. The family keeps
    its channels; the grafted piece's C, E and environment merge into
    the affected entry. *)
Lemma Owners_graft n (IHc : connect_at n) σ Σw Tw Cw Ew :
  Owners (Prel n) σ Σw Tw (Cw, Ew) →
  ∀ c sc Σg Tg Cg Eg Tt,
    Σw !! c = Some sc →
    Prel n (<[c := dual sc]> Σg) Tg (Cg, Eg) →
    ty_one_of Tw Tg Tt → prim Tt →
    Σg ##ₘ Σw → dom σ ## dom Σg → dom σ ## Cg → c ∉ dom Σg → c ∉ Cg →
    Cw ## Cg → Cw ## dom Σg → Cg ## dom Σw → Cw ## dom Σw → Cg ## dom Σg →
    Owners (Prel n) σ (delete c Σw ∪ Σg) Tt (Cw ∪ Cg ∪ {[c]}, Ew ⊎ Eg).
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
        Owners (Prel n) (<[d:=sd]> σ') (delete c (Σd ∪ Σrest) ∪ Σg) Tt
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
        eapply Owners_cons with (Td := T2); try done;
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
        Owners (Prel n) σ' (delete c Σrest ∪ Σg) T3
          (Crest ∪ Cg ∪ {[c]}, Erest ⊎ Eg) →
        Owners (Prel n) (<[d:=sd]> σ') (delete c (Σd ∪ Σrest) ∪ Σg) Tt
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
        eapply Owners_cons with (Td := Td); try done;
          try (by senv_disj); try set_side. }
      assert (∀ T3, prim T3 → ty_one_of Trest Tg T3 →
        Owners (Prel n) σ' (delete c Σrest ∪ Σg) T3
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

(** The CONNECT proof runs [set_solver] in very large ambient contexts
    (dozens of [Prel]/[Owners]/map/multiset hypotheses).  [set_solver]'s
    [naive_solver] scales badly with the number of hypotheses, so before
    every set goal we prune the context to the set-shaped hypotheses that
    can actually contribute.  [prune_drop_neq] keeps membership /
    disjointness / inclusion / gset-equality hypotheses; [prune_keep_neq]
    additionally keeps disequalities (needed to refute the polarity-clash
    and progress contradictions). *)
(** Materialize the domain-level disjointness carried by every map
    disjointness hypothesis, so it survives context pruning and can feed
    [set_solver] (which does not understand [##ₘ] directly). *)
Ltac mapdisj_to_dom :=
  repeat match goal with
  | H : _ ##ₘ _ |- _ => apply map_disjoint_dom in H
  end.
Ltac prune_drop_neq :=
  mapdisj_to_dom;
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ ## _ => fail
      | _ ⊆ _ => fail
      | @eq (gset _) _ _ => fail
      | _ => clear H
      end
  end.
Ltac prune_keep_neq :=
  mapdisj_to_dom;
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ ## _ => fail
      | _ ⊆ _ => fail
      | _ ≠ _ => fail
      | @eq (gset _) _ _ => fail
      | _ => clear H
      end
  end.
Ltac dom_norm :=
  rewrite ?dom_insert_L, ?dom_delete_L, ?dom_union_L, ?dom_fmap_L,
    ?dom_singleton_L, ?dom_empty_L.

(** Map disjointness via domains, then a pruned [set_solver]. *)
Ltac dom_disj :=
  apply map_disjoint_dom_2; prune_drop_neq; dom_norm; set_solver.

(** Any set goal (membership, disjointness, inclusion, gset-equality),
    context-pruned. *)
Ltac dom_solve :=
  prune_drop_neq; dom_norm; set_solver.

(** As [dom_solve] but guarded: succeeds only on set-relation goals and
    fails cleanly on any other goal shape, so it is safe to offer as one
    alternative among several (e.g. inside [connect_prem]). *)
Ltac set_side ::=
  lazymatch goal with
  | |- _ ∈ _ => idtac
  | |- _ ∉ _ => idtac
  | |- _ ## _ => idtac
  | |- _ ⊆ _ => idtac
  | |- _ => fail
  end;
  prune_drop_neq; dom_norm; set_solver.

(** Close a goal (including [False] / disequality goals) whose proof may
    hinge on a channel disequality, context-pruned but keeping [≠]. *)
Ltac set_prune :=
  prune_keep_neq; dom_norm; set_solver.

(** Discharge, per goal, any premise left by [eapply (IHc ...)] /
    [eapply (IHcm ...)] applying the CONNECT induction hypothesis:
    hypotheses ([assumption]), map-disjointness ([dom_disj]), the two
    [Prel] premises (possibly after peeling a [dual (dual _)] or a
    step-index via [Prel_down1]), and the set side-conditions
    ([set_side]).  Leaves any goal it cannot close (no spurious error),
    so a genuine gap surfaces as an unfinished goal rather than a
    diverging or crashing tactic. *)
Ltac connect_prem :=
  try solve
    [ assumption
    | dom_disj
    | set_side
    | (rewrite dual_involutive; assumption)
    | (apply Prel_down1; assumption)
    | (rewrite dual_involutive; apply Prel_down1; assumption)
    | (lazymatch goal with |- context [echans] => idtac end;
       rewrite ?echans_disj_union, ?echans_singleton in * ; set_solver) ].

(** As [connect_prem], but also covers the premises specific to
    [Owners_cons] / [Owners_graft]: the [ty_one_of] disjunction
    ([by left] / [by right]) and lookup-is-[None] side-conditions
    (rephrased as [∉ dom]). *)
Ltac owner_prem :=
  try solve
    [ done
    | assumption
    | (by left)
    | (by right)
    | dom_disj
    | set_side
    | (apply not_elem_of_dom; set_side)
    | (rewrite dual_involutive; assumption)
    | (apply Prel_down1; assumption)
    | (rewrite dual_involutive; apply Prel_down1; assumption)
    | (lazymatch goal with |- context [echans] => idtac end;
       rewrite ?echans_disj_union, ?echans_singleton in * ; set_solver) ].

(** Context-independent set identity, used to reconstruct a channel set
    from its post-send residual and the escaped-channel slice without
    letting [set_solver] scan the (large) ambient context. *)
Lemma gset_split_diff_int (X Y : gset chan) : X = (X ∖ Y) ∪ (Y ∩ X).
Proof. apply set_eq. intros x. set_unfold. destruct (decide (x ∈ Y)); tauto. Qed.

Lemma gset_diff_cover (X Y : gset chan) (c : chan) : X ⊆ (Y ∪ X ∖ {[c]}) ∪ {[c]}.
Proof. intros x Hx. set_unfold. destruct (decide (x = c)); tauto. Qed.

(** Discharge a pure set (in)equality (true by ACI, needing no hypothesis)
    without letting [set_solver] scan the ambient context: clear every
    unused hypothesis first, leaving only the atoms of the goal. *)
Ltac set_pure :=
  repeat match goal with H : _ |- _ => clear H end;
  set_solver.


(** ** Progress: the composition of two connected pieces always has a
    transition, so the irreducibility clause is vacuous. *)
Lemma connect_progress n Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → Σ1 ##ₘ Σ2 → c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel (S n) (<[c := s]> Σ1) T (C1, E1) →
  Prel (S n) (<[c := dual s]> Σ2) TUnit (C2, E2) →
  ¬ pirred (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).
Proof.
  intros Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hirr.
  (* lifting component transitions to the composite *)
  assert (∀ π p1', proc_step (C1, E1) π p1' →
          (∀ σ, π = PSess σ → subjs σ ## C2 ∪ {[c]}) → False) as Hlift1.
  { intros π p1' Hstp Hsubj.
    edestruct (proc_step_frame_l C1 E1 (C2 ∪ {[c]}) E2 π p1')
      as (π' & q & Hq); [done|done|].
    apply (Hirr π' q).
    replace (C1 ∪ C2 ∪ {[c]}) with (C1 ∪ (C2 ∪ {[c]})) by set_prune.
    done. }
  assert (∀ π p2', proc_step (C2, E2) π p2' →
          (∀ σ, π = PSess σ → subjs σ ## C1 ∪ {[c]}) → False) as Hlift2.
  { intros π p2' Hstp Hsubj.
    edestruct (proc_step_frame_l C2 E2 (C1 ∪ {[c]}) E1 π p2')
      as (π' & q & Hq); [done|done|].
    apply (Hirr π' q).
    replace (C1 ∪ C2 ∪ {[c]}) with (C2 ∪ (C1 ∪ {[c]})) by set_prune.
    replace (E1 ⊎ E2) with (E2 ⊎ E1) by multiset_solver.
    done. }
  (* each side can only move, and only on c: any other offer lifts to
     the composite, and a forwarding that merely CONTAINS c fires as
     the composite's internal link step *)
  assert (∃ σ1 p1', proc_step (C1, E1) (PSess σ1) p1' ∧ subjs σ1 = {[c]})
    as (σ1 & p1' & Hst1 & Hsub1c).
  { assert (¬ pirred (C1, E1)) as Hn1.
    { intros Hi1. destruct (Prel_S_irred _ _ _ _ HP1 Hi1)
        as (v & F & _ & _ & HV & _).
      pose proof (Vrel_prim_empty _ _ _ _ Hprim HV) as HΣ.
      exact (insert_non_empty _ _ _ HΣ). }
    destruct (proc_progress (C1, E1)) as [Hi1|(π1 & p1' & Hst1)];
      [by destruct (Hn1 Hi1)|].
    destruct π1 as [|σ1].
    { exfalso. eapply Hlift1; [done|]. by intros ? [=]. }
    destruct (decide (subjs σ1 = {[c]})) as [?|Hne]; [eauto|].
    exfalso.
    pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1) as Hsub.
    rewrite dom_insert_L in Hsub.
    destruct (decide (c ∈ subjs σ1)) as [Hcin|Hcout]; last first.
    { eapply Hlift1; [done|]. intros σ' [= <-]. set_prune. }
    destruct σ1 as [c1 w1|c1 w1|c1|cd1]; simpl in Hcin, Hne;
      try (apply elem_of_singleton in Hcin; congruence).
    apply proc_step_sess_inv in Hst1 as (F1 & e1 & e1' & -> & He1 & _ & _).
    pose proof (tstep_link_shape _ _ _ He1) as (ca & da & ->).
    assert (∃ d', ({[c; d']} : gset chan) = {[ca; da]}) as (d' & Hpair).
    { apply elem_of_union in Hcin as [Hc0|Hc0];
        apply elem_of_singleton in Hc0; subst.
      - by exists da.
      - exists ca. apply upair_comm. }
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ E2) with ((F1 ⊎ E2) ⊎ {[+ e1 +]})
      by multiset_solver.
    eapply (PStepLink _ _ _ c d');
      [rewrite Hpair; exact He1|clear; set_solver]. }
  assert (∃ σ2 p2', proc_step (C2, E2) (PSess σ2) p2' ∧ subjs σ2 = {[c]})
    as (σ2 & p2' & Hst2 & Hsub2c).
  { assert (¬ pirred (C2, E2)) as Hn2.
    { intros Hi2. destruct (Prel_S_irred _ _ _ _ HP2 Hi2)
        as (v & F & _ & _ & HV & _).
      apply Vrel_unit_iff in HV as [HΣ _].
      exact (insert_non_empty _ _ _ HΣ). }
    destruct (proc_progress (C2, E2)) as [Hi2|(π2 & p2' & Hst2)];
      [by destruct (Hn2 Hi2)|].
    destruct π2 as [|σ2].
    { exfalso. eapply Hlift2; [done|]. by intros ? [=]. }
    destruct (decide (subjs σ2 = {[c]})) as [?|Hne]; [eauto|].
    exfalso.
    pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2) as Hsub.
    rewrite dom_insert_L in Hsub.
    destruct (decide (c ∈ subjs σ2)) as [Hcin|Hcout]; last first.
    { eapply Hlift2; [done|]. intros σ' [= <-]. set_prune. }
    destruct σ2 as [c2 w2|c2 w2|c2|cd2]; simpl in Hcin, Hne;
      try (apply elem_of_singleton in Hcin; congruence).
    apply proc_step_sess_inv in Hst2 as (F2 & e2 & e2' & -> & He2 & _ & _).
    pose proof (tstep_link_shape _ _ _ He2) as (ca & da & ->).
    assert (∃ d', ({[c; d']} : gset chan) = {[ca; da]}) as (d' & Hpair).
    { apply elem_of_union in Hcin as [Hc0|Hc0];
        apply elem_of_singleton in Hc0; subst.
      - by exists da.
      - exists ca. apply upair_comm. }
    eapply (Hirr PTau).
    replace (E1 ⊎ (F2 ⊎ {[+ e2 +]})) with ((E1 ⊎ F2) ⊎ {[+ e2 +]})
      by multiset_solver.
    eapply (PStepLink _ _ _ c d');
      [rewrite Hpair; exact He2|clear; set_solver]. }
  (* the two c-actions have matching polarity and synchronize; a
     forwarding cannot have the singleton subject set *)
  pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP1 Hb1 Hst1 Hsub1c) as Hsh1.
  pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP2 Hb2 Hst2 Hsub2c) as Hsh2.
  apply proc_step_sess_inv in Hst1 as (F1 & e1 & e1' & -> & He1 & _ & _).
  apply proc_step_sess_inv in Hst2 as (F2 & f2 & f2' & -> & Hf2 & _ & _).
  destruct σ1 as [c1 w1|c1 w1|c1|cd1]; [ | | |by destruct Hsh1];
    destruct σ2 as [c2 w2|c2 w2|c2|cd2]; try (by destruct Hsh2);
    simpl in Hsub1c, Hsub2c;
    apply gsingleton_inj in Hsub1c; apply gsingleton_inj in Hsub2c;
    subst c1 c2.
  - destruct Hsh1 as (U1 & u1 & Hu1). destruct Hsh2 as (U2 & u2 & Hd').
    rewrite (unfoldS_dual_rcv _ _ _ Hu1) in Hd'. discriminate.
  - (* comp1 receives, comp2 sends *)
    pose proof (tstep_send_val _ _ _ _ Hf2) as Hw2.
    destruct (recv_retarget _ _ _ _ w2 He1 Hw2) as [e1'' He1''].
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ f2 +]}) ⊎ {[+ e1 +]}) by multiset_solver.
    eapply PStepMsg; [exact Hf2|exact He1''|set_solver].
  - destruct Hsh1 as (U1 & u1 & Hu1).
    rewrite (unfoldS_dual_rcv _ _ _ Hu1) in Hsh2. discriminate.
  - (* comp1 sends, comp2 receives *)
    pose proof (tstep_send_val _ _ _ _ He1) as Hw1.
    destruct (recv_retarget _ _ _ _ w1 Hf2 Hw1) as [f2'' Hf2''].
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ e1 +]}) ⊎ {[+ f2 +]}) by multiset_solver.
    eapply PStepMsg; [exact He1|exact Hf2''|set_solver].
  - destruct Hsh1 as (U1 & u1 & Hu1). destruct Hsh2 as (U2 & u2 & Hd').
    rewrite (unfoldS_dual_snd _ _ _ Hu1) in Hd'. discriminate.
  - destruct Hsh1 as (U1 & u1 & Hu1).
    rewrite (unfoldS_dual_snd _ _ _ Hu1) in Hsh2. discriminate.
  - destruct Hsh2 as (U2 & u2 & Hd').
    rewrite (unfoldS_dual_end _ Hsh1) in Hd'. discriminate.
  - destruct Hsh2 as (U2 & u2 & Hd').
    rewrite (unfoldS_dual_end _ Hsh1) in Hd'. discriminate.
  - (* both close *)
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ e1 +]}) ⊎ {[+ f2 +]}) by multiset_solver.
    eapply PStepClose; [exact He1|exact Hf2|set_solver].
Qed.

(** ** The τ cases of CONNECT *)
(** The CONNECT-↔ recombination when the surviving end b is an
    interface channel of the acting component: the actor's residual
    treats c as junk (its clause removed both ends), so the
    retargeting is the junk transport; the passive component first
    junk-renames its b-mentions onto c, after which the transposition
    c ↔ b IS the retargeting ([echswap_echsubst_flip]) and entry
    conversion finishes (docs/link-design.md). *)
Lemma connectx_plink_tail n0 (IHi : independent_at (S n0))
    Σr Σ2 c b (s sb : sty) C1 F1 e' C2 E2 T :
  prim T →
  <[b := sb]> Σr ##ₘ Σ2 →
  c ∉ dom (<[b := sb]> Σr) → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom (<[b := sb]> Σr) →
  C1 ## dom (<[b := sb]> Σr) → C2 ## dom Σ2 →
  b ∉ dom Σr → b ≠ c → b ∉ dom Σ2 →
  unfoldS sb = unfoldS (dual s) →
  Prel (S n0) Σr T (C1, F1 ⊎ {[+ e' +]}) →
  Prel (S (S n0)) (<[c := dual s]> Σ2) TUnit (C2, E2) →
  Prel (S n0) (<[b := sb]> Σr ∪ Σ2) T
    (C1 ∪ C2, echsubst c b ((F1 ⊎ {[+ e' +]}) ⊎ E2)).
Proof.
  intros Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 Hbr Hbc HbΣ2
    Hdub Hcont HP2.
  rewrite dom_insert_L in Hb1, Hd2, Hs1.
  rewrite echsubst_disj_union.
  assert (Prel (S n0) Σr T (C1, echsubst c b (F1 ⊎ {[+ e' +]})))
    as Hcont'.
  { apply Prel_junk_subst;
      [clear -Hb1; set_solver|exact Ha1
      |intros Hb; clear -Hs1 Hb; set_solver|congruence|exact Hcont]. }
  assert (Prel (S n0) (<[c := dual s]> Σ2) TUnit (C2, echsubst b c E2))
    as HP2'.
  { apply Prel_junk_subst;
      [rewrite dom_insert_L; clear -Hbc HbΣ2; set_solver
      |clear -Hd2; set_solver
      |intros Hx; clear -Ha2 Hx; set_solver|congruence
      |by apply Prel_down1]. }
  pose proof (Prel_eswap c b _ _ _ _ HP2') as HQ2.
  rewrite pswap_pair in HQ2.
  rewrite senvswap_insert, cswap_l in HQ2.
  rewrite senvswap_id in HQ2 by set_solver.
  rewrite gswap_id in HQ2 by set_solver.
  rewrite echswap_echsubst_flip in HQ2.
  apply (Prel_entry_conv (S n0) Σ2 b (dual s) sb TUnit
           (C2, echsubst c b E2)) in HQ2; [|by symmetry].
  replace (<[b := sb]> Σr ∪ Σ2) with (Σr ∪ <[b := sb]> Σ2).
  2:{ rewrite <-insert_union_r; [|by apply not_elem_of_dom].
      by rewrite <-insert_union_l. }
  eapply IHi;
    [done| |set_solver| | | | |exact Hcont'|exact HQ2].
  { split; [done|]. apply map_disjoint_dom in Hdd.
    apply map_disjoint_dom. rewrite dom_insert_L in Hdd |- *.
    set_solver. }
  { rewrite dom_insert_L. set_solver. }
  { set_solver. }
  { set_solver. }
  { rewrite dom_insert_L. set_solver. }
Qed.

(** Mirror of [connectx_plink_tail]: the actor is the unit-typed
    component, the T-typed component is transported. *)
Lemma connectx_plink_tail_r n0 (IHi : independent_at (S n0))
    Σr Σ1 c b (s sb : sty) C2 F2 e' C1 E1 T :
  prim T →
  Σ1 ##ₘ <[b := sb]> Σr →
  c ∉ dom Σ1 → c ∉ dom (<[b := sb]> Σr) →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom (<[b := sb]> Σr) → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom (<[b := sb]> Σr) →
  b ∉ dom Σr → b ≠ c → b ∉ dom Σ1 →
  unfoldS sb = unfoldS s →
  Prel (S n0) Σr TUnit (C2, F2 ⊎ {[+ e' +]}) →
  Prel (S (S n0)) (<[c := s]> Σ1) T (C1, E1) →
  Prel (S n0) (Σ1 ∪ <[b := sb]> Σr) T
    (C1 ∪ C2, echsubst c b (E1 ⊎ (F2 ⊎ {[+ e' +]}))).
Proof.
  intros Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 Hbr Hbc HbΣ1
    Hdub Hcont HP1.
  rewrite dom_insert_L in Hb2, Hd1, Hs2.
  rewrite echsubst_disj_union.
  assert (Prel (S n0) Σr TUnit (C2, echsubst c b (F2 ⊎ {[+ e' +]})))
    as Hcont'.
  { apply Prel_junk_subst;
      [clear -Hb2; set_solver|exact Ha2
      |intros Hb; clear -Hs2 Hb; set_solver|congruence|exact Hcont]. }
  assert (Prel (S n0) (<[c := s]> Σ1) T (C1, echsubst b c E1))
    as HP1'.
  { apply Prel_junk_subst;
      [rewrite dom_insert_L; clear -Hbc HbΣ1; set_solver
      |clear -Hd1; set_solver
      |intros Hx; clear -Ha1 Hx; set_solver|congruence
      |by apply Prel_down1]. }
  pose proof (Prel_eswap c b _ _ _ _ HP1') as HQ1.
  rewrite pswap_pair in HQ1.
  rewrite senvswap_insert, cswap_l in HQ1.
  rewrite senvswap_id in HQ1 by set_solver.
  rewrite gswap_id in HQ1 by set_solver.
  rewrite echswap_echsubst_flip in HQ1.
  apply (Prel_entry_conv (S n0) Σ1 b s sb T
           (C1, echsubst c b E1)) in HQ1; [|by symmetry].
  replace (Σ1 ∪ <[b := sb]> Σr) with (<[b := sb]> Σ1 ∪ Σr).
  2:{ rewrite <-insert_union_r; [|by apply not_elem_of_dom].
      rewrite <-insert_union_l. done. }
  eapply IHi;
    [done| |set_solver| | | | |exact HQ1|exact Hcont'].
  { split; [done|]. apply map_disjoint_dom in Hdd.
    apply map_disjoint_dom. rewrite dom_insert_L in Hdd |- *.
    set_solver. }
  { set_solver. }
  { rewrite dom_insert_L. set_solver. }
  { rewrite dom_insert_L. set_solver. }
  { set_solver. }
Qed.

Lemma connect_tau n (IH : ∀ m, m ≤ n → comp_at m)
    Σ1 Σ2 c s C1 E1 C2 E2 T p' :
  prim T → Σ1 ##ₘ Σ2 → c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel (S n) (<[c := s]> Σ1) T (C1, E1) →
  Prel (S n) (<[c := dual s]> Σ2) TUnit (C2, E2) →
  proc_step (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) PTau p' →
  p'.1 ## dom (Σ1 ∪ Σ2) →
  Prel n (Σ1 ∪ Σ2) T p'.
Proof.
  intros Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst Hg.
  assert (independent_at n) as IHi
    by (by destruct (IH n (le_n n)) as (_ & ? & _)).
  assert (connect_at n) as IHc
    by (by destruct (IH n (le_n n)) as (_ & _ & ?)).
  apply proc_step_tau_inv in Hst
    as [(F & e & e' & Heq & He & ->)
       |[(F & e & d & v & e' & Heq & He & HdC & Hde & Hdf & ->)
       |[(F & d & v & e & e' & f & f' & Heq & He & Hf & HdC & ->)
       |[(F & d & e & e' & f & f' & Heq & He & Hf & HdC & ->)
       |(F & e & a & b & e' & Heq & He & HaC & ->)]]]];
    simpl in Hg.
  - (* β *)
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau (C1, F1 ⊎ {[+ e' +]}))
        as Hst1 by (by eapply PStepBeta).
      pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
      specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      eapply IHc; try done. eauto using Prel_down1.
    + assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau (C2, F2 ⊎ {[+ e' +]}))
        as Hst2 by (by eapply PStepBeta).
      pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
      specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      eapply IHc; try done. eauto using Prel_down1.
  - (* fork at fresh d *)
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + rewrite echans_disj_union in Hde.
      assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                (C1 ∪ {[d]}, F1 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]}))
        as Hst1 by (eapply PStepFork; eauto; set_solver).
      pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
      specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
      replace (C1 ∪ C2 ∪ {[c]} ∪ {[d]}) with ((C1 ∪ {[d]}) ∪ C2 ∪ {[c]})
        by set_prune.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]})
        with ((F1 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]}) ⊎ E2)
        by multiset_solver.
      eapply IHc; try done; try set_side. eauto using Prel_down1.
    + rewrite echans_disj_union in Hde.
      assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                (C2 ∪ {[d]}, F2 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]}))
        as Hst2 by (eapply PStepFork; eauto; set_solver).
      pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
      specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
      replace (C1 ∪ C2 ∪ {[c]} ∪ {[d]}) with (C1 ∪ (C2 ∪ {[d]}) ∪ {[c]})
        by set_prune.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]})
        with (E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan d) +]}))
        by multiset_solver.
      eapply IHc; try done; try set_side. eauto using Prel_down1.
  - (* msg at d *)
    apply gmultiset_split_elem_of2 in Heq
      as [(F1 & -> & ->)|[(F2 & -> & ->)
         |[(F1 & F2 & -> & -> & ->)|(F1 & F2 & -> & -> & ->)]]].
    + (* both threads in E1 *)
      destruct (decide (d ∈ C1)) as [HdC1|HdC1].
      * assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst1
          by (by eapply PStepMsg).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
        replace ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with ((F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]}) ⊎ E2) by multiset_solver.
        eapply IHc; try done. eauto using Prel_down1.
      * exfalso.
        assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]})
                  (PSess (SSend d v))
                  (C1 ∖ sentc (SSend d v), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hse.
        { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]}
                  = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        destruct (decide (d = c)) as [->|Hdc].
        -- assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SRecv c v))
                     (C1 ∖ sentc (SRecv c v), (F1 ⊎ {[+ e +]}) ⊎ {[+ f' +]}))
             as Hsr.
           { eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP1 Hb1 Hse eq_refl)
             as (U1 & u1 & Heq1).
           pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP1 Hb1 Hsr eq_refl)
             as (U2 & u2 & Heq2). congruence.
        -- pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hse) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* both threads in E2 *)
      destruct (decide (d ∈ C2)) as [HdC2|HdC2].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C2, F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst2
          by (by eapply PStepMsg).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
        replace ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with (E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) by multiset_solver.
        eapply IHc; try done. eauto using Prel_down1.
      * exfalso.
        assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
                  (PSess (SSend d v))
                  (C2 ∖ sentc (SSend d v), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hse.
        { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]}
                  = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        destruct (decide (d = c)) as [->|Hdc].
        -- assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SRecv c v))
                     (C2 ∖ sentc (SRecv c v), (F2 ⊎ {[+ e +]}) ⊎ {[+ f' +]}))
             as Hsr.
           { eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP2 Hb2 Hse eq_refl)
             as (U1 & u1 & Heq1).
           pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP2 Hb2 Hsr eq_refl)
             as (U2 & u2 & Heq2). congruence.
        -- pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hse) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* sender in E1, receiver in E2 *)
      destruct (decide (d = c)) as [->|Hdc].
      * (* the internal communication over c *)
        assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SSend c v))
                  (C1 ∖ sentc (SSend c v), F1 ⊎ {[+ e' +]})) as Hse
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hse) as Hc1. simpl in Hc1.
        destruct Hc1 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                        & T0 & Tw & HeqΣ & Hd0v & Hd0w & Hdvw & Hc0 & Hcv
                        & Hcw & Hdome & Hσed & Hcσe & HpC & HC0w & HpE
                        & HVw & HP0 & HPw & Hty).
        apply senv_hd_insert_inv in HeqΣ as [Hus HeqΣ1]; [|done|senv_dom].
        subst Σ1.
        assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C2 ∖ sentc (SRecv c v), F2 ⊎ {[+ f' +]})) as Hsr
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hsr) as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2' & U' & u' & HeqΣ2 & Hcs2 & Hcont2).
        apply senv_hd_insert_inv in HeqΣ2 as [Hdual HeqΣ2']; [|done|done].
        rewrite (unfoldS_dual_snd _ _ _ Hus) in Hdual. simplify_eq.
        (* feed the sent value's environment to the receiver *)
        assert (dom σe ⊆ C1) as Hσe1 by (rewrite Hdome; set_solver).
        rewrite dom_insert_L, !dom_union_L in Hσed.
        rewrite !dom_union_L in Hd2, Hs1.
        assert ((Σv ∪ (dual <$> σe)) ##ₘ Σ2') as Hx1.
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_fmap_L.
          apply map_disjoint_dom in Hdd.
          rewrite !dom_union_L in Hdd. set_prune. }
        assert (c ∉ dom (Σv ∪ (dual <$> σe))) as Hx2.
        { rewrite dom_union_L, dom_fmap_L. set_prune. }
        assert (dom (Σv ∪ (dual <$> σe)) ## C2) as Hx3.
        { rewrite dom_union_L, dom_fmap_L. set_prune. }
        pose proof (Vrel_down (S n) n _ _ _ ltac:(lia) HVw) as HVw'.
        specialize (Hcont2 n (Σv ∪ (dual <$> σe)) (le_n n) Hx1 Hx2
                      ltac:(simpl; set_solver) HVw').
        replace (C2 ∖ ∅) with C2 in Hcont2 by set_prune.
        replace (<[c:=dual u]> (Σ2' ∪ (Σv ∪ (dual <$> σe))))
          with ((<[c:=dual u]> (Σ2' ∪ Σv)) ∪ (dual <$> σe)) in Hcont2
          by (by rewrite <-insert_union_l, (assoc_L (∪))).
        (* attach the sender's owner family to the receiver *)
        destruct (ty_one_of_prim _ _ _ Hty Hprim) as [HpT0 HpTw].
        pose proof (connect_owners n IHc _ _ _ _ _ HPw
                      (<[c:=dual u]> (Σ2' ∪ Σv)) TUnit C2 (F2 ⊎ {[+ f' +]})
                      Tw Hcont2) as Hcown.
        rewrite dom_insert_L, dom_union_L in Hcown.
        assert (Prel n ((<[c:=dual u]> (Σ2' ∪ Σv)) ∪ Σw) Tw
                  (C2 ∪ Cw ∪ dom σe, (F2 ⊎ {[+ f' +]}) ⊎ Ew)) as Hrest.
        { apply Hcown; [by right|done|..]; try set_side; try senv_disj. }
        clear Hcown.
        replace ((<[c:=dual u]> (Σ2' ∪ Σv)) ∪ Σw)
          with (<[c:=dual u]> (Σ2' ∪ Σv ∪ Σw)) in Hrest
            by (by rewrite insert_union_l).
        (* connect the sender's continuation over c *)
        simpl in HpC, Hdome.
        assert (C1 = C0 ∪ Cw ∪ dom σe) as HC1eq.
        { rewrite Hdome, <-HpC. apply gset_split_diff_int. }
        assert (Cw ⊆ C1) as HCw1 by set_prune.
        assert (C0 ⊆ C1) as HC01 by set_prune.
        replace (Σ0 ∪ Σv ∪ Σw ∪ Σ2')
          with (Σ0 ∪ (Σ2' ∪ Σv ∪ Σw))
          by (by rewrite !(assoc_L (∪)), (map_union_swap Σ0 Σ2' Σv),
                (map_union_swap (Σ0 ∪ Σv) Σ2' Σw) by senv_disj).
        rewrite HC1eq.
        replace (C0 ∪ Cw ∪ dom σe ∪ C2 ∪ {[c]})
          with (C0 ∪ (C2 ∪ Cw ∪ dom σe) ∪ {[c]}) by set_pure.
        replace ((F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with (E0 ⊎ ((F2 ⊎ {[+ f' +]}) ⊎ Ew)) by multiset_solver.
        destruct Hty as [[-> ->]|[-> ->]].
        -- eapply (IHc _ _ c u); connect_prem.
        -- replace (Σ0 ∪ (Σ2' ∪ Σv ∪ Σw))
             with ((Σ2' ∪ Σv ∪ Σw) ∪ Σ0)
             by (by rewrite (map_union_comm Σ0 (Σ2' ∪ Σv ∪ Σw))
                   by senv_disj).
           replace (C0 ∪ (C2 ∪ Cw ∪ dom σe) ∪ {[c]})
             with ((C2 ∪ Cw ∪ dom σe) ∪ C0 ∪ {[c]}) by set_pure.
           replace (E0 ⊎ ((F2 ⊎ {[+ f' +]}) ⊎ Ew))
             with (((F2 ⊎ {[+ f' +]}) ⊎ Ew) ⊎ E0) by multiset_solver.
           eapply (IHc _ _ c (dual u)); connect_prem.
      * exfalso. destruct (decide (d ∈ C1)) as [HdC1|HdC1].
        -- assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SRecv d v))
                     (C2 ∖ sentc (SRecv d v), F2 ⊎ {[+ f' +]})) as Hsr
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hsr) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
        -- assert (d ∈ C2) as HdC2 by set_prune.
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SSend d v))
                     (C1 ∖ sentc (SSend d v), F1 ⊎ {[+ e' +]})) as Hse
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hse) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* sender in E2, receiver in E1 *)
      destruct (decide (d = c)) as [->|Hdc].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SSend c v))
                  (C2 ∖ sentc (SSend c v), F2 ⊎ {[+ e' +]})) as Hse
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hse) as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                        & T0 & Tw & HeqΣ & Hd0v & Hd0w & Hdvw & Hc0 & Hcv
                        & Hcw & Hdome & Hσed & Hcσe & HpC & HC0w & HpE
                        & HVw & HP0 & HPw & Hty).
        apply senv_hd_insert_inv in HeqΣ as [Hduals HeqΣ2]; [|done|senv_dom].
        subst Σ2.
        apply ty_one_of_unit_inv in Hty as [-> ->].
        assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C1 ∖ sentc (SRecv c v), F1 ⊎ {[+ f' +]})) as Hsr
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hsr) as Hc1. simpl in Hc1.
        destruct Hc1 as (Σ1' & U' & u' & HeqΣ1 & Hcs1 & Hcont1).
        apply senv_hd_insert_inv in HeqΣ1 as [Hseq HeqΣ1']; [|done|done].
        subst Σ1'.
        rewrite (unfoldS_dual_rcv _ _ _ Hseq) in Hduals. simplify_eq.
        (* feed the sent value's environment to the receiver (comp1) *)
        assert (dom σe ⊆ C2) as Hσe2 by (rewrite Hdome; set_solver).
        rewrite dom_insert_L, !dom_union_L in Hσed.
        rewrite !dom_union_L in Hd1, Hs2.
        assert ((Σv ∪ (dual <$> σe)) ##ₘ Σ1) as Hx1.
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_fmap_L.
          apply map_disjoint_dom in Hdd.
          rewrite !dom_union_L in Hdd. set_prune. }
        assert (c ∉ dom (Σv ∪ (dual <$> σe))) as Hx2.
        { rewrite dom_union_L, dom_fmap_L. set_prune. }
        assert (dom (Σv ∪ (dual <$> σe)) ## C1) as Hx3.
        { rewrite dom_union_L, dom_fmap_L. set_prune. }
        pose proof (Vrel_down (S n) n _ _ _ ltac:(lia) HVw) as HVw'.
        specialize (Hcont1 n (Σv ∪ (dual <$> σe)) (le_n n) Hx1 Hx2
                      ltac:(simpl; set_solver) HVw').
        replace (C1 ∖ ∅) with C1 in Hcont1 by set_prune.
        replace (<[c:=u']> (Σ1 ∪ (Σv ∪ (dual <$> σe))))
          with ((<[c:=u']> (Σ1 ∪ Σv)) ∪ (dual <$> σe)) in Hcont1
          by (by rewrite <-insert_union_l, (assoc_L (∪))).
        (* attach comp2's owner family (all unit) to the receiver *)
        pose proof (connect_owners n IHc _ _ _ _ _ HPw
                      (<[c:=u']> (Σ1 ∪ Σv)) T C1 (F1 ⊎ {[+ f' +]})
                      T Hcont1) as Hcown.
        rewrite dom_insert_L, dom_union_L in Hcown.
        assert (Prel n ((<[c:=u']> (Σ1 ∪ Σv)) ∪ Σw) T
                  (C1 ∪ Cw ∪ dom σe, (F1 ⊎ {[+ f' +]}) ⊎ Ew)) as Hrest.
        { apply Hcown; [by left|done|..]; try set_side; try senv_disj. }
        clear Hcown.
        replace ((<[c:=u']> (Σ1 ∪ Σv)) ∪ Σw)
          with (<[c:=u']> (Σ1 ∪ Σv ∪ Σw)) in Hrest
            by (by rewrite insert_union_l).
        simpl in HpC, Hdome.
        assert (C2 = C0 ∪ Cw ∪ dom σe) as HC2eq.
        { rewrite Hdome, <-HpC. apply gset_split_diff_int. }
        assert (Cw ⊆ C2) as HCw2 by set_prune.
        assert (C0 ⊆ C2) as HC02 by set_prune.
        replace (Σ1 ∪ (Σ0 ∪ Σv ∪ Σw))
          with ((Σ1 ∪ Σv ∪ Σw) ∪ Σ0)
          by (by rewrite !(assoc_L (∪)), (map_union_swap (Σ1 ∪ Σv) Σw Σ0),
                (map_union_swap Σ1 Σv Σ0) by senv_disj).
        rewrite HC2eq.
        replace (C1 ∪ (C0 ∪ Cw ∪ dom σe) ∪ {[c]})
          with ((C1 ∪ Cw ∪ dom σe) ∪ C0 ∪ {[c]}) by set_pure.
        replace ((F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with (((F1 ⊎ {[+ f' +]}) ⊎ Ew) ⊎ E0) by multiset_solver.
        eapply (IHc _ _ c u'); connect_prem.
      * exfalso. destruct (decide (d ∈ C2)) as [HdC2|HdC2].
        -- assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SRecv d v))
                     (C1 ∖ sentc (SRecv d v), F1 ⊎ {[+ f' +]})) as Hsr
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hsr) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
        -- assert (d ∈ C1) as HdC1 by set_prune.
           assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SSend d v))
                     (C2 ∖ sentc (SSend d v), F2 ⊎ {[+ e' +]})) as Hse
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hse) as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
  - (* close at d *)
    apply gmultiset_split_elem_of2 in Heq
      as [(F1 & -> & ->)|[(F2 & -> & ->)
         |[(F1 & F2 & -> & -> & ->)|(F1 & F2 & -> & -> & ->)]]].
    + (* both threads in E1 *)
      destruct (decide (d ∈ C1)) as [HdC1|HdC1].
      * assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C1 ∖ {[d]}, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst1
          by (by eapply PStepClose).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[d]})
          with ((C1 ∖ {[d]}) ∪ C2 ∪ {[c]}) by set_prune.
        replace ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with ((F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]}) ⊎ E2) by multiset_solver.
        eapply IHc; try done; try set_side. eauto using Prel_down1.
      * destruct (decide (d = c)) as [->|Hdc].
        -- (* two closers of c inside comp1 *)
           destruct n as [|m]; [apply Prel_0|].
           exfalso.
           assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SClos c))
                     (C1 ∖ sentc (SClos c), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
             as Hs1'.
           { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]}
                     = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hs1') as Hc1.
           simpl in Hc1.
           destruct Hc1 as (Σ1x & HeqΣ1 & Hcx & HPmid).
           apply senv_hd_insert_inv in HeqΣ1 as [_ HeqΣ1x]; [|done|done].
           subst Σ1x.
           replace (C1 ∖ ∅) with C1 in HPmid by set_prune.
           assert (proc_step (C1, (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]})
                     (PSess (SClos c))
                     (C1 ∖ sentc (SClos c), (F1 ⊎ {[+ e' +]}) ⊎ {[+ f' +]}))
             as Hs2'.
           { assert ((F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}
                     = (F1 ⊎ {[+ e' +]}) ⊎ {[+ f +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_S_step _ _ _ _ _ _ HPmid Hs2') as Hc2.
           simpl in Hc2.
           destruct Hc2 as (Σ1y & HeqΣ1y & _).
           assert (c ∈ dom Σ1) as Hcin
             by (rewrite (senv_hd_dom _ _ _ _ HeqΣ1y); set_solver).
           done.
        -- exfalso.
           assert (d ∈ C2) as HdC2 by set_prune.
           assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SClos d))
                     (C1 ∖ sentc (SClos d), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
             as Hs1'.
           { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]}
                     = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hs1') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* both threads in E2 *)
      destruct (decide (d ∈ C2)) as [HdC2|HdC2].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C2 ∖ {[d]}, F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst2
          by (by eapply PStepClose).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[d]})
          with (C1 ∪ (C2 ∖ {[d]}) ∪ {[c]}) by set_prune.
        replace ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with (E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) by multiset_solver.
        eapply IHc; try done; try set_side. eauto using Prel_down1.
      * destruct (decide (d = c)) as [->|Hdc].
        -- destruct n as [|m]; [apply Prel_0|].
           exfalso.
           assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SClos c))
                     (C2 ∖ sentc (SClos c), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
             as Hs1'.
           { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]}
                     = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hs1') as Hc1.
           simpl in Hc1.
           destruct Hc1 as (Σ2x & HeqΣ2 & Hcx & HPmid).
           apply senv_hd_insert_inv in HeqΣ2 as [Hdd' HeqΣ2x]; [|done|done].
           subst Σ2x.
           replace (C2 ∖ ∅) with C2 in HPmid by set_prune.
           assert (proc_step (C2, (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]})
                     (PSess (SClos c))
                     (C2 ∖ sentc (SClos c), (F2 ⊎ {[+ e' +]}) ⊎ {[+ f' +]}))
             as Hs2'.
           { assert ((F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}
                     = (F2 ⊎ {[+ e' +]}) ⊎ {[+ f +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_S_step _ _ _ _ _ _ HPmid Hs2') as Hc2.
           simpl in Hc2.
           destruct Hc2 as (Σ2y & HeqΣ2y & _).
           assert (c ∈ dom Σ2) as Hcin
             by (rewrite (senv_hd_dom _ _ _ _ HeqΣ2y); set_solver).
           done.
        -- exfalso.
           assert (d ∈ C1) as HdC1 by set_prune.
           assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
                     (PSess (SClos d))
                     (C2 ∖ sentc (SClos d), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
             as Hs1'.
           { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]}
                     = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]}) as ->
               by multiset_solver.
             eapply PStepSession; [done|set_solver]. }
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hs1') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* one closer on each side *)
      destruct (decide (d = c)) as [->|Hdc].
      * assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), F1 ⊎ {[+ e' +]})) as Hs1'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hs1') as Hc1. simpl in Hc1.
        destruct Hc1 as (Σ1x & HeqΣ1 & Hcx & HP1').
        apply senv_hd_insert_inv in HeqΣ1 as [_ HeqΣ1x]; [|done|done].
        subst Σ1x.
        assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ f' +]})) as Hs2'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hs2') as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2x & HeqΣ2 & Hcy & HP2').
        apply senv_hd_insert_inv in HeqΣ2 as [_ HeqΣ2x]; [|done|done].
        subst Σ2x.
        replace (C1 ∖ ∅) with C1 in HP1' by set_prune.
        replace (C2 ∖ ∅) with C2 in HP2' by set_prune.
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[c]}) with (C1 ∪ C2) by set_prune.
        replace ((F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with ((F1 ⊎ {[+ e' +]}) ⊎ (F2 ⊎ {[+ f' +]})) by multiset_solver.
        eapply IHi; try done; try (by split).
      * exfalso. destruct (decide (d ∈ C1)) as [HdC1|HdC1].
        -- assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SClos d))
                     (C2 ∖ sentc (SClos d), F2 ⊎ {[+ f' +]})) as Hs2'
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hs2') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
        -- destruct (decide (d ∈ C2)) as [HdC2|HdC2]; [|set_prune].
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SClos d))
                     (C1 ∖ sentc (SClos d), F1 ⊎ {[+ e' +]})) as Hs1'
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hs1') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
    + (* one closer on each side, mirrored *)
      destruct (decide (d = c)) as [->|Hdc].
      * assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), F1 ⊎ {[+ f' +]})) as Hs1'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hs1') as Hc1. simpl in Hc1.
        destruct Hc1 as (Σ1x & HeqΣ1 & Hcx & HP1').
        apply senv_hd_insert_inv in HeqΣ1 as [_ HeqΣ1x]; [|done|done].
        subst Σ1x.
        assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ e' +]})) as Hs2'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hs2') as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2x & HeqΣ2 & Hcy & HP2').
        apply senv_hd_insert_inv in HeqΣ2 as [_ HeqΣ2x]; [|done|done].
        subst Σ2x.
        replace (C1 ∖ ∅) with C1 in HP1' by set_prune.
        replace (C2 ∖ ∅) with C2 in HP2' by set_prune.
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[c]}) with (C1 ∪ C2) by set_prune.
        replace ((F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]})
          with ((F1 ⊎ {[+ f' +]}) ⊎ (F2 ⊎ {[+ e' +]})) by multiset_solver.
        eapply IHi; try done; try (by split).
      * exfalso. destruct (decide (d ∈ C1)) as [HdC1|HdC1].
        -- assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SClos d))
                     (C2 ∖ sentc (SClos d), F2 ⊎ {[+ e' +]})) as Hs2'
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hs2') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
        -- destruct (decide (d ∈ C2)) as [HdC2|HdC2]; [|set_prune].
           assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SClos d))
                     (C1 ∖ sentc (SClos d), F1 ⊎ {[+ f' +]})) as Hs1'
             by (eapply PStepSession; [done|set_solver]).
           pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hs1') as Hsub.
           simpl in Hsub. rewrite dom_insert_L in Hsub. set_prune.
  - (* link: an internal forward of one component, a forward that
       CONSUMES the connect channel (the ↔{c,b} case of §4.5), or a
       forward whose retired end belongs to the sibling — re-oriented
       first so that the actor's component retires its own end.  The
       sibling's copy of the retargeting is the junk transport. *)
    destruct n as [|n0]; [apply Prel_0|].
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + (* actor in E1 *)
      destruct (decide (a = c)) as [->|Hac].
      * (* the forward consumes the connect channel *)
        destruct (decide (b = c)) as [->|Hbc].
        { (* singleton ↔{c}: comp1 offers it, the clause refutes it *)
          exfalso.
          assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SLink {[c; c]}))
                    (C1 ∖ sentc (SLink {[c; c]}), F1 ⊎ {[+ e' +]})) as Hst1.
          { eapply PStepSession; [exact He|]. simpl.
            clear -Ha1. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0 & _).
          apply Hne0.
          assert (c1 ∈ ({[c; c]} : gset chan)) as H1
            by (rewrite Hpair; clear; set_solver).
          assert (d1 ∈ ({[c; c]} : gset chan)) as H2
            by (rewrite Hpair; clear; set_solver).
          clear -H1 H2. set_solver. }
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[c]}) with (C1 ∪ C2) by set_prune.
        replace (F1 ⊎ E2 ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
          by multiset_solver.
        destruct (decide (b ∈ C1)) as [HbC1|HbC1].
        -- (* the surviving end is comp1-restricted: remove it on
              comp1's side instead and transpose the recombination;
              the sibling's b-mentions ride along by the junk
              transport *)
           rewrite upair_comm in He.
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                     (C1 ∖ {[b]}, echsubst b c (F1 ⊎ {[+ e' +]}))) as Hst1
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1.
           simpl in HC1.
           specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
           assert (Prel (S n0) (<[c := dual s]> Σ2) TUnit
                     (C2, echsubst b c E2)) as HP2'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Hd1 HbC1 Hbc; set_solver
               |clear -Hcc HbC1; set_solver
               |intros Hx; clear -Ha2 Hx; set_solver|congruence
               |by apply Prel_down1]. }
           assert (Prel (S n0) (Σ1 ∪ Σ2) T
                     ((C1 ∖ {[b]}) ∪ C2 ∪ {[c]},
                      echsubst b c (F1 ⊎ {[+ e' +]}) ⊎ echsubst b c E2))
             as Hcomb.
           { eapply IHc;
               [done|done|done|done|set_solver|set_solver|done
               |set_solver|done|set_solver|done|exact HC1|exact HP2']. }
           pose proof (Prel_eswap c b _ _ _ _ Hcomb) as HQ.
           rewrite pswap_pair in HQ.
           rewrite senvswap_id in HQ
             by (rewrite dom_union_L; set_solver).
           assert (gswap c b ((C1 ∖ {[b]}) ∪ C2 ∪ {[c]}) = C1 ∪ C2) as HgC.
           { apply set_eq. intros y. rewrite elem_of_gswap'.
             unfold cswap. repeat case_decide; subst; set_solver. }
           rewrite HgC in HQ.
           rewrite msswap_disj_union, !echswap_echsubst_flip in HQ.
           rewrite <-echsubst_disj_union in HQ.
           exact HQ.
        -- destruct (decide (b ∈ dom Σ1)) as [HbΣ1|HbΣ1]; last first.
           { (* b is foreign to comp1, yet comp1's offer clause would
                place it in comp1's interface *)
             exfalso.
             assert (proc_step (C1, F1 ⊎ {[+ e +]})
                       (PSess (SLink {[c; b]}))
                       (C1 ∖ sentc (SLink {[c; b]}), F1 ⊎ {[+ e' +]}))
               as Hst1.
             { eapply PStepSession; [exact He|]. simpl.
               clear -Ha1 HbC1. set_solver. }
             pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl.
             simpl in Hcl.
             destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0
                              & HeqΣ & _).
             assert (b ∈ dom (<[c := s]> Σ1)) as Hbin.
             { assert (b ∈ ({[c1; d1]} : gset chan)) as Hbin'
                 by (rewrite <-Hpair; clear; set_solver).
               rewrite HeqΣ, !dom_insert_L. clear -Hbin'. set_solver. }
             rewrite dom_insert_L in Hbin.
             clear -Hbin Hbc HbΣ1. set_solver. }
           (* the surviving end is a comp1 interface channel: comp1
              offers the forward; comp2 is transported by the junk
              transport and transposition *)
           assert (b ∉ dom Σ2) as HbΣ2
             by (apply map_disjoint_dom in Hdd; set_solver).
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SLink {[c; b]}))
                     (C1 ∖ sentc (SLink {[c; b]}), F1 ⊎ {[+ e' +]}))
             as Hst1.
           { eapply PStepSession; [exact He|]. simpl.
             clear -Ha1 HbC1. set_solver. }
           pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl.
           simpl in Hcl.
           destruct Hcl as (c0 & d0 & Σr & sc0 & sd0 & Hpair & Hne0
                            & HeqΣ & Hc0r & Hd0r & Hdu & Hcont).
           replace (C1 ∖ ∅) with C1 in Hcont by set_prune.
           destruct (upair_eq_inv _ _ _ _ Hpair ltac:(congruence))
             as [[<- <-]|[<- <-]].
           ++ (* orientation ⟨c,b⟩ *)
              pose proof (f_equal (lookup c) HeqΣ) as Hlc.
              rewrite !lookup_insert_eq in Hlc.
              injection Hlc as <-.
              apply (f_equal (delete c)) in HeqΣ.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              rewrite delete_insert_id in HeqΣ
                by (rewrite lookup_insert_ne by congruence;
                    by apply not_elem_of_dom).
              subst Σ1.
              eapply (connectx_plink_tail n0 IHi); eauto.
           ++ (* orientation ⟨b,c⟩: normalize the duality *)
              pose proof (f_equal (lookup c) HeqΣ) as Hlc.
              rewrite lookup_insert_eq, lookup_insert_ne, lookup_insert_eq
                in Hlc by congruence.
              injection Hlc as <-.
              apply (f_equal (delete c)) in HeqΣ.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              rewrite delete_insert_ne in HeqΣ by congruence.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              subst Σ1.
              assert (unfoldS sc0 = unfoldS (dual s)) as Hdub.
              { rewrite <-dual_unfoldS, Hdu, <-dual_unfoldS.
                by rewrite dual_involutive. }
              eapply (connectx_plink_tail n0 IHi); eauto.
      * (* the retired end is a component's restricted name *)
        assert (a ∈ C1 ∪ C2) as HaC'
          by (clear -HaC Hac; set_solver).
        apply elem_of_union in HaC' as [HaC1|HaC2].
        -- (* comp1's own: it steps, the sibling junk-renames a to b *)
           destruct (decide (a = b)) as [<-|Hab].
           { (* degenerate self-forwarding: identity substitution *)
             assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                       (C1 ∖ {[a]}, echsubst a a (F1 ⊎ {[+ e' +]})))
               as Hst1 by (by eapply PStepLink).
             pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1.
             simpl in HC1.
             specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
             replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[a]})
               with ((C1 ∖ {[a]}) ∪ C2 ∪ {[c]}) by set_prune.
             assert (echsubst a a (F1 ⊎ E2 ⊎ {[+ e' +]})
                     = echsubst a a (F1 ⊎ {[+ e' +]}) ⊎ E2) as ->
               by (rewrite !echsubst_refl; multiset_solver).
             eapply IHc;
               [done|done|done|done|set_solver|set_solver|done
               |set_solver|done|set_solver|done|exact HC1
               |eauto using Prel_down1]. }
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                     (C1 ∖ {[a]}, echsubst a b (F1 ⊎ {[+ e' +]}))) as Hst1
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1.
           simpl in HC1.
           specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
           replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[a]})
             with ((C1 ∖ {[a]}) ∪ C2 ∪ {[c]}) by set_prune.
           assert (Prel (S n0) (<[c := dual s]> Σ2) TUnit
                     (C2, echsubst a b E2)) as HP2'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Hac Hd1 HaC1; set_solver
               |clear -Hcc HaC1; set_solver
               |intros Hb; rewrite dom_insert_L;
                clear -Ha2 Hs2 Hb; set_solver
               |congruence
               |by apply Prel_down1]. }
           assert (echsubst a b (F1 ⊎ E2 ⊎ {[+ e' +]})
                   = echsubst a b (F1 ⊎ {[+ e' +]}) ⊎ echsubst a b E2)
             as -> by (rewrite !echsubst_disj_union; multiset_solver).
           eapply IHc;
             [done|done|done|done|set_solver|set_solver|done
             |set_solver|done|set_solver|done|exact HC1|exact HP2'].
        -- (* the sibling's: re-orient so comp1's end is retired *)
           destruct (decide (b ∈ C1)) as [HbC1|HbC1]; last first.
           { (* comp1's offer clause would place a in comp1's
                interface, contradicting C2 ## dom Σ1 *)
             exfalso.
             assert (proc_step (C1, F1 ⊎ {[+ e +]})
                       (PSess (SLink {[a; b]}))
                       (C1 ∖ sentc (SLink {[a; b]}), F1 ⊎ {[+ e' +]}))
               as Hst1.
             { eapply PStepSession; [exact He|]. simpl.
               clear -Hcc HaC2 HbC1. set_solver. }
             pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl.
             simpl in Hcl.
             destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0
                              & HeqΣ & _).
             assert (a ∈ dom (<[c := s]> Σ1)) as Hain.
             { assert (a ∈ ({[c1; d1]} : gset chan)) as Hain'
                 by (rewrite <-Hpair; clear; set_solver).
               rewrite HeqΣ, !dom_insert_L. clear -Hain'. set_solver. }
             rewrite dom_insert_L in Hain.
             clear -Hain Hac Hd2 HaC2. set_solver. }
           apply (Prel_link_orient (S n0) (Σ1 ∪ Σ2) T
                    (C1 ∪ C2 ∪ {[c]}) _ a b);
             [clear -Hcc HaC2 HbC1; set_solver
             |clear -HaC2; set_solver
             |clear -HbC1; set_solver
             |rewrite dom_union_L; clear -Hd2 Hs2 HaC2; set_solver
             |rewrite dom_union_L; clear -Hd1 Hs1 HbC1; set_solver|].
           rewrite upair_comm in He.
           assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                     (C1 ∖ {[b]}, echsubst b a (F1 ⊎ {[+ e' +]}))) as Hst1
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1.
           simpl in HC1.
           specialize (HC1 ltac:(rewrite dom_insert_L; set_solver)).
           replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[b]})
             with ((C1 ∖ {[b]}) ∪ C2 ∪ {[c]}) by set_prune.
           assert (Prel (S n0) (<[c := dual s]> Σ2) TUnit
                     (C2, echsubst b a E2)) as HP2'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Ha1 Hd1 HbC1; set_solver
               |clear -Hcc HbC1; set_solver
               |intros Hb; rewrite dom_insert_L;
                clear -Ha2 Hs2 Hb; set_solver
               |clear -Hcc HaC2 HbC1; set_solver
               |by apply Prel_down1]. }
           assert (echsubst b a (F1 ⊎ E2 ⊎ {[+ e' +]})
                   = echsubst b a (F1 ⊎ {[+ e' +]}) ⊎ echsubst b a E2)
             as -> by (rewrite !echsubst_disj_union; multiset_solver).
           eapply IHc;
             [done|done|done|done|set_solver|set_solver|done
             |set_solver|done|set_solver|done|exact HC1|exact HP2'].
    + (* actor in E2, mirrored *)
      destruct (decide (a = c)) as [->|Hac].
      * destruct (decide (b = c)) as [->|Hbc].
        { exfalso.
          assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SLink {[c; c]}))
                    (C2 ∖ sentc (SLink {[c; c]}), F2 ⊎ {[+ e' +]})) as Hst2.
          { eapply PStepSession; [exact He|]. simpl.
            clear -Ha2. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0 & _).
          apply Hne0.
          assert (c1 ∈ ({[c; c]} : gset chan)) as H1
            by (rewrite Hpair; clear; set_solver).
          assert (d1 ∈ ({[c; c]} : gset chan)) as H2
            by (rewrite Hpair; clear; set_solver).
          clear -H1 H2. set_solver. }
        replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[c]}) with (C1 ∪ C2) by set_prune.
        replace (E1 ⊎ F2 ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
          by multiset_solver.
        destruct (decide (b ∈ C2)) as [HbC2|HbC2].
        -- (* the surviving end is comp2-restricted: flip *)
           rewrite upair_comm in He.
           assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                     (C2 ∖ {[b]}, echsubst b c (F2 ⊎ {[+ e' +]}))) as Hst2
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2.
           simpl in HC2.
           specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
           assert (Prel (S n0) (<[c := s]> Σ1) T
                     (C1, echsubst b c E1)) as HP1'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Hd2 HbC2 Hbc; set_solver
               |clear -Hcc HbC2; set_solver
               |intros Hx; clear -Ha1 Hx; set_solver|congruence
               |by apply Prel_down1]. }
           assert (Prel (S n0) (Σ1 ∪ Σ2) T
                     (C1 ∪ (C2 ∖ {[b]}) ∪ {[c]},
                      echsubst b c E1 ⊎ echsubst b c (F2 ⊎ {[+ e' +]})))
             as Hcomb.
           { eapply IHc;
               [done|done|done|done|set_solver|done|set_solver
               |done|set_solver|done|set_solver|exact HP1'|exact HC2]. }
           pose proof (Prel_eswap c b _ _ _ _ Hcomb) as HQ.
           rewrite pswap_pair in HQ.
           rewrite senvswap_id in HQ
             by (rewrite dom_union_L; set_solver).
           assert (gswap c b (C1 ∪ (C2 ∖ {[b]}) ∪ {[c]}) = C1 ∪ C2) as HgC.
           { apply set_eq. intros y. rewrite elem_of_gswap'.
             unfold cswap. repeat case_decide; subst; set_solver. }
           rewrite HgC in HQ.
           rewrite msswap_disj_union, !echswap_echsubst_flip in HQ.
           rewrite <-echsubst_disj_union in HQ.
           exact HQ.
        -- destruct (decide (b ∈ dom Σ2)) as [HbΣ2|HbΣ2]; last first.
           { exfalso.
             assert (proc_step (C2, F2 ⊎ {[+ e +]})
                       (PSess (SLink {[c; b]}))
                       (C2 ∖ sentc (SLink {[c; b]}), F2 ⊎ {[+ e' +]}))
               as Hst2.
             { eapply PStepSession; [exact He|]. simpl.
               clear -Ha2 HbC2. set_solver. }
             pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl.
             simpl in Hcl.
             destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0
                              & HeqΣ & _).
             assert (b ∈ dom (<[c := dual s]> Σ2)) as Hbin.
             { assert (b ∈ ({[c1; d1]} : gset chan)) as Hbin'
                 by (rewrite <-Hpair; clear; set_solver).
               rewrite HeqΣ, !dom_insert_L. clear -Hbin'. set_solver. }
             rewrite dom_insert_L in Hbin.
             clear -Hbin Hbc HbΣ2. set_solver. }
           assert (b ∉ dom Σ1) as HbΣ1
             by (apply map_disjoint_dom in Hdd; set_solver).
           assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SLink {[c; b]}))
                     (C2 ∖ sentc (SLink {[c; b]}), F2 ⊎ {[+ e' +]}))
             as Hst2.
           { eapply PStepSession; [exact He|]. simpl.
             clear -Ha2 HbC2. set_solver. }
           pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl.
           simpl in Hcl.
           destruct Hcl as (c0 & d0 & Σr & sc0 & sd0 & Hpair & Hne0
                            & HeqΣ & Hc0r & Hd0r & Hdu & Hcont).
           replace (C2 ∖ ∅) with C2 in Hcont by set_prune.
           destruct (upair_eq_inv _ _ _ _ Hpair ltac:(congruence))
             as [[<- <-]|[<- <-]].
           ++ (* orientation ⟨c,b⟩ *)
              pose proof (f_equal (lookup c) HeqΣ) as Hlc.
              rewrite !lookup_insert_eq in Hlc.
              injection Hlc as Hlc.
              apply (f_equal (delete c)) in HeqΣ.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              rewrite delete_insert_id in HeqΣ
                by (rewrite lookup_insert_ne by congruence;
                    by apply not_elem_of_dom).
              subst Σ2.
              assert (unfoldS sd0 = unfoldS s) as Hdub.
              { rewrite <-Hlc, dual_involutive in Hdu. exact Hdu. }
              eapply (connectx_plink_tail_r n0 IHi); eauto.
           ++ (* orientation ⟨b,c⟩ *)
              pose proof (f_equal (lookup c) HeqΣ) as Hlc.
              rewrite lookup_insert_eq, lookup_insert_ne, lookup_insert_eq
                in Hlc by congruence.
              injection Hlc as Hlc.
              apply (f_equal (delete c)) in HeqΣ.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              rewrite delete_insert_ne in HeqΣ by congruence.
              rewrite delete_insert_id in HeqΣ
                by (by apply not_elem_of_dom).
              subst Σ2.
              assert (unfoldS sc0 = unfoldS s) as Hdub.
              { rewrite <-Hlc in Hdu. apply (f_equal dual) in Hdu.
                rewrite !dual_unfoldS, !dual_involutive in Hdu.
                by symmetry. }
              eapply (connectx_plink_tail_r n0 IHi); eauto.
      * assert (a ∈ C1 ∪ C2) as HaC'
          by (clear -HaC Hac; set_solver).
        apply elem_of_union in HaC' as [HaC1|HaC2].
        -- (* the sibling's: re-orient so comp2's end is retired *)
           destruct (decide (b ∈ C2)) as [HbC2|HbC2]; last first.
           { exfalso.
             assert (proc_step (C2, F2 ⊎ {[+ e +]})
                       (PSess (SLink {[a; b]}))
                       (C2 ∖ sentc (SLink {[a; b]}), F2 ⊎ {[+ e' +]}))
               as Hst2.
             { eapply PStepSession; [exact He|]. simpl.
               clear -Hcc HaC1 HbC2. set_solver. }
             pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl.
             simpl in Hcl.
             destruct Hcl as (c1 & d1 & Σr & sc0 & sd0 & Hpair & Hne0
                              & HeqΣ & _).
             assert (a ∈ dom (<[c := dual s]> Σ2)) as Hain.
             { assert (a ∈ ({[c1; d1]} : gset chan)) as Hain'
                 by (rewrite <-Hpair; clear; set_solver).
               rewrite HeqΣ, !dom_insert_L. clear -Hain'. set_solver. }
             rewrite dom_insert_L in Hain.
             clear -Hain Hac Hd1 HaC1. set_solver. }
           apply (Prel_link_orient (S n0) (Σ1 ∪ Σ2) T
                    (C1 ∪ C2 ∪ {[c]}) _ a b);
             [clear -Hcc HaC1 HbC2; set_solver
             |clear -HaC1; set_solver
             |clear -HbC2; set_solver
             |rewrite dom_union_L; clear -Hd1 Hs1 HaC1; set_solver
             |rewrite dom_union_L; clear -Hd2 Hs2 HbC2; set_solver|].
           rewrite upair_comm in He.
           assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                     (C2 ∖ {[b]}, echsubst b a (F2 ⊎ {[+ e' +]}))) as Hst2
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2.
           simpl in HC2.
           specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
           replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[b]})
             with (C1 ∪ (C2 ∖ {[b]}) ∪ {[c]}) by set_prune.
           assert (Prel (S n0) (<[c := s]> Σ1) T
                     (C1, echsubst b a E1)) as HP1'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Ha2 Hd2 HbC2; set_solver
               |clear -Hcc HbC2; set_solver
               |intros Hb; rewrite dom_insert_L;
                clear -Ha1 Hs1 Hb; set_solver
               |clear -Hcc HaC1 HbC2; set_solver
               |by apply Prel_down1]. }
           assert (echsubst b a (E1 ⊎ F2 ⊎ {[+ e' +]})
                   = echsubst b a E1 ⊎ echsubst b a (F2 ⊎ {[+ e' +]}))
             as -> by (rewrite !echsubst_disj_union; multiset_solver).
           eapply IHc;
             [done|done|done|done|set_solver|done|set_solver
             |done|set_solver|done|set_solver|exact HP1'|exact HC2].
        -- (* comp2's own: it steps, the sibling junk-renames a to b *)
           destruct (decide (a = b)) as [<-|Hab].
           { assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                       (C2 ∖ {[a]}, echsubst a a (F2 ⊎ {[+ e' +]})))
               as Hst2 by (by eapply PStepLink).
             pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2.
             simpl in HC2.
             specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
             replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[a]})
               with (C1 ∪ (C2 ∖ {[a]}) ∪ {[c]}) by set_prune.
             assert (echsubst a a (E1 ⊎ F2 ⊎ {[+ e' +]})
                     = E1 ⊎ echsubst a a (F2 ⊎ {[+ e' +]})) as ->
               by (rewrite !echsubst_refl; multiset_solver).
             eapply IHc;
               [done|done|done|done|set_solver|done|set_solver
               |done|set_solver|done|set_solver
               |eauto using Prel_down1|exact HC2]. }
           assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                     (C2 ∖ {[a]}, echsubst a b (F2 ⊎ {[+ e' +]}))) as Hst2
             by (by eapply PStepLink).
           pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2.
           simpl in HC2.
           specialize (HC2 ltac:(rewrite dom_insert_L; set_solver)).
           replace ((C1 ∪ C2 ∪ {[c]}) ∖ {[a]})
             with (C1 ∪ (C2 ∖ {[a]}) ∪ {[c]}) by set_prune.
           assert (Prel (S n0) (<[c := s]> Σ1) T
                     (C1, echsubst a b E1)) as HP1'.
           { apply Prel_junk_subst;
               [rewrite dom_insert_L; clear -Hac Hd2 HaC2; set_solver
               |clear -Hcc HaC2; set_solver
               |intros Hb; rewrite dom_insert_L;
                clear -Ha1 Hs1 Hb; set_solver
               |congruence
               |by apply Prel_down1]. }
           assert (echsubst a b (E1 ⊎ F2 ⊎ {[+ e' +]})
                   = echsubst a b E1 ⊎ echsubst a b (F2 ⊎ {[+ e' +]}))
             as -> by (rewrite !echsubst_disj_union; multiset_solver).
           eapply IHc;
             [done|done|done|done|set_solver|done|set_solver
             |done|set_solver|done|set_solver|exact HP1'|exact HC2].
Qed.

(** ** The external session cases of CONNECT *)
Lemma connect_sess n (IH : ∀ m, m ≤ n → comp_at m)
    Σ1 Σ2 c s C1 E1 C2 E2 T σ p' :
  prim T → Σ1 ##ₘ Σ2 → c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel (S n) (<[c := s]> Σ1) T (C1, E1) →
  Prel (S n) (<[c := dual s]> Σ2) TUnit (C2, E2) →
  proc_step (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) (PSess σ) p' →
  Pcase n (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) (PSess σ) p'.
Proof.
  intros Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst.
  assert (independent_at n) as IHi
    by (by destruct (IH n (le_n n)) as (_ & ? & _)).
  assert (connect_at n) as IHc
    by (by destruct (IH n (le_n n)) as (_ & _ & ?)).
  assert (∀ m, m ≤ n → connect_at m) as IHcm
    by (intros m Hm; by destruct (IH m Hm) as (_ & _ & ?)).
  apply proc_step_sess_inv in Hst as (F & e & e' & Heq & He & Hsub & ->).
  assert (c ∉ subjs σ) as Hsc by set_prune.
  apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
  - (* the acting thread is in E1 *)
    assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess σ)
              (C1 ∖ sentc σ, F1 ⊎ {[+ e' +]})) as Hst1
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hc1.
    destruct σ as [d w|d w|d|cd]; simpl in Hc1, Hsc |- *.
    + (* external receive on d by comp1 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc1 as (Σ1x & U & u & (s1 & HeqΣ & Hu1) & Hcd' & Hcont).
      assert (Σ1 !! d = Some s1) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ1x = <[c:=s]> (delete d Σ1)) as HΣ1x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ1x.
      assert (Σ1 = <[d:=s1]> (delete d Σ1)) as HΣ1d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ1) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ2) as Hd2' by (apply map_disjoint_dom in Hdd; set_solver).
      exists (delete d Σ1 ∪ Σ2), U, u. split_and!.
      { eapply senv_hd_intro; [exact Hu1|].
        rewrite HΣ1d at 1. by rewrite insert_union_l. }
      { rewrite dom_union_L, dom_delete_L. set_prune. }
      intros j Σn Hj Hdn Hcn Hfr HVw. simpl in Hfr.
      apply map_disjoint_dom in Hdn.
      rewrite dom_union_L, dom_delete_L in Hdn.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      specialize (Hcont j Σn Hj ltac:(dom_disj) Hcn
                    ltac:(simpl; set_solver) HVw).
      replace (C1 ∖ ∅) with C1 in Hcont by set_prune.
      rewrite <-insert_union_l, (insert_insert_ne _ d c) in Hcont; [|done].
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_prune.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      rewrite (map_union_swap _ Σ2 Σn); [|dom_disj].
      rewrite insert_union_l.
      eapply (IHcm j Hj _ _ c s); connect_prem.
      eapply Prel_down; [|exact HP2]. lia.
    + (* external send on d by comp1 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc1 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                      & T0 & Tw & (s1 & HeqΣ & Hu1) & Hd0v & Hd0w & Hdvw
                      & Hn0 & Hnv & Hnw & Hdome & Hσed & Hdσe & HpC & HC0w
                      & HpE & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome.
      assert ((Σ0 ∪ Σv ∪ Σw) !! c = Some s) as Hlkc.
      { pose proof (f_equal (λ m, m !! c) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_eq in Hl.
        by rewrite lookup_insert_ne in Hl. }
      assert (Σ1 = <[d:=s1]> (delete c (Σ0 ∪ Σv ∪ Σw))) as HΣ1.
      { pose proof (f_equal (delete c) HeqΣ) as Hl.
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        rewrite Hl. by rewrite delete_insert_ne. }
      pose proof (Vrel_fchans _ _ _ _ HVw) as Hfw.
      rewrite dom_union_L, dom_fmap_L in Hfw.
      assert (dom σe ⊆ C1) as Hσe1 by (rewrite Hdome; set_solver).
      assert (d ∈ dom Σ1) as Hddom by (rewrite HΣ1; senv_dom).
      assert (d ∉ dom Σ2) as Hd2'
        by (apply map_disjoint_dom in Hdd; set_solver).
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σv) as H0vs by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σw) as H0ws by (by apply map_disjoint_dom).
      assert (dom Σv ## dom Σw) as Hvws by (by apply map_disjoint_dom).
      assert (dom Σ0 ∪ dom Σv ∪ dom Σw ⊆ dom Σ1 ∪ {[c]}) as Hcover.
      { rewrite HΣ1, dom_insert_L, dom_delete_L, !dom_union_L.
        apply gset_diff_cover. }
      rewrite dom_insert_L in Hσed.
      assert (C0 ⊆ C1) as HC01 by dom_solve.
      assert (Cw ⊆ C1) as HCw1 by dom_solve.
      destruct (ty_one_of_prim _ _ _ Hty Hprim) as [HpT0 HpTw].
      apply lookup_union_Some_raw in Hlkc
        as [Hlk0v|[Hn0v Hlkw]];
        [apply lookup_union_Some_raw in Hlk0v as [Hlk0|[Hc0N Hlkv]]|
         apply lookup_union_None_1 in Hn0v as [Hc0N HcvN]].
      * (* the sender's continuation piece holds c *)
        assert (c ∈ dom Σ0) as Hc0 by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σv) as Hcvd by dom_solve.
        assert (c ∉ dom Σw) as Hcwd by dom_solve.
        assert (fchans w ## C2 ∪ {[c]}) as Hwc2 by (rewrite Hfw; dom_solve).
        rewrite !delete_union, (delete_id Σv c), (delete_id Σw c)
          in HΣ1; [|by apply not_elem_of_dom..].
        rewrite <-(insert_delete_id Σ0 c s Hlk0) in HP0.
        rewrite (insert_insert_ne _ d c) in HP0; [|done].
        assert (Prel n (<[d:=u]> (delete c Σ0) ∪ Σ2) T0
                  (C0 ∪ C2 ∪ {[c]}, E0 ⊎ E2)) as HPmid.
        { eapply (IHc _ _ c s); connect_prem. }
        rewrite <-insert_union_l in HPmid.
        eexists (delete c Σ0 ∪ Σ2), Σv, U, u, σe, Σw,
          (C0 ∪ C2 ∪ {[c]}), (E0 ⊎ E2), Cw, Ew, T0, Tw.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ1, <-insert_union_l. f_equal.
          rewrite (map_union_swap _ Σw Σ2); [|dom_disj].
          rewrite (map_union_swap _ Σv Σ2); [|dom_disj].
          done. }
        { dom_disj. }
        { dom_disj. }
        { done. }
        { dom_solve. }
        { done. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { multiset_solver. }
        { exact HVw. }
        { exact HPmid. }
        { exact HPw. }
        { exact Hty. }
      * (* the sent value carries c: the peer becomes an owner of c *)
        assert (c ∈ dom Σv) as Hcv by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σ0) as Hc0d by (by apply not_elem_of_dom).
        assert (c ∉ dom Σw) as Hcwd by dom_solve.
        assert (σe !! c = None) as HσeN
          by (apply not_elem_of_dom; dom_solve).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σw c)
          in HΣ1; [|by apply not_elem_of_dom..].
        assert (Owners (Prel n) (<[c := dual s]> σe) (Σ2 ∪ Σw) Tw
                  (C2 ∪ Cw, E2 ⊎ Ew)) as HPw'.
        { eapply Owners_cons with (Td := TUnit); owner_prem. }
        assert (delete c Σv ∪ (dual <$> <[c := dual s]> σe)
                = Σv ∪ (dual <$> σe)) as Hvenv.
        { rewrite fmap_insert, dual_involutive.
          rewrite <-insert_union_r; [|apply lookup_delete_eq].
          rewrite insert_union_l. by rewrite insert_delete_id. }
        eexists Σ0, (delete c Σv), U, u, (<[c := dual s]> σe), (Σ2 ∪ Σw),
          C0, E0, (C2 ∪ Cw), (E2 ⊎ Ew), T0, Tw.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ1, <-insert_union_l. f_equal.
          rewrite <-(assoc_L (∪) (Σ0 ∪ delete c Σv)).
          rewrite (map_union_comm Σw Σ2); [done|dom_disj]. }
        { by apply map_disjoint_delete_r. }
        { apply map_disjoint_dom_2. rewrite dom_union_L.
          clear -Hcover Hdds H0ws Hc0d. set_solver. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds Hvws. set_solver. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { rewrite Hfw. dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { clear -HpC Hfw Hcv Hcover Hd2 Ha2 Hσe1 Hcc. set_solver. }
        { clear -HC0w HC01 Hcc. set_solver. }
        { multiset_solver. }
        { by rewrite Hvenv. }
        { exact HP0. }
        { exact HPw'. }
        { exact Hty. }
      * (* an owner piece holds c: graft the peer into the family *)
        assert (c ∈ dom Σw) as Hcw by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σ0) as Hc0d by (by apply not_elem_of_dom).
        assert (c ∉ dom Σv) as Hcvd by (by apply not_elem_of_dom).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σv c)
          in HΣ1; [|by apply not_elem_of_dom..].
        assert (Owners (Prel n) σe (delete c Σw ∪ Σ2) Tw
                  (Cw ∪ C2 ∪ {[c]}, Ew ⊎ E2)) as HPw'.
        { eapply (Owners_graft n IHc σe Σw Tw Cw Ew HPw c s Σ2 TUnit
                    C2 E2 Tw Hlkw); owner_prem. }
        eexists Σ0, Σv, U, u, σe, (delete c Σw ∪ Σ2),
          C0, E0, (Cw ∪ C2 ∪ {[c]}), (Ew ⊎ E2), T0, Tw.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ1, <-insert_union_l. f_equal.
          by rewrite <-(assoc_L (∪) (Σ0 ∪ Σv)). }
        { done. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds H0ws Hc0d. set_solver. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds Hvws Hcvd. set_solver. }
        { done. }
        { done. }
        { dom_solve. }
        { clear -Hdome Hfw Hcover Hd2 Ha2 Ha1 Hσe1 Hcc Hcvd. set_solver. }
        { dom_solve. }
        { done. }
        { clear -HpC Hfw Hcover Hd2 Ha2 Ha1 Hσe1 Hcc Hcvd. set_solver. }
        { clear -HC0w HC01 Hcc Ha1. set_solver. }
        { multiset_solver. }
        { exact HVw. }
        { exact HP0. }
        { exact HPw'. }
        { exact Hty. }
    + (* external close on d by comp1 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc1 as (Σ1x & (s1 & HeqΣ & Hu1) & Hcd' & Hcont).
      assert (Σ1 !! d = Some s1) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ1x = <[c:=s]> (delete d Σ1)) as HΣ1x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ1x.
      assert (Σ1 = <[d:=s1]> (delete d Σ1)) as HΣ1d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ1) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ2) as Hd2'
        by dom_solve.
      exists (delete d Σ1 ∪ Σ2). split_and!.
      { eapply senv_hd_intro; [exact Hu1|].
        rewrite HΣ1d at 1. by rewrite insert_union_l. }
      { rewrite dom_union_L, dom_delete_L. dom_solve. }
      replace (C1 ∖ ∅) with C1 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      eapply (IHc _ _ c s); connect_prem.
    + (* forwarding offered by comp1: the pair misses the connect
         channel (the composite restricts it), so both ends are
         interface channels of comp1 beside the c-entry, and the
         clause reassembles over the union *)
      destruct Hc1 as (a & b & Σ1a & sa & sb & -> & Hne & HeqΣ & Ha1a
                       & Hb1a & Hdu & Hcont).
      assert (a ≠ c) as Hac by (clear -Hsc; set_solver).
      assert (b ≠ c) as Hbc by (clear -Hsc; set_solver).
      assert (Σ1a !! c = Some s) as Hlk.
      { pose proof (f_equal (lookup c) HeqΣ) as Hlc.
        rewrite lookup_insert_eq, !lookup_insert_ne in Hlc by congruence.
        done. }
      apply (f_equal (delete c)) in HeqΣ.
      rewrite delete_insert_id in HeqΣ by (by apply not_elem_of_dom).
      rewrite !delete_insert_ne in HeqΣ by congruence.
      subst Σ1.
      assert (a ∉ dom Σ2 ∧ b ∉ dom Σ2) as [HaΣ2 HbΣ2].
      { apply map_disjoint_dom in Hdd.
        rewrite !dom_insert_L, dom_delete_L in Hdd. set_solver. }
      exists a, b, (delete c Σ1a ∪ Σ2), sa, sb. split_and!.
      { done. }
      { done. }
      { by rewrite !insert_union_l. }
      { rewrite dom_union_L, dom_delete_L. set_solver. }
      { rewrite dom_union_L, dom_delete_L. set_solver. }
      { done. }
      replace (C1 ∖ ∅) with C1 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      rewrite <-(insert_delete_id Σ1a c s Hlk) in Hcont.
      eapply IHc;
        [done| | |done|done|done|done|done| | |done|exact Hcont
        |eauto using Prel_down1].
      { apply map_disjoint_dom in Hdd.
        apply map_disjoint_dom. rewrite !dom_insert_L in Hdd. set_solver. }
      { rewrite dom_delete_L. set_solver. }
      { clear -Hd2. rewrite !dom_insert_L in Hd2. set_solver. }
      { clear -Hs1. rewrite !dom_insert_L in Hs1. set_solver. }
  - (* the acting thread is in E2 *)
    assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess σ)
              (C2 ∖ sentc σ, F2 ⊎ {[+ e' +]})) as Hst2
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hc2.
    destruct σ as [d w|d w|d|cd]; simpl in Hc2, Hsc |- *.
    + (* external receive on d by comp2 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc2 as (Σ2x & U & u & (s1 & HeqΣ & Hu1) & Hcd' & Hcont).
      assert (Σ2 !! d = Some s1) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ2x = <[c:=dual s]> (delete d Σ2)) as HΣ2x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ2x.
      assert (Σ2 = <[d:=s1]> (delete d Σ2)) as HΣ2d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ2) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by dom_solve.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      exists (Σ1 ∪ delete d Σ2), U, u. split_and!.
      { eapply senv_hd_intro; [exact Hu1|].
        rewrite HΣ2d at 1.
        rewrite <-insert_union_r; [done|by apply not_elem_of_dom]. }
      { dom_solve. }
      intros j Σn Hj Hdn Hcn Hfr HVw. simpl in Hfr.
      apply map_disjoint_dom in Hdn.
      rewrite dom_union_L, dom_delete_L in Hdn.
      specialize (Hcont j Σn Hj ltac:(dom_disj) Hcn
                    ltac:(simpl; set_solver) HVw).
      replace (C2 ∖ ∅) with C2 in Hcont by set_pure.
      rewrite <-insert_union_l, (insert_insert_ne _ d c) in Hcont; [|done].
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      rewrite <-(assoc_L (∪) Σ1).
      rewrite insert_union_r; [|by apply not_elem_of_dom].
      eapply (IHcm j Hj _ _ c s); connect_prem.
      eapply Prel_down; [|exact HP1]. lia.
    + (* external send on d by comp2 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc2 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                      & T0 & Tw & (s1 & HeqΣ & Hu1) & Hd0v & Hd0w & Hdvw
                      & Hn0 & Hnv & Hnw & Hdome & Hσed & Hdσe & HpC & HC0w
                      & HpE & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome.
      apply ty_one_of_unit_inv in Hty as [-> ->].
      assert ((Σ0 ∪ Σv ∪ Σw) !! c = Some (dual s)) as Hlkc.
      { pose proof (f_equal (λ m, m !! c) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_eq in Hl.
        by rewrite lookup_insert_ne in Hl. }
      assert (Σ2 = <[d:=s1]> (delete c (Σ0 ∪ Σv ∪ Σw))) as HΣ2.
      { pose proof (f_equal (delete c) HeqΣ) as Hl.
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        rewrite Hl. by rewrite delete_insert_ne. }
      pose proof (Vrel_fchans _ _ _ _ HVw) as Hfw.
      rewrite dom_union_L, dom_fmap_L in Hfw.
      assert (dom σe ⊆ C2) as Hσe2 by (rewrite Hdome; set_solver).
      assert (d ∈ dom Σ2) as Hddom by (rewrite HΣ2; senv_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by dom_solve.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σv) as H0vs by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σw) as H0ws by (by apply map_disjoint_dom).
      assert (dom Σv ## dom Σw) as Hvws by (by apply map_disjoint_dom).
      assert (dom Σ0 ∪ dom Σv ∪ dom Σw ⊆ dom Σ2 ∪ {[c]}) as Hcover.
      { rewrite HΣ2, dom_insert_L, dom_delete_L, !dom_union_L.
        apply gset_diff_cover. }
      rewrite dom_insert_L in Hσed.
      assert (C0 ⊆ C2) as HC02 by dom_solve.
      assert (Cw ⊆ C2) as HCw2 by dom_solve.
      apply lookup_union_Some_raw in Hlkc
        as [Hlk0v|[Hn0v Hlkw]];
        [apply lookup_union_Some_raw in Hlk0v as [Hlk0|[Hc0N Hlkv]]|
         apply lookup_union_None_1 in Hn0v as [Hc0N HcvN]].
      * (* the sender's continuation piece holds c *)
        assert (c ∈ dom Σ0) as Hc0 by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σv) as Hcvd by dom_solve.
        assert (c ∉ dom Σw) as Hcwd by dom_solve.
        assert (fchans w ## C1 ∪ {[c]}) as Hwc1 by (rewrite Hfw; dom_solve).
        rewrite !delete_union, (delete_id Σv c), (delete_id Σw c)
          in HΣ2; [|by apply not_elem_of_dom..].
        rewrite <-(insert_delete_id Σ0 c (dual s) Hlk0) in HP0.
        rewrite (insert_insert_ne _ d c) in HP0; [|done].
        assert (Prel n (Σ1 ∪ <[d:=u]> (delete c Σ0)) T
                  (C1 ∪ C0 ∪ {[c]}, E1 ⊎ E0)) as HPmid.
        { eapply (IHc _ _ c s); connect_prem. }
        rewrite <-insert_union_r in HPmid; [|by apply not_elem_of_dom].
        eexists (Σ1 ∪ delete c Σ0), Σv, U, u, σe, Σw,
          (C1 ∪ C0 ∪ {[c]}), (E1 ⊎ E0), Cw, Ew, T, TUnit.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          by rewrite !(assoc_L (∪)). }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds H0vs Hcvd. set_solver. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds H0ws Hcwd. set_solver. }
        { done. }
        { dom_solve. }
        { done. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { multiset_solver. }
        { exact HVw. }
        { exact HPmid. }
        { exact HPw. }
        { by left. }
      * (* the sent value carries c: comp1 becomes an owner of c *)
        assert (c ∈ dom Σv) as Hcv by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σ0) as Hc0d by (by apply not_elem_of_dom).
        assert (c ∉ dom Σw) as Hcwd by dom_solve.
        assert (σe !! c = None) as HσeN
          by (apply not_elem_of_dom; dom_solve).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σw c)
          in HΣ2; [|by apply not_elem_of_dom..].
        assert (Owners (Prel n) (<[c := s]> σe) (Σ1 ∪ Σw) T
                  (C1 ∪ Cw, E1 ⊎ Ew)) as HPw'.
        { eapply Owners_cons with (Td := T); owner_prem. }
        assert (delete c Σv ∪ (dual <$> <[c := s]> σe)
                = Σv ∪ (dual <$> σe)) as Hvenv.
        { rewrite fmap_insert.
          rewrite <-insert_union_r; [|apply lookup_delete_eq].
          rewrite insert_union_l. by rewrite insert_delete_id. }
        eexists Σ0, (delete c Σv), U, u, (<[c := s]> σe), (Σ1 ∪ Σw),
          C0, E0, (C1 ∪ Cw), (E1 ⊎ Ew), TUnit, T.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          rewrite !(assoc_L (∪)). f_equal.
          rewrite (map_union_swap Σ0 (delete c Σv) Σ1); [|dom_disj].
          rewrite (map_union_comm Σ0 Σ1);
            [done|apply map_disjoint_dom_2; clear -Hcover Hdds Hc0d; set_solver]. }
        { by apply map_disjoint_delete_r. }
        { apply map_disjoint_dom_2. rewrite dom_union_L.
          clear -Hcover Hdds H0ws Hc0d. set_solver. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds Hvws. set_solver. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { rewrite Hfw. dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { clear -HpC Hfw Hcv Hcover Hd1 Ha1 Hσe2 Hcc. set_solver. }
        { clear -HC0w HC02 Hcc. set_solver. }
        { multiset_solver. }
        { by rewrite Hvenv. }
        { exact HP0. }
        { exact HPw'. }
        { by right. }
      * (* an owner piece holds c: graft comp1 into the family *)
        assert (c ∈ dom Σw) as Hcw by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σ0) as Hc0d by (by apply not_elem_of_dom).
        assert (c ∉ dom Σv) as Hcvd by (by apply not_elem_of_dom).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σv c)
          in HΣ2; [|by apply not_elem_of_dom..].
        assert (Prel n (<[c:=dual (dual s)]> Σ1) T (C1, E1)) as HP1'.
        { rewrite dual_involutive. eauto using Prel_down1. }
        assert (Owners (Prel n) σe (delete c Σw ∪ Σ1) T
                  (Cw ∪ C1 ∪ {[c]}, Ew ⊎ E1)) as HPw'.
        { eapply (Owners_graft n IHc σe Σw TUnit Cw Ew HPw c (dual s) Σ1 T
                    C1 E1 T Hlkw HP1'); owner_prem. }
        eexists Σ0, Σv, U, u, σe, (delete c Σw ∪ Σ1),
          C0, E0, (Cw ∪ C1 ∪ {[c]}), (Ew ⊎ E1), TUnit, T.
        split_and!.
        { eapply senv_hd_intro; [exact Hu1|].
          rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          f_equal.
          rewrite (map_union_comm Σ1);
            [|apply map_disjoint_dom_2; rewrite !dom_union_L, dom_delete_L;
              clear -Hcover Hdds Hc0d Hcvd; set_solver].
          by rewrite !(assoc_L (∪)). }
        { done. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds H0ws Hc0d. set_solver. }
        { apply map_disjoint_dom_2. rewrite dom_union_L, dom_delete_L.
          clear -Hcover Hdds Hvws Hcvd. set_solver. }
        { done. }
        { done. }
        { dom_solve. }
        { clear -Hdome Hfw Hcover Hd1 Ha1 Ha2 Hσe2 Hcc Hcvd. set_solver. }
        { dom_solve. }
        { done. }
        { clear -HpC Hfw Hcover Hd1 Ha1 Ha2 Hσe2 Hcc Hcvd. set_solver. }
        { clear -HC0w HC02 Hcc Ha2. set_solver. }
        { multiset_solver. }
        { exact HVw. }
        { exact HP0. }
        { exact HPw'. }
        { by right. }
    + (* external close on d by comp2 *)
      assert (c ≠ d) as Hcd1 by (clear -Hsc; set_solver).
      assert (d ≠ c) as Hcd2 by congruence.
      destruct Hc2 as (Σ2x & (s1 & HeqΣ & Hu1) & Hcd' & Hcont).
      assert (Σ2 !! d = Some s1) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ2x = <[c:=dual s]> (delete d Σ2)) as HΣ2x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ2x.
      assert (Σ2 = <[d:=s1]> (delete d Σ2)) as HΣ2d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ2) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by dom_solve.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      exists (Σ1 ∪ delete d Σ2). split_and!.
      { eapply senv_hd_intro; [exact Hu1|].
        rewrite HΣ2d at 1.
        rewrite <-insert_union_r; [done|by apply not_elem_of_dom]. }
      { dom_solve. }
      replace (C2 ∖ ∅) with C2 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      eapply (IHc _ _ c s); connect_prem.
    + (* forwarding offered by comp2, mirrored *)
      destruct Hc2 as (a & b & Σ2a & sa & sb & -> & Hne & HeqΣ & Ha2a
                       & Hb2a & Hdu & Hcont).
      assert (a ≠ c) as Hac by (clear -Hsc; set_solver).
      assert (b ≠ c) as Hbc by (clear -Hsc; set_solver).
      assert (Σ2a !! c = Some (dual s)) as Hlk.
      { pose proof (f_equal (lookup c) HeqΣ) as Hlc.
        rewrite lookup_insert_eq, !lookup_insert_ne in Hlc by congruence.
        done. }
      apply (f_equal (delete c)) in HeqΣ.
      rewrite delete_insert_id in HeqΣ by (by apply not_elem_of_dom).
      rewrite !delete_insert_ne in HeqΣ by congruence.
      subst Σ2.
      assert (a ∉ dom Σ1 ∧ b ∉ dom Σ1) as [HaΣ1 HbΣ1].
      { apply map_disjoint_dom in Hdd.
        rewrite !dom_insert_L, dom_delete_L in Hdd. set_solver. }
      exists a, b, (Σ1 ∪ delete c Σ2a), sa, sb. split_and!.
      { done. }
      { done. }
      { rewrite !insert_union_r; [done| |]; by apply not_elem_of_dom. }
      { rewrite dom_union_L, dom_delete_L. set_solver. }
      { rewrite dom_union_L, dom_delete_L. set_solver. }
      { done. }
      replace (C2 ∖ ∅) with C2 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      rewrite <-(insert_delete_id Σ2a c (dual s) Hlk) in Hcont.
      eapply IHc;
        [done| |done| |done|done|done| |done|done| | |exact Hcont].
      { apply map_disjoint_dom in Hdd.
        apply map_disjoint_dom. rewrite !dom_insert_L in Hdd. set_solver. }
      { rewrite dom_delete_L. set_solver. }
      { clear -Hd1. rewrite !dom_insert_L in Hd1. set_solver. }
      { clear -Hs2. rewrite !dom_insert_L in Hs2. set_solver. }
      { eauto using Prel_down1. }
Qed.

(** ** CONNECT (Lemma 3.10) at successor index *)
Lemma connect_S n (IH : ∀ m, m ≤ n → comp_at m) : connect_at (S n).
Proof.
  intros Σ1 Σ2 c s C1 E1 C2 E2 T Hprim Hdd Hb1 Hb2 Hcc Ha1 Ha2 Hd1 Hd2
    Hs1 Hs2 HP1 HP2.
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    exact (connect_progress n Σ1 Σ2 c s C1 E1 C2 E2 T Hprim Hdd Hb1 Hb2
             Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hirr).
  - intros π p' Hst. destruct π as [|σ].
    + exact (connect_tau n IH Σ1 Σ2 c s C1 E1 C2 E2 T p' Hprim Hdd Hb1 Hb2
               Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst).
    + exact (connect_sess n IH Σ1 Σ2 c s C1 E1 C2 E2 T σ p' Hprim Hdd Hb1
               Hb2 Hcc Ha1 Ha2 Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst).
Qed.
