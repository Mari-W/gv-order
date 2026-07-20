(** Development scratch file for CONNECT (Lemma 3.10); its contents
    are folded back into Compositionality.v once complete. *)

From Coq Require Import Classical.
From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Compositionality.

(** The CONNECT proof runs [set_solver] in very large ambient contexts
    (dozens of [Prel]/[Powners]/map/multiset hypotheses).  [set_solver]'s
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
Ltac set_side :=
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
    | (rewrite dual_involutive; apply Prel_down1; assumption) ].

(** As [connect_prem], but also covers the premises specific to
    [Powners_cons] / [Powners_graft]: the [ty_one_of] disjunction
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
    | (rewrite dual_involutive; apply Prel_down1; assumption) ].

(** Context-independent set identity, used to reconstruct a channel set
    from its post-send residual and the escaped-channel slice without
    letting [set_solver] scan the (large) ambient context. *)
Lemma gset_split_diff_int (X Y : gset chan) : X = (X ∖ Y) ∪ (Y ∩ X).
Proof. apply set_eq. intros x. set_unfold. destruct (decide (x ∈ Y)); tauto. Qed.

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
          (∀ σ, π = PSess σ → subj σ ∉ C2 ∪ {[c]}) → False) as Hlift1.
  { intros π p1' Hstp Hsubj.
    edestruct (proc_step_frame_l C1 E1 (C2 ∪ {[c]}) E2 π p1')
      as (π' & q & Hq); [done|done|].
    apply (Hirr π' q).
    replace (C1 ∪ C2 ∪ {[c]}) with (C1 ∪ (C2 ∪ {[c]})) by set_prune.
    done. }
  assert (∀ π p2', proc_step (C2, E2) π p2' →
          (∀ σ, π = PSess σ → subj σ ∉ C1 ∪ {[c]}) → False) as Hlift2.
  { intros π p2' Hstp Hsubj.
    edestruct (proc_step_frame_l C2 E2 (C1 ∪ {[c]}) E1 π p2')
      as (π' & q & Hq); [done|done|].
    apply (Hirr π' q).
    replace (C1 ∪ C2 ∪ {[c]}) with (C2 ∪ (C1 ∪ {[c]})) by set_prune.
    replace (E1 ⊎ E2) with (E2 ⊎ E1) by multiset_solver.
    done. }
  (* each side can only move, and only on c *)
  assert (∃ σ1 p1', proc_step (C1, E1) (PSess σ1) p1' ∧ subj σ1 = c)
    as (σ1 & p1' & Hst1 & Hsub1c).
  { assert (¬ pirred (C1, E1)) as Hn1.
    { intros Hi1. destruct (Prel_S_irred _ _ _ _ HP1 Hi1)
        as (v & F & _ & _ & HV & _).
      pose proof (Vrel_prim_empty _ _ _ _ Hprim HV) as HΣ.
      exact (insert_non_empty _ _ _ HΣ). }
    apply not_all_ex_not in Hn1 as [π1 Hπ1].
    apply not_all_ex_not in Hπ1 as [p1' Hst1].
    apply NNPP in Hst1.
    destruct π1 as [|σ1].
    { exfalso. eapply Hlift1; [done|]. by intros ? [=]. }
    destruct (decide (subj σ1 = c)) as [?|Hne]; [eauto|].
    exfalso.
    pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1) as Hsub.
    rewrite dom_insert_L in Hsub.
    eapply Hlift1; [done|]. intros σ' [= <-]. set_prune. }
  assert (∃ σ2 p2', proc_step (C2, E2) (PSess σ2) p2' ∧ subj σ2 = c)
    as (σ2 & p2' & Hst2 & Hsub2c).
  { assert (¬ pirred (C2, E2)) as Hn2.
    { intros Hi2. destruct (Prel_S_irred _ _ _ _ HP2 Hi2)
        as (v & F & _ & _ & HV & _).
      apply Vrel_unit_iff in HV as [HΣ _].
      exact (insert_non_empty _ _ _ HΣ). }
    apply not_all_ex_not in Hn2 as [π2 Hπ2].
    apply not_all_ex_not in Hπ2 as [p2' Hst2].
    apply NNPP in Hst2.
    destruct π2 as [|σ2].
    { exfalso. eapply Hlift2; [done|]. by intros ? [=]. }
    destruct (decide (subj σ2 = c)) as [?|Hne]; [eauto|].
    exfalso.
    pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2) as Hsub.
    rewrite dom_insert_L in Hsub.
    eapply Hlift2; [done|]. intros σ' [= <-]. set_prune. }
  (* the two c-actions have matching polarity and synchronize *)
  pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP1 Hb1 Hst1 Hsub1c) as Hsh1.
  pose proof (Prel_cstep_shape _ _ _ _ _ _ _ _ _ HP2 Hb2 Hst2 Hsub2c) as Hsh2.
  apply proc_step_sess_inv in Hst1 as (F1 & e1 & e1' & -> & He1 & _ & _).
  apply proc_step_sess_inv in Hst2 as (F2 & f2 & f2' & -> & Hf2 & _ & _).
  destruct σ1 as [c1 w1|c1 w1|c1], σ2 as [c2 w2|c2 w2|c2];
    simpl in Hsub1c, Hsub2c; subst c1 c2.
  - destruct Hsh1 as (U1 & u1 & ->). destruct Hsh2 as (U2 & u2 & Hd').
    simpl in Hd'. discriminate.
  - (* comp1 receives, comp2 sends *)
    pose proof (tstep_send_val _ _ _ _ Hf2) as Hw2.
    destruct (recv_retarget _ _ _ _ w2 He1 Hw2) as [e1'' He1''].
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ f2 +]}) ⊎ {[+ e1 +]}) by multiset_solver.
    eapply PStepMsg; [exact Hf2|exact He1''|set_solver].
  - destruct Hsh1 as (U1 & u1 & ->). simpl in Hsh2. discriminate.
  - (* comp1 sends, comp2 receives *)
    pose proof (tstep_send_val _ _ _ _ He1) as Hw1.
    destruct (recv_retarget _ _ _ _ w1 Hf2 Hw1) as [f2'' Hf2''].
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ e1 +]}) ⊎ {[+ f2 +]}) by multiset_solver.
    eapply PStepMsg; [exact He1|exact Hf2''|set_solver].
  - destruct Hsh1 as (U1 & u1 & ->). destruct Hsh2 as (U2 & u2 & Hd').
    simpl in Hd'. discriminate.
  - destruct Hsh1 as (U1 & u1 & ->). simpl in Hsh2. discriminate.
  - subst. destruct Hsh2 as (U2 & u2 & Hd'). simpl in Hd'. discriminate.
  - subst. destruct Hsh2 as (U2 & u2 & Hd'). simpl in Hd'. discriminate.
  - (* both close *)
    eapply (Hirr PTau).
    replace ((F1 ⊎ {[+ e1 +]}) ⊎ (F2 ⊎ {[+ f2 +]}))
      with (((F1 ⊎ F2) ⊎ {[+ e1 +]}) ⊎ {[+ f2 +]}) by multiset_solver.
    eapply PStepClose; [exact He1|exact Hf2|set_solver].
Qed.

(** ** The τ cases of CONNECT *)
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
       |(F & d & e & e' & f & f' & Heq & He & Hf & HdC & ->)]]];
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
        apply insert_fresh_inv in HeqΣ as [-> HeqΣ1]; [|done|senv_dom].
        subst Σ1.
        assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C2 ∖ sentc (SRecv c v), F2 ⊎ {[+ f' +]})) as Hsr
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hsr) as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2' & U' & u' & HeqΣ2 & Hcs2 & Hcont2).
        apply insert_fresh_inv in HeqΣ2 as [Hdual HeqΣ2']; [|done|done].
        simpl in Hdual. simplify_eq.
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
        apply insert_fresh_inv in HeqΣ as [Hduals HeqΣ2]; [|done|senv_dom].
        subst Σ2.
        apply ty_one_of_unit_inv in Hty as [-> ->].
        assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C1 ∖ sentc (SRecv c v), F1 ⊎ {[+ f' +]})) as Hsr
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hsr) as Hc1. simpl in Hc1.
        destruct Hc1 as (Σ1' & U' & u' & HeqΣ1 & Hcs1 & Hcont1).
        apply insert_fresh_inv in HeqΣ1 as [Hseq HeqΣ1']; [|done|done].
        subst Σ1'.
        rewrite Hseq in Hduals. simpl in Hduals. simplify_eq.
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
           apply insert_fresh_inv in HeqΣ1 as [-> HeqΣ1x]; [|done|done].
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
           assert (c ∈ dom Σ1) as Hcin by (rewrite HeqΣ1y; senv_dom).
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
           apply insert_fresh_inv in HeqΣ2 as [Hdd' HeqΣ2x]; [|done|done].
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
           assert (c ∈ dom Σ2) as Hcin by (rewrite HeqΣ2y; senv_dom).
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
        apply insert_fresh_inv in HeqΣ1 as [-> HeqΣ1x]; [|done|done].
        subst Σ1x.
        assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ f' +]})) as Hs2'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hs2') as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2x & HeqΣ2 & Hcy & HP2').
        apply insert_fresh_inv in HeqΣ2 as [_ HeqΣ2x]; [|done|done].
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
        apply insert_fresh_inv in HeqΣ1 as [-> HeqΣ1x]; [|done|done].
        subst Σ1x.
        assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ e' +]})) as Hs2'
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hs2') as Hc2. simpl in Hc2.
        destruct Hc2 as (Σ2x & HeqΣ2 & Hcy & HP2').
        apply insert_fresh_inv in HeqΣ2 as [_ HeqΣ2x]; [|done|done].
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
  assert (subj σ ≠ c) as Hsc by set_prune.
  apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
  - (* the acting thread is in E1 *)
    assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess σ)
              (C1 ∖ sentc σ, F1 ⊎ {[+ e' +]})) as Hst1
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hc1.
    destruct σ as [d w|d w|d]; simpl in Hc1, Hsc |- *.
    + (* external receive on d by comp1 *)
      destruct Hc1 as (Σ1x & U & u & HeqΣ & Hcd' & Hcont).
      assert (Σ1 !! d = Some (SRcv U u)) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ1x = <[c:=s]> (delete d Σ1)) as HΣ1x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ1x.
      assert (Σ1 = <[d:=SRcv U u]> (delete d Σ1)) as HΣ1d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ1) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ2) as Hd2' by (apply map_disjoint_dom in Hdd; set_solver).
      exists (delete d Σ1 ∪ Σ2), U, u. split_and!.
      { rewrite HΣ1d at 1. by rewrite insert_union_l. }
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
      destruct Hc1 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                      & T0 & Tw & HeqΣ & Hd0v & Hd0w & Hdvw & Hn0 & Hnv
                      & Hnw & Hdome & Hσed & Hdσe & HpC & HC0w & HpE
                      & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome.
      assert ((Σ0 ∪ Σv ∪ Σw) !! c = Some s) as Hlkc.
      { pose proof (f_equal (λ m, m !! c) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_eq in Hl.
        by rewrite lookup_insert_ne in Hl. }
      assert (Σ1 = <[d:=SSnd U u]> (delete c (Σ0 ∪ Σv ∪ Σw))) as HΣ1.
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
      { rewrite HΣ1, dom_insert_L, dom_delete_L, !dom_union_L. set_prune. }
      rewrite dom_insert_L in Hσed.
      assert (C0 ⊆ C1) as HC01 by set_prune.
      assert (Cw ⊆ C1) as HCw1 by set_prune.
      destruct (ty_one_of_prim _ _ _ Hty Hprim) as [HpT0 HpTw].
      apply lookup_union_Some_raw in Hlkc
        as [Hlk0v|[Hn0v Hlkw]];
        [apply lookup_union_Some_raw in Hlk0v as [Hlk0|[Hc0N Hlkv]]|
         apply lookup_union_None_1 in Hn0v as [Hc0N HcvN]].
      * (* the sender's continuation piece holds c *)
        assert (c ∈ dom Σ0) as Hc0 by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σv) as Hcvd by set_prune.
        assert (c ∉ dom Σw) as Hcwd by set_prune.
        assert (fchans w ## C2 ∪ {[c]}) as Hwc2 by (rewrite Hfw; set_solver).
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
        { rewrite HΣ1, <-insert_union_l. f_equal.
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
        assert (c ∉ dom Σw) as Hcwd by set_prune.
        assert (σe !! c = None) as HσeN
          by (apply not_elem_of_dom; set_solver).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σw c)
          in HΣ1; [|by apply not_elem_of_dom..].
        assert (Powners (Prel n) (<[c := dual s]> σe) (Σ2 ∪ Σw) Tw
                  (C2 ∪ Cw, E2 ⊎ Ew)) as HPw'.
        { eapply Powners_cons with (Td := TUnit); owner_prem. }
        assert (delete c Σv ∪ (dual <$> <[c := dual s]> σe)
                = Σv ∪ (dual <$> σe)) as Hvenv.
        { rewrite fmap_insert, dual_involutive.
          rewrite <-insert_union_r; [|apply lookup_delete_eq].
          rewrite insert_union_l. by rewrite insert_delete_id. }
        eexists Σ0, (delete c Σv), U, u, (<[c := dual s]> σe), (Σ2 ∪ Σw),
          C0, E0, (C2 ∪ Cw), (E2 ⊎ Ew), T0, Tw.
        split_and!.
        { rewrite HΣ1, <-insert_union_l. f_equal.
          rewrite <-(assoc_L (∪) (Σ0 ∪ delete c Σv)).
          rewrite (map_union_comm Σw Σ2); [done|dom_disj]. }
        { by apply map_disjoint_delete_r. }
        { dom_disj. }
        { dom_disj. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { rewrite Hfw. dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
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
        assert (Powners (Prel n) σe (delete c Σw ∪ Σ2) Tw
                  (Cw ∪ C2 ∪ {[c]}, Ew ⊎ E2)) as HPw'.
        { eapply (Powners_graft n IHc σe Σw Tw Cw Ew HPw c s Σ2 TUnit
                    C2 E2 Tw Hlkw); owner_prem. }
        eexists Σ0, Σv, U, u, σe, (delete c Σw ∪ Σ2),
          C0, E0, (Cw ∪ C2 ∪ {[c]}), (Ew ⊎ E2), T0, Tw.
        split_and!.
        { rewrite HΣ1, <-insert_union_l. f_equal.
          by rewrite <-(assoc_L (∪) (Σ0 ∪ Σv)). }
        { done. }
        { dom_disj. }
        { dom_disj. }
        { done. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { multiset_solver. }
        { exact HVw. }
        { exact HP0. }
        { exact HPw'. }
        { exact Hty. }
    + (* external close on d by comp1 *)
      destruct Hc1 as (Σ1x & HeqΣ & Hcd' & Hcont).
      assert (Σ1 !! d = Some SEnd) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ1x = <[c:=s]> (delete d Σ1)) as HΣ1x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ1x.
      assert (Σ1 = <[d:=SEnd]> (delete d Σ1)) as HΣ1d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ1) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ2) as Hd2'
        by (apply map_disjoint_dom in Hdd; set_solver).
      exists (delete d Σ1 ∪ Σ2). split_and!.
      { rewrite HΣ1d at 1. by rewrite insert_union_l. }
      { rewrite dom_union_L, dom_delete_L. set_prune. }
      replace (C1 ∖ ∅) with C1 in Hcont by set_prune.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_prune.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      eapply (IHc _ _ c s); connect_prem.
      eauto using Prel_down1.
  - (* the acting thread is in E2 *)
    assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess σ)
              (C2 ∖ sentc σ, F2 ⊎ {[+ e' +]})) as Hst2
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hc2.
    destruct σ as [d w|d w|d]; simpl in Hc2, Hsc |- *.
    + (* external receive on d by comp2 *)
      destruct Hc2 as (Σ2x & U & u & HeqΣ & Hcd' & Hcont).
      assert (Σ2 !! d = Some (SRcv U u)) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ2x = <[c:=dual s]> (delete d Σ2)) as HΣ2x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ2x.
      assert (Σ2 = <[d:=SRcv U u]> (delete d Σ2)) as HΣ2d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ2) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by (apply map_disjoint_dom in Hdd; set_solver).
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      exists (Σ1 ∪ delete d Σ2), U, u. split_and!.
      { rewrite HΣ2d at 1.
        rewrite <-insert_union_r; [done|by apply not_elem_of_dom]. }
      { dom_solve. }
      intros j Σn Hj Hdn Hcn Hfr HVw. simpl in Hfr.
      apply map_disjoint_dom in Hdn.
      rewrite dom_union_L, dom_delete_L in Hdn.
      specialize (Hcont j Σn Hj ltac:(dom_disj) Hcn
                    ltac:(simpl; set_solver) HVw).
      replace (C2 ∖ ∅) with C2 in Hcont by set_prune.
      rewrite <-insert_union_l, (insert_insert_ne _ d c) in Hcont; [|done].
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_prune.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      rewrite <-(assoc_L (∪) Σ1).
      rewrite insert_union_r; [|by apply not_elem_of_dom].
      eapply (IHcm j Hj _ _ c s); connect_prem.
      eapply Prel_down; [|exact HP1]. lia.
    + (* external send on d by comp2 *)
      destruct Hc2 as (Σ0 & Σv & U & u & σe & Σw & C0 & E0 & Cw & Ew
                      & T0 & Tw & HeqΣ & Hd0v & Hd0w & Hdvw & Hn0 & Hnv
                      & Hnw & Hdome & Hσed & Hdσe & HpC & HC0w & HpE
                      & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome.
      apply ty_one_of_unit_inv in Hty as [-> ->].
      assert ((Σ0 ∪ Σv ∪ Σw) !! c = Some (dual s)) as Hlkc.
      { pose proof (f_equal (λ m, m !! c) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_eq in Hl.
        by rewrite lookup_insert_ne in Hl. }
      assert (Σ2 = <[d:=SSnd U u]> (delete c (Σ0 ∪ Σv ∪ Σw))) as HΣ2.
      { pose proof (f_equal (delete c) HeqΣ) as Hl.
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        rewrite Hl. by rewrite delete_insert_ne. }
      pose proof (Vrel_fchans _ _ _ _ HVw) as Hfw.
      rewrite dom_union_L, dom_fmap_L in Hfw.
      assert (dom σe ⊆ C2) as Hσe2 by (rewrite Hdome; set_solver).
      assert (d ∈ dom Σ2) as Hddom by (rewrite HΣ2; senv_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by (apply map_disjoint_dom in Hdd; set_solver).
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σv) as H0vs by (by apply map_disjoint_dom).
      assert (dom Σ0 ## dom Σw) as H0ws by (by apply map_disjoint_dom).
      assert (dom Σv ## dom Σw) as Hvws by (by apply map_disjoint_dom).
      assert (dom Σ0 ∪ dom Σv ∪ dom Σw ⊆ dom Σ2 ∪ {[c]}) as Hcover.
      { rewrite HΣ2, dom_insert_L, dom_delete_L, !dom_union_L. set_prune. }
      rewrite dom_insert_L in Hσed.
      assert (C0 ⊆ C2) as HC02 by set_prune.
      assert (Cw ⊆ C2) as HCw2 by set_prune.
      apply lookup_union_Some_raw in Hlkc
        as [Hlk0v|[Hn0v Hlkw]];
        [apply lookup_union_Some_raw in Hlk0v as [Hlk0|[Hc0N Hlkv]]|
         apply lookup_union_None_1 in Hn0v as [Hc0N HcvN]].
      * (* the sender's continuation piece holds c *)
        assert (c ∈ dom Σ0) as Hc0 by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σv) as Hcvd by set_prune.
        assert (c ∉ dom Σw) as Hcwd by set_prune.
        assert (fchans w ## C1 ∪ {[c]}) as Hwc1 by (rewrite Hfw; set_solver).
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
        { rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          by rewrite !(assoc_L (∪)). }
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
        { by left. }
      * (* the sent value carries c: comp1 becomes an owner of c *)
        assert (c ∈ dom Σv) as Hcv by (apply elem_of_dom; eauto).
        assert (c ∉ dom Σ0) as Hc0d by (by apply not_elem_of_dom).
        assert (c ∉ dom Σw) as Hcwd by set_prune.
        assert (σe !! c = None) as HσeN
          by (apply not_elem_of_dom; set_solver).
        rewrite !delete_union, (delete_id Σ0 c), (delete_id Σw c)
          in HΣ2; [|by apply not_elem_of_dom..].
        assert (Powners (Prel n) (<[c := s]> σe) (Σ1 ∪ Σw) T
                  (C1 ∪ Cw, E1 ⊎ Ew)) as HPw'.
        { eapply Powners_cons with (Td := T); owner_prem. }
        assert (delete c Σv ∪ (dual <$> <[c := s]> σe)
                = Σv ∪ (dual <$> σe)) as Hvenv.
        { rewrite fmap_insert.
          rewrite <-insert_union_r; [|apply lookup_delete_eq].
          rewrite insert_union_l. by rewrite insert_delete_id. }
        eexists Σ0, (delete c Σv), U, u, (<[c := s]> σe), (Σ1 ∪ Σw),
          C0, E0, (C1 ∪ Cw), (E1 ⊎ Ew), TUnit, T.
        split_and!.
        { rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          rewrite !(assoc_L (∪)). f_equal.
          rewrite (map_union_swap Σ0 (delete c Σv) Σ1); [|dom_disj].
          rewrite (map_union_comm Σ0 Σ1); [done|dom_disj]. }
        { by apply map_disjoint_delete_r. }
        { dom_disj. }
        { dom_disj. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { rewrite Hfw. dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
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
        assert (Powners (Prel n) σe (delete c Σw ∪ Σ1) T
                  (Cw ∪ C1 ∪ {[c]}, Ew ⊎ E1)) as HPw'.
        { eapply (Powners_graft n IHc σe Σw TUnit Cw Ew HPw c (dual s) Σ1 T
                    C1 E1 T Hlkw HP1'); owner_prem. }
        eexists Σ0, Σv, U, u, σe, (delete c Σw ∪ Σ1),
          C0, E0, (Cw ∪ C1 ∪ {[c]}), (Ew ⊎ E1), TUnit, T.
        split_and!.
        { rewrite HΣ2.
          rewrite <-insert_union_r; [|by apply not_elem_of_dom].
          f_equal.
          rewrite (map_union_comm Σ1); [|dom_disj].
          by rewrite !(assoc_L (∪)). }
        { done. }
        { dom_disj. }
        { dom_disj. }
        { done. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { dom_solve. }
        { done. }
        { dom_solve. }
        { dom_solve. }
        { multiset_solver. }
        { exact HVw. }
        { exact HP0. }
        { exact HPw'. }
        { by right. }
    + (* external close on d by comp2 *)
      destruct Hc2 as (Σ2x & HeqΣ & Hcd' & Hcont).
      assert (Σ2 !! d = Some SEnd) as Hlkd.
      { pose proof (f_equal (λ m, m !! d) HeqΣ) as Hl. cbv beta in Hl.
        rewrite lookup_insert_ne in Hl; [|done].
        by rewrite lookup_insert_eq in Hl. }
      assert (Σ2x = <[c:=dual s]> (delete d Σ2)) as HΣ2x.
      { pose proof (f_equal (delete d) HeqΣ) as Hl.
        rewrite delete_insert_ne in Hl; [|done].
        rewrite delete_insert_id in Hl; [|by apply not_elem_of_dom].
        by rewrite <-Hl. }
      subst Σ2x.
      assert (Σ2 = <[d:=SEnd]> (delete d Σ2)) as HΣ2d
        by (by rewrite insert_delete_id).
      assert (d ∈ dom Σ2) as Hddom by (by apply elem_of_dom).
      assert (d ∉ dom Σ1) as Hd1'
        by (apply map_disjoint_dom in Hdd; set_solver).
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      exists (Σ1 ∪ delete d Σ2). split_and!.
      { rewrite HΣ2d at 1.
        rewrite <-insert_union_r; [done|by apply not_elem_of_dom]. }
      { dom_solve. }
      replace (C2 ∖ ∅) with C2 in Hcont by set_prune.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_prune.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      eapply (IHc _ _ c s); connect_prem.
      eauto using Prel_down1.
Qed.

(** ** CONNECT (Lemma 3.10) at successor index *)
Lemma connect_S_proof n (IH : ∀ m, m ≤ n → comp_at m) : connect_at (S n).
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
