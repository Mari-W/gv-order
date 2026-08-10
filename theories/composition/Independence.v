(** * INDEPENDENT (Lemma 3.9)

    Two components that share no channel compose: every transition of
    the union comes from one side, and the other side is carried along
    unchanged. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Principles.

(** The irreducible case: both components are irreducible, hence
    terminated; the unit side contributes only ∗-threads. *)
Lemma indep_irred n Σ1 Σ2 C1 E1 C2 E2 T :
  Prel (S n) Σ1 T (C1, E1) → Prel (S n) Σ2 TUnit (C2, E2) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  pirred (C1 ∪ C2, E1 ⊎ E2) →
  ∃ v E, (C1 ∪ C2, E1 ⊎ E2) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
         Vrel (S n) (Σ1 ∪ Σ2) T v ∧ (∀ e, e ∈ E → e = EUnit).
Proof.
  intros HP1 HP2 Hd1 Hd2 Hirr.
  assert (pirred (C1, E1)) as Hirr1 by (eapply pirred_split_l; eauto).
  assert (pirred (C2, E2)) as Hirr2 by (eapply pirred_split_r; eauto).
  apply Prel_S_iff in HP1 as (H1 & _).
  destruct (H1 Hirr1) as (v1 & F1 & Heq1 & Hv1 & HV1 & HU1).
  apply Prel_S_iff in HP2 as (H2 & _).
  destruct (H2 Hirr2) as (v2 & F2 & Heq2 & Hv2 & HV2 & HU2).
  simplify_eq.
  apply Vrel_unit_iff in HV2 as [-> ->].
  exists v1, (F1 ⊎ ({[+ EUnit +]} ⊎ F2)). split_and!.
  - f_equal. multiset_solver.
  - done.
  - by rewrite (right_id ∅ (∪) Σ1).
  - intros e He.
    apply gmultiset_elem_of_disj_union in He as [He|He]; [by auto|].
    apply gmultiset_elem_of_disj_union in He as [He|He]; [|by auto].
    apply gmultiset_elem_of_singleton in He. by subst.
Qed.

(** The τ case. Internal steps of one component are propagated by the
    induction hypothesis; cross-component communication contradicts
    the ownership discipline (the partner channel would have to be in
    both a restricted set and the other side's environment). *)
Lemma indep_tau n Σ1 Σ2 C1 E1 C2 E2 T p'
    (IH : independent_at n) :
  prim T → Σ1 ##ₘ Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel (S n) Σ1 T (C1, E1) → Prel (S n) Σ2 TUnit (C2, E2) →
  proc_step (C1 ∪ C2, E1 ⊎ E2) PTau p' →
  p'.1 ## dom (Σ1 ∪ Σ2) →
  Prel n (Σ1 ∪ Σ2) T p'.
Proof.
  intros Hprim Hdd Hcc Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst Hg.
  apply proc_step_tau_inv in Hst
    as [(F & e & e' & Heq & He & ->)
       |[(F & e & c & v & e' & Heq & He & Hc1 & Hce & Hcf & ->)
       |[(F & c & v & e & e' & f & f' & Heq & He & Hf & Hc & ->)
       |[(F & c & e & e' & f & f' & Heq & He & Hf & Hc & ->)
       |(F & e & c & d & e' & Heq & He & Hc & ->)]]]];
    simpl in Hg.
  - (* β *)
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau (C1, F1 ⊎ {[+ e' +]}))
        as Hst1 by (by eapply PStepBeta).
      pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
      specialize (HC1 ltac:(set_solver)).
      assert ((F1 ⊎ E2) ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as ->
        by multiset_solver.
      eapply IH;
        [done|by split|set_solver|set_solver|set_solver|set_solver
        |set_solver
        |eauto using Prel_down1|eauto using Prel_down1].
    + assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau (C2, F2 ⊎ {[+ e' +]}))
        as Hst2 by (by eapply PStepBeta).
      pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
      specialize (HC2 ltac:(set_solver)).
      assert ((E1 ⊎ F2) ⊎ {[+ e' +]} = E1 ⊎ (F2 ⊎ {[+ e' +]})) as ->
        by multiset_solver.
      eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
  - (* fork *)
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + rewrite echans_disj_union in Hce.
      assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                (C1 ∪ {[c]}, F1 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}))
        as Hst1 by (eapply PStepFork; eauto; set_solver).
      pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
      specialize (HC1 ltac:(set_solver)).
      assert (C1 ∪ C2 ∪ {[c]} = (C1 ∪ {[c]}) ∪ C2) as -> by set_solver.
      assert ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}
              = (F1 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}) ⊎ E2) as ->
        by multiset_solver.
      eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
    + rewrite echans_disj_union in Hce.
      assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                (C2 ∪ {[c]}, F2 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}))
        as Hst2 by (eapply PStepFork; eauto; set_solver).
      pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
      specialize (HC2 ltac:(set_solver)).
      assert (C1 ∪ C2 ∪ {[c]} = C1 ∪ (C2 ∪ {[c]})) as -> by set_solver.
      assert ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}
              = E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]})) as ->
        by multiset_solver.
      eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
  - (* msg *)
    apply gmultiset_split_elem_of2 in Heq
      as [(F1 & -> & ->)|[(F2 & -> & ->)
         |[(F1 & F2 & -> & -> & ->)|(F1 & F2 & -> & -> & ->)]]].
    + (* both threads in E1 *)
      destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst1
          by (by eapply PStepMsg).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(set_solver)).
        assert ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}
                = (F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]}) ⊎ E2) as ->
          by multiset_solver.
        eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SSend c v))
                  (C1 ∖ sentc (SSend c v), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst1.
        { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
    + (* both threads in E2 *)
      destruct (decide (c ∈ C2)) as [HcC2|HcC2].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C2, F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst2
          by (by eapply PStepMsg).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(set_solver)).
        assert ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}
                = E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as ->
          by multiset_solver.
        eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SSend c v))
                  (C2 ∖ sentc (SSend c v), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst2.
        { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
    + (* sender in E1, receiver in E2 *)
      exfalso. destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C2 ∖ sentc (SRecv c v), F2 ⊎ {[+ f' +]})) as Hst2
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
      * assert (c ∈ C2) as HcC2 by set_solver.
        assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SSend c v))
                  (C1 ∖ sentc (SSend c v), F1 ⊎ {[+ e' +]})) as Hst1
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
    + (* sender in E2, receiver in E1 *)
      exfalso. destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SSend c v))
                  (C2 ∖ sentc (SSend c v), F2 ⊎ {[+ e' +]})) as Hst2
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
      * assert (c ∈ C2) as HcC2 by set_solver.
        assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SRecv c v))
                  (C1 ∖ sentc (SRecv c v), F1 ⊎ {[+ f' +]})) as Hst1
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
  - (* close *)
    apply gmultiset_split_elem_of2 in Heq
      as [(F1 & -> & ->)|[(F2 & -> & ->)
         |[(F1 & F2 & -> & -> & ->)|(F1 & F2 & -> & -> & ->)]]].
    + destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C1 ∖ {[c]}, F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst1
          by (by eapply PStepClose).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(set_solver)).
        assert ((C1 ∪ C2) ∖ {[c]} = (C1 ∖ {[c]}) ∪ C2) as -> by set_solver.
        assert ((F1 ⊎ E2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}
                = (F1 ⊎ {[+ e' +]} ⊎ {[+ f' +]}) ⊎ E2) as ->
          by multiset_solver.
        eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst1.
        { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
    + destruct (decide (c ∈ C2)) as [HcC2|HcC2].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                  (C2 ∖ {[c]}, F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as Hst2
          by (by eapply PStepClose).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(set_solver)).
        assert ((C1 ∪ C2) ∖ {[c]} = C1 ∪ (C2 ∖ {[c]})) as -> by set_solver.
        assert ((E1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}
                = E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ f' +]})) as ->
          by multiset_solver.
        eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver
            |eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst2.
        { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          eapply PStepSession; [done|set_solver]. }
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
    + exfalso. destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C2, F2 ⊎ {[+ f +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ f' +]})) as Hst2
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
      * assert (c ∈ C2) as HcC2 by set_solver.
        assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), F1 ⊎ {[+ e' +]})) as Hst1
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
    + exfalso. destruct (decide (c ∈ C1)) as [HcC1|HcC1].
      * assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), F2 ⊎ {[+ e' +]})) as Hst2
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP2 Hst2). simpl in *.
        set_solver.
      * assert (c ∈ C2) as HcC2 by set_solver.
        assert (proc_step (C1, F1 ⊎ {[+ f +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), F1 ⊎ {[+ f' +]})) as Hst1
          by (eapply PStepSession; [done|set_solver]).
        pose proof (Prel_sess_subj _ _ _ _ _ _ HP1 Hst1). simpl in *.
        set_solver.
  - (* link: attribution by cases on which side restricts the retired
       end.  The sibling's copy of the retargeting is the junk-renaming
       transport — the sibling neither owns nor restricts either end it
       mentions, except possibly the survivor, which the transport now
       tolerates.  When the actor's component restricts only the
       SURVIVING end, the composite step is first re-oriented
       ([Prel_link_orient]) so that the retired end is the actor's. *)
    apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
    + (* actor in E1 *)
      destruct (decide (c = d)) as [<-|Hcd].
      { (* degenerate self-forwarding: the substitution is the identity *)
        destruct (decide (c ∈ C1)) as [HcC1|HcC1].
        - (* comp1 releases its own name *)
          assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                    (C1 ∖ {[c]}, echsubst c c (F1 ⊎ {[+ e' +]}))) as Hst1
            by (by eapply PStepLink).
          pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
          specialize (HC1 ltac:(clear -Hs1; set_solver)).
          assert ((C1 ∪ C2) ∖ {[c]} = (C1 ∖ {[c]}) ∪ C2) as ->
            by (clear -Hcc HcC1; set_solver).
          assert (echsubst c c (F1 ⊎ E2 ⊎ {[+ e' +]})
                  = echsubst c c (F1 ⊎ {[+ e' +]}) ⊎ E2) as ->
            by (rewrite !echsubst_refl; multiset_solver).
          eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver|exact HC1|eauto using Prel_down1].
        - (* c is the sibling's name: comp1 offers the singleton
             forwarding, which the relation refutes *)
          exfalso.
          assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SLink {[c; c]}))
                    (C1 ∖ sentc (SLink {[c; c]}), F1 ⊎ {[+ e' +]})) as Hst1.
          { eapply PStepSession; [exact He|]. simpl.
            clear -HcC1. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σ1a & sc & sd & Hset & Hne & _).
          apply Hne.
          assert (c1 ∈ ({[c; c]} : gset chan)) as H1
            by (rewrite Hset; clear; set_solver).
          assert (d1 ∈ ({[c; c]} : gset chan)) as H2
            by (rewrite Hset; clear; set_solver).
          clear -H1 H2. set_solver. }
      apply elem_of_union in Hc as [HcC1|HcC2].
      * (* the retired end is comp1's: comp1 steps, the sibling
           junk-renames c to d *)
        assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                  (C1 ∖ {[c]}, echsubst c d (F1 ⊎ {[+ e' +]}))) as Hst1
          by (by eapply PStepLink).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(clear -Hs1; set_solver)).
        assert ((C1 ∪ C2) ∖ {[c]} = (C1 ∖ {[c]}) ∪ C2) as ->
          by (clear -Hcc HcC1; set_solver).
        assert (echsubst c d (F1 ⊎ E2 ⊎ {[+ e' +]})
                = echsubst c d (F1 ⊎ {[+ e' +]}) ⊎ echsubst c d E2) as ->
          by (rewrite !echsubst_disj_union; multiset_solver).
        assert (Prel n Σ2 TUnit (C2, echsubst c d E2)) as HP2'.
        { apply Prel_junk_subst;
            [clear -Hd1 HcC1; set_solver
            |clear -Hcc HcC1; set_solver
            |intros Hb; clear -Hs2 Hb; set_solver
            |clear -Hcd; congruence
            |by apply Prel_down1]. }
        eapply IH;
          [done|by split|set_solver|set_solver|set_solver|set_solver
          |set_solver|exact HC1|exact HP2'].
      * (* the retired end is the sibling's *)
        destruct (decide (d ∈ C1)) as [HdC1|HdC1]; last first.
        { (* both label ends are free for comp1: it offers the
             forwarding, and the clause puts c into dom Σ1 — refuted
             by C2 ## dom Σ1 *)
          exfalso.
          assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess (SLink {[c; d]}))
                    (C1 ∖ sentc (SLink {[c; d]}), F1 ⊎ {[+ e' +]})) as Hst1.
          { eapply PStepSession; [exact He|]. simpl.
            clear -Hcc HcC2 HdC1. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σ1a & sc & sd & Hset & Hne & HeqΣ & _).
          assert (c ∈ dom Σ1) as HcΣ1.
          { assert (c ∈ ({[c1; d1]} : gset chan)) as Hcin
              by (rewrite <-Hset; clear; set_solver).
            subst Σ1. rewrite !dom_insert_L. clear -Hcin. set_solver. }
          clear -HcΣ1 Hd2 HcC2. set_solver. }
        (* c ∈ C2 and d ∈ C1: re-orient so that comp1's end is the
           retired one, then proceed as above with the roles of c and
           d exchanged *)
        apply (Prel_link_orient n (Σ1 ∪ Σ2) T (C1 ∪ C2) _ c d);
          [done
          |clear -HcC2; set_solver
          |clear -HdC1; set_solver
          |rewrite dom_union_L; clear -Hd2 Hs2 HcC2; set_solver
          |rewrite dom_union_L; clear -Hd1 Hs1 HdC1; set_solver|].
        assert (tstep e (LSess (SLink {[d; c]})) e') as He'
          by (rewrite upair_comm; exact He).
        assert (proc_step (C1, F1 ⊎ {[+ e +]}) PTau
                  (C1 ∖ {[d]}, echsubst d c (F1 ⊎ {[+ e' +]}))) as Hst1
          by (by eapply PStepLink).
        pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as HC1. simpl in HC1.
        specialize (HC1 ltac:(clear -Hs1; set_solver)).
        assert ((C1 ∪ C2) ∖ {[d]} = (C1 ∖ {[d]}) ∪ C2) as ->
          by (clear -Hcc HdC1; set_solver).
        assert (echsubst d c (F1 ⊎ E2 ⊎ {[+ e' +]})
                = echsubst d c (F1 ⊎ {[+ e' +]}) ⊎ echsubst d c E2) as ->
          by (rewrite !echsubst_disj_union; multiset_solver).
        assert (Prel n Σ2 TUnit (C2, echsubst d c E2)) as HP2'.
        { apply Prel_junk_subst;
            [clear -Hd1 HdC1; set_solver
            |clear -Hcc HdC1; set_solver
            |intros Hb; clear -Hs2 Hb; set_solver
            |exact Hcd
            |by apply Prel_down1]. }
        eapply IH;
          [done|by split|set_solver|set_solver|set_solver|set_solver
          |set_solver|exact HC1|exact HP2'].
    + (* actor in E2, mirrored *)
      destruct (decide (c = d)) as [<-|Hcd].
      { destruct (decide (c ∈ C2)) as [HcC2|HcC2].
        - assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                    (C2 ∖ {[c]}, echsubst c c (F2 ⊎ {[+ e' +]}))) as Hst2
            by (by eapply PStepLink).
          pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
          specialize (HC2 ltac:(clear -Hs2; set_solver)).
          assert ((C1 ∪ C2) ∖ {[c]} = C1 ∪ (C2 ∖ {[c]})) as ->
            by (clear -Hcc HcC2; set_solver).
          assert (echsubst c c (E1 ⊎ F2 ⊎ {[+ e' +]})
                  = E1 ⊎ echsubst c c (F2 ⊎ {[+ e' +]})) as ->
            by (rewrite !echsubst_refl; multiset_solver).
          eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver|eauto using Prel_down1|exact HC2].
        - exfalso.
          assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SLink {[c; c]}))
                    (C2 ∖ sentc (SLink {[c; c]}), F2 ⊎ {[+ e' +]})) as Hst2.
          { eapply PStepSession; [exact He|]. simpl.
            clear -HcC2. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σ2a & sc & sd & Hset & Hne & _).
          apply Hne.
          assert (c1 ∈ ({[c; c]} : gset chan)) as H1
            by (rewrite Hset; clear; set_solver).
          assert (d1 ∈ ({[c; c]} : gset chan)) as H2
            by (rewrite Hset; clear; set_solver).
          clear -H1 H2. set_solver. }
      apply elem_of_union in Hc as [HcC1|HcC2].
      * (* the retired end is the sibling's *)
        destruct (decide (d ∈ C2)) as [HdC2|HdC2]; last first.
        { exfalso.
          assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess (SLink {[c; d]}))
                    (C2 ∖ sentc (SLink {[c; d]}), F2 ⊎ {[+ e' +]})) as Hst2.
          { eapply PStepSession; [exact He|]. simpl.
            clear -Hcc HcC1 HdC2. set_solver. }
          pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hcl. simpl in Hcl.
          destruct Hcl as (c1 & d1 & Σ2a & sc & sd & Hset & Hne & HeqΣ & _).
          assert (c ∈ dom Σ2) as HcΣ2.
          { assert (c ∈ ({[c1; d1]} : gset chan)) as Hcin
              by (rewrite <-Hset; clear; set_solver).
            subst Σ2. rewrite !dom_insert_L. clear -Hcin. set_solver. }
          clear -HcΣ2 Hd1 HcC1. set_solver. }
        apply (Prel_link_orient n (Σ1 ∪ Σ2) T (C1 ∪ C2) _ c d);
          [done
          |clear -HcC1; set_solver
          |clear -HdC2; set_solver
          |rewrite dom_union_L; clear -Hd1 Hs1 HcC1; set_solver
          |rewrite dom_union_L; clear -Hd2 Hs2 HdC2; set_solver|].
        assert (tstep e (LSess (SLink {[d; c]})) e') as He'
          by (rewrite upair_comm; exact He).
        assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                  (C2 ∖ {[d]}, echsubst d c (F2 ⊎ {[+ e' +]}))) as Hst2
          by (by eapply PStepLink).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(clear -Hs2; set_solver)).
        assert ((C1 ∪ C2) ∖ {[d]} = C1 ∪ (C2 ∖ {[d]})) as ->
          by (clear -Hcc HdC2; set_solver).
        assert (echsubst d c (E1 ⊎ F2 ⊎ {[+ e' +]})
                = echsubst d c E1 ⊎ echsubst d c (F2 ⊎ {[+ e' +]})) as ->
          by (rewrite !echsubst_disj_union; multiset_solver).
        assert (Prel n Σ1 T (C1, echsubst d c E1)) as HP1'.
        { apply Prel_junk_subst;
            [clear -Hd2 HdC2; set_solver
            |clear -Hcc HdC2; set_solver
            |intros Hb; clear -Hs1 Hb; set_solver
            |exact Hcd
            |by apply Prel_down1]. }
        eapply IH;
          [done|by split|set_solver|set_solver|set_solver|set_solver
          |set_solver|exact HP1'|exact HC2].
      * (* the retired end is comp2's *)
        assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau
                  (C2 ∖ {[c]}, echsubst c d (F2 ⊎ {[+ e' +]}))) as Hst2
          by (by eapply PStepLink).
        pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
        specialize (HC2 ltac:(clear -Hs2; set_solver)).
        assert ((C1 ∪ C2) ∖ {[c]} = C1 ∪ (C2 ∖ {[c]})) as ->
          by (clear -Hcc HcC2; set_solver).
        assert (echsubst c d (E1 ⊎ F2 ⊎ {[+ e' +]})
                = echsubst c d E1 ⊎ echsubst c d (F2 ⊎ {[+ e' +]})) as ->
          by (rewrite !echsubst_disj_union; multiset_solver).
        assert (Prel n Σ1 T (C1, echsubst c d E1)) as HP1'.
        { apply Prel_junk_subst;
            [clear -Hd2 HcC2; set_solver
            |clear -Hcc HcC2; set_solver
            |intros Hb; clear -Hs1 Hb; set_solver
            |clear -Hcd; congruence
            |by apply Prel_down1]. }
        eapply IH;
          [done|by split|set_solver|set_solver|set_solver|set_solver
          |set_solver|exact HP1'|exact HC2].
Qed.

(** ** The session cases of INDEPENDENT *)

Lemma indep_sess n Σ1 Σ2 C1 E1 C2 E2 T σ p'
    (IH : ∀ m, m ≤ n → independent_at m) :
  prim T → Σ1 ##ₘ Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel (S n) Σ1 T (C1, E1) → Prel (S n) Σ2 TUnit (C2, E2) →
  proc_step (C1 ∪ C2, E1 ⊎ E2) (PSess σ) p' →
  Pcase n (Σ1 ∪ Σ2) T (C1 ∪ C2, E1 ⊎ E2) (PSess σ) p'.
Proof.
  intros Hprim Hdd Hcc Hd1 Hd2 Hs1 Hs2 HP1 HP2 Hst.
  assert (independent_at n) as IHn by (apply IH; lia).
  apply proc_step_sess_inv in Hst as (F & e & e' & Heq & He & Hsub & ->).
  apply gmultiset_split_elem_of in Heq as [(F1 & -> & ->)|(F2 & -> & ->)].
  - (* the acting thread is in E1 *)
    assert (proc_step (C1, F1 ⊎ {[+ e +]}) (PSess σ)
              (C1 ∖ sentc σ, F1 ⊎ {[+ e' +]})) as Hst1
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP1 Hst1) as Hc.
    destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
    + (* recv *)
      destruct Hc as (Σ1a & U & s & (s0 & HeqΣ & Hu) & Hca & Hcont).
      subst Σ1.
      assert (c ∉ dom Σ2) as Hc2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1a ∪ Σ2), U, s. split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_dom. }
      intros j Σn Hj Hdn Hcn Hfr HVw.
      assert (Σn ##ₘ Σ1a) by senv_disj.
      specialize (Hcont j Σn Hj ltac:(done) Hcn ltac:(set_solver) HVw).
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C1 ∖ ∅) with C1 in Hcont by set_solver.
      replace (F1 ⊎ E2 ⊎ {[+ e' +]})
        with ((F1 ⊎ {[+ e' +]}) ⊎ E2) by multiset_solver.
      replace (<[c:=s]> (Σ1a ∪ Σ2 ∪ Σn)) with (<[c:=s]> (Σ1a ∪ Σn) ∪ Σ2)
        by senv_perm.
      eapply (IH j Hj);
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver
        |exact Hcont|eapply Prel_down; [|exact HP2]; lia].
    + (* send *)
      destruct Hc as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew & T0 & Tw
                      & (s0 & HeqΣ & Hu) & Hd0v & Hd0w & Hdvw & Hc0 & Hcv & Hcw
                      & Hdome & Hσed & Hcσe & HpC & HC0w & HpE
                      & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome. subst Σ1.
      destruct (ty_one_of_prim _ _ _ Hty Hprim) as [HpT0 HpTw].
      assert (fchans w ⊆ dom Σv ∪ dom σe) as Hfw.
      { pose proof (Vrel_fchans _ _ _ _ HVw) as Hf.
        rewrite dom_union_L, dom_fmap_L in Hf. by rewrite Hf. }
      assert (fchans w ## C2) as HwC2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      assert (c ∉ dom Σ2) as Hc2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ0 ∪ Σ2), Σv, U, s, σe, Σw, (C0 ∪ C2), (E0 ⊎ E2), Cw, Ew, T0, Tw.
      split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_disj. }
      { senv_disj. }
      { done. }
      { senv_dom. }
      { done. }
      { done. }
      { set_solver. }
      { apply map_disjoint_dom in Hdd. set_solver. }
      { done. }
      { set_solver. }
      { set_solver. }
      { multiset_solver. }
      { done. }
      { replace (<[c:=s]> (Σ0 ∪ Σ2)) with (<[c:=s]> Σ0 ∪ Σ2) by senv_perm.
        eapply IHn;
          [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
          |set_solver
          |exact HP0|eauto using Prel_down1]. }
      { exact HPw. }
      { exact Hty. }
    + (* close *)
      destruct Hc as (Σ1a & (s0 & HeqΣ & Hu) & Hca & Hcont). subst Σ1.
      assert (c ∉ dom Σ2) as Hc2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1a ∪ Σ2). split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_dom. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C1 ∖ ∅) with C1 in Hcont by set_solver.
      replace (F1 ⊎ E2 ⊎ {[+ e' +]})
        with ((F1 ⊎ {[+ e' +]}) ⊎ E2) by multiset_solver.
      eapply IHn;
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver
        |exact Hcont|eauto using Prel_down1].
    + (* forwarding: both ends are interface channels of the acting
         component (by its forwarding clause), and the composite clause
         reassembles the two inserts over the union *)
      destruct Hc as (c & d & Σ1a & sc & sd & -> & Hne & HeqΣ & Hc1a & Hd1a
                      & Hdu & Hcont).
      subst Σ1.
      assert (c ∉ dom Σ2 ∧ d ∉ dom Σ2) as [Hc2 Hd2'].
      { apply map_disjoint_dom in Hdd. rewrite !dom_insert_L in Hdd.
        set_solver. }
      exists c, d, (Σ1a ∪ Σ2), sc, sd. split_and!.
      { done. }
      { done. }
      { by rewrite !insert_union_l. }
      { rewrite dom_union_L. set_solver. }
      { rewrite dom_union_L. set_solver. }
      { done. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C1 ∖ ∅) with C1 in Hcont by set_solver.
      replace (F1 ⊎ E2 ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      eapply IHn;
        [done| |set_solver| | | | 
        |exact Hcont|eauto using Prel_down1].
      { split; [done|]. apply map_disjoint_dom in Hdd.
        apply map_disjoint_dom. rewrite !dom_insert_L in Hdd. set_solver. }
      { set_solver. }
      { rewrite !dom_insert_L in Hd2. set_solver. }
      { rewrite !dom_insert_L in Hs1. set_solver. }
      { set_solver. }
  - (* the acting thread is in E2 (the unit side) *)
    assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess σ)
              (C2 ∖ sentc σ, F2 ⊎ {[+ e' +]})) as Hst2
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hc.
    destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
    + (* recv *)
      destruct Hc as (Σ2a & U & s & (s0 & HeqΣ & Hu) & Hca & Hcont).
      subst Σ2.
      assert (c ∉ dom Σ1) as Hc1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1 ∪ Σ2a), U, s. split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_dom. }
      intros j Σn Hj Hdn Hcn Hfr HVw.
      assert (Σn ##ₘ Σ2a) by senv_disj.
      specialize (Hcont j Σn Hj ltac:(done) Hcn ltac:(set_solver) HVw).
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C2 ∖ ∅) with C2 in Hcont by set_solver.
      replace (E1 ⊎ F2 ⊎ {[+ e' +]})
        with (E1 ⊎ (F2 ⊎ {[+ e' +]})) by multiset_solver.
      replace (<[c:=s]> (Σ1 ∪ Σ2a ∪ Σn)) with (Σ1 ∪ <[c:=s]> (Σ2a ∪ Σn))
        by senv_perm.
      eapply (IH j Hj);
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver
        |eapply Prel_down; [|exact HP1]; lia|exact Hcont].
    + (* send *)
      destruct Hc as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew & T0 & Tw
                      & (s0 & HeqΣ & Hu) & Hd0v & Hd0w & Hdvw & Hc0 & Hcv & Hcw
                      & Hdome & Hσed & Hcσe & HpC & HC0w & HpE
                      & HVw & HP0 & HPw & Hty).
      simpl in HpC, HpE, Hdome. subst Σ2.
      apply ty_one_of_unit_inv in Hty as [-> ->].
      assert (fchans w ⊆ dom Σv ∪ dom σe) as Hfw.
      { pose proof (Vrel_fchans _ _ _ _ HVw) as Hf.
        rewrite dom_union_L, dom_fmap_L in Hf. by rewrite Hf. }
      assert (fchans w ## C1) as HwC1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      assert (c ∉ dom Σ1) as Hc1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ0 ∪ Σ1), Σv, U, s, σe, Σw, (C0 ∪ C1), (E0 ⊎ E1), Cw, Ew,
        T, TUnit.
      split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_disj. }
      { senv_disj. }
      { done. }
      { senv_dom. }
      { done. }
      { done. }
      { set_solver. }
      { apply map_disjoint_dom in Hdd. set_solver. }
      { done. }
      { set_solver. }
      { set_solver. }
      { multiset_solver. }
      { done. }
      { replace (<[c:=s]> (Σ0 ∪ Σ1)) with (Σ1 ∪ <[c:=s]> Σ0) by senv_perm.
        replace (C0 ∪ C1) with (C1 ∪ C0) by set_solver.
        replace (E0 ⊎ E1) with (E1 ⊎ E0) by multiset_solver.
        eapply IHn;
          [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
          |set_solver
          |eauto using Prel_down1|exact HP0]. }
      { exact HPw. }
      { by left. }
    + (* close *)
      destruct Hc as (Σ2a & (s0 & HeqΣ & Hu) & Hca & Hcont). subst Σ2.
      assert (c ∉ dom Σ1) as Hc1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1 ∪ Σ2a). split_and!.
      { eapply senv_hd_intro; [done|senv_perm]. }
      { senv_dom. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C2 ∖ ∅) with C2 in Hcont by set_solver.
      replace (E1 ⊎ F2 ⊎ {[+ e' +]})
        with (E1 ⊎ (F2 ⊎ {[+ e' +]})) by multiset_solver.
      eapply IHn;
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver
        |eauto using Prel_down1|exact Hcont].
    + (* forwarding, mirrored *)
      destruct Hc as (c & d & Σ2a & sc & sd & -> & Hne & HeqΣ & Hc2a & Hd2a
                      & Hdu & Hcont).
      subst Σ2.
      assert (c ∉ dom Σ1 ∧ d ∉ dom Σ1) as [Hc1' Hd1'].
      { apply map_disjoint_dom in Hdd. rewrite !dom_insert_L in Hdd.
        set_solver. }
      exists c, d, (Σ1 ∪ Σ2a), sc, sd. split_and!.
      { done. }
      { done. }
      { rewrite !insert_union_r; [done| |]; by apply not_elem_of_dom. }
      { rewrite dom_union_L. set_solver. }
      { rewrite dom_union_L. set_solver. }
      { done. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C2 ∖ ∅) with C2 in Hcont by set_solver.
      replace (E1 ⊎ F2 ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      eapply IHn;
        [done| |set_solver| | | | 
        |eauto using Prel_down1|exact Hcont].
      { split; [done|]. apply map_disjoint_dom in Hdd.
        apply map_disjoint_dom. rewrite !dom_insert_L in Hdd. set_solver. }
      { rewrite !dom_insert_L in Hd1. set_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite !dom_insert_L in Hs2. set_solver. }
Qed.

Lemma independent_S n (IH : ∀ m, m ≤ n → comp_at m) : independent_at (S n).
Proof.
  intros Σ Σ1 Σ2 C1 E1 C2 E2 T Hprim [-> Hdd] Hcc Hd1 Hd2 Hs1 Hs2
    HP1 HP2.
  assert (∀ m, m ≤ n → independent_at m) as IHi.
  { intros m Hm. by destruct (IH m Hm) as (_ & ? & _). }
  apply Prel_S_intro.
  - intros Hirr.
    exact (indep_irred n Σ1 Σ2 C1 E1 C2 E2 T HP1 HP2 Hd1 Hd2 Hirr).
  - intros π p' Hst. destruct π as [|σ]; simpl.
    + intros Hg.
      assert (independent_at n) as IHn by (apply IHi; lia).
      eapply (indep_tau n Σ1 Σ2 C1 E1 C2 E2 T p' IHn); try done.
    + eapply (indep_sess n Σ1 Σ2 C1 E1 C2 E2 T σ p' IHi); try done.
Qed.
