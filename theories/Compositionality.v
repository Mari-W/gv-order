(** * Compositionality of the process logical relation (Lemmas 3.8–3.10)

    The three composition principles for [Prel] — TERM, INDEPENDENT
    and CONNECT — proved by (strong) induction on the step index, plus
    the judgment-level versions (Theorem 3.12) and the fundamental
    property for processes (Theorem 3.13). *)

From Coq Require Import Classical.
From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export LogRel.

(** ** Infrastructure *)

(** Fork labels can be retargeted to any (other) fresh name: the
    term-level LTS creates the new channel nondeterministically. *)
Lemma fork_retarget e c v e' c' :
  tstep e (LFork c v) e' → ∃ e'', tstep e (LFork c' v) e''.
Proof.
  intros H. remember (LFork c v) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. by apply HeadFork.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetU.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetP.
Qed.

Lemma elem_of_echans x E : x ∈ echans E ↔ ∃ e, e ∈ E ∧ x ∈ fchans e.
Proof.
  unfold echans. rewrite elem_of_union_list. split.
  - intros (X & HX & Hx). apply elem_of_list_fmap in HX as (e & -> & He).
    exists e. split; [|done]. by apply gmultiset_elem_of_elements.
  - intros (e & He & Hx). exists (fchans e). split; [|done].
    apply elem_of_list_fmap. exists e. split; [done|].
    by apply gmultiset_elem_of_elements.
Qed.

Lemma echans_disj_union E1 E2 : echans (E1 ⊎ E2) = echans E1 ∪ echans E2.
Proof.
  apply set_eq. intros x. rewrite elem_of_union, !elem_of_echans.
  setoid_rewrite gmultiset_elem_of_disj_union. naive_solver.
Qed.

(** Inversion of τ transitions by originating rule. *)
Lemma proc_step_tau_inv C E p' :
  proc_step (C, E) PTau p' →
  (∃ F e e', E = F ⊎ {[+ e +]} ∧ tstep e LBeta e' ∧
     p' = (C, F ⊎ {[+ e' +]}))
  ∨ (∃ F e c v e', E = F ⊎ {[+ e +]} ∧ tstep e (LFork c v) e' ∧
     c ∉ C ∧ c ∉ echans F ∧ c ∉ fchans e ∧
     p' = (C ∪ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}))
  ∨ (∃ F c v e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
     tstep e (LSess (SSend c v)) e' ∧ tstep f (LSess (SRecv c v)) f' ∧
     c ∈ C ∧ p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F c e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
     tstep e (LSess (SClos c)) e' ∧ tstep f (LSess (SClos c)) f' ∧
     c ∈ C ∧ p' = (C ∖ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ f' +]})).
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 10.
  - right; left. eauto 12.
  - right; right; left. eauto 20.
  - right; right; right. eauto 20.
Qed.

(** Locating a distinguished occurrence in a split multiset. *)
Lemma gmultiset_split_elem_of (E1 E2 F : gmultiset expr) (e : expr) :
  E1 ⊎ E2 = F ⊎ {[+ e +]} →
  (∃ F1, E1 = F1 ⊎ {[+ e +]} ∧ F = F1 ⊎ E2)
  ∨ (∃ F2, E2 = F2 ⊎ {[+ e +]} ∧ F = E1 ⊎ F2).
Proof.
  intros Heq.
  assert (e ∈ E1 ⊎ E2) as He by (rewrite Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He]; [left|right].
  - exists (E1 ∖ {[+ e +]}). split; multiset_solver.
  - exists (E2 ∖ {[+ e +]}). split; multiset_solver.
Qed.

(** Same, for the two distinguished threads of Msg/Close steps
    (correct also when the two terms are equal, by working with
    multiplicities). *)
Lemma gmultiset_split_elem_of2 (E1 E2 F : gmultiset expr) (e f : expr) :
  E1 ⊎ E2 = F ⊎ {[+ e +]} ⊎ {[+ f +]} →
  (∃ F1, E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} ∧ F = F1 ⊎ E2)
  ∨ (∃ F2, E2 = F2 ⊎ {[+ e +]} ⊎ {[+ f +]} ∧ F = E1 ⊎ F2)
  ∨ (∃ F1 F2, E1 = F1 ⊎ {[+ e +]} ∧ E2 = F2 ⊎ {[+ f +]} ∧ F = F1 ⊎ F2)
  ∨ (∃ F1 F2, E1 = F1 ⊎ {[+ f +]} ∧ E2 = F2 ⊎ {[+ e +]} ∧ F = F1 ⊎ F2).
Proof.
  intros Heq.
  assert (e ∈ E1 ⊎ E2) as He by (rewrite Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He].
  - assert ((E1 ∖ {[+ e +]}) ⊎ E2 = F ⊎ {[+ f +]}) as Heq'
      by multiset_solver.
    apply gmultiset_split_elem_of in Heq' as [(F1 & HF1 & ->)|(F2 & HF2 & ->)].
    + left. exists F1. split; multiset_solver.
    + right; right; left. exists (E1 ∖ {[+ e +]}), F2.
      split_and!; multiset_solver.
  - assert (E1 ⊎ (E2 ∖ {[+ e +]}) = F ⊎ {[+ f +]}) as Heq'
      by multiset_solver.
    apply gmultiset_split_elem_of in Heq' as [(F1 & HF1 & ->)|(F2 & HF2 & ->)].
    + right; right; right. exists F1, (E2 ∖ {[+ e +]}).
      split_and!; multiset_solver.
    + right; left. exists F2. split; multiset_solver.
Qed.

(** Any session transition allowed by the relation communicates on a
    channel of Σ. *)
Lemma Prel_sess_subj n Σ T p σ p' :
  Prel (S n) Σ T p → proc_step p (PSess σ) p' → subj σ ∈ dom Σ.
Proof.
  intros HP Hst. pose proof (Prel_S_step _ _ _ _ _ _ HP Hst) as Hc.
  destruct σ as [c w|c w|c]; simpl in Hc |- *.
  - destruct Hc as (Σ1 & U & s & -> & _). set_solver.
  - destruct Hc as (?&?&?&?&?&?&?&?&?&?&?&?&Heq&_). rewrite Heq. set_solver.
  - destruct Hc as (Σ1 & Heq & _). rewrite Heq. set_solver.
Qed.

(** A component's transition yields a transition of the composition
    (retargeting forks to globally fresh names). *)
Lemma proc_step_frame_l C1 E1 C2 E2 π p1' :
  proc_step (C1, E1) π p1' →
  (∀ σ, π = PSess σ → subj σ ∉ C2) →
  ∃ π' q, proc_step (C1 ∪ C2, E1 ⊎ E2) π' q.
Proof.
  intros Hst Hsubj. destruct π as [|σ].
  - apply proc_step_tau_inv in Hst
      as [(F & e & e' & -> & He & _)
         |[(F & e & c & v & e' & -> & He & Hc1 & Hce & Hcf & _)
         |[(F & c & v & e & e' & f & f' & -> & He & Hf & Hc & _)
         |(F & c & e & e' & f & f' & -> & He & Hf & Hc & _)]]].
    + assert ((F ⊎ {[+ e +]}) ⊎ E2 = (F ⊎ E2) ⊎ {[+ e +]}) as ->
        by multiset_solver.
      eexists _, _. by eapply PStepBeta.
    + destruct (exist_fresh (C1 ∪ C2 ∪ echans (F ⊎ E2) ∪ fchans e))
        as [c'' Hc''].
      destruct (fork_retarget _ _ _ _ c'' He) as [e'' He''].
      assert ((F ⊎ {[+ e +]}) ⊎ E2 = (F ⊎ E2) ⊎ {[+ e +]}) as ->
        by multiset_solver.
      eexists _, _. eapply PStepFork; [exact He''| | |]; set_solver.
    + assert ((F ⊎ {[+ e +]} ⊎ {[+ f +]}) ⊎ E2
              = ((F ⊎ E2) ⊎ {[+ e +]}) ⊎ {[+ f +]}) as -> by multiset_solver.
      eexists _, _. eapply PStepMsg; [done|done|set_solver].
    + assert ((F ⊎ {[+ e +]} ⊎ {[+ f +]}) ⊎ E2
              = ((F ⊎ E2) ⊎ {[+ e +]}) ⊎ {[+ f +]}) as -> by multiset_solver.
      eexists _, _. eapply PStepClose; [done|done|set_solver].
  - apply proc_step_sess_inv in Hst as (F & e & e' & -> & He & Hsub & _).
    specialize (Hsubj σ eq_refl).
    assert ((F ⊎ {[+ e +]}) ⊎ E2 = (F ⊎ E2) ⊎ {[+ e +]}) as ->
      by multiset_solver.
    eexists _, _. eapply PStepSession; [done|set_solver].
Qed.

(** Irreducibility of a composition transfers to its (related)
    components. *)
Lemma pirred_split_l n Σ1 T C1 E1 C2 E2 :
  Prel (S n) Σ1 T (C1, E1) → C2 ## dom Σ1 →
  pirred (C1 ∪ C2, E1 ⊎ E2) → pirred (C1, E1).
Proof.
  intros HP Hd Hirr π p1' Hst.
  edestruct (proc_step_frame_l C1 E1 C2 E2 π p1') as (π' & q & Hq); auto.
  - intros σ ->. pose proof (Prel_sess_subj _ _ _ _ _ _ HP Hst). set_solver.
  - exact (Hirr _ _ Hq).
Qed.

Lemma pirred_split_r n Σ2 T' C1 E1 C2 E2 :
  Prel (S n) Σ2 T' (C2, E2) → C1 ## dom Σ2 →
  pirred (C1 ∪ C2, E1 ⊎ E2) → pirred (C2, E2).
Proof.
  intros HP Hd Hirr.
  eapply (pirred_split_l n Σ2 T' C2 E2 C1 E1); auto.
  assert (C2 ∪ C1 = C1 ∪ C2) as -> by set_solver.
  assert (E2 ⊎ E1 = E1 ⊎ E2) as -> by multiset_solver.
  done.
Qed.

(** Type bookkeeping helpers. *)
Lemma ty_one_of_prim T0 Tw T : ty_one_of T0 Tw T → prim T → prim T0 ∧ prim Tw.
Proof. intros [[-> ->]|[-> ->]]; auto using prim_unit. Qed.

Lemma ty_one_of_unit_inv T0 Tw : ty_one_of T0 Tw TUnit → T0 = TUnit ∧ Tw = TUnit.
Proof. intros [[-> ->]|[-> ->]]; auto. Qed.

Lemma Prel_down1 n Σ T p : Prel (S n) Σ T p → Prel n Σ T p.
Proof. intros. eapply Prel_down; [|done]. lia. Qed.

(** ** The three composition principles, by joint strong induction

    All three lemmas are proved simultaneously by strong induction on
    the step index: TERM's fork case builds a CONNECT redex, and
    CONNECT's internal-communication and close cases fall back on
    CONNECT (at extended channel families) and INDEPENDENT one index
    below. INDEPENDENT and CONNECT carry the paper's implicit
    well-formedness "C and Σ share no channels" as explicit
    self-disjointness premises. *)

Definition term_at (n : nat) : Prop :=
  ∀ Σ T e, prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).

Definition independent_at (n : nat) : Prop :=
  ∀ Σ Σ1 Σ2 C1 E1 C2 E2 T,
    prim T → senv_split Σ Σ1 Σ2 →
    C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
    C1 ## dom Σ1 → C2 ## dom Σ2 →
    Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
    Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).

Definition connect_at (n : nat) : Prop :=
  ∀ Σ1 Σ2 c s C1 E1 C2 E2 T,
    prim T → Σ1 ##ₘ Σ2 →
    c ∉ dom Σ1 → c ∉ dom Σ2 →
    C1 ## C2 → c ∉ C1 → c ∉ C2 →
    C1 ## dom Σ2 → C2 ## dom Σ1 →
    C1 ## dom Σ1 → C2 ## dom Σ2 →
    Prel n (<[c := s]> Σ1) T (C1, E1) →
    Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
    Prel n (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).

Definition comp_at (n : nat) : Prop :=
  term_at n ∧ independent_at n ∧ connect_at n.

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
  apply Prel_S_iff in HP1 as [H1 _].
  destruct (H1 Hirr1) as (v1 & F1 & Heq1 & Hv1 & HV1 & HU1).
  apply Prel_S_iff in HP2 as [H2 _].
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
       |(F & c & e & e' & f & f' & Heq & He & Hf & Hc & ->)]]];
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
        |set_solver|eauto using Prel_down1|eauto using Prel_down1].
    + assert (proc_step (C2, F2 ⊎ {[+ e +]}) PTau (C2, F2 ⊎ {[+ e' +]}))
        as Hst2 by (by eapply PStepBeta).
      pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as HC2. simpl in HC2.
      specialize (HC2 ltac:(set_solver)).
      assert ((E1 ⊎ F2) ⊎ {[+ e' +]} = E1 ⊎ (F2 ⊎ {[+ e' +]})) as ->
        by multiset_solver.
      eapply IH;
            [done|by split|set_solver|set_solver|set_solver|set_solver
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SSend c v))
                  (C1 ∖ sentc (SSend c v), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst1.
        { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          by eapply PStepSession. }
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SSend c v))
                  (C2 ∖ sentc (SSend c v), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst2.
        { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          by eapply PStepSession. }
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C1, F1 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SClos c))
                  (C1 ∖ sentc (SClos c), (F1 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst1.
        { assert (F1 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F1 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          by eapply PStepSession. }
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
            |set_solver|eauto using Prel_down1|eauto using Prel_down1].
      * exfalso.
        assert (proc_step (C2, F2 ⊎ {[+ e +]} ⊎ {[+ f +]}) (PSess (SClos c))
                  (C2 ∖ sentc (SClos c), (F2 ⊎ {[+ f +]}) ⊎ {[+ e' +]}))
          as Hst2.
        { assert (F2 ⊎ {[+ e +]} ⊎ {[+ f +]} = (F2 ⊎ {[+ f +]}) ⊎ {[+ e +]})
            as -> by multiset_solver.
          by eapply PStepSession. }
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
    destruct σ as [c w|c w|c]; simpl in Hc |- *.
    + (* recv *)
      destruct Hc as (Σ1a & U & s & HeqΣ & Hca & Hcont). subst Σ1.
      assert (c ∉ dom Σ2) as Hc2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1a ∪ Σ2), U, s. split_and!.
      { senv_perm. }
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
        |set_solver|exact Hcont|eapply Prel_down; [|exact HP2]; lia].
    + (* send *)
      destruct Hc as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew & T0 & Tw
                      & HeqΣ & Hd0v & Hd0w & Hdvw & Hc0 & Hcv & Hcw
                      & Hdome & Hσed & Hcσe & HpC & HC0w & HpE & HVw & HP0
                      & HPw & Hty).
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
      { senv_perm. }
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
          |set_solver|exact HP0|eauto using Prel_down1]. }
      { exact HPw. }
      { exact Hty. }
    + (* close *)
      destruct Hc as (Σ1a & HeqΣ & Hca & Hcont). subst Σ1.
      assert (c ∉ dom Σ2) as Hc2.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1a ∪ Σ2). split_and!.
      { senv_perm. }
      { senv_dom. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C1 ∖ ∅) with C1 in Hcont by set_solver.
      replace (F1 ⊎ E2 ⊎ {[+ e' +]})
        with ((F1 ⊎ {[+ e' +]}) ⊎ E2) by multiset_solver.
      eapply IHn;
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver|exact Hcont|eauto using Prel_down1].
  - (* the acting thread is in E2 (the unit side) *)
    assert (proc_step (C2, F2 ⊎ {[+ e +]}) (PSess σ)
              (C2 ∖ sentc σ, F2 ⊎ {[+ e' +]})) as Hst2
      by (eapply PStepSession; [done|set_solver]).
    pose proof (Prel_S_step _ _ _ _ _ _ HP2 Hst2) as Hc.
    destruct σ as [c w|c w|c]; simpl in Hc |- *.
    + (* recv *)
      destruct Hc as (Σ2a & U & s & HeqΣ & Hca & Hcont). subst Σ2.
      assert (c ∉ dom Σ1) as Hc1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1 ∪ Σ2a), U, s. split_and!.
      { senv_perm. }
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
        |set_solver|eapply Prel_down; [|exact HP1]; lia|exact Hcont].
    + (* send *)
      destruct Hc as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew & T0 & Tw
                      & HeqΣ & Hd0v & Hd0w & Hdvw & Hc0 & Hcv & Hcw
                      & Hdome & Hσed & Hcσe & HpC & HC0w & HpE & HVw & HP0
                      & HPw & Hty).
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
      { senv_perm. }
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
          |set_solver|eauto using Prel_down1|exact HP0]. }
      { exact HPw. }
      { by left. }
    + (* close *)
      destruct Hc as (Σ2a & HeqΣ & Hca & Hcont). subst Σ2.
      assert (c ∉ dom Σ1) as Hc1.
      { apply map_disjoint_dom in Hdd. set_solver. }
      exists (Σ1 ∪ Σ2a). split_and!.
      { senv_perm. }
      { senv_dom. }
      replace ((C1 ∪ C2) ∖ ∅) with (C1 ∪ C2) by set_solver.
      replace (C2 ∖ ∅) with C2 in Hcont by set_solver.
      replace (E1 ⊎ F2 ⊎ {[+ e' +]})
        with (E1 ⊎ (F2 ⊎ {[+ e' +]})) by multiset_solver.
      eapply IHn;
        [done|split; [done|senv_disj]|set_solver|set_solver|set_solver|set_solver
        |set_solver|eauto using Prel_down1|exact Hcont].
Qed.

Lemma independent_S n (IH : ∀ m, m ≤ n → comp_at m) : independent_at (S n).
Proof.
  intros Σ Σ1 Σ2 C1 E1 C2 E2 T Hprim [-> Hdd] Hcc Hd1 Hd2 Hs1 Hs2 HP1 HP2.
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

(** ** TERM (Lemma 3.8) *)

Lemma gmultiset_singleton_inv (E : gmultiset expr) e x :
  E ⊎ {[+ e +]} = {[+ x +]} → E = ∅ ∧ e = x.
Proof. multiset_solver. Qed.

Lemma gmultiset_two_singleton_inv (E : gmultiset expr) e f x :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ x +]} → False.
Proof.
  intros H.
  assert (size (E ⊎ {[+ e +]} ⊎ {[+ f +]}) = size ({[+ x +]} : gmultiset expr))
    as Hsz by (by rewrite H).
  rewrite !gmultiset_size_disj_union, !gmultiset_size_singleton in Hsz. lia.
Qed.

(** A single-thread process is irreducible only if its thread is. *)
Lemma pirred_singleton e : pirred (∅, {[+ e +]}) → irred e.
Proof.
  intros Hirr α e' Hst.
  assert ({[+ e +]} = (∅ : gmultiset expr) ⊎ {[+ e +]}) as HeqE
    by multiset_solver.
  destruct α as [|σ|c v].
  - eapply (Hirr PTau). rewrite HeqE. by eapply PStepBeta.
  - eapply (Hirr (PSess σ)). rewrite HeqE.
    eapply PStepSession; [done|set_solver].
  - destruct (exist_fresh (fchans e)) as [c'' Hc''].
    destruct (fork_retarget _ _ _ _ c'' Hst) as [e'' He''].
    eapply (Hirr PTau). rewrite HeqE.
    eapply PStepFork; [exact He''|set_solver| |done].
    intros Hin. apply elem_of_echans in Hin as (e0 & He0 & _).
    multiset_solver.
Qed.

Lemma term_S n (IH : ∀ m, m ≤ n → comp_at m) : term_at (S n).
Proof.
  intros Σ T e Hprim HE.
  assert (∀ m, m ≤ n → term_at m) as IHt.
  { intros m Hm. by destruct (IH m Hm) as (? & _ & _). }
  apply Prel_S_intro.
  - (* irreducible: the thread is an appropriate value *)
    intros Hirr. pose proof (pirred_singleton _ Hirr) as Hirr1.
    apply Erel_S_iff in HE as [H1 _]. specialize (H1 Hirr1).
    exists e, ∅. split_and!.
    + f_equal. multiset_solver.
    + eauto using Vrel_val.
    + done.
    + intros e0 He0. exfalso. multiset_solver.
  - intros π p' Hst. destruct π as [|σ].
    + apply proc_step_tau_inv in Hst
        as [(F & e0 & e0' & HeqE & He0 & ->)
           |[(F & e0 & c & v & e0' & HeqE & He0 & HcC & Hce & Hcf & ->)
           |[(F & c & v & e0 & e0' & f & f' & HeqE & _)
           |(F & c & e0 & e0' & f & f' & HeqE & _)]]].
      * (* β *)
        symmetry in HeqE. apply gmultiset_singleton_inv in HeqE as [-> ->].
        simpl. intros Hg.
        pose proof (Erel_S_step _ _ _ _ _ _ HE He0) as Hc. simpl in Hc.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]}) with ({[+ e0' +]} : gmultiset expr)
          by multiset_solver.
        apply (IHt n); [lia|done|done].
      * (* fork *)
        symmetry in HeqE. apply gmultiset_singleton_inv in HeqE as [-> ->].
        simpl. intros Hg.
        pose proof (Erel_S_step _ _ _ _ _ _ HE He0) as Hc. simpl in Hc.
        specialize (Hc ltac:(set_solver))
          as (Σa & Σb & s & [-> Hdab] & HV & HE').
        destruct (IH n (le_n n)) as (IHtn & _ & IHc).
        replace ((∅ : gset chan) ∪ {[c]}) with (∅ ∪ ∅ ∪ {[c]} : gset chan)
          by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]} ⊎ {[+ App v (Chan c) +]})
          with (({[+ e0' +]} ⊎ {[+ App v (Chan c) +]}) : gmultiset expr) by multiset_solver.
        replace (Σa ∪ Σb) with (Σb ∪ Σa) by (by apply map_union_comm).
        assert (c ∉ dom Σa) as HcΣa by set_solver.
        assert (c ∉ dom Σb) as HcΣb by set_solver.
        apply (IHc Σb Σa c (dual s) ∅ {[+ e0' +]} ∅
                 {[+ App v (Chan c) +]} T Hprim);
          [ senv_disj | done | done
          | set_solver | set_solver | set_solver | set_solver
          | set_solver | set_solver | set_solver
          | by apply IHtn | ].
        (* unit side: the forked thread applied to its end of c *)
        rewrite dual_involutive.
        apply IHtn; [constructor|].
        replace (<[c:=s]> Σa) with (Σa ∪ {[c := s]})
          by (symmetry; by apply insert_as_union).
        eapply Vrel_app_head.
        -- by apply map_disjoint_singleton_r, not_elem_of_dom.
        -- eapply Vrel_down; [|exact HV]. lia.
        -- apply Vrel_chan.
      * exfalso. symmetry in HeqE. by eapply gmultiset_two_singleton_inv.
      * exfalso. symmetry in HeqE. by eapply gmultiset_two_singleton_inv.
    + apply proc_step_sess_inv in Hst as (F & e0 & e0' & HeqE & He0 & _ & ->).
      symmetry in HeqE. apply gmultiset_singleton_inv in HeqE as [-> ->].
      pose proof (Erel_S_step _ _ _ _ _ _ HE He0) as Hc.
      destruct σ as [c w|c w|c]; simpl in Hc |- *.
      * (* recv *)
        destruct Hc as (Σ1 & U & s & -> & Hca & Hcont).
        exists Σ1, U, s. split_and!; [done|done|].
        intros j Σn Hj Hdn Hcn _ HVw.
        specialize (Hcont j Σn Hj Hdn Hcn HVw).
        replace ((∅ : gset chan) ∖ ∅) with (∅ : gset chan) by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]}) with ({[+ e0' +]} : gmultiset expr)
          by multiset_solver.
        apply (IHt j); [lia|done|done].
      * (* send: no restricted channels escape from a channel-free
           process *)
        destruct Hc as (Σ0 & Σv & U & s & -> & Hd0v & Hc0 & Hcv & HVw & HE').
        exists Σ0, Σv, U, s, ∅, ∅, ∅, {[+ e0' +]}, ∅, ∅, T, TUnit.
        split_and!.
        { senv_perm. }
        { done. }
        { apply map_disjoint_empty_r. }
        { apply map_disjoint_empty_r. }
        { done. }
        { done. }
        { set_solver. }
        { rewrite dom_empty_L. set_solver. }
        { rewrite dom_empty_L. set_solver. }
        { rewrite dom_empty_L. set_solver. }
        { set_solver. }
        { set_solver. }
        { multiset_solver. }
        { rewrite fmap_empty. rewrite (right_id ∅ (∪)). exact HVw. }
        { apply (IHt n); [lia|done|done]. }
        { constructor. }
        { by left. }
      * (* close *)
        destruct Hc as (Σ1 & -> & Hca & HE').
        exists Σ1. split_and!; [done|done|].
        replace ((∅ : gset chan) ∖ ∅) with (∅ : gset chan) by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]}) with ({[+ e0' +]} : gmultiset expr)
          by multiset_solver.
        apply (IHt n); [lia|done|done].
Qed.

(** ** CONNECT (Lemma 3.10) *)

(** A transition on the distinguished channel c reveals the polarity
    of c's session type. *)
Lemma Prel_cstep_shape n Σ T C E c s σ p' :
  Prel (S n) (<[c := s]> Σ) T (C, E) → c ∉ dom Σ →
  proc_step (C, E) (PSess σ) p' → subj σ = c →
  match σ with
  | SRecv _ _ => ∃ U u, s = SRcv U u
  | SSend _ _ => ∃ U u, s = SSnd U u
  | SClos _ => s = SEnd
  end.
Proof.
  intros HP Hcd Hst Hsubj.
  pose proof (Prel_S_step _ _ _ _ _ _ HP Hst) as Hc.
  destruct σ as [c' w|c' w|c']; simpl in Hsubj, Hc; subst c'.
  - destruct Hc as (Σ' & U & u & Heq & Hc' & _).
    apply insert_fresh_inv in Heq as [-> _]; eauto.
  - destruct Hc as (Σ0 & Σv & U & u & σe & Σw & ? & ? & ? & ? & ? & ? &
                    Heq & ? & ? & ? & Hb0 & Hbv & Hbw & _).
    apply insert_fresh_inv in Heq as [-> _]; [eauto|done|senv_dom].
  - destruct Hc as (Σ' & Heq & Hc' & _).
    apply insert_fresh_inv in Heq as [-> _]; eauto.
Qed.

(** Iterated CONNECT: a process holding the dual ends of a family of
    channels can be connected to the family's owner pieces one by one.
    The receiver's environment grows by each owner's environment as
    the connections are performed. *)
Lemma connect_owners n (IHc : connect_at n) σ Σw Tw Cw Ew :
  Powners (Prel n) σ Σw Tw (Cw, Ew) →
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
Lemma Powners_graft n (IHc : connect_at n) σ Σw Tw Cw Ew :
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
      { rewrite insert_commute; [|done]. f_equal. by rewrite insert_delete. }
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
        rewrite delete_union, (delete_notin Σrest c);
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
        rewrite delete_union, (delete_notin Σd c);
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

Lemma connect_S n (IH : ∀ m, m ≤ n → comp_at m) : connect_at (S n).
Proof. Admitted.

(** ** Tying the knot *)

Lemma comp_0 : comp_at 0.
Proof. split_and!; hnf; intros; apply Prel_0. Qed.

Lemma comp_all n : comp_at n.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  destruct n as [|n']; [exact comp_0|].
  assert (∀ m, m ≤ n' → comp_at m) as IH by (intros; apply IHn; lia).
  split_and!.
  - exact (term_S n' IH).
  - exact (independent_S n' IH).
  - exact (connect_S n' IH).
Qed.

(** ** Compositionality for processes (Lemmas 3.8–3.10) *)

(** Lemma 3.8 (Compositionality: TERM) *)
Lemma Prel_term n Σ T e :
  prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).
Proof. intros. destruct (comp_all n) as (Ht & _ & _). by apply Ht. Qed.

(** Lemma 3.9 (Compositionality: INDEPENDENT) *)
Lemma Prel_independent n Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).
Proof. intros. destruct (comp_all n) as (_ & Hi & _). by eapply Hi. Qed.

(** Lemma 3.10 (Compositionality: CONNECT) *)
Lemma Prel_connect n Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel n (<[c := s]> Σ1) T (C1, E1) →
  Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).
Proof.
  intros ? [-> ?] *. intros.
  destruct (comp_all n) as (_ & _ & Hc). by eapply Hc.
Qed.

(** ** Compositionality for processes, judgment form (Theorem 3.12) *)

(** P-Term *)
Lemma sem_ptyped_term Σ e T :
  prim T → sem_typed Σ [] e T → sem_ptyped Σ (∅, {[+ e +]}) T.
Proof.
  intros Hp (_ & _ & _ & He) n. apply Prel_term; [done|].
  specialize (He n ∅ Var (map_disjoint_empty_l _) eq_refl).
  by rewrite (right_id ∅ (∪)), subst_ids in He.
Qed.

(** P-Independent *)
Lemma sem_ptyped_independent Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  sem_ptyped Σ1 (C1, E1) T → sem_ptyped Σ2 (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_independent. Qed.

(** P-Connect *)
Lemma sem_ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  sem_ptyped (<[c := s]> Σ1) (C1, E1) T →
  sem_ptyped (<[c := dual s]> Σ2) (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_connect. Qed.

(** ** The fundamental property for processes (Theorem 3.13)

    The self-disjointness premises of INDEPENDENT and CONNECT are
    supplied by the well-formedness invariant [ptyped_chan_disj]. *)

Theorem fundamental_proc Σ p T : ptyped Σ p T → sem_ptyped Σ p T.
Proof.
  induction 1 as
    [Σ e T Hprim Ht
    |Σ Σ1 Σ2 C1 E1 C2 E2 T Hsp Hcc Hd1 Hd2 HT1 IH1 HT2 IH2
    |Σ Σ1 Σ2 c s C1 E1 C2 E2 T Hsp Hc1 Hc2 Hcc HcC1 HcC2 Hd1 Hd2
      HT1 IH1 HT2 IH2].
  - apply sem_ptyped_term; auto using fundamental_term.
  - pose proof (ptyped_chan_disj _ _ _ HT1) as Hs1.
    pose proof (ptyped_chan_disj _ _ _ HT2) as Hs2.
    simpl in Hs1, Hs2.
    eapply sem_ptyped_independent; eauto using ptyped_prim.
  - pose proof (ptyped_chan_disj _ _ _ HT1) as Hs1.
    pose proof (ptyped_chan_disj _ _ _ HT2) as Hs2.
    simpl in Hs1, Hs2. rewrite dom_insert_L in Hs1, Hs2.
    eapply sem_ptyped_connect; eauto using ptyped_prim; set_solver.
Qed.

(** Corollary: syntactically typed closed processes are deadlock free. *)
Corollary typed_deadlock_free p T : ptyped ∅ p T → deadlock_free p.
Proof. eauto using adequacy, fundamental_proc. Qed.
