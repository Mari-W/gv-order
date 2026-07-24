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
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj1.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj2.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepCase.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepForce.
Qed.

Lemma elem_of_echans x E : x ∈ echans E ↔ ∃ e, e ∈ E ∧ x ∈ fchans e.
Proof.
  unfold echans. rewrite elem_of_union_list. split.
  - intros (X & HX & Hx). apply list_elem_of_fmap in HX as (e & -> & He).
    exists e. split; [|done]. by apply gmultiset_elem_of_elements.
  - intros (e & He & Hx). exists (fchans e). split; [|done].
    apply list_elem_of_fmap. exists e. split; [done|].
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
        assert (c ∉ dom Σw) as Hcwd by dom_solve.
        assert (σe !! c = None) as HσeN
          by (apply not_elem_of_dom; dom_solve).
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
        by dom_solve.
      exists (delete d Σ1 ∪ Σ2). split_and!.
      { rewrite HΣ1d at 1. by rewrite insert_union_l. }
      { rewrite dom_union_L, dom_delete_L. dom_solve. }
      replace (C1 ∖ ∅) with C1 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((F1 ⊎ E2) ⊎ {[+ e' +]}) with ((F1 ⊎ {[+ e' +]}) ⊎ E2)
        by multiset_solver.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      eapply (IHc _ _ c s); connect_prem.
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
        by dom_solve.
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
        { rewrite HΣ2.
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
        by dom_solve.
      assert (dom Σ1 ## dom Σ2) as Hdds by (by apply map_disjoint_dom).
      exists (Σ1 ∪ delete d Σ2). split_and!.
      { rewrite HΣ2d at 1.
        rewrite <-insert_union_r; [done|by apply not_elem_of_dom]. }
      { dom_solve. }
      replace (C2 ∖ ∅) with C2 in Hcont by set_pure.
      replace ((C1 ∪ C2 ∪ {[c]}) ∖ ∅) with (C1 ∪ C2 ∪ {[c]}) by set_pure.
      replace ((E1 ⊎ F2) ⊎ {[+ e' +]}) with (E1 ⊎ (F2 ⊎ {[+ e' +]}))
        by multiset_solver.
      eapply (IHc _ _ c s); connect_prem.
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
