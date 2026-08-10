(** * Compositionality of the process logical relation (Lemmas 3.8–3.10)

    The three composition principles for [Prel] — TERM, INDEPENDENT
    and CONNECT — proved by (strong) induction on the step index, plus
    the judgment-level versions (Theorem 3.12) and the fundamental
    property for processes (Theorem 3.13). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Junk.

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

(** Normalize echans of multiset unions everywhere, then solve. *)
Local Ltac esolve :=
  repeat (progress (rewrite ?echans_disj_union, ?echans_singleton in * );
          simpl in * );
  set_solver.

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
     c ∈ C ∧ p' = (C ∖ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F e c d e', E = F ⊎ {[+ e +]} ∧ tstep e (LSess (SLink {[c; d]})) e' ∧
     c ∈ C ∧ p' = (C ∖ {[c]}, echsubst c d (F ⊎ {[+ e' +]}))).
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 10.
  - right; left. eauto 12.
  - do 2 right; left. eauto 20.
  - do 3 right; left. eauto 20.
  - do 4 right. eauto 14.
Qed.

(** Subjects of session transitions occur free in the source. *)
Lemma tstep_subj_occ e σ e' :
  tstep e (LSess σ) e' → subjs σ ⊆ fchans e.
Proof.
  intros H. remember (LSess σ) as α eqn:Hα.
  induction H; subst; simpl; try set_solver.
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; simpl; set_solver end.
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
  Prel (S n) Σ T p → proc_step p (PSess σ) p' → subjs σ ⊆ dom Σ.
Proof.
  intros HP Hst. pose proof (Prel_S_step _ _ _ _ _ _ HP Hst) as Hc.
  destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
  - destruct Hc as (Σ1 & U & s & Hhd & _).
    rewrite (senv_hd_dom _ _ _ _ Hhd). set_solver.
  - destruct Hc as (?&?&?&?&?&?&?&?&?&?&?&?&Hhd&_).
    rewrite (senv_hd_dom _ _ _ _ Hhd). set_solver.
  - destruct Hc as (Σ1 & Hhd & _).
    rewrite (senv_hd_dom _ _ _ _ Hhd). set_solver.
  - (* forwarding: both ends are entries of Σ *)
    destruct Hc as (c & d & Σ1 & sc & sd & -> & Hcd & -> & _).
    rewrite !dom_insert_L. set_solver.
Qed.

(** A component's transition yields a transition of the composition
    (retargeting forks to globally fresh names). *)
Lemma proc_step_frame_l C1 E1 C2 E2 π p1' :
  proc_step (C1, E1) π p1' →
  (∀ σ, π = PSess σ → subjs σ ## C2) →
  ∃ π' q, proc_step (C1 ∪ C2, E1 ⊎ E2) π' q.
Proof.
  intros Hst Hsubj. destruct π as [|σ].
  - apply proc_step_tau_inv in Hst
      as [(F & e & e' & -> & He & _)
         |[(F & e & c & v & e' & -> & He & Hc1 & Hce & Hcf & _)
         |[(F & c & v & e & e' & f & f' & -> & He & Hf & Hc & _)
         |[(F & c & e & e' & f & f' & -> & He & Hf & Hc & _)
         |(F & e & c & d & e' & -> & He & Hc & _)]]]].
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
    + assert ((F ⊎ {[+ e +]}) ⊎ E2 = (F ⊎ E2) ⊎ {[+ e +]}) as ->
        by multiset_solver.
      eexists _, _. eapply PStepLink; [done|set_solver].
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
