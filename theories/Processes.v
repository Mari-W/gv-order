(** * Process LTS of GV♯ (Fig. 3) and deadlock freedom (§2.1)

    A process is a pair (C, E) of a finite set C of (restricted)
    channels and a finite multiset E of closed terms running in
    parallel. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Semantics.

Definition proc : Type := gset chan * gmultiset expr.

(** Process labels π ::= τ | σ

    Forwarding is not a label of its own: an offer ↔{c,d} whose ends
    are both free is an offer like any other, lifted by the single
    rule P-Act-Session. *)
Inductive plabel :=
  | PTau
  | PSess (σ : slabel).

(** Channels occurring free in some thread of E. *)
Definition echans (E : gmultiset expr) : gset chan :=
  ⋃ (fchans <$> elements E).

(** E[d/c] — retarget channel c to d in every thread. *)
Definition echsubst (c d : chan) (E : gmultiset expr) : gmultiset expr :=
  gmultiset_map (chsubst c d) E.

(** E[c↔d] — transpose the two channel names in every thread. The
    forwarding step uses the transposition rather than the paper's
    one-sided substitution: on soups where the surviving end does not
    already occur — in particular every typed configuration, by
    channel-tightness — the two coincide ([echswap_echsubst]), and the
    transposition keeps the rule total and the composition lemmas
    compositional (a one-sided substitution can merge a dead ⟨d,d⟩
    forwarding pair into a live one, which no renaming-stability lemma
    survives; see docs/link-design.md). *)
Definition echswap (c d : chan) (E : gmultiset expr) : gmultiset expr :=
  gmultiset_map (eswap c d) E.

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

Lemma echans_empty : echans ∅ = ∅.
Proof.
  unfold echans. by rewrite gmultiset_elements_empty.
Qed.

Lemma echans_singleton e : echans {[+ e +]} = fchans e.
Proof.
  unfold echans. rewrite gmultiset_elements_singleton. simpl. set_solver.
Qed.

(** Substituting a channel that occurs in no thread is the identity. *)
Lemma echswap_comm c d E : echswap c d E = echswap d c E.
Proof.
  unfold echswap. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite eswap_comm.
Qed.

Lemma echswap_echsubst_flip a b E :
  echswap a b (echsubst b a E) = echsubst a b E.
Proof.
  unfold echswap, echsubst. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite eswap_chsubst_flip.
Qed.

Lemma echsubst_id c d E : c ∉ echans E → echsubst c d E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; intros Hc.
  - unfold echsubst. by rewrite gmultiset_map_empty.
  - rewrite echans_disj_union, echans_singleton in Hc.
    unfold echsubst in *.
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
    rewrite chsubst_id by set_solver. rewrite IH by set_solver. done.
Qed.

Lemma echsubst_disj_union c d E1 E2 :
  echsubst c d (E1 ⊎ E2) = echsubst c d E1 ⊎ echsubst c d E2.
Proof. apply gmultiset_map_disj_union. Qed.

Lemma echsubst_singleton c d e :
  echsubst c d {[+ e +]} = {[+ chsubst c d e +]}.
Proof. apply gmultiset_map_singleton. Qed.

(** The soup substitution only introduces the surviving name. *)
Lemma echans_echsubst_sub c d E :
  echans (echsubst c d E) ⊆ echans E ∪ {[d]}.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echsubst. rewrite gmultiset_map_empty. set_solver.
  - unfold echsubst in *.
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton,
      !echans_disj_union, !echans_singleton.
    pose proof (fchans_chsubst c d e). set_solver.
Qed.

(** ** The labelled transition relation (Fig. 3)

    In P-Act-Fork the new channel c must be globally fresh: not
    restricted yet, and not free in any thread (the paper keeps this
    implicit in the well-formedness of the "new" name). Rules
    P-Act-Msg and P-Act-Close write the paper's C ∪ {c} source as
    membership c ∈ C. *)

Inductive proc_step : proc → plabel → proc → Prop :=
  | PStepSession C E e σ e' :                          (* P-Act-Session *)
      (* one rule for every external offer, forwarding included: all
         of the label's subjects must be free *)
      tstep e (LSess σ) e' →
      subjs σ ## C →
      proc_step (C, E ⊎ {[+ e +]}) (PSess σ)
                (C ∖ sentc σ, E ⊎ {[+ e' +]})
  | PStepBeta C E e e' :                               (* P-Act-Beta *)
      tstep e LBeta e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | PStepFork C E e c v e' :                           (* P-Act-Fork *)
      tstep e (LFork c v) e' →
      c ∉ C → c ∉ echans E → c ∉ fchans e →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∪ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]})
  | PStepMsg C E c v e e' f f' :                       (* P-Act-Msg *)
      tstep e (LSess (SSend c v)) e' →
      tstep f (LSess (SRecv c v)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepClose C E c e e' f f' :                       (* P-Act-Close *)
      tstep e (LSess (SClos c)) e' →
      tstep f (LSess (SClos c)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepLink C E e c d e' :                           (* P-Act-Link *)
      (* the paper's rule, verbatim: the removed end c must be
         restricted, and the whole resulting configuration — the other
         threads AND the actor's continuation — is substituted, so
         c's peer gets fused with whoever holds d.  The label set is
         unordered, so this one rule also removes the other end
         (instantiate c and d the other way round, [upair_comm]).
         Soundness of the whole-soup substitution against the logical
         relation rests on channel tightness — without it the
         substitution rewrites junk-carrying siblings and no
         renaming-transport lemma exists (mechanized counterexamples: commit 25c38d8).
         The ends need not be distinct: for c = d the substitution is
         the identity and the rule simply releases the name, which is
         what a self-forwarding means — the thread held both ends, so
         the channel is spent.  Releasing is safe precisely because a
         configuration carrying a self-forwarding on a FREE channel
         offers the singleton label and is refuted by the relation, so
         no live name can be stolen this way.  There is no separate
         lifted rule: an offer with both ends free is P-Act-Session. *)
      tstep e (LSess (SLink {[c; d]})) e' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∖ {[c]}, echsubst c d (E ⊎ {[+ e' +]})).

(** Process reduction p --> p' is p --τ--> p'. *)
Definition preduction (p p' : proc) : Prop := proc_step p PTau p'.
Notation pred_star := (rtc preduction).

(** Irreducible processes (Def. 3.1). *)
Definition pirred (p : proc) : Prop := ∀ π p', ¬ proc_step p π p'.

(** ** Properties of processes (Defs. 2.4–2.6) *)

(** A terminated process has released all channels; the main thread
    has computed a value and all forked threads have reduced to ∗. *)
Definition terminated (p : proc) : Prop :=
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ (∀ e, e ∈ E → e = EUnit).

Definition safe (p : proc) : Prop :=
  terminated p ∨ ∃ p', preduction p p'.

Definition deadlock_free (p : proc) : Prop :=
  ∀ p', pred_star p p' → safe p'.

(** Inversion for session-labelled process transitions: only
    P-Act-Session can produce them. *)
Lemma proc_step_sess_inv C E σ p' :
  proc_step (C, E) (PSess σ) p' →
  ∃ E0 e e',
    E = E0 ⊎ {[+ e +]} ∧ tstep e (LSess σ) e' ∧ subjs σ ## C ∧
    p' = (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
Proof. intros H. inversion H; simplify_eq. eauto 10. Qed.

(** ** Internalizing communication (Lemma 2.3)

    Two disjoint processes communicating over an external channel c can
    be put together and c closed over, turning the communication into
    an internal τ step. Note: following P-Act-Msg (Fig. 3), the
    combined channel set is unchanged — the channels sent along c stay
    in scope of the combined process (the draft's Eq. (9) instead
    subtracts sentc(c!v); that spot is marked "XXX (not yet)" in the
    margin, and is not derivable from Fig. 3 as stated). *)

Lemma internalize_comm C1 E1 C1' E1' C2 E2 C2' E2' c v :
  proc_step (C1, E1) (PSess (SSend c v)) (C1', E1') →
  proc_step (C2, E2) (PSess (SRecv c v)) (C2', E2') →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  proc_step (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) PTau
            (C1 ∪ C2 ∪ {[c]}, E1' ⊎ E2').
Proof.
  intros Hs Hr _ _ _.
  apply proc_step_sess_inv in Hs as (F1 & e & e' & -> & Hstep1 & _ & Heq1).
  apply proc_step_sess_inv in Hr as (F2 & f & f' & -> & Hstep2 & _ & Heq2).
  simplify_eq.
  assert (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})
          = (F1 ⊎ F2) ⊎ {[+ e +]} ⊎ {[+ f +]}) as -> by multiset_solver.
  assert (F1 ⊎ {[+ e' +]} ⊎ (F2 ⊎ {[+ f' +]})
          = (F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}) as -> by multiset_solver.
  eapply PStepMsg; [done|done|set_solver].
Qed.
