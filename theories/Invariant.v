(** * A proof method for membership in the process logical relation

    Proving [Prel n Σ T p] directly requires an induction on the step
    index interleaved with the transition analysis of p, which forces
    one lemma per reachable configuration, sequenced bottom-up.  This
    file factors the step-index recursion out once and for all:

    - [Prel_by_invariant]: to show that every configuration in a
      step-closed family I is in the relation at every index, it
      suffices to check I against the one-step obligations ([inv_case]
      — the index-free image of [Pcase]).  The proof is a single
      strong induction on the index.

    - [sem_ptyped_closed]: for closed processes (Σ = ∅, return type ∗)
      whose threads mention only restricted channels, no session
      transition is ever enabled, and the semantic judgment collapses
      to a reachability invariant: closure under τ-steps plus
      termination of irreducible states.  This is a converse to
      adequacy for closed processes.

    The file also collects generic single-thread transition inversion
    lemmas for the common term shapes, used to enumerate the
    transitions of concrete processes. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Fundamental.

(** ** Subjects of session transitions are free channels *)

Lemma tstep_sess_subj e σ e' :
  tstep e (LSess σ) e' → subjs σ ⊆ fchans e.
Proof.
  intros H. remember (LSess σ) as α eqn:Hα.
  induction H; subst; simpl; try set_solver.
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; simpl; set_solver end.
Qed.

(** Every session label names at least one subject — a forwarding
    label carries a pair, degenerate or not. *)
Lemma subjs_ne_empty e σ e' : tstep e (LSess σ) e' → subjs σ ≠ ∅.
Proof.
  intros H. destruct σ; simpl; try (clear; set_solver).
  destruct (tstep_link_shape _ _ _ H) as (a & b & ->). clear. set_solver.
Qed.

(** ** The invariant rule *)

(** The one-step obligations for a family [I], mirroring [Pcase] with
    every step-indexed hypothesis strengthened to all indices and
    every step-indexed conclusion replaced by membership in [I].  The
    strengthening is what makes the rule index-free; it is harmless
    whenever the exchanged values are of first-order type, where
    membership in the value relation at one index determines the
    value. *)
Definition inv_case (I : senv → ty → proc → Prop)
    (Σ : senv) (T : ty) (p : proc) (π : plabel) (p' : proc) : Prop :=
  match π with
  | PTau =>
      p'.1 ## dom Σ →
      I Σ T p'
  | PSess (SRecv c w) =>
      ∃ Σ1 U s,
        Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ j Σ2, Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
          Vrel j Σ2 U w →
          I (<[c := s]> (Σ1 ∪ Σ2)) T p'
  | PSess (SSend c w) =>
      ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
        Σ = <[c := SSnd U s]> (Σ0 ∪ Σv ∪ Σw) ∧
        Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
        c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
        dom σe = fchans w ∩ p.1 ∧
        dom σe ## dom Σ ∧ c ∉ dom σe ∧
        p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
        p'.2 = E0 ⊎ Ew ∧
        (∀ n, Vrel n (Σv ∪ (dual <$> σe)) U w) ∧
        I (<[c := s]> Σ0) T0 (C0, E0) ∧
        topo_split I σe Σw Tw (Cw, Ew) ∧
        ty_one_of T0 Tw T
  | PSess (SClos c) =>
      ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧ I Σ1 T p'
  | PSess (SLink cd) =>
      ∃ c d Σ1 sc sd,
        cd = {[c; d]} ∧ c ≠ d ∧
        Σ = <[c := sc]> (<[d := sd]> Σ1) ∧
        c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
        unfoldS sd = unfoldS (dual sc) ∧
        I Σ1 T p'
  end.

(** A family is an invariant if every member satisfies the termination
    clause and its one-step obligations stay in the family.  There is
    no channel-occurrence obligation: the relation constrains only
    what a configuration DOES, so a thread may mention a channel it
    does not own as long as it never acts on it. *)
Definition proc_invariant (I : senv → ty → proc → Prop) : Prop :=
  ∀ Σ T p, I Σ T p →
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
             (∀ n, Vrel n Σ T v) ∧ (∀ e, e ∈ E → e = EUnit)) ∧
    (∀ π p', proc_step p π p' → inv_case I Σ T p π p').

Lemma Prel_by_invariant I Σ T p :
  proc_invariant I → I Σ T p → ∀ n, Prel n Σ T p.
Proof.
  intros HI HIp n. revert Σ T p HIp.
  induction n as [n IHn] using lt_wf_ind. intros Σ T p HIp.
  destruct n as [|n']; [apply Prel_0|].
  destruct (HI Σ T p HIp) as (Hirr & Hstep).
  apply Prel_S_intro.
  - intros Hpi.
    destruct (Hirr Hpi) as (v & E & -> & Hv & HV & HE). eauto 10.
  - intros π p' Hst. specialize (Hstep π p' Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* τ *)
      intros Hg. apply IHn; [lia|auto].
    + (* input *)
      destruct Hstep as (Σ1 & U & s & -> & Hc & H).
      exists Σ1, U, s. split_and!; [by apply senv_hd_nf|done|].
      intros j Σ2 Hj Hd Hcd Hfr HV.
      apply IHn; [lia|]. eapply H; eauto.
    + (* output *)
      destruct Hstep as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew
        & T0 & Tw & HΣ & Hd1 & Hd2 & Hd3 & Hc1 & Hc2 & Hc3 & Hσe & Hσd
        & Hcσ & Hp1 & Hcw & Hp2 & HV & HI0 & HPo & Hty).
      exists Σ0, Σv, U, s, σe, Σw, C0, E0, Cw, Ew, T0, Tw.
      split_and!; try done.
      * subst Σ. by apply senv_hd_nf.
      * apply IHn; [lia|done].
      * eapply topo_split_mono; [|exact HPo].
        intros Σ' T' q HIq. apply IHn; [lia|done].
    + (* close *)
      destruct Hstep as (Σ1 & -> & Hc & H).
      exists Σ1. split_and!; [by apply senv_hd_nf|done|].
      apply IHn; [lia|done].
    + (* forwarding *)
      destruct Hstep as (c & d & Σ1 & sc & sd & -> & ? & -> & ? & ? & ? & H).
      eexists _, _, _, _, _. split_and!; [done..|]. apply IHn; [lia|done].
Qed.

(** ** Closed processes: the semantic judgment as a reachability
    invariant *)

(** For processes whose threads mention only restricted channels, no
    session transition is enabled (its subject would have to be both
    free in a thread and outside C), so at Σ = ∅ and return type ∗ the
    process relation reduces to: closed under τ-steps, and every
    irreducible member has released all channels and consists of unit
    threads only. *)
Definition closed_invariant (P : proc → Prop) : Prop :=
  ∀ p, P p →
    echans p.2 ⊆ p.1 ∧
    (pirred p →
      p.1 = ∅ ∧ p.2 ≠ ∅ ∧ (∀ e, e ∈ p.2 → e = EUnit)) ∧
    (∀ p', preduction p p' → P p').

Lemma sem_ptyped_closed P p :
  closed_invariant P → P p → sem_ptyped ∅ p TUnit.
Proof.
  intros HP HPp n.
  apply (Prel_by_invariant (λ Σ T q, Σ = ∅ ∧ T = TUnit ∧ P q));
    [|by auto].
  clear p HPp. intros Σ T p (-> & -> & HPp).
  destruct (HP p HPp) as (Hech & Hirr & Hτ). split_and!.
  - intros Hpi. destruct (Hirr Hpi) as (HC & Hne & HE).
    destruct p as [C E]. simpl in *. subst C.
    assert (EUnit ∈ E) as Hin.
    { destruct (gmultiset_choose_or_empty E) as [[x Hx]|]; [|done].
      rewrite <-(HE x Hx). done. }
    exists EUnit, (E ∖ {[+ EUnit +]}).
    split_and!.
    + f_equal. by apply gmultiset_disj_union_difference'.
    + done.
    + intros m. apply Vrel_unit.
    + intros e He. apply HE. multiset_solver.
  - intros π p' Hst.
    destruct π as [|σ]; simpl.
    + intros _. auto.
    + (* no offer is enabled — forwarding included: some subject of
         the label is free in the acting thread, hence restricted by
         the closedness hypothesis, contradicting the rule's guard *)
      exfalso. destruct p as [C E].
      apply proc_step_sess_inv in Hst as (E0 & e0 & e0' & -> & Hts & Hsub & _).
      pose proof (tstep_sess_subj _ _ _ Hts) as Hsu.
      destruct (set_choose_L _ (subjs_ne_empty _ _ _ Hts)) as [x Hx].
      apply (Hsub x); [done|].
      apply Hech. simpl. apply elem_of_echans.
      exists e0. split; [multiset_solver|set_solver].
Qed.

Corollary closed_deadlock_free P p :
  closed_invariant P → P p → deadlock_free p.
Proof. eauto using adequacy, sem_ptyped_closed. Qed.

(** ** A singleton owner family *)

Lemma topo_split_single (P : senv → ty → proc → Prop) d s Σd Td Cd Ed :
  d ∉ dom Σd → d ∉ Cd →
  P (<[d := s]> Σd) Td (Cd, Ed) →
  topo_split P {[d := s]} Σd Td (Cd, Ed).
Proof.
  intros Hd HdC HP.
  replace Σd with (Σd ∪ ∅) by (by rewrite (right_id ∅ (∪))).
  replace Cd with (Cd ∪ ∅ : gset chan) by set_solver.
  replace Ed with (Ed ⊎ ∅) by multiset_solver.
  eapply topo_split_cons.
  - apply lookup_empty.
  - done.
  - set_solver.
  - done.
  - set_solver.
  - set_solver.
  - set_solver.
  - apply map_disjoint_empty_r.
  - set_solver.
  - set_solver.
  - set_solver.
  - exact HP.
  - apply topo_split_nil.
  - left. done.
Qed.

(** ** Generic transition inversions for common thread shapes

    Each lemma states that the listed transitions are the only ones of
    the given shape; they are the building blocks for enumerating the
    transitions of concrete processes. *)

(** The only transition of clos applied to a channel is the close
    action on that channel. *)
Lemma tstep_clos_inv ch α e' :
  tstep (App EClos (Chan ch)) α e' → α = LSess (SClos ch) ∧ e' = EUnit.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Konst _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep (Chan _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

Lemma tstep_recv_chan_inv c α e' :
  tstep (App ERecv (Chan c)) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv c v) ∧ e' = Pair v (Chan c).
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; eauto end.
  - exfalso. match goal with Hs : tstep (Konst _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep (Chan _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

Lemma tstep_send_val_inv v c α e' :
  is_val v →
  tstep (App ESend (Pair v (Chan c))) α e' →
  α = LSess (SSend c v) ∧ e' = Chan c.
Proof.
  intros Hv H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Konst _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      eapply val_no_tstep; [exact Hs|simpl; apply andb_True; done] end.
Qed.

Lemma tstep_letp_recv_inv c K α e' :
  tstep (LetP (App ERecv (Chan c)) K) α e' →
  ∃ v, is_val v ∧ α = LSess (SRecv c v) ∧ e' = LetP (Pair v (Chan c)) K.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - match goal with Hs : tstep (App _ _) _ _ |- _ =>
      apply tstep_recv_chan_inv in Hs as (v & ? & -> & ->); eauto end.
Qed.

Lemma tstep_letp_pair_inv u v K α e' :
  is_val u → is_val v →
  tstep (LetP (Pair u v) K) α e' →
  α = LBeta ∧ e' = subst2 u v K.
Proof.
  intros Hu Hv H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Pair _ _) _ _ |- _ =>
      eapply val_no_tstep; [exact Hs|simpl; apply andb_True; done] end.
Qed.

Lemma tstep_lam_val_inv B v α e' :
  tstep (App (Lam B) v) α e' → is_val v →
  α = LBeta ∧ e' = subst1 v B.
Proof.
  intros H Hv. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ =>
      inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Lam _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep v _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

Lemma tstep_lam_chan_inv B c α e' :
  tstep (App (Lam B) (Chan c)) α e' →
  α = LBeta ∧ e' = subst1 (Chan c) B.
Proof. intros H. exact (tstep_lam_val_inv B (Chan c) α e' H I). Qed.

Lemma tstep_lam_send_inv B v c α e' :
  is_val v →
  tstep (App (Lam B) (App ESend (Pair v (Chan c)))) α e' →
  α = LSess (SSend c v) ∧ e' = App (Lam B) (Chan c).
Proof.
  intros Hv H.
  apply tstep_app_inv in H
    as [(e1' & Hst & _)|[(_ & e2' & Hst & ->)|(_ & Hnv & _)]].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - apply tstep_send_val_inv in Hst as [-> ->]; auto.
  - done.
Qed.

Lemma tstep_lam_fork_inv B v α e' :
  tstep (App (Lam B) (App EFork v)) α e' → is_val v →
  ∃ w, α = LFork w v ∧ e' = App (Lam B) (Chan w).
Proof.
  intros H Hv.
  apply tstep_app_inv in H
    as [(e1' & Hst & _)|[(_ & e2' & Hst & ->)|(_ & Hnv & _)]].
  - exfalso. eapply val_no_tstep; [exact Hst|done].
  - apply tstep_app_inv in Hst
      as [(e1'' & Hst' & _)|[(_ & e2'' & Hst' & ->)|(_ & _ & Hh)]].
    + exfalso. eapply val_no_tstep; [exact Hst'|done].
    + exfalso. eapply val_no_tstep; [exact Hst'|exact Hv].
    + inversion Hh; subst; eauto.
  - done.
Qed.

Lemma tstep_letu_clos_inv c K α e' :
  tstep (LetU (App EClos (Chan c)) K) α e' →
  α = LSess (SClos c) ∧ e' = LetU EUnit K.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - match goal with Hs : tstep (App _ _) _ _ |- _ =>
      apply tstep_clos_inv in Hs as [-> ->]; auto end.
Qed.
