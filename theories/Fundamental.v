(** * TERM (Lemma 3.8), and the fundamental property for processes
      (Theorem 3.13)

    TERM, then the knot: the three composition principles are proved
    simultaneously by strong induction on the step index, each taking
    the induction hypothesis as an explicit parameter, so [comp_all]
    is the only place the recursion is tied. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Independence Connection Terms.

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
    apply Erel_S_iff in HE as (H1 & _). specialize (H1 Hirr1).
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
           |[(F & c & e0 & e0' & f & f' & HeqE & _)
           |(F & e0 & c & d & e0' & HeqE & He0 & HcC & ->)]]]].
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
      * exfalso. clear -HcC. set_solver.
    + apply proc_step_sess_inv in Hst as (F & e0 & e0' & HeqE & He0 & _ & ->).
      symmetry in HeqE. apply gmultiset_singleton_inv in HeqE as [-> ->].
      pose proof (Erel_S_step _ _ _ _ _ _ HE He0) as Hc.
      destruct σ as [c w|c w|c|cd]; simpl in Hc |- *.
      * (* recv *)
        destruct Hc as (Σ1 & U & s & Hhd & Hca & Hcont).
        exists Σ1, U, s. split_and!; [done|done|].
        intros j Σn Hj Hdn Hcn _ HVw.
        specialize (Hcont j Σn Hj Hdn Hcn HVw).
        replace ((∅ : gset chan) ∖ ∅) with (∅ : gset chan) by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]}) with ({[+ e0' +]} : gmultiset expr)
          by multiset_solver.
        apply (IHt j); [lia|done|done].
      * (* send: no restricted channels escape from a channel-free
           process *)
        destruct Hc as (Σ0 & Σv & U & s & (s0 & -> & Hu) & Hd0v & Hc0 & Hcv
                        & HVw & HE').
        exists Σ0, Σv, U, s, ∅, ∅, ∅, {[+ e0' +]}, ∅, ∅, T, TUnit.
        split_and!.
        { eapply senv_hd_intro; [done|senv_perm]. }
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
        destruct Hc as (Σ1 & Hhd & Hca & HE').
        exists Σ1. split_and!; [done|done|].
        replace ((∅ : gset chan) ∖ ∅) with (∅ : gset chan) by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]}) with ({[+ e0' +]} : gmultiset expr)
          by multiset_solver.
        apply (IHt n); [lia|done|done].
      * (* forwarding: the term-level clause is the process-level
           clause, one index below *)
        destruct Hc as (c & d & Σ1 & sc & sd & -> & Hne & -> & Hc1 & Hd1
                        & Hdu & HE').
        exists c, d, Σ1, sc, sd. split_and!; [done..|].
        replace ((∅ : gset chan) ∖ ∅) with (∅ : gset chan) by set_solver.
        replace ((∅ : gmultiset expr) ⊎ {[+ e0' +]})
          with ({[+ e0' +]} : gmultiset expr) by multiset_solver.
        apply (IHt n); [lia|done|done].
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
