(** * The fundamental property for processes (Theorem 3.13)

    Tying the knot.  The three composition principles are proved
    simultaneously by strong induction on the step index -- each of
    [term_S], [independent_S] and [connect_S] takes the induction
    hypothesis as an explicit parameter, so [comp_all] below is the
    only place the recursion is actually tied -- and the syntactic
    type system follows rule by rule. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Independence Connection Term.

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
  intros Hp He n. apply Prel_term; [done|].
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
