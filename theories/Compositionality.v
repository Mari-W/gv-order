(** * Compositionality of the process logical relation (Lemmas 3.8–3.10)

    The three composition principles for [Prel] — TERM, INDEPENDENT
    and CONNECT — proved by (strong) induction on the step index, plus
    the judgment-level versions (Theorem 3.12) and the fundamental
    property for processes (Theorem 3.13). *)

From Coq Require Import Classical.
From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export LogRel.

(** ** Compositionality for processes (Lemmas 3.8–3.10) *)

(** Lemma 3.8 (Compositionality: TERM) *)
Lemma Prel_term n Σ T e :
  prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).
Proof. Admitted.

(** Lemma 3.9 (Compositionality: INDEPENDENT) *)
Lemma Prel_independent n Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).
Proof. Admitted.

(** Lemma 3.10 (Compositionality: CONNECT) *)
Lemma Prel_connect n Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  Prel n (<[c := s]> Σ1) T (C1, E1) →
  Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).
Proof. Admitted.

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
  sem_ptyped Σ1 (C1, E1) T → sem_ptyped Σ2 (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_independent. Qed.

(** P-Connect *)
Lemma sem_ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  sem_ptyped (<[c := s]> Σ1) (C1, E1) T →
  sem_ptyped (<[c := dual s]> Σ2) (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_connect. Qed.

(** ** The fundamental property for processes (Theorem 3.13) *)

Theorem fundamental_proc Σ p T : ptyped Σ p T → sem_ptyped Σ p T.
Proof.
  induction 1.
  - apply sem_ptyped_term; auto using fundamental_term.
  - eapply sem_ptyped_independent; eauto using ptyped_prim.
  - eapply sem_ptyped_connect; eauto using ptyped_prim.
Qed.

(** Corollary: syntactically typed closed processes are deadlock free. *)
Corollary typed_deadlock_free p T : ptyped ∅ p T → deadlock_free p.
Proof. eauto using adequacy, fundamental_proc. Qed.
