(** * The lock-free judgment Σ ⊩^N _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental : strict W → Σ ⊩^N _ W p : T → Σ ⊪_W p : T
      lf_soundness   : lfworld W → ∅ ⊩^N _ W p : T → lock_free p

    Σ ⊩^N _ W p : T is process typing [ptyped] at Some N together with
    the guard of every thread, ⊢▷ p. P-Term of [ptyped] asks at a finite
    N a ticket count that meets the transformer of the thread at 0, and
    P-Connect types the cut at exactly dual types ([senv_dual]). No rule
    renames families. The proof reads fsem^N off the typing through
    [fsem_of_cost] and the live relation through
    [live_fundamental_typed], inside [lf_p_term]. *)

From GV Require Import soup.LFAdequacy.
From GV Require Export soup.LFCompose static.FundamentalProc.

Notation "Σ ⊩^ N '_' W p : T" := (ptyped (Some N) W Σ p T ∧ ⊢▷ p)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N  '_'  W  p  :  T").

(** ** The fundamental theorem *)

Theorem lf_fundamental N W Σ p T : strict W → Σ ⊩^N _ W p : T → Σ ⊪_W p : T.
Proof.
  intros HW [Hty Hg]. remember (Some N) as N' eqn:EN. revert HW Hg. induction Hty as
    [W Σ ΘB C0 t T a c ϑ Hp HB HΣ Hpf Hd Ht Hfin
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hw1 Hw2 Hfam HJ];
    intros HW Hg; subst.
  - destruct Hfin as [Hn|[tk Hm]]; [discriminate|].
    eapply lf_p_term; [done|done|done|done|exact Hd|exact Ht| |exact Hm].
    apply Hg. simpl. multiset_solver.
  - destruct (proj1 (p_join_iff_connect W1 W2 Hw1 Hw2 Hfam) HJ) as (HS1 & HS2 & _).
    apply lf_p_connect; auto.
    + apply IH1; [done|]. intros t Ht. apply Hg. simpl. multiset_solver.
    + apply IH2; [done|]. intros t Ht. apply Hg. simpl. multiset_solver.
Qed.

(** ** Soundness *)

Theorem lf_soundness N W p T : lfworld W → ∅ ⊩^N _ W p : T → lock_free p.
Proof.
  intros HW Hty. apply (lf_adequacy W T p HW). exact (lf_fundamental N W ∅ p T (proj1 HW) Hty).
Qed.
