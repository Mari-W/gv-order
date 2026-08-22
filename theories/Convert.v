(** * Conversion: the logical relation is invariant under ≈

    The semantic counterpart of E-Conv. Where Typing.v's conversion
    rule lets a term change its type along ≈, this file shows the
    logical relation does not notice:

      teq T T' → Vrel n Σ T v → Vrel n Σ T' v      ([Vrel_teq])
      teq T T' → Erel n Σ T e → Erel n Σ T' e      ([Erel_teq])
      teq T T' → sem_typed Σ Δ e T → sem_typed Σ Δ e T'
                                                  ([sem_typed_teq])

    ≈ is symmetric, so each of these is really a biconditional
    ([Vrel_teq_iff], [Erel_teq_iff]).

    ** The shape of the induction

    Both relations are step-indexed, and ≈ is a step-indexed
    approximation too, which is what makes this go through without any
    coinduction: everything is an induction on the step index.

    [Vrel] at index n needs [Vrel] and [Erel] at every j < n (the ⊸
    and □ clauses quantify over lower levels), while [Erel] at index n
    needs [Vrel] at the *same* n (the irreducible-value conjunct) and
    [Erel] at n-1 (every transition case). So the two are proved
    simultaneously by strong induction on n, with [Vrel]'s half run by
    an inner structural induction on the type — which terminates
    because ⊗, ⊕ and the ⊸/□ payloads all shrink the type, and the
    session case is a leaf: [Vrel]'s [TSess] clause stores the protocol
    up to ≈ and never descends into it.

    ** Why the result type is carried through the step cases for free

    [Ecase] threads the result type T unchanged through every
    transition — the types it *inspects* (the payload U and
    continuation s of a communication) come from Σ via [senv_hd], not
    from T. So the [Erel] half is a routine relay of the induction
    hypothesis, exactly as the old [Erel_sess_conv] was; the content is
    all in the [Vrel] half. *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Relation.

(** The two halves have to be proved together: see the header. *)
Lemma Vrel_Erel_teq n :
  (∀ Σ T T' v, teq T T' → Vrel n Σ T v → Vrel n Σ T' v) ∧
  (∀ Σ T T' e, teq T T' → Erel n Σ T e → Erel n Σ T' e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ Σ T T' v, teq T T' → Vrel n Σ T v → Vrel n Σ T' v) as HV.
  { intros Σ T. revert Σ. unfold teq.
    induction T as [|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1|s];
      intros Σ [] v Hteq HVv; try done.
    - (* ⊸ *)
      destruct Hteq as [Hteq1 Hteq2].
      apply Vrel_lolli_iff in HVv as [(eb & -> & Hsup & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!; [done|done|].
        intros j Σ' w Hj Hd HVw.
        eapply (proj2 (IHn j Hj)); [exact Hteq2|].
        apply HL; [done|done|].
        eapply (proj1 (IHn j Hj)); [|exact HVw].
        by apply teq_sym.
      + apply Vrel_lolli_iff. right. exists k, T0. split_and!; [done|done|done|].
        eapply teq_trans; [exact Ht|]. by split.
    - (* ⊗ *)
      destruct Hteq as [Hteq1 Hteq2].
      apply Vrel_prod_iff in HVv as (v1 & v2 & Σ1 & Σ2 & -> & Hsp & H1 & H2).
      apply Vrel_prod_iff. exists v1, v2, Σ1, Σ2. split_and!; eauto.
    - (* ⊕ *)
      destruct Hteq as [Hteq1 Hteq2].
      apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; eauto.
    - (* □ *)
      apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply Vrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros j Hj. eapply (proj2 (IHn j Hj)); [exact Hteq|]. by apply HK.
    - (* session: the protocol is stored up to ≈ already *)
      apply Vrel_sess_iff in HVv as (c & s0 & -> & -> & Hs0).
      apply Vrel_sess_iff. exists c, s0. split_and!; [done|done|].
      by eapply seq_trans. }
  split; [exact HV|].
  intros Σ T T' e Hteq HE.
  destruct n as [|n']; [apply Erel_0|].
  (* the induction hypothesis, packaged for the transition cases:
     every one of them continues at a strictly smaller index *)
  assert (∀ j Σ0 T0 T0' e0,
            j < S n' → teq T0 T0' → Erel j Σ0 T0 e0 → Erel j Σ0 T0' e0) as HEj.
  { intros j ? ? ? ? Hj. by apply (proj2 (IHn j Hj)). }
  apply Erel_S_iff in HE as (Hval & Hstep).
  apply Erel_S_iff. split.
  { intros Hirr. eapply HV; [exact Hteq|]. by apply Hval. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c w]; simpl in Hstep |- *.
  - eapply HEj; [lia|exact Hteq|exact Hstep].
  - destruct Hstep as (Σ1 & U & u & Hhd & Hc & H).
    exists Σ1, U, u. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HVw.
    eapply HEj; [lia|exact Hteq|]. by apply H.
  - destruct Hstep as (Σ1 & Σ2 & U & u & Hhd & Hd & Hc1 & Hc2 & HVw & HE').
    exists Σ1, Σ2, U, u. split_and!; try done.
    eapply HEj; [lia|exact Hteq|exact HE'].
  - destruct Hstep as (Σ1 & Hhd & Hc & HE').
    exists Σ1. split_and!; [done|done|].
    eapply HEj; [lia|exact Hteq|exact HE'].
  - destruct Hstep as (c & d & Σ1 & sc & sd & -> & ? & -> & ? & ? & ? & HE').
    eexists _, _, _, _, _. split_and!; [done..|].
    eapply HEj; [lia|exact Hteq|exact HE'].
  - intros Hcd. specialize (Hstep Hcd) as (Σ1 & Σ2 & sf & Hsp & HVw & HE').
    exists Σ1, Σ2, sf. split_and!; [done|done|].
    eapply HEj; [lia|exact Hteq|exact HE'].
Qed.

Lemma Vrel_teq n Σ T T' v : teq T T' → Vrel n Σ T v → Vrel n Σ T' v.
Proof. apply (proj1 (Vrel_Erel_teq n)). Qed.

Lemma Erel_teq n Σ T T' e : teq T T' → Erel n Σ T e → Erel n Σ T' e.
Proof. apply (proj2 (Vrel_Erel_teq n)). Qed.

Lemma Vrel_teq_iff n Σ T T' v : teq T T' → Vrel n Σ T v ↔ Vrel n Σ T' v.
Proof. intros Ht. split; apply Vrel_teq; [done|by apply teq_sym]. Qed.

Lemma Erel_teq_iff n Σ T T' e : teq T T' → Erel n Σ T e ↔ Erel n Σ T' e.
Proof. intros Ht. split; apply Erel_teq; [done|by apply teq_sym]. Qed.

(** The compositionality lemma for E-Conv: semantic typing transports
    along ≈. This is the semantic side of Typing.v's [typed_conv], and
    the case the fundamental theorem discharges with it. *)
Lemma sem_typed_teq Σ Δ e T T' :
  teq T T' → sem_typed Σ Δ e T → sem_typed Σ Δ e T'.
Proof.
  intros Ht He n Σ' γ Hd Hg. eapply Erel_teq; [exact Ht|]. by apply He.
Qed.

(** ** Reading a constant back out of the ⊸ clause

    [konst_ty] is not closed under ≈, so the relation types a constant
    at its own [konst_ty] type and converts ([Relation.Vdef]). Every
    [konst_ty] type is a ⊸, so a constant related at T ⊸ U is typed at
    some A ⊸ B with A ≈ T and B ≈ U. Users then [inversion] the
    [konst_ty] to fix A and B, convert the argument along [teq_sym] of
    the first component, and convert the result along the second —
    which is the only way the ≈-quotient shows up in the constant's
    reduction lemmas. *)
Lemma Vrel_konst_inv n Σ T U k :
  Vrel n Σ (TLolli T U) (Konst k) →
  ∃ A B, konst_ty k (TLolli A B) ∧ teq A T ∧ teq B U ∧ Σ = ∅.
Proof.
  intros HV. apply Vrel_lolli_iff in HV as [(eb & ? & _)|(k' & T0 & Hk' & -> & Hk & Ht)];
    [done|simplify_eq].
  destruct Hk; destruct Ht as [Ht1 Ht2]; eauto 10 using konst_ty.
Qed.

(** ** Conversion at a session type

    The special case the old E-Conv was stated at, kept under its
    former name so that its users need not change. *)

Lemma Vrel_sess_seq n Σ s s' v :
  seq s s' → Vrel n Σ (TSess s) v → Vrel n Σ (TSess s') v.
Proof. intros Hs. by apply Vrel_teq. Qed.

Lemma Erel_sess_seq n Σ s s' e :
  seq s s' → Erel n Σ (TSess s) e → Erel n Σ (TSess s') e.
Proof. intros Hs. by apply Erel_teq. Qed.

Lemma Vrel_sess_conv n Σ s s' v :
  unfoldS s = unfoldS s' → Vrel n Σ (TSess s) v → Vrel n Σ (TSess s') v.
Proof. intros Hu. by apply Vrel_sess_seq, unfoldS_seq. Qed.

Lemma Erel_sess_conv n Σ s s' e :
  unfoldS s = unfoldS s' → Erel n Σ (TSess s) e → Erel n Σ (TSess s') e.
Proof. intros Hu. by apply Erel_sess_seq, unfoldS_seq. Qed.
