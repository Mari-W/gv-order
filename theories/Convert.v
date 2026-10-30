(** * Conversion: the logical relation is invariant under ≈

    The semantic counterpart of E-Conv. Where Typing.v's conversion
    rule lets a term change its type along ≈, this file shows the
    logical relation does not notice:

      teq T T' → Vrel n W Θ T v → Vrel n W Θ T' v        ([Vrel_teq])
      teq T T' → Erel n W Θ T F e → Erel n W Θ T' F e    ([Erel_teq])
      teq T T' → sem_typed W Θ Δ F e T → sem_typed W Θ Δ F e T'
                                                        ([sem_typed_teq])

    in every (well-formed) world and under every frame. ≈ keeps the
    points of a type outside its session types on the nose. Session
    payloads may differ, so at [new] the fresh point is renamed away
    from the points of the converted type ([Points.Erel_new_rename]).

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
    continuation s of a communication) come from Θ via [tenv_hd], not
    from T. So the [Erel] half is a routine relay of the induction
    hypothesis, exactly as the old [Erel_sess_conv] was; the content is
    all in the [Vrel] half. *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Points.

(** ≈ commutes with instantiating point variables: the points of
    both sides agree on the nose. *)
Lemma eqT_pinst ρ T : ∀ U σ, eqT ρ T U → eqT ρ (pinst_ty σ T) (pinst_ty σ U).
Proof.
  induction T; intros [] σ; simpl; try done; naive_solver.
Qed.

Lemma teq_ty_inst xs T U : teq T U → teq (ty_inst xs T) (ty_inst xs U).
Proof. apply eqT_pinst. Qed.

(** ≈_W absorbs ≈ on the right. *)
Lemma teqW_teq_r W T : ∀ U U', teqW W T U → teq U U' → teqW W T U'.
Proof.
  unfold teq. induction T; intros [] [] H1 H2; simpl in *; try done.
  - destruct H1 as (? & ? & ? & ?), H2 as (<- & <- & ? & ?). split_and!; eauto.
  - destruct H1, H2. split; eauto.
  - destruct H1, H2. split; eauto.
  - destruct H1 as (-> & ? & ? & ?), H2 as (<- & <- & <- & ?). split_and!; eauto.
  - destruct H1 as [? ?], H2 as [<- ?]. split; [done|]. by eapply seq_trans.
Qed.

(** The two halves have to be proved together: see the header. *)
Lemma Vrel_Erel_teq n :
  (∀ W Θ T T' v, teq T T' → Vrel n W Θ T v → Vrel n W Θ T' v) ∧
  (∀ W Θ T T' F e, world_wf W → teq T T' → Erel n W Θ T F e → Erel n W Θ T' F e).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W Θ T T' v, teq T T' → Vrel n W Θ T v → Vrel n W Θ T' v) as HV.
  { intros W Θ T. revert Θ. unfold teq.
    induction T as [|ub lb T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2
                   |m C0 ub T1 IHT1|s x];
      intros Θ [] v Hteq HVv; try done.
    - (* ⊸ *)
      destruct Hteq as (<- & <- & Hteq1 & Hteq2).
      apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hsup & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!; [done|done|done|].
        intros W' j Θ' Θ'' w F HW Hj Hc HVw Hub.
        eapply (proj2 (IHn j Hj)); [apply HW|exact Hteq2|].
        apply (HL W' j Θ' Θ'' w F); [done|done|done| |done].
        eapply (proj1 (IHn j Hj)); [|exact HVw].
        by apply teq_sym.
      + apply Vrel_lolli_iff. right. exists k, T0. split_and!; [done|done|done|].
        eapply teqW_teq_r; [exact Ht|]. by split_and!.
    - (* ⊗ *)
      destruct Hteq as [Hteq1 Hteq2].
      apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      apply Vrel_prod_iff. exists v1, v2, Θ1, Θ2. split_and!; eauto.
    - (* ⊕ *)
      destruct Hteq as [Hteq1 Hteq2].
      apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; eauto.
    - (* □ *)
      destruct Hteq as (<- & <- & <- & Hteq).
      apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply Vrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros W' j xs F HW Hj Hxs HC Hub. eapply (proj2 (IHn j Hj)).

      + apply HW.
      + by apply teq_ty_inst.
      + by apply HK.
    - (* session: the protocol is stored up to ≈ already *)
      destruct Hteq as [<- Hs].
      apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs0 & Hx).
      apply Vrel_sess_iff. exists c, s0, k. split_and!; [done|done| |done].
      by eapply seq_trans. }
  split; [exact HV|].
  destruct n as [|n']; [intros; apply Erel_0|].
  intros W Θ T T' F e HW Hteq HE. revert T' HW Hteq.
  induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
  intros T' HW Hteq.
  assert (∀ j W0 Θ0 T0 T0' F0 e0, j < S n' → world_wf W0 → teq T0 T0' →
            Erel j W0 Θ0 T0 F0 e0 → Erel j W0 Θ0 T0' F0 e0) as HEj.
  { intros j ? ? ? ? ? ? Hj. by apply (proj2 (IHn j Hj)). }
  apply Erel_S_iff. split_and!; [|done|].
  { intros Hirr. eapply HV; [exact Hteq|]. by apply Hval. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
  - eapply HEj; [lia|done|exact Hteq|exact Hstep].
  - destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ1c Θ' HW0 Hj Hext Hc HVw.
    eapply HEj; [lia|apply HW0|exact Hteq|]. by apply (H W' j Θ2 Θ1c Θ').
  - destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                       Hhd & Hc & HVw & Hext & HE').
    exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done.
    exact (proj2 HE' T' HW Hteq).
  - destruct Hstep as (Θ1 & k & Hhd & HE').
    exists Θ1, k. split; [done|].
    exact (proj2 HE' T' HW Hteq).
  - destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                       -> & ? & ? & ? & ? & HE').
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|].
    exact (proj2 HE' T' HW Hteq).
  - (* O-New: rename the new point away from the points of T' *)
    intros Hc. destruct (Hstep Hc) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
    destruct (fresh_const (w_names W ∪ tenv_roots Θ ∪ ty_roots T ∪ ty_roots T'
                           ∪ frame_roots F)) as [a1 Ha1].
    destruct (Erel_new_rename _ _ _ _ _ _ _ c s s' a a1 HW Hfr Ha
                ltac:(set_solver) HE') as (W1' & Hfr' & HE1).
    exists a1, (stysw a a1 s), (stysw a a1 s'), W1'. split_and!.
    + set_solver.
    + by apply sdual_sw.
    + done.
    + eapply HEj; [lia| |exact Hteq|exact HE1].
      by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
  - destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
    exists Θ1, Θ2, ub, lb. split_and!; [done|done|].
    eapply HEj; [lia|done|exact Hteq|exact HE'].
Qed.

Lemma Vrel_teq n W Θ T T' v : teq T T' → Vrel n W Θ T v → Vrel n W Θ T' v.
Proof. apply (proj1 (Vrel_Erel_teq n)). Qed.

Lemma Erel_teq n W Θ T T' F e :
  world_wf W → teq T T' → Erel n W Θ T F e → Erel n W Θ T' F e.
Proof. apply (proj2 (Vrel_Erel_teq n)). Qed.

Lemma Vrel_teq_iff n W Θ T T' v :
  teq T T' → Vrel n W Θ T v ↔ Vrel n W Θ T' v.
Proof. intros Ht. split; apply Vrel_teq; [done|by apply teq_sym]. Qed.

Lemma Erel_teq_iff n W Θ T T' F e :
  world_wf W → teq T T' → Erel n W Θ T F e ↔ Erel n W Θ T' F e.
Proof. intros HW Ht. split; apply Erel_teq; [done|done|done|by apply teq_sym]. Qed.

(** The compositionality lemma for E-Conv: semantic typing transports
    along ≈, under any world and frame. *)
Lemma sem_typed_teq W Θ Δ F e T T' :
  teq T T' → sem_typed W Θ Δ F e T → sem_typed W Θ Δ F e T'.
Proof.
  intros Ht He n W' Θ' Θ'' γ HW Hd Hg. eapply Erel_teq; [apply HW|exact Ht|]. by apply (He n W' Θ').
Qed.

(** ** Reading a constant back out of the ⊸ clause

    [konst_ty] is not closed under ≈, so the relation types a constant
    at its own [konst_ty] type and converts ([Relation.Vdef]). Every
    [konst_ty] type is a ⊸, so a constant related at T ⊸ U is typed at
    some A ⊸ B with A ≈_W T and B ≈_W U. Users then [inversion] the
    [konst_ty] to fix A and B, convert the argument along [teq_sym] of
    the first component, and convert the result along the second —
    which is the only way the ≈-quotient shows up in the constant's
    reduction lemmas. *)
Lemma Vrel_konst_inv n W Θ ub lb T U k :
  Vrel n W Θ (TLolli ub lb T U) (Konst k) →
  ∃ ub0 lb0 A B, konst_ty (w_eq W) (w_lt W) (pt_known W) k (TLolli ub0 lb0 A B) ∧
    opt_rel (pteqW W) ub0 ub ∧ opt_rel (pteqW W) lb0 lb ∧
    teqW W A T ∧ teqW W B U ∧ Θ = ∅.
Proof.
  intros HV. apply Vrel_lolli_iff in HV
    as [(eb & ? & _)|(k' & T0 & Hk' & -> & Hk & Ht)]; [done|simplify_eq].
  destruct T0; try done. destruct Ht as (? & ? & Ht1 & Ht2). eauto 10.
Qed.

(** ** Conversion at a session type *)

Lemma Vrel_sess_seq n W Θ s s' x v :
  seq s s' → Vrel n W Θ (TSess s x) v → Vrel n W Θ (TSess s' x) v.
Proof. intros Hs. apply Vrel_teq. by split. Qed.

Lemma Erel_sess_seq n W Θ s s' x F e :
  world_wf W → seq s s' → Erel n W Θ (TSess s x) F e → Erel n W Θ (TSess s' x) F e.
Proof. intros HW Hs. apply Erel_teq; [done|]. by split. Qed.
