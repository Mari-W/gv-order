(** * Progress for the term and process LTS (constructively)

    [act e] computes the action offered at the unique evaluation
    position of [e], or [None] when [e] is irreducible. [act_step] and
    [act_offer] show it is sound and complete for [tstep] (Fig. 2), and
    [proc_progress] lifts this along the five rules of Fig. 3: a
    process either is irreducible or has a transition.

    That disjunction is the paper's step "if p is not irreducible then
    it has some transition". Deriving it here rather than from
    excluded middle is what keeps Lemma 3.5 ([Prel_safe]) and the two
    CONNECT cases of Lemma 3.13 free of axioms.

    A term does not determine its label: T-Act-Recv offers an input for
    every value and T-Act-Fork a channel of every name. So [act]
    returns the redex and [offers] relates it to the family of labels
    that redex admits. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export Processes.

(** ** The action offered by a term *)

Inductive action :=
  | ABeta
  | AFork (v : expr)
  | ARecv (c : chan)
  | ASend (c : chan) (v : expr)
  | AClos (c : chan).

Global Instance action_eq_dec : EqDecision action.
Proof. solve_decision. Defined.

(** The channel a communicating action acts on. *)
Definition asubj (a : action) : option chan :=
  match a with
  | ABeta | AFork _ => None
  | ARecv c | ASend c _ | AClos c => Some c
  end.

(** The redex of [e] under the evaluation contexts of Fig. 2. The
    value side conditions of the right-of-value frames are exactly the
    [is_val] guards below, so the position found is the unique one. *)
Fixpoint act (e : expr) : option action :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ | Lam _ | EBang _ => None
  | App e1 e2 =>
      if is_val e1 then
        if is_val e2 then
          match e1, e2 with
          | Lam _, _ => Some ABeta
          | Konst KFork, v => Some (AFork v)
          | Konst KRecv, Chan c => Some (ARecv c)
          | Konst KSend, Pair v (Chan c) => Some (ASend c v)
          | Konst KClos, Chan c => Some (AClos c)
          | _, _ => None
          end
        else act e2
      else act e1
  | Pair e1 e2 => if is_val e1 then act e2 else act e1
  | LetU e1 e2 =>
      if is_val e1 then match e1 with EUnit => Some ABeta | _ => None end
      else act e1
  | LetP e1 e2 =>
      if is_val e1 then match e1 with Pair _ _ => Some ABeta | _ => None end
      else act e1
  | Inj1 e1 | Inj2 e1 => act e1
  | Case e1 _ _ =>
      if is_val e1 then match e1 with Inj1 _ | Inj2 _ => Some ABeta | _ => None end
      else act e1
  (* [EBang _] is unconditionally a value, so no [is_val] guard is
     needed here: [act e1] is [None] for every other value. *)
  | Force e1 => match e1 with EBang _ => Some ABeta | _ => act e1 end
  end.

(** The labels an action admits. *)
Definition offers (a : action) (α : tlabel) : Prop :=
  match a, α with
  | ABeta, LBeta => True
  | AFork v, LFork _ w => v = w
  | ARecv c, LSess (SRecv d w) => c = d ∧ is_val w
  | ASend c v, LSess (SSend d w) => c = d ∧ v = w
  | AClos c, LSess (SClos d) => c = d
  | _, _ => False
  end.

(** [is_val] is used both as a guard and as a side condition; these
    move between the two readings. *)
Lemma is_val_true e : is_val e → is_val e = true.
Proof. by destruct (is_val e). Qed.

Lemma is_val_of_true e : is_val e = true → is_val e.
Proof. by intros ->. Qed.

(** ** [act] is sound and complete for [tstep] *)

Lemma act_step e α e' : tstep e α e' → ∃ a, act e = Some a ∧ offers a α.
Proof.
  induction 1 as [e α e' Hh|e1 α e1' e2 Hst IH|v e2 α e2' Hv Hst IH
                 |e1 α e1' e2 Hst IH|v e2 α e2' Hv Hst IH
                 |e1 α e1' e2 Hst IH|e1 α e1' e2 Hst IH
                 |e α e' Hst IH|e α e' Hst IH|e α e' e1 e2 Hst IH
                 |e α e' Hst IH]; simpl.
  - (* T-Act-Ctx at the hole: read the redex off the head step *)
    inversion Hh; simplify_eq; simpl;
      repeat match goal with
             | Hb : Is_true (is_val ?u) |- _ => rewrite (is_val_true u Hb)
             end.
    + (* T-Act-App *) by exists ABeta.
    + (* T-Act-Let* *) by exists ABeta.
    + (* T-Act-LetPair *) by exists ABeta.
    + (* T-Act-Fork *) by exists (AFork v).
    + (* T-Act-Recv *) exists (ARecv c). split; [done|by split].
    + (* T-Act-Send *) by exists (ASend c v).
    + (* T-Act-Close *) by exists (AClos c).
    + (* T-Act-Case-Inl *) by exists ABeta.
    + (* T-Act-Case-Inr *) by exists ABeta.
    + (* T-Act-Force *) by exists ABeta.
  - destruct (is_val e1) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - rewrite (is_val_true _ Hv). destruct (is_val e2) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - destruct (is_val e1) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - by rewrite (is_val_true _ Hv).
  - destruct (is_val e1) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - destruct (is_val e1) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - done.
  - done.
  - destruct (is_val e) eqn:Hb; [|done].
    exfalso. eapply val_no_tstep; [exact Hst|by rewrite Hb].
  - (* force: the operand steps, so it cannot be a bang *)
    destruct e as [| | | | | | | | | | | |eb | ]; try done.
    exfalso. eapply val_no_tstep; [exact Hst|done].
Qed.

Lemma act_offer e a α : act e = Some a → offers a α → ∃ e', tstep e α e'.
Proof.
  revert a α.
  induction e as [x| |k|c|e0 IHe|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e1 IH1 e2 IH2|e1 IH|e1 IH|e0 IH0 e1 IH1 e2 IH2
                 |e1 IH|e1 IH];
    simpl; intros a α Ha Hoff; try discriminate.
  - (* application *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (App e1' e2);
        by apply TStepAppL].
    destruct (is_val e2) eqn:Hb2;
      [|destruct (IH2 _ _ Ha Hoff) as [e2' Hst]; exists (App e1 e2');
        apply TStepAppR; [by rewrite Hb1|done]].
    destruct e1 as [| |k| |e0 | | | | | | | | | ]; try discriminate.
    + (* a concurrency primitive *)
      destruct k; simplify_eq.
      * (* T-Act-Fork *)
        destruct α as [|σ|c w]; try done. simpl in Hoff. simplify_eq.
        exists (Chan c). apply TStepHead, HeadFork. by rewrite Hb2.
      * (* T-Act-Recv *)
        destruct e2 as [| | |c | | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ|]; try done.
        destruct σ as [d w|d w|d]; try done.
        destruct Hoff as [-> Hw]. exists (Pair w (Chan d)).
        by apply TStepHead, HeadRecv.
      * (* T-Act-Send *)
        destruct e2 as [| | | | | |v w | | | | | | | ]; try discriminate.
        destruct w as [| | |d | | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ|]; try done.
        destruct σ as [d' w'|d' w'|d']; try done.
        destruct Hoff as [-> ->].
        pose proof (is_val_of_true _ Hb2) as Hv2. simpl in Hv2.
        apply andb_True in Hv2 as [Hv _].
        exists (Chan d'). by apply TStepHead, HeadSend.
      * (* T-Act-Close *)
        destruct e2 as [| | |c | | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ|]; try done.
        destruct σ as [d w|d w|d]; try done. simpl in Hoff. simplify_eq.
        exists EUnit. by apply TStepHead, HeadClos.
    + (* T-Act-App *)
      simplify_eq. destruct α; try done.
      exists (subst1 e2 e0). apply TStepHead, HeadApp. by rewrite Hb2.
  - (* pair *)
    destruct (is_val e1) eqn:Hb1.
    + destruct (IH2 _ _ Ha Hoff) as [e2' Hst]. exists (Pair e1 e2').
      apply TStepPairR; [by rewrite Hb1|done].
    + destruct (IH1 _ _ Ha Hoff) as [e1' Hst]. exists (Pair e1' e2).
      by apply TStepPairL.
  - (* let ∗ = e1 in e2 *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetU e1' e2);
        by apply TStepLetU].
    destruct e1; try discriminate. simplify_eq.
    destruct α; try done. exists e2. by apply TStepHead, HeadLetU.
  - (* let ⟨a,b⟩ = e1 in e2 *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetP e1' e2);
        by apply TStepLetP].
    destruct e1 as [| | | | | |u w | | | | | | | ]; try discriminate.
    simplify_eq. destruct α; try done.
    pose proof (is_val_of_true _ Hb1) as Hv1. simpl in Hv1.
    apply andb_True in Hv1 as [Hu Hw].
    exists (subst2 u w e2). by apply TStepHead, HeadLetP.
  - (* inl *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj1 e1').
    by apply TStepInj1.
  - (* inr *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj2 e1').
    by apply TStepInj2.
  - (* case *)
    destruct (is_val e0) eqn:Hb0;
      [|destruct (IH0 _ _ Ha Hoff) as [e0' Hst]; exists (Case e0' e1 e2);
        by apply TStepCase].
    destruct e0 as [| | | | | | | | |v |w | | | ]; try discriminate.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 v e1). apply TStepHead, HeadCase1. by rewrite Hb0.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 w e2). apply TStepHead, HeadCase2. by rewrite Hb0.
  - (* force (the [EBang] case above is a value, hence discriminated) *)
    destruct e1 as [| | | | | | | | | | | |eb | ];
      try (destruct (IH _ _ Ha Hoff) as [e1' Hst]; exists (Force e1');
           by apply TStepForce).
    simplify_eq. destruct α; try done.
    exists eb. by apply TStepHead, HeadForce.
Qed.

(** ** Consequences at the term level *)

Lemma act_None_irred e : act e = None → irred e.
Proof. intros Ha α e' Hst. apply act_step in Hst as (a & ? & _). congruence. Qed.

Lemma act_send_val e c v : act e = Some (ASend c v) → is_val v.
Proof.
  intros Ha.
  destruct (act_offer _ _ (LSess (SSend c v)) Ha (conj eq_refl eq_refl))
    as [e' Hst].
  by eapply tstep_send_val.
Qed.

(** Progress for terms: an expression is irreducible or it steps. *)
Lemma tstep_progress e : irred e ∨ ∃ α e', tstep e α e'.
Proof.
  destruct (act e) as [a|] eqn:Ha; [right|left; by apply act_None_irred].
  destruct a as [|v|c|c v|c].
  - destruct (act_offer _ _ LBeta Ha I) as [e' ?]. by exists LBeta, e'.
  - destruct (act_offer _ _ (LFork "" v) Ha eq_refl) as [e' ?].
    by exists (LFork "" v), e'.
  - destruct (act_offer _ _ (LSess (SRecv c EUnit)) Ha (conj eq_refl I))
      as [e' ?].
    by exists (LSess (SRecv c EUnit)), e'.
  - destruct (act_offer _ _ (LSess (SSend c v)) Ha (conj eq_refl eq_refl))
      as [e' ?].
    by exists (LSess (SSend c v)), e'.
  - destruct (act_offer _ _ (LSess (SClos c)) Ha eq_refl) as [e' ?].
    by exists (LSess (SClos c)), e'.
Qed.

(** ** Reading an action back off a label *)

Lemma offers_beta a : offers a LBeta → a = ABeta.
Proof. by destruct a. Qed.

Lemma offers_fork a c v : offers a (LFork c v) → a = AFork v.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_send a c v : offers a (LSess (SSend c v)) → a = ASend c v.
Proof. destruct a; try done. by intros [-> ->]. Qed.

Lemma offers_recv a c v : offers a (LSess (SRecv c v)) → a = ARecv c.
Proof. destruct a; try done. by intros [-> _]. Qed.

Lemma offers_clos a c : offers a (LSess (SClos c)) → a = AClos c.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_asubj a σ : offers a (LSess σ) → asubj a = Some (subj σ).
Proof. destruct a, σ; naive_solver. Qed.

Lemma asubj_offers a c :
  asubj a = Some c → ∃ σ, subj σ = c ∧ offers a (LSess σ).
Proof.
  destruct a as [|v|d|d v|d]; simpl; intros Hs; try discriminate;
    injection Hs as <-.
  - exists (SRecv d EUnit). by split.
  - exists (SSend d v). by split.
  - exists (SClos d). by split.
Qed.

(** ** Searching a process for a transition

    Every side condition of Fig. 3 is decidable and the thread pool is
    finite, so the five rules can simply be searched for. *)

Lemma list_exists_dec {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  Decision (∃ x, x ∈ l ∧ P x).
Proof.
  induction l as [|y l IH].
  - right. intros (x & Hx & _). by apply elem_of_nil in Hx.
  - destruct (decide (P y)) as [Hy|Hy].
    { left. exists y. split; [apply elem_of_cons; by left|done]. }
    destruct IH as [IH|IH].
    + left. destruct IH as (x & Hx & HP). exists x.
      split; [apply elem_of_cons; by right|done].
    + right. intros (x & Hx & HP).
      apply elem_of_cons in Hx as [->|Hx]; [done|]. apply IH. by exists x.
Defined.

Global Instance gmultiset_exists_dec (P : expr → Prop) `{∀ e, Decision (P e)}
    (E : gmultiset expr) : Decision (∃ e, e ∈ E ∧ P e).
Proof.
  destruct (list_exists_dec P (elements E)) as [H'|H'].
  - left. destruct H' as (e & He & HP). exists e.
    split; [by apply gmultiset_elem_of_elements|done].
  - right. intros (e & He & HP). apply H'. exists e.
    split; [by apply gmultiset_elem_of_elements|done].
Defined.

Global Instance act_fork_dec e : Decision (∃ v, act e = Some (AFork v)).
Proof.
  destruct (act e) as [[|v|c|c v|c]|] eqn:Ha;
    try (right; intros (? & ?); simplify_eq; done).
  left. by exists v.
Defined.

Global Instance act_free_dec (C : gset chan) e :
  Decision (∃ a c, act e = Some a ∧ asubj a = Some c ∧ c ∉ C).
Proof.
  destruct (act e) as [a|] eqn:Ha;
    [|right; intros (? & ? & ? & _); simplify_eq].
  destruct (asubj a) as [c|] eqn:Hs;
    [|right; intros (? & ? & ? & ? & _); simplify_eq].
  destruct (decide (c ∉ C)) as [Hc|Hc]; [left; by exists a, c|].
  right. intros (? & ? & ? & ? & ?); simplify_eq. done.
Defined.

Global Instance act_msg_dec (C : gset chan) (E : gmultiset expr) e :
  Decision (∃ c v, act e = Some (ASend c v) ∧ c ∈ C
                   ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv c)).
Proof.
  destruct (act e) as [[|v|d|d v|d]|] eqn:Ha;
    try (right; intros (? & ? & ? & _); simplify_eq; done).
  destruct (decide (d ∈ C)) as [Hd|Hd];
    [|right; intros (? & ? & ? & ? & _); simplify_eq; contradiction].
  destruct (decide (∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv d)))
    as [Hf|Hf]; [left; by exists d, v|].
  right. intros (? & ? & ? & ? & ?); simplify_eq. contradiction.
Defined.

Global Instance act_clos_dec (C : gset chan) (E : gmultiset expr) e :
  Decision (∃ c, act e = Some (AClos c) ∧ c ∈ C
                 ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos c)).
Proof.
  destruct (act e) as [[|v|d|d v|d]|] eqn:Ha;
    try (right; intros (? & ? & _); simplify_eq; done).
  destruct (decide (d ∈ C)) as [Hd|Hd];
    [|right; intros (? & ? & ? & _); simplify_eq; contradiction].
  destruct (decide (∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos d)))
    as [Hf|Hf]; [left; by exists d|].
  right. intros (? & ? & ? & ?); simplify_eq. contradiction.
Defined.

(** ** Splitting the thread pool *)

Lemma gmultiset_split1 (E : gmultiset expr) e :
  e ∈ E → ∃ E0, E = E0 ⊎ {[+ e +]}.
Proof. intros. exists (E ∖ {[+ e +]}). multiset_solver. Qed.

Lemma gmultiset_split2 (E : gmultiset expr) e f :
  e ∈ E → f ∈ E ∖ {[+ e +]} → ∃ E0, E = E0 ⊎ {[+ e +]} ⊎ {[+ f +]}.
Proof. intros. exists (E ∖ {[+ e +]} ∖ {[+ f +]}). multiset_solver. Qed.

(** ** Progress for processes

    The constructive form of the case split Lemma 3.5 makes on
    [pirred p]. *)

Lemma proc_progress p : pirred p ∨ ∃ π p', proc_step p π p'.
Proof.
  destruct p as [C E].
  (* P-Act-Beta *)
  destruct (decide (∃ e, e ∈ E ∧ act e = Some ABeta)) as [(e & He & Ha)|Hbeta].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    destruct (act_offer _ _ LBeta Ha I) as [e' Hst].
    exists PTau, (C, E0 ⊎ {[+ e' +]}). by apply PStepBeta. }
  (* P-Act-Fork: every name is offered, so take a globally fresh one *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ v, act e = Some (AFork v)))
    as [(e & He & v & Ha)|Hfork].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    pose (c := fresh (C ∪ echans E0 ∪ fchans e)).
    assert (c ∉ C ∪ echans E0 ∪ fchans e) as Hc by apply is_fresh.
    destruct (act_offer _ _ (LFork c v) Ha eq_refl) as [e' Hst].
    exists PTau, (C ∪ {[c]}, E0 ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]}).
    apply PStepFork; [done|set_solver..]. }
  (* P-Act-Session: a communication whose subject is not restricted *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ a c,
                      act e = Some a ∧ asubj a = Some c ∧ c ∉ C))
    as [(e & He & a & c & Ha & Hs & Hc)|Hsess].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    destruct (asubj_offers _ _ Hs) as (σ & Hσ & Hoff).
    destruct (act_offer _ _ (LSess σ) Ha Hoff) as [e' Hst].
    exists (PSess σ), (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
    apply PStepSession; [done|by rewrite Hσ]. }
  (* P-Act-Msg: the receiver is retargeted to the value the sender emits *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c v, act e = Some (ASend c v) ∧ c ∈ C
                          ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv c)))
    as [(e & He & c & v & Hae & Hc & f & Hf & Haf)|Hmsg].
  { right. destruct (gmultiset_split2 _ _ _ He Hf) as [E0 ->].
    destruct (act_offer _ _ (LSess (SSend c v)) Hae (conj eq_refl eq_refl))
      as [e' Hste].
    destruct (act_offer _ _ (LSess (SRecv c v)) Haf
                (conj eq_refl (act_send_val _ _ _ Hae))) as [f' Hstf].
    exists PTau, (C, E0 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
    eapply PStepMsg; [exact Hste|exact Hstf|done]. }
  (* P-Act-Close *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c, act e = Some (AClos c) ∧ c ∈ C
                          ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos c)))
    as [(e & He & c & Hae & Hc & f & Hf & Haf)|Hclos].
  { right. destruct (gmultiset_split2 _ _ _ He Hf) as [E0 ->].
    destruct (act_offer _ _ (LSess (SClos c)) Hae eq_refl) as [e' Hste].
    destruct (act_offer _ _ (LSess (SClos c)) Haf eq_refl) as [f' Hstf].
    exists PTau, (C ∖ {[c]}, E0 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
    by apply PStepClose. }
  (* no rule of Fig. 3 applies *)
  left. intros π p' Hst. inversion Hst; simplify_eq.
  - (* P-Act-Session *)
    apply Hsess.
    match goal with H : tstep ?e (LSess ?σ) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      exists e; split; [multiset_solver|]; exists a, (subj σ)
    end.
    split_and!; [done|by apply offers_asubj|done].
  - (* P-Act-Beta *)
    apply Hbeta.
    match goal with H : tstep ?e LBeta _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_beta in Hoff as ->; exists e
    end.
    split; [multiset_solver|done].
  - (* P-Act-Fork *)
    apply Hfork.
    match goal with H : tstep ?e (LFork _ ?v) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_fork in Hoff as ->;
      exists e; split; [multiset_solver|]; by exists v
    end.
  - (* P-Act-Msg *)
    apply Hmsg.
    match goal with H : tstep _ (LSess (SRecv _ _)) _ |- _ =>
      apply act_step in H as (b & Hbf & Hofff);
      apply offers_recv in Hofff as ->
    end.
    match goal with H : tstep ?e (LSess (SSend ?c ?v)) _ |- _ =>
      apply act_step in H as (a & Hae & Hoffe);
      apply offers_send in Hoffe as ->; exists e; split; [multiset_solver|];
      exists c, v
    end.
    split_and!; [done|done|].
    match goal with Hb : act ?f = Some (ARecv _) |- _ =>
      exists f; split; [multiset_solver|done]
    end.
  - (* P-Act-Close *)
    apply Hclos.
    match goal with H : tstep ?e (LSess (SClos ?c)) _ |- _ =>
      apply act_step in H as (a & Hae & Hoffe);
      apply offers_clos in Hoffe as ->; exists e; split; [multiset_solver|];
      exists c
    end.
    split_and!; [done|done|].
    match goal with H : tstep ?f (LSess (SClos _)) _ |- _ =>
      apply act_step in H as (b & Hbf & Hofff);
      apply offers_clos in Hofff as ->; exists f;
      split; [multiset_solver|done]
    end.
Qed.
