(** * Deadlock freedom and progress

    The correctness criteria for processes (Defs. 2.4-2.6) and the
    progress theorem. A process that offers no action is terminated or
    stuck. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lang.Semantics.

(** ** Properties of processes (Defs. 2.4–2.6) *)

(** A terminated process has released all channels; the main thread
    has computed a value and all spawned threads have reduced to ∗. *)
Definition terminated (p : proc) : Prop :=
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ (∀ e, e ∈ E → e = EUnit).

Definition safe (p : proc) : Prop :=
  terminated p ∨ ∃ p', preduction p p'.

Definition deadlock_free (p : proc) : Prop :=
  ∀ p', pred_star p p' → safe p'.

(** ** The action offered by a term *)

Inductive action :=
  | ABeta
  | ANew (x : point)
  | ASpawn (v : expr)
  | ARecv (c : cend)
  | ASend (c : cend) (v : expr)
  | AClos (c : cend)
  | ALink (c d : cend)
  | ASel (c : cend) (b : bool)
  | ABra (c : cend).

Global Instance action_eq_dec : EqDecision action.
Proof. solve_decision. Defined.

(** The channels a communicating action acts on — [None] for the
    silent ones. A forwarding acts on both of its ends, which is why
    this is set-valued (cf. [subjs]). *)
Definition asubjs (a : action) : option (gset chan) :=
  match a with
  | ABeta | ANew _ | ASpawn _ => None
  | ARecv c | ASend c _ | AClos c | ASel c _ | ABra c => Some {[c.1]}
  | ALink c d => Some {[c.1; d.1]}
  end.

(** The redex of [e] under the evaluation contexts of Fig. 2. The
    value side conditions of the right-of-value frames are exactly the
    [is_val] guards below, so the position found is the unique one. *)
Fixpoint act (e : expr) : option action :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ _ | EPt _ | Lam _ | EBox _ => None
  | App e1 e2 =>
      if is_val e1 then
        if is_val e2 then
          match e1, e2 with
          | Lam _, _ => Some ABeta
          | Konst KNew, EPt x => Some (ANew x)
          | Konst (KPay _), EPt _ => Some ABeta
          | Konst KSucc, EPt _ => Some ABeta
          | Konst KSpawn, v => Some (ASpawn v)
          | Konst KRecv, Chan c b => Some (ARecv (c, b))
          | Konst KSend, Pair v (Chan c b) => Some (ASend (c, b) v)
          | Konst KClos, Chan c b => Some (AClos (c, b))
          | Konst KLink, Pair (Chan c bc) (Chan d bd) => Some (ALink (c, bc) (d, bd))
          | Konst KForce, EBox _ => Some ABeta
          | Konst KSel1, Chan c b => Some (ASel (c, b) false)
          | Konst KSel2, Chan c b => Some (ASel (c, b) true)
          | Konst KBra, Chan c b => Some (ABra (c, b))
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
  end.

(** The labels an action admits. *)
Definition offers (a : action) (α : tlabel) : Prop :=
  match a, α with
  | ABeta, LBeta => True
  | ANew x, LNew _ y => x = y
  | ASpawn v, LSpawn w => v = w
  | ARecv c, LSess (SRecv d w) => c = d ∧ is_val w
  | ASend c v, LSess (SSend d w) => c = d ∧ v = w
  | AClos c, LSess (SClos d) => c = d
  | ALink c d, LSess (SLink cd) => cd = {[c; d]}
  | ASel c b, LSess (SSel d b') => c = d ∧ b = b'
  | ABra c, LSess (SBra d _) => c = d
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
                 |e α e' Hst IH|e α e' Hst IH|e α e' e1 e2 Hst IH]; simpl.
  - (* T-Act-Ctx at the hole: read the redex off the head step *)
    inversion Hh; simplify_eq; simpl;
      repeat match goal with
             | Hb : Is_true (is_val ?u) |- _ => rewrite (is_val_true u Hb)
             end.
    + (* T-Act-App *) by exists ABeta.
    + (* T-Act-Let* *) by exists ABeta.
    + (* T-Act-LetPair *) by exists ABeta.
    + (* T-Act-New *) by exists (ANew x).
    + (* T-Act-Pay *) by exists ABeta.
    + (* T-Act-Succ *) by exists ABeta.
    + (* T-Act-Spawn *) by exists (ASpawn v).
    + (* T-Act-Recv *) exists (ARecv (c, β)). split; [done|by split].
    + (* T-Act-Send *) by exists (ASend (c, β) v).
    + (* T-Act-Close *) by exists (AClos (c, β)).
    + (* T-Act-Select₁ *) by exists (ASel (c, β) false).
    + (* T-Act-Select₂ *) by exists (ASel (c, β) true).
    + (* T-Act-Branch *) by exists (ABra (c, β)).
    + (* T-Act-Case-Inl *) by exists ABeta.
    + (* T-Act-Case-Inr *) by exists ABeta.
    + (* T-Act-Force *) by exists ABeta.
    + (* T-Act-Link *) by exists (ALink (c, bc) (d, bd)).
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
Qed.

Lemma act_offer e a α : act e = Some a → offers a α → ∃ e', tstep e α e'.
Proof.
  revert a α.
  induction e as [x| |k|c b|x|e0 IHe|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e1 IH1 e2 IH2|e1 IH|e1 IH|e0 IH0 e1 IH1 e2 IH2
                 |e1 IH];
    simpl; intros a α Ha Hoff; try discriminate.
  - (* application *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (App e1' e2);
        by apply TStepAppL].
    destruct (is_val e2) eqn:Hb2;
      [|destruct (IH2 _ _ Ha Hoff) as [e2' Hst]; exists (App e1 e2');
        apply TStepAppR; [by rewrite Hb1|done]].
    destruct e1 as [| |k| | |e0 | | | | | | | | ]; try discriminate.
    + (* a concurrency primitive *)
      destruct k; simplify_eq.
      * (* T-Act-New *)
        destruct e2 as [| | | |x| | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ|c y|w]; try done. simpl in Hoff; subst y.
        eexists. apply TStepHead, HeadNew.
      * (* T-Act-Spawn *)
        destruct α as [|σ|c|w]; try done. simpl in Hoff. simplify_eq.
        exists EUnit. apply TStepHead, HeadSpawn. by rewrite Hb2.
      * (* T-Act-Recv *)
        destruct e2 as [| | |c b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d w|d w|d|cd|d b'|d b']; try done.
        destruct Hoff as [<- Hw]. exists (Pair w (Chan c b)).
        by apply TStepHead, HeadRecv.
      * (* T-Act-Send *)
        destruct e2 as [| | | | | | |v w | | | | | | ]; try discriminate.
        destruct w as [| | |d b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d' w'|d' w'|d'|cd'|d' b'|d' b']; try done.
        destruct Hoff as [<- ->].
        pose proof (is_val_of_true _ Hb2) as Hv2. simpl in Hv2.
        apply andb_True in Hv2 as [Hv _].
        exists (Chan d b). by apply TStepHead, HeadSend.
      * (* T-Act-Close *)
        destruct e2 as [| | |c b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d w|d w|d|cd|d b'|d b']; try done. simpl in Hoff. simplify_eq.
        exists EUnit. by apply TStepHead, HeadClos.
      * (* T-Act-Link *)
        destruct e2 as [| | | | | | |v w | | | | | | ]; try discriminate.
        destruct v as [| | |c' bc| | | | | | | | | | ]; try discriminate.
        destruct w as [| | |d' bd| | | | | | | | | | ]; try discriminate.
        simplify_eq.
        destruct α as [|σ| | ]; try done.
        destruct σ as [| | |cd''| | ]; try done.
        simpl in Hoff. subst cd''.
        exists EUnit. by apply TStepHead, HeadLink.
      * (* T-Act-Force: [EBox _] is unconditionally a value *)
        destruct e2 as [| | | | | | | | | | | | |eb ]; try discriminate.
        simplify_eq. destruct α; try done.
        exists (subst1 (EBox eb) eb). by apply TStepHead, HeadForce.
      * (* T-Act-Select₁ *)
        destruct e2 as [| | |c b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. destruct Hoff as [<- <-].
        eexists. by apply TStepHead, HeadSel1.
      * (* T-Act-Select₂ *)
        destruct e2 as [| | |c b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. destruct Hoff as [<- <-].
        eexists. by apply TStepHead, HeadSel2.
      * (* T-Act-Branch *)
        destruct e2 as [| | |c b| | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. simpl in Hoff. subst.
        eexists. by apply TStepHead, HeadBra.
      * (* T-Act-Pay *)
        destruct e2 as [| | | |x| | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α; try done.
        eexists. by apply TStepHead, HeadPay.
      * (* T-Act-Succ *)
        destruct e2 as [| | | |x| | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α; try done.
        eexists. by apply TStepHead, HeadSucc.
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
    destruct e1 as [| | | | | | |u w | | | | | | ]; try discriminate.
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
    destruct e0 as [| | | | | | | | | |v |w | | ]; try discriminate.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 v e1). apply TStepHead, HeadCase1. by rewrite Hb0.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 w e2). apply TStepHead, HeadCase2. by rewrite Hb0.
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
  destruct a as [|x|v|c|c v|c|c d|c b|c].
  - destruct (act_offer _ _ LBeta Ha I) as [e' ?]. by exists LBeta, e'.
  - destruct (act_offer _ _ (LNew "" x) Ha eq_refl) as [e' ?].
    by exists (LNew "" x), e'.
  - destruct (act_offer _ _ (LSpawn v) Ha eq_refl) as [e' ?].
    by exists (LSpawn v), e'.
  - destruct (act_offer _ _ (LSess (SRecv c EUnit)) Ha (conj eq_refl I))
      as [e' ?].
    by exists (LSess (SRecv c EUnit)), e'.
  - destruct (act_offer _ _ (LSess (SSend c v)) Ha (conj eq_refl eq_refl))
      as [e' ?].
    by exists (LSess (SSend c v)), e'.
  - destruct (act_offer _ _ (LSess (SClos c)) Ha eq_refl) as [e' ?].
    by exists (LSess (SClos c)), e'.
  - destruct (act_offer _ _ (LSess (SLink {[c; d]})) Ha eq_refl) as [e' ?].
    by exists (LSess (SLink {[c; d]})), e'.
  - destruct (act_offer _ _ (LSess (SSel c b)) Ha (conj eq_refl eq_refl)) as [e' ?].
    by exists (LSess (SSel c b)), e'.
  - destruct (act_offer _ _ (LSess (SBra c false)) Ha eq_refl) as [e' ?].
    by exists (LSess (SBra c false)), e'.
Qed.

(** ** Reading an action back off a label *)

Lemma offers_beta a : offers a LBeta → a = ABeta.
Proof. by destruct a. Qed.

Lemma offers_new a c x : offers a (LNew c x) → a = ANew x.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_spawn a v : offers a (LSpawn v) → a = ASpawn v.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_send a c v : offers a (LSess (SSend c v)) → a = ASend c v.
Proof. destruct a; try done. by intros [-> ->]. Qed.

Lemma offers_recv a c v : offers a (LSess (SRecv c v)) → a = ARecv c.
Proof. destruct a; try done. by intros [-> _]. Qed.

Lemma offers_clos a c : offers a (LSess (SClos c)) → a = AClos c.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_link a cd :
  offers a (LSess (SLink cd)) → ∃ c d, a = ALink c d ∧ cd = {[c; d]}.
Proof. destruct a; try done. intros ->. eauto. Qed.

Lemma offers_sel a c b : offers a (LSess (SSel c b)) → a = ASel c b.
Proof. destruct a; try done. by intros [-> ->]. Qed.

Lemma offers_bra a c b : offers a (LSess (SBra c b)) → a = ABra c.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_asubjs a σ : offers a (LSess σ) → asubjs a = Some (subjs σ).
Proof.
  destruct a, σ; simpl; try naive_solver.
  intros ->. f_equal. rewrite set_map_union_L, !set_map_singleton_L. done.
Qed.

Lemma asubjs_offers a S :
  asubjs a = Some S → ∃ σ, subjs σ = S ∧ offers a (LSess σ).
Proof.
  destruct a as [|x|v|d|d v|d|d d'|d b|d]; simpl; intros Hs; try discriminate;
    injection Hs as <-.
  - exists (SRecv d EUnit). by split.
  - exists (SSend d v). by split.
  - exists (SClos d). by split.
  - exists (SLink {[d; d']}). split; [|done].
    simpl. by rewrite set_map_union_L, !set_map_singleton_L.
  - exists (SSel d b). by split.
  - exists (SBra d false). by split.
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

Global Instance act_spawn_dec e : Decision (∃ v, act e = Some (ASpawn v)).
Proof.
  destruct (act e) as [[|x|v|c|c v|c|c d|c b|c]|] eqn:Ha;
    try (right; intros (? & ?); simplify_eq; done).
  left. by exists v.
Defined.

Global Instance act_new_dec e : Decision (∃ x, act e = Some (ANew x)).
Proof.
  destruct (act e) as [[|x|v|c|c v|c|c d|c b|c]|] eqn:Ha;
    try (right; intros (? & ?); simplify_eq; done).
  left. by exists x.
Defined.

Global Instance act_link_dec e : Decision (∃ c d, act e = Some (ALink c d)).
Proof.
  destruct (act e) as [[|x|v|c|c v|c|c d|c b|c]|] eqn:Ha;
    try (right; intros (? & ? & ?); simplify_eq; done).
  left. by exists c, d.
Defined.

Global Instance act_free_dec (C : gset chan) e :
  Decision (∃ a S, act e = Some a ∧ asubjs a = Some S ∧ S ## C).
Proof.
  destruct (act e) as [a|] eqn:Ha;
    [|right; intros (? & ? & ? & _); simplify_eq].
  destruct (asubjs a) as [S|] eqn:Hs;
    [|right; intros (? & ? & ? & ? & _); simplify_eq].
  destruct (decide (S ## C)) as [Hc|Hc]; [left; by exists a, S|].
  right. intros (? & ? & ? & ? & ?); simplify_eq. done.
Defined.

Global Instance act_msg_dec (C : gset chan) (E : gmultiset expr) e :
  Decision (∃ c v, act e = Some (ASend c v) ∧ c.1 ∈ C
                   ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv (c.1, negb c.2))).
Proof.
  destruct (act e) as [[|x|v|d|d v|d|d d'|d b|d]|] eqn:Ha;
    try (right; intros (? & ? & ? & _); simplify_eq; done).
  destruct (decide (d.1 ∈ C)) as [Hd|Hd];
    [|right; intros (? & ? & ? & ? & _); simplify_eq; contradiction].
  destruct (decide (∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv (d.1, negb d.2))))
    as [Hf|Hf]; [left; by exists d, v|].
  right. intros (? & ? & ? & ? & ?); simplify_eq. contradiction.
Defined.

Global Instance act_clos_dec (C : gset chan) (E : gmultiset expr) e :
  Decision (∃ c, act e = Some (AClos c) ∧ c.1 ∈ C
                 ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos (c.1, negb c.2))).
Proof.
  destruct (act e) as [[|x|v|d|d v|d|d d'|d b|d]|] eqn:Ha;
    try (right; intros (? & ? & _); simplify_eq; done).
  destruct (decide (d.1 ∈ C)) as [Hd|Hd];
    [|right; intros (? & ? & ? & _); simplify_eq; contradiction].
  destruct (decide (∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos (d.1, negb d.2))))
    as [Hf|Hf]; [left; by exists d|].
  right. intros (? & ? & ? & ?); simplify_eq. contradiction.
Defined.

Global Instance act_choice_dec (E : gmultiset expr) e :
  Decision (∃ c b, act e = Some (ASel c b)
                   ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ABra (c.1, negb c.2))).
Proof.
  destruct (act e) as [[|x|v|d|d v|d|d d'|d b|d]|] eqn:Ha;
    try (right; intros (? & ? & ? & _); simplify_eq; done).
  destruct (decide (∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ABra (d.1, negb d.2))))
    as [Hf|Hf]; [left; by exists d, b|].
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
  (* P-Act-New: every name is offered, so take a globally fresh one *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ x, act e = Some (ANew x)))
    as [(e & He & x & Ha)|Hnew].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    pose (c := fresh (C ∪ echans E0 ∪ fchans e)).
    assert (c ∉ C ∪ echans E0 ∪ fchans e) as Hc by apply is_fresh.
    destruct (act_offer _ _ (LNew c x) Ha eq_refl) as [e' Hst].
    exists PTau, (C ∪ {[c]}, E0 ⊎ {[+ e' +]}).
    eapply PStepNew; [done|set_solver..]. }
  (* P-Act-Spawn *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ v, act e = Some (ASpawn v)))
    as [(e & He & v & Ha)|Hspawn].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    destruct (act_offer _ _ (LSpawn v) Ha eq_refl) as [e' Hst].
    exists PTau, (C, E0 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}).
    by apply PStepSpawn. }
  (* P-Act-Session: a communication whose subject is not restricted *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ a S,
                      act e = Some a ∧ asubjs a = Some S ∧ S ## C))
    as [(e & He & a & S & Ha & Hs & Hc)|Hsess].
  { right. destruct (gmultiset_split1 _ _ He) as [E0 ->].
    destruct (asubjs_offers _ _ Hs) as (σ & Hσ & Hoff).
    destruct (act_offer _ _ (LSess σ) Ha Hoff) as [e' Hst].
    exists (PSess σ), (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
    apply PStepSession; [done|by rewrite Hσ]. }
  (* P-Act-Msg: the receiver is retargeted to the value the sender emits *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c v, act e = Some (ASend c v) ∧ c.1 ∈ C
                          ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ARecv (c.1, negb c.2))))
    as [(e & He & [c b] & v & Hae & Hc & f & Hf & Haf)|Hmsg].
  { right. destruct (gmultiset_split2 _ _ _ He Hf) as [E0 ->].
    destruct (act_offer _ _ (LSess (SSend (c, b) v)) Hae (conj eq_refl eq_refl))
      as [e' Hste].
    destruct (act_offer _ _ (LSess (SRecv (c, negb b) v)) Haf
                (conj eq_refl (act_send_val _ _ _ Hae))) as [f' Hstf].
    exists PTau, (C, E0 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
    eapply PStepMsg; [exact Hste|exact Hstf]. }
  (* P-Act-Close *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c, act e = Some (AClos c) ∧ c.1 ∈ C
                          ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (AClos (c.1, negb c.2))))
    as [(e & He & [c b] & Hae & Hc & f & Hf & Haf)|Hclos].
  { right. destruct (gmultiset_split2 _ _ _ He Hf) as [E0 ->].
    destruct (act_offer _ _ (LSess (SClos (c, b))) Hae eq_refl) as [e' Hste].
    destruct (act_offer _ _ (LSess (SClos (c, negb b))) Haf eq_refl) as [f' Hstf].
    exists PTau, (C ∖ {[c]}, E0 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
    by eapply PStepClose. }
  (* P-Act-Choice *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c b, act e = Some (ASel c b)
                          ∧ ∃ f, f ∈ E ∖ {[+ e +]} ∧ act f = Some (ABra (c.1, negb c.2))))
    as [(e & He & [c β] & b & Hae & f & Hf & Haf)|Hchoice].
  { right. destruct (gmultiset_split2 _ _ _ He Hf) as [E0 ->].
    destruct (act_offer _ _ (LSess (SSel (c, β) b)) Hae (conj eq_refl eq_refl)) as [e' Hste].
    destruct (act_offer _ _ (LSess (SBra (c, negb β) b)) Haf eq_refl) as [f' Hstf].
    exists PTau, (C, E0 ⊎ {[+ e' +]} ⊎ {[+ f' +]}).
    eapply PStepChoice; [exact Hste|exact Hstf]. }
  (* P-Act-Link: a forwarding redex whose offer was NOT enabled above
     has an end in C, and that end is retired by the τ rule. A
     forwarding with both ends free was already handled as an offer. *)
  destruct (decide (∃ e, e ∈ E ∧ ∃ c d, act e = Some (ALink c d)))
    as [(e & He & [c bc] & [d bd] & Ha)|Hlink].
  { right.
    assert (c ∈ C ∨ d ∈ C) as Hin.
    { destruct (decide (c ∈ C)) as [|Hc]; [by left|].
      destruct (decide (d ∈ C)) as [|Hd]; [by right|].
      exfalso. apply Hsess.
      exists e. split; [done|].
      exists (ALink (c, bc) (d, bd)), {[c; d]}. split_and!; [done|done|].
      clear -Hc Hd. set_solver. }
    destruct (gmultiset_split1 _ _ He) as [E0 ->].
    destruct (act_offer _ _ (LSess (SLink {[(c, bc); (d, bd)]})) Ha eq_refl)
      as [e' Hst].
    destruct Hin as [Hc|Hd].
    { exists PTau, (C ∖ {[c]}, echsubst c d (E0 ⊎ {[+ e' +]})).
      by eapply PStepLink. }
    { rewrite upair_comm in Hst.
      exists PTau, (C ∖ {[d]}, echsubst d c (E0 ⊎ {[+ e' +]})).
      by eapply PStepLink. } }
  (* no rule of Fig. 3 / Fig. 10 applies *)
  left. intros π p' Hst. inversion Hst; simplify_eq.
  - (* P-Act-Session, forwarding offers included *)
    apply Hsess.
    match goal with H : tstep ?e (LSess ?σ) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      exists e; split; [multiset_solver|]; exists a, (subjs σ)
    end.
    split_and!; [done|by apply offers_asubjs|done].
  - (* P-Act-Beta *)
    apply Hbeta.
    match goal with H : tstep ?e LBeta _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_beta in Hoff as ->; exists e
    end.
    split; [multiset_solver|done].
  - (* P-Act-New *)
    apply Hnew.
    match goal with H : tstep ?e (LNew _ ?x) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_new in Hoff as ->;
      exists e; split; [multiset_solver|by exists x]
    end.
  - (* P-Act-Spawn *)
    apply Hspawn.
    match goal with H : tstep ?e (LSpawn ?v) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_spawn in Hoff as ->;
      exists e; split; [multiset_solver|]; by exists v
    end.
  - (* P-Act-Msg: on a free channel the send is also an external
       offer, already excluded *)
    match goal with H : tstep _ (LSess (SRecv _ _)) _ |- _ =>
      apply act_step in H as (ab & Hbf & Hofff);
      apply offers_recv in Hofff as ->
    end.
    match goal with H : tstep ?e (LSess (SSend ?c ?v)) _ |- _ =>
      apply act_step in H as (a & Hae & Hoffe);
      apply offers_send in Hoffe as ->;
      destruct (decide (c.1 ∈ C)) as [Hc|Hc];
        [apply Hmsg; exists e; split; [multiset_solver|]; exists c, v
        |exfalso; apply Hsess; exists e; split; [multiset_solver|];
         exists (ASend c v), {[c.1]};
         split_and!; [done|done|clear -Hc; set_solver]]
    end.
    split_and!; [done|done|].
    match goal with Hb : act ?f = Some (ARecv _) |- _ =>
      exists f; split; [multiset_solver|done]
    end.
  - (* P-Act-Close *)
    apply Hclos.
    match goal with H : tstep ?f (LSess (SClos (_, negb _))) _ |- _ =>
      apply act_step in H as (ab & Hbf & Hofff);
      apply offers_clos in Hofff as ->
    end.
    match goal with H : tstep ?e (LSess (SClos ?c)) _ |- _ =>
      apply act_step in H as (a & Hae & Hoffe);
      apply offers_clos in Hoffe as ->; exists e; split; [multiset_solver|];
      exists c
    end.
    split_and!; [done|done|].
    match goal with Hb : act ?f = Some (AClos (_, negb _)) |- _ =>
      exists f; split; [multiset_solver|done]
    end.
  - (* P-Act-Choice *)
    apply Hchoice.
    match goal with H : tstep ?e (LSess (SSel ?c ?b)) _ |- _ =>
      apply act_step in H as (a & Hae & Hoffe);
      apply offers_sel in Hoffe as ->; exists e; split; [multiset_solver|];
      exists c, b
    end.
    split; [done|].
    match goal with H : tstep ?f (LSess (SBra _ _)) _ |- _ =>
      apply act_step in H as (ab & Hbf & Hofff);
      apply offers_bra in Hofff as ->; exists f;
      split; [multiset_solver|done]
    end.
  - (* P-Act-Link *)
    apply Hlink;
    match goal with H : tstep ?e (LSess (SLink _)) _ |- _ =>
      apply act_step in H as (a & Ha & Hoff);
      apply offers_link in Hoff as (c' & d' & -> & _); exists e;
      split; [multiset_solver|]; by eauto
    end.
Qed.
