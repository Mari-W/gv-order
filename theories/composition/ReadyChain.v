(** * The chain arguments for readiness (§11)

    [ready_term] turns a ready thread that holds both ends of the
    channels of C₀ into a ready process. [ready_connect] turns two ready
    components over a cut C₀ into a ready composite. In a stable
    composite the two ends of a cut channel are never both offered, so a
    chain of unoffered entries descends strictly in the world, visits
    each cut channel at most once, and ends at an external offered
    entry. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export relation.LogicalRelation.

(** ** Lifting transitions into a larger soup *)

Lemma new_retarget e c e' c' : tstep e (LNew c) e' → ∃ e'', tstep e (LNew c') e''.
Proof.
  intros H. remember (LNew c) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. by apply HeadNew.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetU.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetP.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj1.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj2.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepCase.
Qed.

Lemma tau_lift C1 E1 C E2 q :
  proc_step (C1, E1) PTau q → C1 ⊆ C → ∃ q', proc_step (C, E1 ⊎ E2) PTau q'.
Proof.
  intros H HC. inversion H; subst.
  - eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    by apply PStepBeta.
  - destruct (exist_fresh (C ∪ echans (E ⊎ E2) ∪ fchans e)) as [z Hz].
    destruct (new_retarget _ _ _ z H2) as [e'' He''].
    assert (z ∉ C ∧ z ∉ echans (E ⊎ E2) ∧ z ∉ fchans e) as (? & ? & ?)
      by (clear -Hz; set_solver).
    eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    by apply PStepNew.
  - eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    by apply PStepSpawn.
  - eexists.
    replace (E ⊎ {[+ e +]} ⊎ {[+ f +]} ⊎ E2) with (E ⊎ E2 ⊎ {[+ e +]} ⊎ {[+ f +]})
      by multiset_solver.
    by eapply PStepMsg.
  - eexists.
    replace (E ⊎ {[+ e +]} ⊎ {[+ f +]} ⊎ E2) with (E ⊎ E2 ⊎ {[+ e +]} ⊎ {[+ f +]})
      by multiset_solver.
    eapply PStepClose; [done|done|]. clear -HC H4. set_solver.
  - eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    eapply PStepLink; [done|]. clear -HC H3. set_solver.
Qed.

Lemma sess_lift C1 E1 C E2 σ q :
  proc_step (C1, E1) (PSess σ) q → subjs σ ## C →
  ∃ q', proc_step (C, E1 ⊎ E2) (PSess σ) q'.
Proof.
  intros H HC. apply proc_step_sess_inv in H as (E0 & e & e' & -> & Hst & _ & _).
  eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
  by apply PStepSession.
Qed.

Lemma link_tau C1 E1 C E2 cd q :
  proc_step (C1, E1) (PSess (SLink cd)) q → (∃ x, x ∈ cd ∧ x ∈ C) →
  ∃ q', proc_step (C, E1 ⊎ E2) PTau q'.
Proof.
  intros H (x & Hx & HxC).
  apply proc_step_sess_inv in H as (E0 & e & e' & -> & Hst & _ & _).
  destruct (tstep_link_shape _ _ _ Hst) as (c & d & ->).
  assert (x = c ∨ x = d) as [->| ->] by set_solver.
  - eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    by eapply PStepLink.
  - rewrite upair_comm in Hst.
    eexists. rewrite <-(assoc_L (⊎)), (comm_L (⊎) {[+ e +]}), (assoc_L (⊎)).
    by eapply PStepLink.
Qed.

Lemma msg_tau C1 E1 C2 E2 C c v v' q1 q2 :
  proc_step (C1, E1) (PSess (SSend c v)) q1 →
  proc_step (C2, E2) (PSess (SRecv c v')) q2 →
  ∃ q, proc_step (C, E1 ⊎ E2) PTau q.
Proof.
  intros H1 H2.
  apply proc_step_sess_inv in H1 as (F1 & e & e' & -> & Hst1 & _ & _).
  apply proc_step_sess_inv in H2 as (F2 & f & f' & -> & Hst2 & _ & _).
  destruct (recv_retarget _ _ _ _ v Hst2 (tstep_send_val _ _ _ _ Hst1)) as [f'' Hf].
  eexists.
  replace (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})) with (F1 ⊎ F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
    by multiset_solver.
  by eapply PStepMsg.
Qed.

Lemma close_tau C1 E1 C2 E2 C c q1 q2 :
  proc_step (C1, E1) (PSess (SClos c)) q1 →
  proc_step (C2, E2) (PSess (SClos c)) q2 → c ∈ C →
  ∃ q, proc_step (C, E1 ⊎ E2) PTau q.
Proof.
  intros H1 H2 Hc.
  apply proc_step_sess_inv in H1 as (F1 & e & e' & -> & Hst1 & _ & _).
  apply proc_step_sess_inv in H2 as (F2 & f & f' & -> & Hst2 & _ & _).
  eexists.
  replace (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})) with (F1 ⊎ F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
    by multiset_solver.
  by eapply PStepClose.
Qed.

(** ** Duality at the head *)

Lemma sdual_snd s r m T s' : sdual s r → unfoldS s = SSnd m T s' →
  ∃ U r', unfoldS r = SRcv m U r'.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite Hs in H. destruct (unfoldS r); simpl in H; try done;
    try (destruct H as (-> & _); by eexists _, _).
Qed.

Lemma sdual_rcv s r m T s' : sdual s r → unfoldS s = SRcv m T s' →
  ∃ U r', unfoldS r = SSnd m U r'.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite Hs in H. destruct (unfoldS r); simpl in H; try done;
    try (destruct H as (-> & _); by eexists _, _).
Qed.

Lemma sdual_end s r : sdual s r → unfoldS s = SEnd → unfoldS r = SEnd.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite Hs in H. by destruct (unfoldS r).
Qed.

(** ** Entries of a process-level environment *)

Lemma tenv_entry_of Σ c b :
  tenv_entry (tenv_of Σ) (c, b) = if b then None else Σ !! c.
Proof.
  unfold tenv_entry, tenv_of. simpl. rewrite lookup_fmap.
  destruct (Σ !! c), b; done.
Qed.

Lemma tenv_entry_of_key Σ k e :
  tenv_entry (tenv_of Σ) k = Some e → k = (k.1, false) ∧ Σ !! k.1 = Some e.
Proof.
  destruct k as [c []]; rewrite tenv_entry_of; simpl; [done|]. done.
Qed.

Lemma selects_entry Θ σ k : selects Θ σ k → ∃ e, tenv_entry Θ k = Some e.
Proof.
  destruct σ; simpl.
  - intros (_ & e & _ & _ & _ & ? & _). eauto.
  - intros (_ & e & _ & _ & _ & ? & _). eauto.
  - intros (_ & e & ? & _). eauto.
  - intros (_ & ?). done.
Qed.

Lemma selects_subj Θ σ k : selects Θ σ k → k.1 ∈ subjs σ.
Proof. destruct σ; simpl; intros H; try (destruct H as [-> _]; set_solver). by destruct H. Qed.

(** [selects] reads only the entries of the selected channel. *)
Lemma selects_agree Θ Θ' σ k :
  (∀ b, tenv_entry Θ (k.1, b) = tenv_entry Θ' (k.1, b)) →
  selects Θ σ k → selects Θ' σ k.
Proof.
  intros Hag. destruct k as [c b]. simpl in Hag.
  destruct σ as [d v|d v|d|cd]; simpl.
  - intros (Hk & e & m & T & s & He & Hu). split; [done|].
    exists e, m, T, s. by rewrite <-Hag.
  - intros (Hk & e & m & T & s & He & Hu). split; [done|].
    exists e, m, T, s. by rewrite <-Hag.
  - intros (Hk & e & He & Hu & Ht). simpl in Hk. subst d. split; [done|].
    exists e. rewrite <-Hag. split_and!; [done|done|].
    intros Hb e' He'. apply (Ht Hb e'). by rewrite Hag.
  - intros (Hk & He). split; [done|]. by rewrite <-Hag.
Qed.

Lemma not_disjoint_ex (X Y : gset chan) : ¬ X ## Y → ∃ x, x ∈ X ∧ x ∈ Y.
Proof.
  intros H. destruct (set_choose_or_empty (X ∩ Y)) as [[x Hx]|He].
  - exists x. set_solver.
  - exfalso. apply H. set_solver.
Qed.

(** ** Two components over a cut *)

Section connect.
  Context (W W1 W2 : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr).
  Context (HW : strict W).
  Context (Hd1 : Σ1 ##ₘ ΣC) (Hd2 : Σ2 ##ₘ ΣC') (Hd12 : Σ1 ##ₘ Σ2).
  Context (HC0 : dom ΣC = C0) (HC0' : dom ΣC' = C0).
  Context (Hcut : ∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
                    w_eq W e.2 e'.2 ∧ sdual e.1 e'.1).
  Context (HC2 : C2 ## dom Σ1) (HC1 : C1 ## dom Σ2).
  Context (Hl1 : ∀ k e k' e',
             tenv_entry (tenv_of (Σ1 ∪ ΣC)) k = Some e →
             tenv_entry (tenv_of (Σ1 ∪ ΣC)) k' = Some e' →
             w_lt W1 (entry_head k' e') (entry_head k e) →
             w_lt W (entry_head k' e') (entry_head k e)).
  Context (Hl2 : ∀ k e k' e',
             tenv_entry (tenv_of (Σ2 ∪ ΣC')) k = Some e →
             tenv_entry (tenv_of (Σ2 ∪ ΣC')) k' = Some e' →
             w_lt W2 (entry_head k' e') (entry_head k e) →
             w_lt W (entry_head k' e') (entry_head k e)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation p := (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
  Local Notation Σa := (Σ1 ∪ ΣC).
  Local Notation Σb := (Σ2 ∪ ΣC').
  Local Notation Σ := (Σ1 ∪ Σ2).

  Lemma soup_comm : E1 ⊎ E2 = E2 ⊎ E1.
  Proof. by rewrite (comm_L (⊎)). Qed.

  Lemma stable_l : stable_p p → stable_p (C1, E1).
  Proof.
    intros Hs q Hq. destruct (tau_lift _ _ C E2 _ Hq) as [q' Hq'];
      [set_solver|]. exact (Hs _ Hq').
  Qed.

  Lemma stable_r : stable_p p → stable_p (C2, E2).
  Proof.
    intros Hs q Hq. destruct (tau_lift _ _ C E1 _ Hq) as [q' Hq'];
      [set_solver|]. rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
  Qed.

  Lemma lookup_a_l c : c ∈ dom Σ1 → Σa !! c = Σ !! c.
  Proof.
    intros Hc. apply elem_of_dom in Hc as [e He].
    rewrite !lookup_union, He. by destruct (ΣC !! c), (Σ2 !! c).
  Qed.

  Lemma lookup_b_r c : c ∈ dom Σ2 → Σb !! c = Σ !! c.
  Proof.
    intros Hc. apply elem_of_dom in Hc as [e He].
    assert (Σ1 !! c = None) as H1.
    { specialize (Hd12 c). rewrite He in Hd12. by destruct (Σ1 !! c). }
    rewrite !lookup_union, He, H1. by destruct (ΣC' !! c).
  Qed.

  Lemma lookup_a_cut c : c ∈ C0 → Σa !! c = ΣC !! c.
  Proof.
    intros Hc. rewrite <-HC0 in Hc. apply elem_of_dom in Hc as [e He].
    assert (Σ1 !! c = None) as H1.
    { specialize (Hd1 c). rewrite He in Hd1. by destruct (Σ1 !! c). }
    by rewrite lookup_union, H1, He.
  Qed.

  Lemma lookup_b_cut c : c ∈ C0 → Σb !! c = ΣC' !! c.
  Proof.
    intros Hc. rewrite <-HC0' in Hc. apply elem_of_dom in Hc as [e He].
    assert (Σ2 !! c = None) as H2.
    { specialize (Hd2 c). rewrite He in Hd2. by destruct (Σ2 !! c). }
    by rewrite lookup_union, H2, He.
  Qed.

  (** An offer of a component on its own external channel is an offer
      of the composite. *)
  Lemma ext_l k :
    stable_p p → k.1 ∈ dom Σ1 → offered_p Σa (C1, E1) k → offered_p Σ p k.
  Proof.
    intros Hs Hk (σ & q & Hst & Hsel).
    pose proof (selects_subj _ _ _ Hsel) as Hsub.
    destruct (decide (subjs σ ## C)) as [Hdj|Hdj].
    - destruct (sess_lift _ _ C E2 _ _ Hst Hdj) as [q' Hq'].
      exists σ, q'. split; [done|]. eapply selects_agree; [|exact Hsel].
      intros b. rewrite !tenv_entry_of. destruct b; [done|]. by apply lookup_a_l.
    - exfalso. destruct σ as [c v|c v|c|cd].
      1-3: (apply proc_step_sess_inv in Hst as (? & ? & ? & _ & _ & HdC & _);
            simpl in Hsub, HdC; apply elem_of_singleton in Hsub; subst c;
            apply Hdj; simpl; apply disjoint_singleton_l;
            assert (k.1 ∉ C0) by (rewrite <-HC0; apply not_elem_of_dom;
              apply elem_of_dom in Hk as [? He]; specialize (Hd1 k.1);
              rewrite He in Hd1; by destruct (ΣC !! k.1));
            assert (k.1 ∉ C2) by (clear -HC2 Hk; set_solver);
            assert (k.1 ∉ C1) by (clear -HdC; set_solver);
            clear -H H0 H1; set_solver).
      destruct (link_tau _ _ C E2 _ _ Hst) as [q' Hq'].
      { apply not_disjoint_ex in Hdj as (x & Hx & Hx'). by exists x. }
      exact (Hs _ Hq').
  Qed.

  Lemma ext_r k :
    stable_p p → k.1 ∈ dom Σ2 → offered_p Σb (C2, E2) k → offered_p Σ p k.
  Proof.
    intros Hs Hk (σ & q & Hst & Hsel).
    pose proof (selects_subj _ _ _ Hsel) as Hsub.
    destruct (decide (subjs σ ## C)) as [Hdj|Hdj].
    - destruct (sess_lift _ _ C E1 _ _ Hst Hdj) as [q' Hq'].
      rewrite <-soup_comm in Hq'.
      exists σ, q'. split; [done|]. eapply selects_agree; [|exact Hsel].
      intros b. rewrite !tenv_entry_of. destruct b; [done|]. by apply lookup_b_r.
    - exfalso. destruct σ as [c v|c v|c|cd].
      1-3: (apply proc_step_sess_inv in Hst as (? & ? & ? & _ & _ & HdC & _);
            simpl in Hsub, HdC; apply elem_of_singleton in Hsub; subst c;
            apply Hdj; simpl; apply disjoint_singleton_l;
            assert (k.1 ∉ C0) by (rewrite <-HC0'; apply not_elem_of_dom;
              apply elem_of_dom in Hk as [? He]; specialize (Hd2 k.1);
              rewrite He in Hd2; by destruct (ΣC' !! k.1));
            assert (k.1 ∉ C1) by (clear -HC1 Hk; set_solver);
            assert (k.1 ∉ C2) by (clear -HdC; set_solver);
            clear -H H0 H1; set_solver).
      destruct (link_tau _ _ C E1 _ _ Hst) as [q' Hq'].
      { apply not_disjoint_ex in Hdj as (x & Hx & Hx'). by exists x. }
      rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
  Qed.
  Lemma offered_entry Σ' q k :
    offered_p Σ' q k → k = (k.1, false) ∧ ∃ e, Σ' !! k.1 = Some e.
  Proof.
    intros (σ & q' & _ & Hsel). destruct (selects_entry _ _ _ Hsel) as [e He].
    apply tenv_entry_of_key in He as [Hk He]. split; [done|]. by exists e.
  Qed.

  Lemma sel_recv Σ' d v c b :
    selects (tenv_of Σ') (SRecv d v) (c, b) →
    d = c ∧ ∃ e m T s, Σ' !! c = Some e ∧ unfoldS e.1 = SRcv m T s.
  Proof.
    intros (Hk & e & m & T & s & He & Hu). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e, m, T, s.
  Qed.

  Lemma sel_send Σ' d v c b :
    selects (tenv_of Σ') (SSend d v) (c, b) →
    d = c ∧ ∃ e m T s, Σ' !! c = Some e ∧ unfoldS e.1 = SSnd m T s.
  Proof.
    intros (Hk & e & m & T & s & He & Hu). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e, m, T, s.
  Qed.

  Lemma sel_clos Σ' d c b :
    selects (tenv_of Σ') (SClos d) (c, b) →
    d = c ∧ ∃ e, Σ' !! c = Some e ∧ unfoldS e.1 = SEnd.
  Proof.
    intros (Hk & e & He & Hu & _). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e.
  Qed.

  (** In a stable composite the two ends of a cut channel are never
      both offered: they would synchronize. *)
  Lemma cut_not_both c b1 b2 :
    stable_p p → c ∈ C0 →
    offered_p Σa (C1, E1) (c, b1) → offered_p Σb (C2, E2) (c, b2) → False.
  Proof.
    intros Hs Hc (σ1 & q1 & Hst1 & Hsel1) (σ2 & q2 & Hst2 & Hsel2).
    pose proof (lookup_a_cut c Hc) as Ha. pose proof (lookup_b_cut c Hc) as Hb.
    assert (c ∈ C) as HcC by set_solver.
    destruct σ1 as [d1 v1|d1 v1|d1|cd1].
    4: { destruct (link_tau _ _ C E2 _ _ Hst1) as [q' Hq'];
         [exists c; split; [exact (selects_subj _ _ _ Hsel1)|done]|].
         exact (Hs _ Hq'). }
    all: destruct σ2 as [d2 v2|d2 v2|d2|cd2].
    all: try (destruct (link_tau _ _ C E1 _ _ Hst2) as [q' Hq'];
              [exists c; split; [exact (selects_subj _ _ _ Hsel2)|done]|];
              rewrite <-soup_comm in Hq'; exact (Hs _ Hq')).
    all: repeat match goal with
         | H : selects _ (SRecv _ _) _ |- _ =>
             apply sel_recv in H as (-> & ? & ? & ? & ? & ? & ?)
         | H : selects _ (SSend _ _) _ |- _ =>
             apply sel_send in H as (-> & ? & ? & ? & ? & ? & ?)
         | H : selects _ (SClos _) _ |- _ =>
             apply sel_clos in H as (-> & ? & ? & ?)
         end.
    all: try rewrite Ha in H; try rewrite Ha in H1;
         try rewrite Hb in H; try rewrite Hb in H1.
    all: match goal with
         | H1 : ΣC !! ?d = Some ?e1, H2 : ΣC' !! ?d = Some ?e2 |- _ =>
             destruct (Hcut _ _ _ H1 H2) as [_ Hdu]
         end.
    - (* recv / recv *)
      match goal with H : unfoldS _ = SRcv _ _ _ |- _ =>
        destruct (sdual_rcv _ _ _ _ _ Hdu H) as (? & ? & ?) end. congruence.
    - (* recv / send *)
      destruct (msg_tau _ _ _ _ C _ _ _ _ _ Hst2 Hst1) as [q' Hq'].
      rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
    - (* recv / close *)
      match goal with H : unfoldS _ = SRcv _ _ _ |- _ =>
        destruct (sdual_rcv _ _ _ _ _ Hdu H) as (? & ? & ?) end. congruence.
    - (* send / recv *)
      destruct (msg_tau _ _ _ _ C _ _ _ _ _ Hst1 Hst2) as [q' Hq'].
      exact (Hs _ Hq').
    - (* send / send *)
      match goal with H : unfoldS _ = SSnd _ _ _ |- _ =>
        destruct (sdual_snd _ _ _ _ _ Hdu H) as (? & ? & ?) end. congruence.
    - (* send / close *)
      match goal with H : unfoldS _ = SSnd _ _ _ |- _ =>
        destruct (sdual_snd _ _ _ _ _ Hdu H) as (? & ? & ?) end. congruence.
    - (* close / recv *)
      match goal with H : unfoldS _ = SEnd |- _ =>
        pose proof (sdual_end _ _ Hdu H) end. congruence.
    - (* close / send *)
      match goal with H : unfoldS _ = SEnd |- _ =>
        pose proof (sdual_end _ _ Hdu H) end. congruence.
    - (* close / close *)
      destruct (close_tau _ _ _ _ C _ _ _ Hst1 Hst2 HcC) as [q' Hq'].
      exact (Hs _ Hq').
  Qed.
  Context (Hr1 : ready_p W1 Σa (C1, E1)) (Hr2 : ready_p W2 Σb (C2, E2)).
  Context (Hu2 : terminated (C2, E2) → ∀ e, e ∈ E2 → e = EUnit).

  Lemma lt_irrefl_W x : ¬ w_lt W x x.
  Proof. destruct HW as [_ Hi]. apply Hi. Qed.

  Lemma lt_trans_W x y z : w_lt W x y → w_lt W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. apply (wf_lt_trans _ HWf). Qed.

  Lemma lt_eq_l x y z : w_eq W x y → w_lt W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. intros. eapply (wf_lt_eq _ HWf); [done|done|apply HWf]. Qed.

  Lemma lt_eq_r x y z : w_lt W x y → w_eq W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. intros. eapply (wf_lt_eq _ HWf); [apply HWf|done|done]. Qed.

  Lemma eq_sym_W x y : w_eq W x y → w_eq W y x.
  Proof. destruct HW as [HWf _]. apply (wf_eq_sym _ HWf). Qed.

  (** One step of the descent from each side: an unoffered entry lies
      above a composite offer, or above an unoffered entry of the
      other side on a cut channel, at an aliased head. *)
  Definition coffer_below (h : point) : Prop :=
    ∃ k' e', offered_p Σ p k' ∧ tenv_entry (tenv_of Σ) k' = Some e' ∧
      w_lt W (entry_head k' e') h.

  Lemma step_l k e :
    stable_p p →
    tenv_entry (tenv_of Σa) k = Some e → ¬ offered_p Σa (C1, E1) k →
    coffer_below (entry_head k e) ∨
    ∃ c e1 e2, c ∈ C0 ∧ ΣC !! c = Some e1 ∧ ΣC' !! c = Some e2 ∧ w_eq W e1.2 e2.2 ∧
      ¬ offered_p Σb (C2, E2) (c, false) ∧
      w_lt W e1.2 (entry_head k e).
  Proof.
    intros Hs He Hno. destruct (Hr1 (stable_l Hs)) as [_ Hab].
    destruct (Hab k e He Hno) as (k' & e' & Ho & He' & Hlt).
    apply Hl1 in Hlt; [|done|done].
    pose proof He' as He'0. apply tenv_entry_of_key in He'0 as [Hk' Hk'e].
    destruct (decide (k'.1 ∈ dom Σ1)) as [Hin|Hout].
    - left. exists k', e'. split_and!; [by apply ext_l| |done].
      rewrite Hk', tenv_entry_of. simpl. by rewrite <-lookup_a_l.
    - right. assert (k'.1 ∈ C0) as Hc.
      { rewrite <-HC0. apply elem_of_dom. rewrite lookup_union in Hk'e.
        apply not_elem_of_dom in Hout. rewrite Hout in Hk'e.
        by destruct (ΣC !! k'.1). }
      assert (ΣC !! k'.1 = Some e') as He1 by (by rewrite <-lookup_a_cut).
      assert (is_Some (ΣC' !! k'.1)) as [e2 He2]
        by (apply elem_of_dom; by rewrite HC0').
      destruct (Hcut _ _ _ He1 He2) as [Hcnt _].
      exists k'.1, e', e2. split_and!; [done..| |].
      + intros Ho2. apply (cut_not_both k'.1 false false Hs Hc); [|done].
        by rewrite <-Hk'.
      + exact Hlt.
  Qed.

  Lemma step_r k e :
    stable_p p →
    tenv_entry (tenv_of Σb) k = Some e → ¬ offered_p Σb (C2, E2) k →
    coffer_below (entry_head k e) ∨
    ∃ c e1 e2, c ∈ C0 ∧ ΣC !! c = Some e1 ∧ ΣC' !! c = Some e2 ∧ w_eq W e1.2 e2.2 ∧
      ¬ offered_p Σa (C1, E1) (c, false) ∧
      w_lt W e1.2 (entry_head k e).
  Proof.
    intros Hs He Hno. destruct (Hr2 (stable_r Hs)) as [_ Hab].
    destruct (Hab k e He Hno) as (k' & e' & Ho & He' & Hlt).
    apply Hl2 in Hlt; [|done|done].
    pose proof He' as He'0. apply tenv_entry_of_key in He'0 as [Hk' Hk'e].
    destruct (decide (k'.1 ∈ dom Σ2)) as [Hin|Hout].
    - left. exists k', e'. split_and!; [by apply ext_r| |done].
      rewrite Hk', tenv_entry_of. simpl. by rewrite <-lookup_b_r.
    - right. assert (k'.1 ∈ C0) as Hc.
      { rewrite <-HC0'. apply elem_of_dom. rewrite lookup_union in Hk'e.
        apply not_elem_of_dom in Hout. rewrite Hout in Hk'e.
        by destruct (ΣC' !! k'.1). }
      assert (ΣC' !! k'.1 = Some e') as He2 by (by rewrite <-lookup_b_cut).
      assert (is_Some (ΣC !! k'.1)) as [e1 He1]
        by (apply elem_of_dom; by rewrite HC0).
      destruct (Hcut _ _ _ He1 He2) as [Hcnt _].
      exists k'.1, e1, e'. split_and!; [done..| |].
      + intros Ho1. apply (cut_not_both k'.1 false false Hs Hc); [done|].
        by rewrite <-Hk'.
      + eapply lt_eq_l; [exact Hcnt|]. exact Hlt.
  Qed.

  (** The descent. V collects the cut channels visited so far; their
      heads lie at or above the current entry, so none is visited
      twice, and the chain ends at an offer of the composite. *)
  Lemma descent n : ∀ (V : gset chan) (i : bool) k e,
    stable_p p →
    size (C0 ∖ V) ≤ n →
    (if i then tenv_entry (tenv_of Σa) k = Some e ∧ ¬ offered_p Σa (C1, E1) k
     else tenv_entry (tenv_of Σb) k = Some e ∧ ¬ offered_p Σb (C2, E2) k) →
    (∀ v ev, v ∈ V → ΣC !! v = Some ev →
       w_eq W (entry_head k e) ev.2 ∨ w_lt W (entry_head k e) ev.2) →
    coffer_below (entry_head k e).
  Proof.
    induction n as [|n IH]; intros V i k e Hs Hn Hq Hinv.
    all: assert (coffer_below (entry_head k e) ∨
           ∃ c e1 e2, c ∈ C0 ∧ ΣC !! c = Some e1 ∧ ΣC' !! c = Some e2 ∧
             w_eq W e1.2 e2.2 ∧
             (if i then ¬ offered_p Σb (C2, E2) (c, false)
              else ¬ offered_p Σa (C1, E1) (c, false)) ∧
             w_lt W e1.2 (entry_head k e))
           as [Hdone|(c & e1 & e2 & Hc & He1 & He2 & Hcnt & Hpart & Hlt)];
      [destruct i, Hq; [by apply step_l|by apply step_r]|done|].
    all: assert (c ∉ V) as HcV.
    1,3: intros HcV; destruct (Hinv c e1 HcV He1) as [Heq|Hlt'];
         [apply (lt_irrefl_W (entry_head k e)); by eapply lt_eq_l
         |by eapply lt_irrefl_W, lt_trans_W].
    - exfalso. assert (c ∈ C0 ∖ V) as Hin by set_solver.
      assert (size (C0 ∖ V) ≠ 0) as Hnz.
      { intros Hz. apply size_empty_inv in Hz. rewrite Hz in Hin. set_solver. }
      lia.
    - assert (C0 ∖ (V ∪ {[c]}) ⊂ C0 ∖ V) as Hsub by set_solver.
      apply subset_size in Hsub.
      assert (∀ h, w_eq W h e1.2 → ∀ v ev, v ∈ V ∪ {[c]} → ΣC !! v = Some ev →
                w_eq W h ev.2 ∨ w_lt W h ev.2) as Hinv'.
      { intros h Hh v ev Hv Hev. apply elem_of_union in Hv as [Hv| ->%elem_of_singleton].
        - right. destruct (Hinv v ev Hv Hev) as [Heq|Hlt'].
          + eapply lt_eq_l; [exact Hh|]. by eapply lt_eq_r.
          + eapply lt_eq_l; [exact Hh|]. by eapply lt_trans_W.
        - left. rewrite He1 in Hev. by injection Hev as <-. }
      destruct i.
      + destruct (IH (V ∪ {[c]}) false (c, false) e2) as (k'' & e'' & ? & ? & Hlt'').
        * done.
        * lia.
        * split; [|done]. rewrite tenv_entry_of. by rewrite lookup_b_cut.
        * apply Hinv'. unfold entry_head. simpl. by apply eq_sym_W.
        * exists k'', e''. split_and!; [done|done|].
          eapply lt_trans_W; [|exact Hlt]. eapply lt_eq_r; [exact Hlt''|].
          unfold entry_head. simpl. by apply eq_sym_W.
      + destruct (IH (V ∪ {[c]}) true (c, false) e1) as (k'' & e'' & ? & ? & Hlt'').
        * done.
        * lia.
        * split; [|done]. rewrite tenv_entry_of. by rewrite lookup_a_cut.
        * apply Hinv'. destruct HW as [HWf _]. apply HWf.
        * exists k'', e''. split_and!; [done|done|].
          by eapply lt_trans_W.
  Qed.
  Lemma no_offers_l :
    stable_p p → (∀ k, ¬ offered_p Σ p k) → ∀ k, ¬ offered_p Σa (C1, E1) k.
  Proof.
    intros Hs Hno k Ho. pose proof Ho as Ho'.
    apply offered_entry in Ho' as [Hk [e He]].
    destruct (decide (k.1 ∈ dom Σ1)) as [Hin|Hout].
    - by apply (Hno k), ext_l.
    - assert (k.1 ∈ C0) as Hc.
      { rewrite <-HC0. apply elem_of_dom. rewrite lookup_union in He.
        apply not_elem_of_dom in Hout. rewrite Hout in He. by destruct (ΣC !! k.1). }
      assert (is_Some (ΣC' !! k.1)) as [e2 He2] by (apply elem_of_dom; by rewrite HC0').
      destruct (descent (size C0) ∅ false (k.1, false) e2) as (k' & ? & Ho2 & _);
        [done|by rewrite difference_empty_L| |set_solver|by apply (Hno k')].
      split; [rewrite tenv_entry_of; by rewrite lookup_b_cut|].
      intros Ho2. apply (cut_not_both k.1 false false Hs Hc); [|done]. by rewrite <-Hk.
  Qed.

  Lemma no_offers_r :
    stable_p p → (∀ k, ¬ offered_p Σ p k) → ∀ k, ¬ offered_p Σb (C2, E2) k.
  Proof.
    intros Hs Hno k Ho. pose proof Ho as Ho'.
    apply offered_entry in Ho' as [Hk [e He]].
    destruct (decide (k.1 ∈ dom Σ2)) as [Hin|Hout].
    - by apply (Hno k), ext_r.
    - assert (k.1 ∈ C0) as Hc.
      { rewrite <-HC0'. apply elem_of_dom. rewrite lookup_union in He.
        apply not_elem_of_dom in Hout. rewrite Hout in He. by destruct (ΣC' !! k.1). }
      assert (is_Some (ΣC !! k.1)) as [e1 He1] by (apply elem_of_dom; by rewrite HC0).
      destruct (descent (size C0) ∅ true (k.1, false) e1) as (k' & ? & Ho1 & _);
        [done|by rewrite difference_empty_L| |set_solver|by apply (Hno k')].
      split; [rewrite tenv_entry_of; by rewrite lookup_a_cut|].
      intros Ho1. apply (cut_not_both k.1 false false Hs Hc); [done|]. by rewrite <-Hk.
  Qed.

  (** No offers and no entries: an environment with every entry above
      an offer, and no offers, is empty. *)
  Lemma empty_of_no_offers W' Σ' q :
    above_offered W' (tenv_of Σ') (offered_p Σ' q) →
    (∀ k, ¬ offered_p Σ' q k) → Σ' = ∅.
  Proof.
    intros Hab Hno. apply map_empty. intros c.
    destruct (Σ' !! c) as [e|] eqn:He; [|done]. exfalso.
    destruct (Hab (c, false) e) as (k' & e' & Ho & _).
    - by rewrite tenv_entry_of.
    - apply Hno.
    - by apply (Hno k').
  Qed.

  Theorem ready_connect : ready_p W Σ p.
  Proof.
    intros Hs. split.
    - intros Hno.
      destruct (Hr1 (stable_l Hs)) as [Ht1 Hab1].
      destruct (Hr2 (stable_r Hs)) as [Ht2 Hab2].
      pose proof (no_offers_l Hs Hno) as Hno1.
      pose proof (no_offers_r Hs Hno) as Hno2.
      apply empty_of_no_offers in Hab1; [|done].
      apply empty_of_no_offers in Hab2; [|done].
      destruct (Ht1 Hno1) as (v & U & Heq1 & Hv & HU).
      destruct (Ht2 Hno2) as (v2 & U2 & Heq2 & Hv2 & HU2).
      pose proof (Hu2 (Ht2 Hno2)) as HE2.
      injection Heq1 as -> ->. injection Heq2 as -> ->.
      assert (ΣC = ∅) as HΣC.
      { apply map_empty. intros c. pose proof (f_equal (lookup c) Hab1) as H.
        rewrite lookup_union, lookup_empty in H. by destruct (Σ1 !! c), (ΣC !! c). }
      assert (C0 = ∅) as -> by (by rewrite <-HC0, HΣC, dom_empty_L).
      exists v, (U ⊎ ({[+ v2 +]} ⊎ U2)). split_and!.
      + apply pair_equal_spec. split; [set_solver|multiset_solver].
      + done.
      + intros e0 He0. apply gmultiset_elem_of_disj_union in He0 as [He0|He0];
          [by apply HU|by apply HE2].
    - intros k e He Hk.
      pose proof He as He0. apply tenv_entry_of_key in He0 as [Hkk HΣk].
      assert (k.1 ∈ dom Σ1 ∨ k.1 ∈ dom Σ2) as [Hin|Hin].
      { apply elem_of_dom_2 in HΣk. rewrite dom_union_L in HΣk. set_solver. }
      + destruct (descent (size C0) ∅ true k e) as (k' & e' & ? & ? & ?).
        * done.
        * by rewrite difference_empty_L.
        * split.
          -- rewrite Hkk, tenv_entry_of. simpl. by rewrite lookup_a_l.
          -- intros Ho. by apply Hk, ext_l.
        * set_solver.
        * by exists k', e'.
      + destruct (descent (size C0) ∅ false k e) as (k' & e' & ? & ? & ?).
        * done.
        * by rewrite difference_empty_L.
        * split.
          -- rewrite Hkk, tenv_entry_of. simpl. by rewrite lookup_b_r.
          -- intros Ho. by apply Hk, ext_r.
        * set_solver.
        * by exists k', e'.
  Qed.
End connect.

(** ** One thread holding both ends of its restricted channels *)

(** All labels of a term come from its one redex. *)
Lemma tstep_same_act e α α' e' e'' :
  tstep e α e' → tstep e α' e'' → ∃ a, offers a α ∧ offers a α'.
Proof.
  intros H1 H2. destruct (act_step _ _ _ H1) as (a & Ha & Ho).
  destruct (act_step _ _ _ H2) as (a' & Ha' & Ho'). rewrite Ha in Ha'.
  injection Ha' as <-. eauto.
Qed.

Section term.
  Context (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr).
  Context (HW : strict W).
  Context (HB : dom ΘB = C0) (HΣB : dom Σ ## C0).
  Context (HBoth : ∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2).
  Context (HBdual : tenv_dual (w_eq W) ΘB).
  Context (F : gset point) (Hr : ready_t W (tenv_of Σ ∪ ΘB) F t).
  Context (Hni : ¬ irred t).
  Context (Hsome : ∀ σ t', tstep t (LSess σ) t' → ∃ k, offered_t (tenv_of Σ ∪ ΘB) t k).

  Local Notation Θ := (tenv_of Σ ∪ ΘB).
  Local Notation p := (C0, {[+ t +]} : gmultiset expr).

  Lemma single_soup : ({[+ t +]} : gmultiset expr) = ∅ ⊎ {[+ t +]}.
  Proof. by rewrite (left_id_L ∅ (⊎)). Qed.

  Lemma entry_ext c b : c ∈ dom Σ → tenv_entry Θ (c, b) = tenv_entry (tenv_of Σ) (c, b).
  Proof.
    intros Hc. unfold tenv_entry. simpl. rewrite lookup_union.
    apply elem_of_dom in Hc as [e He]. unfold tenv_of. rewrite lookup_fmap, He.
    simpl. by destruct (ΘB !! c).
  Qed.

  Lemma entry_cut c b : c ∈ C0 → tenv_entry Θ (c, b) = tenv_entry ΘB (c, b).
  Proof.
    intros Hc. unfold tenv_entry. simpl. rewrite lookup_union.
    assert (Σ !! c = None) as HΣc by (apply not_elem_of_dom; set_solver).
    unfold tenv_of. rewrite lookup_fmap, HΣc. simpl. by destruct (ΘB !! c).
  Qed.

  Lemma entry_dom k e : tenv_entry Θ k = Some e → k.1 ∈ dom Σ ∨ k.1 ∈ C0.
  Proof.
    destruct k as [c b]. simpl. intros He.
    destruct (decide (c ∈ dom Σ)); [by left|right].
    rewrite <-HB. apply elem_of_dom. unfold tenv_entry in He. simpl in He.
    rewrite lookup_union in He. unfold tenv_of in He. rewrite lookup_fmap in He.
    rewrite (proj1 (not_elem_of_dom _ _) n) in He. simpl in He.
    destruct (ΘB !! c); [done|]. by destruct b.
  Qed.

  Lemma stable_thread : stable_p p → stable_t t.
  Proof.
    intros Hs α t' Hst. destruct α as [| |c|v]; try done.
    - eapply (Hs (C0, ∅ ⊎ {[+ t' +]})). rewrite single_soup. by apply PStepBeta.
    - destruct (exist_fresh (C0 ∪ fchans t)) as [z Hz].
      destruct (new_retarget _ _ _ z Hst) as [t'' Ht''].
      eapply (Hs (C0 ∪ {[z]}, ∅ ⊎ {[+ t'' +]})). rewrite single_soup.
      apply PStepNew; [done|set_solver|rewrite echans_empty; set_solver|set_solver].
    - eapply (Hs (C0, ∅ ⊎ {[+ t' +]} ⊎ {[+ App v EUnit +]})). rewrite single_soup.
      by apply PStepSpawn.
  Qed.

  Lemma link_cut_tau cd t' x :
    tstep t (LSess (SLink cd)) t' → x ∈ cd → x ∈ C0 → ¬ stable_p p.
  Proof.
    intros Hst Hx HxC Hs.
    destruct (tstep_link_shape _ _ _ Hst) as (c & d & ->).
    assert (x = c ∨ x = d) as [->| ->] by set_solver.
    - eapply Hs. rewrite single_soup. by eapply PStepLink.
    - rewrite upair_comm in Hst. eapply Hs. rewrite single_soup. by eapply PStepLink.
  Qed.

  (** A stable thread offers no entry of a restricted channel. *)
  Lemma no_cut_offer k : stable_p p → offered_t Θ t k → k.1 ∉ C0.
  Proof.
    intros Hs (σ & t' & Hst & Hsel) Hc.
    destruct σ as [c v|c v|c|cd].
    4: { apply (link_cut_tau cd t' k.1 Hst); [exact (selects_subj _ _ _ Hsel)|done|done]. }
    all: destruct k as [c' b]; simpl in Hc.
    all: assert (is_Some (ΘB !! c')) as [o Ho] by (apply elem_of_dom; by rewrite HB).
    all: destruct (HBoth _ _ Ho) as (e1 & e2 & ->).
    all: destruct (HBdual _ _ _ Ho) as [Hcnt Hdu].
    all: pose proof (stable_thread Hs) as Hst_t.
    all: destruct (Hr Hst_t) as [_ Hab].
    (* the other end of c' *)
    all: assert (tenv_entry Θ (c', negb b) = Some (if b then e1 else e2)) as Hother
           by (rewrite entry_cut by done; unfold tenv_entry; simpl; rewrite Ho; by destruct b).
    all: assert (tenv_entry Θ (c', b) = Some (if b then e2 else e1)) as Hself
           by (rewrite entry_cut by done; unfold tenv_entry; simpl; rewrite Ho; by destruct b).
    all: assert (w_eq W (entry_head (c', negb b) (if b then e1 else e2))
                 (entry_head (c', b) (if b then e2 else e1))) as Hhead
           by (unfold entry_head; simpl; destruct HW as [HWf _];
               destruct b; simpl; [done|by apply (wf_eq_sym _ HWf)]).
    (* every offer of the thread is on c', from the same action *)
    all: assert (∀ k' σ' t'', tstep t (LSess σ') t'' → selects Θ σ' k' → k'.1 = c') as Hsame.
    1,3,5: intros k' σ' t'' Hst' Hsel'; destruct (tstep_same_act _ _ _ _ _ Hst Hst') as (a & Ha & Ha');
      destruct a; simpl in Ha, Ha'; try done; destruct σ'; try done;
      first [destruct Ha as [<- _]|subst c]; destruct Ha' as [<- _] || subst;
      simpl in Hsel; first [destruct Hsel as [<- _]|idtac];
      destruct Hsel' as [? _]; congruence.
    all: assert (¬ offered_t Θ t (c', negb b)) as Hnoff.
    1,3,5: (intros (σ' & t'' & Hst' & Hsel');
      destruct (tstep_same_act _ _ _ _ _ Hst Hst') as (a & Ha & Ha');
      destruct a; simpl in Ha, Ha'; try done; destruct σ'; try done).
    all: first
      [ solve [ (* recv/recv or send/send: both ends with one polarity *)
          destruct Hsel as (_ & ? & ? & ? & ? & Hs1 & Hu1);
          destruct Hsel' as (_ & ? & ? & ? & ? & Hs2 & Hu2);
          rewrite Hself in Hs1; rewrite Hother in Hs2;
          injection Hs1 as <-; injection Hs2 as <-;
          destruct b; try apply sdual_sym in Hdu;
          first [ destruct (sdual_rcv _ _ _ _ _ Hdu ltac:(eassumption)) as (? & ? & ?)
                | destruct (sdual_snd _ _ _ _ _ Hdu ltac:(eassumption)) as (? & ? & ?) ];
          congruence ]
      | solve [ (* close/close: only the first end is selected *)
          destruct Hsel as (Hk1 & ? & Hs1 & Hu1 & Ht1);
          destruct Hsel' as (Hk2 & ? & Hs2 & Hu2 & Ht2);
          simpl in Hk1, Hk2; subst;
          destruct b; simpl in *;
          [apply (Ht1 eq_refl _ Hs2 Hu2)|apply (Ht2 eq_refl _ Hs1 Hu1)] ]
      | idtac ].
    all: pose proof (proj1 (Hab (c', b) _ (ex_intro _ _ (ex_intro _ _ (conj Hst Hsel))) Hself)
                       _ _ Hother Hnoff) as Hlt.
    all: destruct HW as [HWf Hirr]; apply (Hirr (entry_head (c', b) (if b then e2 else e1)));
       eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlt|exact Hhead].
  Qed.
  Lemma lift_offer k : stable_p p → k.1 ∈ dom Σ → offered_t Θ t k → offered_p Σ p k.
  Proof.
    intros Hs Hk (σ & t' & Hst & Hsel).
    pose proof (selects_subj _ _ _ Hsel) as Hsub.
    assert (subjs σ ## C0) as Hdj.
    { destruct σ as [c v|c v|c|cd].
      4: { apply elem_of_disjoint. intros x Hx HxC.
           by apply (link_cut_tau cd t' x Hst). }
      all: simpl in *; apply elem_of_singleton in Hsub; subst c;
        apply disjoint_singleton_l; set_solver. }
    exists σ, (C0 ∖ sentc σ, ∅ ⊎ {[+ t' +]}). split.
    - rewrite single_soup. by apply PStepSession.
    - eapply selects_agree; [|exact Hsel]. intros b. by apply entry_ext.
  Qed.

  Theorem ready_term : ready_p W Σ p.
  Proof.
    intros Hs. pose proof (stable_thread Hs) as Hst. destruct (Hr Hst) as [Hv Hab0].
    destruct (tstep_progress t) as [Hi|(α & t0 & Hst0)]; [by destruct Hni|].
    pose proof (Hst _ _ Hst0) as Hα. destruct α as [|σ0|c|w]; try done.
    destruct (Hsome _ _ Hst0) as [k0 Hk0].
    assert (∃ e0, tenv_entry Θ k0 = Some e0) as [e0 He0].
    { destruct Hk0 as (σ1 & t1 & _ & Hsel1). by apply (selects_entry _ σ1). }
    pose proof (below_rest_above _ _ _ _ _ _ Hk0 He0 Hab0) as Hab. split.
    - intros Hno. exfalso. destruct (entry_dom _ _ He0) as [Hin|Hc].
      + apply (Hno k0). by apply lift_offer.
      + by apply (no_cut_offer k0 Hs Hk0).
    - intros k e He Hk.
      pose proof He as He0'. apply tenv_entry_of_key in He0' as [Hkk HΣk].
      assert (k.1 ∈ dom Σ) as Hin by (by apply elem_of_dom_2 in HΣk).
      destruct (Hab k e) as (k' & e' & Ho & He' & Hlt).
      + rewrite Hkk, entry_ext by done. by rewrite <-Hkk.
      + intros Ho. by apply Hk, lift_offer.
      + destruct (entry_dom _ _ He') as [Hin'|Hc].
        * exists k', e'. split_and!.
          -- by apply lift_offer.
          -- destruct k' as [c' b']. rewrite <-entry_ext by done. done.
          -- done.
        * by destruct (no_cut_offer k' Hs Ho).
  Qed.
End term.
