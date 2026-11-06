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

(** Branch no-eq: [w_eq W] abbreviates equality and leaves W untyped. *)
Implicit Types W : world.


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
  - eexists.
    replace (E ⊎ {[+ e +]} ⊎ {[+ f +]} ⊎ E2) with (E ⊎ E2 ⊎ {[+ e +]} ⊎ {[+ f +]})
      by multiset_solver.
    by eapply PStepChoice.
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

Lemma choice_tau C1 E1 C2 E2 C c i j q1 q2 :
  proc_step (C1, E1) (PSess (SSel c i)) q1 →
  proc_step (C2, E2) (PSess (SBra c j)) q2 →
  ∃ q, proc_step (C, E1 ⊎ E2) PTau q.
Proof.
  intros H1 H2.
  apply proc_step_sess_inv in H1 as (F1 & e & e' & -> & Hst1 & _ & _).
  apply proc_step_sess_inv in H2 as (F2 & f & f' & -> & Hst2 & _ & _).
  destruct (bra_retarget _ _ _ _ i Hst2) as [f'' Hf].
  eexists.
  replace (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})) with (F1 ⊎ F2 ⊎ {[+ e +]} ⊎ {[+ f +]})
    by multiset_solver.
  by eapply PStepChoice.
Qed.

(** ** Duality at the head *)

Lemma sdual_snd s r m T s' : sdual s r → unfoldS s = SSeq (SSnd m T) s' →
  ∃ U r', unfoldS r = SSeq (SRcv m U) r'.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite (hd_of _ _ Hs) in H. rewrite unfoldS_unview.
  hd_cases r; simpl in H; try done. destruct H as (-> & _). by eexists _, _.
Qed.

Lemma sdual_rcv s r m T s' : sdual s r → unfoldS s = SSeq (SRcv m T) s' →
  ∃ U r', unfoldS r = SSeq (SSnd m U) r'.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite (hd_of _ _ Hs) in H. rewrite unfoldS_unview.
  hd_cases r; simpl in H; try done. destruct H as (-> & _). by eexists _, _.
Qed.

Lemma sdual_end s r : sdual s r → unfoldS s = SEnd → unfoldS r = SEnd.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite (hd_of _ _ Hs) in H. rewrite unfoldS_unview. by hd_cases r.
Qed.

Lemma sdual_plus s r s1 s2 : sdual s r → unfoldS s = SPlus s1 s2 →
  ∃ r1 r2, unfoldS r = SWith r1 r2.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite (hd_of _ _ Hs) in H. rewrite unfoldS_unview.
  hd_cases r; simpl in H; try done. by eexists _, _.
Qed.

Lemma sdual_with s r s1 s2 : sdual s r → unfoldS s = SWith s1 s2 →
  ∃ r1 r2, unfoldS r = SPlus r1 r2.
Proof.
  intros H Hs. specialize (H 1). simpl in H. unfold dual_step in H.
  rewrite (hd_of _ _ Hs) in H. rewrite unfoldS_unview.
  hd_cases r; simpl in H; try done. by eexists _, _.
Qed.

(** The kind of head a session label selects. *)
Definition lkind (σ : slabel) : hkind :=
  match σ with
  | SRecv _ _ => KdRcv | SSend _ _ => KdSnd | SClos _ => KdEnd
  | SSel _ _ => KdPlus | SBra _ _ => KdWith | SLink _ => KdStuck
  end.

Lemma selects_kind Θ σ k e :
  selects Θ σ k → tenv_entry Θ k = Some e → (∀ cd, σ ≠ SLink cd) →
  kind (hd e.1) = lkind σ.
Proof.
  intros Hs He Hl. destruct σ; simpl in Hs.
  - destruct Hs as (_ & e' & ? & ? & ? & He' & Hu). rewrite He in He'. injection He' as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hs as (_ & e' & ? & ? & ? & He' & Hu). rewrite He in He'. injection He' as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hs as (_ & e' & He' & Hu & _). rewrite He in He'. injection He' as <-.
    by rewrite (hd_of _ _ Hu).
  - by destruct (Hl cd).
  - destruct Hs as (_ & e' & ? & ? & He' & Hu). rewrite He in He'. injection He' as <-.
    by rewrite (hd_of _ _ Hu).
  - destruct Hs as (_ & e' & ? & ? & He' & Hu). rewrite He in He'. injection He' as <-.
    by rewrite (hd_of _ _ Hu).
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
  - intros (_ & e & _ & _ & ? & _). eauto.
  - intros (_ & e & _ & _ & ? & _). eauto.
Qed.

Lemma selects_subj Θ σ k : selects Θ σ k → k.1 ∈ subjs σ.
Proof. destruct σ; simpl; intros H; try (destruct H as [-> _]; set_solver). by destruct H. Qed.

(** [selects] reads only the entries of the selected channel. *)
Lemma selects_agree Θ Θ' σ k :
  (∀ b, tenv_entry Θ (k.1, b) = tenv_entry Θ' (k.1, b)) →
  selects Θ σ k → selects Θ' σ k.
Proof.
  intros Hag. destruct k as [c b]. simpl in Hag.
  destruct σ as [d v|d v|d|cd|d i|d i]; simpl.
  - intros (Hk & e & m & T & s & He & Hu). split; [done|].
    exists e, m, T, s. by rewrite <-Hag.
  - intros (Hk & e & m & T & s & He & Hu). split; [done|].
    exists e, m, T, s. by rewrite <-Hag.
  - intros (Hk & e & He & Hu & Ht). simpl in Hk. subst d. split; [done|].
    exists e. rewrite <-Hag. split_and!; [done|done|].
    intros Hb e' He'. apply (Ht Hb e'). by rewrite Hag.
  - intros (Hk & He). split; [done|]. by rewrite <-Hag.
  - intros (Hk & e & s1 & s2 & He & Hu). split; [done|].
    exists e, s1, s2. by rewrite <-Hag.
  - intros (Hk & e & s1 & s2 & He & Hu). split; [done|].
    exists e, s1, s2. by rewrite <-Hag.
Qed.

Lemma not_disjoint_ex (X Y : gset chan) : ¬ X ## Y → ∃ x, x ∈ X ∧ x ∈ Y.
Proof.
  intros H. destruct (set_choose_or_empty (X ∩ Y)) as [[x Hx]|He].
  - exists x. set_solver.
  - exfalso. apply H. set_solver.
Qed.

(** ** Two components over a cut *)

(** Readiness of a process without its link disjunct. *)
Definition ready_core (W : world) (Σ : senv) (p : proc) : Prop :=
  ((∀ k, ¬ offered_p Σ p k) → terminated p) ∧ above_offered W (tenv_of Σ) (offered_p Σ p).

Section connect.
  Context (W W1 W2 : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr).
  Context (HW : strict W).
  Context (Hd1 : Σ1 ##ₘ ΣC) (Hd2 : Σ2 ##ₘ ΣC') (Hd12 : Σ1 ##ₘ Σ2).
  Context (HC0 : dom ΣC = C0) (HC0' : dom ΣC' = C0).
  Context (Hcut : ∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
                    w_eq W e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1).
  Context (HC2 : C2 ## dom Σ1) (HC1 : C1 ## dom Σ2).
  Context (Hl1 : ∀ k e k' e',
             tenv_entry (tenv_of (Σ1 ∪ ΣC)) k = Some e →
             tenv_entry (tenv_of (Σ1 ∪ ΣC)) k' = Some e' →
             w_lt W1 (entry_head k' e') (pt_dual (entry_head k e)) →
             w_lt W (entry_head k' e') (pt_dual (entry_head k e))).
  Context (Hl2 : ∀ k e k' e',
             tenv_entry (tenv_of (Σ2 ∪ ΣC')) k = Some e →
             tenv_entry (tenv_of (Σ2 ∪ ΣC')) k' = Some e' →
             w_lt W2 (entry_head k' e') (pt_dual (entry_head k e)) →
             w_lt W (entry_head k' e') (pt_dual (entry_head k e))).

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
    - exfalso. destruct σ as [c v|c v|c|cd|c i|c i].
      1-3,5-6: (apply proc_step_sess_inv in Hst as (? & ? & ? & _ & _ & HdC & _);
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
    - exfalso. destruct σ as [c v|c v|c|cd|c i|c i].
      1-3,5-6: (apply proc_step_sess_inv in Hst as (? & ? & ? & _ & _ & HdC & _);
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
    d = c ∧ ∃ e m T s, Σ' !! c = Some e ∧ unfoldS e.1 = SSeq (SRcv m T) s.
  Proof.
    intros (Hk & e & m & T & s & He & Hu). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e, m, T, s.
  Qed.

  Lemma sel_send Σ' d v c b :
    selects (tenv_of Σ') (SSend d v) (c, b) →
    d = c ∧ ∃ e m T s, Σ' !! c = Some e ∧ unfoldS e.1 = SSeq (SSnd m T) s.
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

  Lemma sel_sel Σ' d i c b :
    selects (tenv_of Σ') (SSel d i) (c, b) →
    d = c ∧ ∃ e s1 s2, Σ' !! c = Some e ∧ unfoldS e.1 = SPlus s1 s2.
  Proof.
    intros (Hk & e & s1 & s2 & He & Hu). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e, s1, s2.
  Qed.

  Lemma sel_bra Σ' d i c b :
    selects (tenv_of Σ') (SBra d i) (c, b) →
    d = c ∧ ∃ e s1 s2, Σ' !! c = Some e ∧ unfoldS e.1 = SWith s1 s2.
  Proof.
    intros (Hk & e & s1 & s2 & He & Hu). simpl in Hk.
    apply tenv_entry_of_key in He as [_ He]. simpl in He. split; [done|].
    by exists e, s1, s2.
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
    destruct σ1 as [d1 v1|d1 v1|d1|cd1|d1 i1|d1 i1].
    4: { destruct (link_tau _ _ C E2 _ _ Hst1) as [q' Hq'];
         [exists c; split; [exact (selects_subj _ _ _ Hsel1)|done]|].
         exact (Hs _ Hq'). }
    all: destruct σ2 as [d2 v2|d2 v2|d2|cd2|d2 i2|d2 i2].
    all: try (destruct (link_tau _ _ C E1 _ _ Hst2) as [q' Hq'];
              [exists c; split; [exact (selects_subj _ _ _ Hsel2)|done]|];
              rewrite <-soup_comm in Hq'; exact (Hs _ Hq')).
    (* the two ends are dual, so their kinds are dual *)
    all: try (
      destruct (selects_entry _ _ _ Hsel1) as [e1 He1];
      destruct (selects_entry _ _ _ Hsel2) as [e2 He2];
      pose proof (selects_kind _ _ _ _ Hsel1 He1 ltac:(by intros ? ?)) as K1;
      pose proof (selects_kind _ _ _ _ Hsel2 He2 ltac:(by intros ? ?)) as K2;
      apply tenv_entry_of_key in He1 as [_ He1]; simpl in He1; rewrite Ha in He1;
      apply tenv_entry_of_key in He2 as [_ He2]; simpl in He2; rewrite Hb in He2;
      destruct (Hcut _ _ _ He1 He2) as [_ Hdu]; apply sdual_kind in Hdu;
      rewrite K1, K2 in Hdu; simpl in Hdu; discriminate Hdu).
    all: pose proof (selects_subj _ _ _ Hsel1) as Hs1; pose proof (selects_subj _ _ _ Hsel2) as Hs2;
      simpl in Hs1, Hs2; apply elem_of_singleton in Hs1, Hs2; subst d1 d2.
    - destruct (msg_tau _ _ _ _ C _ _ _ _ _ Hst2 Hst1) as [q' Hq'].
      rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
    - destruct (msg_tau _ _ _ _ C _ _ _ _ _ Hst1 Hst2) as [q' Hq'].
      exact (Hs _ Hq').
    - destruct (close_tau _ _ _ _ C _ _ _ Hst1 Hst2 HcC) as [q' Hq'].
      exact (Hs _ Hq').
    - destruct (choice_tau _ _ _ _ C _ _ _ _ _ Hst1 Hst2) as [q' Hq'].
      exact (Hs _ Hq').
    - destruct (choice_tau _ _ _ _ C _ _ _ _ _ Hst2 Hst1) as [q' Hq'].
      rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
  Qed.
  Context (Hr1 : ready_p W1 Σa (C1, E1)) (Hr2 : ready_p W2 Σb (C2, E2)).
  Context (Hu2 : terminated (C2, E2) → ∀ e, e ∈ E2 → e = EUnit).

  (** A link redex of a component in a stable composite touches no
      restricted channel, so it is a link redex of the composite
      (sharp edges 68). *)
  Lemma link_l : stable_p p → link_p (C1, E1) → link_p p.
  Proof.
    intros Hs (cd & q & Hst).
    destruct (decide (subjs (SLink cd) ## C)) as [Hdj|Hdj].
    - destruct (sess_lift _ _ C E2 _ _ Hst Hdj) as [q' Hq']. by exists cd, q'.
    - exfalso. destruct (link_tau _ _ C E2 _ _ Hst) as [q' Hq'].
      { apply not_disjoint_ex in Hdj as (x & Hx & Hx'). by exists x. }
      exact (Hs _ Hq').
  Qed.

  Lemma link_r : stable_p p → link_p (C2, E2) → link_p p.
  Proof.
    intros Hs (cd & q & Hst).
    destruct (decide (subjs (SLink cd) ## C)) as [Hdj|Hdj].
    - destruct (sess_lift _ _ C E1 _ _ Hst Hdj) as [q' Hq']. rewrite <-soup_comm in Hq'.
      by exists cd, q'.
    - exfalso. destruct (link_tau _ _ C E1 _ _ Hst) as [q' Hq'].
      { apply not_disjoint_ex in Hdj as (x & Hx & Hx'). by exists x. }
      rewrite <-soup_comm in Hq'. exact (Hs _ Hq').
  Qed.

  (** The chain argument proper, for components without link redexes. *)
  Section core.
  Context (Hc1 : ready_core W1 Σa (C1, E1)) (Hc2 : ready_core W2 Σb (C2, E2)).

  Lemma lt_irrefl_W x : ¬ w_lt W x x.
  Proof. destruct HW as [_ Hi]. apply Hi. Qed.

  Lemma lt_trans_W x y z : w_lt W x y → w_lt W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. apply (wf_lt_trans _ HWf). Qed.

  Lemma lt_eq_l x y z : w_eq W x y → w_lt W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. intros. eapply (wf_lt_eq _ HWf); [done|done|reflexivity]. Qed.

  Lemma lt_eq_r x y z : w_lt W x y → w_eq W y z → w_lt W x z.
  Proof. destruct HW as [HWf _]. intros. eapply (wf_lt_eq _ HWf); [reflexivity|done|done]. Qed.

  Lemma eq_sym_W x y : w_eq W x y → w_eq W y x.
  Proof. destruct HW as [HWf _]. apply (wf_eq_sym _ HWf). Qed.

  Lemma eq_dual_W x y : w_eq W x (pt_dual y) → w_eq W (pt_dual x) y.
  Proof.
    destruct HW as [HWf _]. intros H. rewrite <-(pt_dual_dual y). by apply (wf_eq_dual _ HWf).
  Qed.

  (** One step of the descent from each side (end points). The partner
      point of an unoffered entry lies above a composite offer, or above
      the offered end of a cut channel, whose other end is unoffered on
      the other side at the dual point. *)
  Definition coffer_below (h : point) : Prop :=
    ∃ k' e', offered_p Σ p k' ∧ tenv_entry (tenv_of Σ) k' = Some e' ∧
      w_lt W (entry_head k' e') h.

  Lemma step_l k e :
    stable_p p →
    tenv_entry (tenv_of Σa) k = Some e → ¬ offered_p Σa (C1, E1) k →
    coffer_below (pt_dual (entry_head k e)) ∨
    ∃ c e1 e2, c ∈ C0 ∧ ΣC !! c = Some e1 ∧ ΣC' !! c = Some e2 ∧ w_eq W e1.2 (pt_dual e2.2) ∧
      offered_p Σa (C1, E1) (c, false) ∧ ¬ offered_p Σb (C2, E2) (c, false) ∧
      w_lt W e1.2 (pt_dual (entry_head k e)).
  Proof.
    intros Hs He Hno. destruct Hc1 as [_ Hab].
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
      exists k'.1, e', e2. split_and!; [done..| | |].
      + by rewrite <-Hk'.
      + intros Ho2. apply (cut_not_both k'.1 false false Hs Hc); [|done].
        by rewrite <-Hk'.
      + exact Hlt.
  Qed.

  Lemma step_r k e :
    stable_p p →
    tenv_entry (tenv_of Σb) k = Some e → ¬ offered_p Σb (C2, E2) k →
    coffer_below (pt_dual (entry_head k e)) ∨
    ∃ c e1 e2, c ∈ C0 ∧ ΣC !! c = Some e1 ∧ ΣC' !! c = Some e2 ∧ w_eq W e1.2 (pt_dual e2.2) ∧
      offered_p Σb (C2, E2) (c, false) ∧ ¬ offered_p Σa (C1, E1) (c, false) ∧
      w_lt W e2.2 (pt_dual (entry_head k e)).
  Proof.
    intros Hs He Hno. destruct Hc2 as [_ Hab].
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
      exists k'.1, e1, e'. split_and!; [done..| | |].
      + by rewrite <-Hk'.
      + intros Ho1. apply (cut_not_both k'.1 false false Hs Hc); [done|].
        by rewrite <-Hk'.
      + exact Hlt.
  Qed.

  (** The descent. V collects the cut channels visited so far. The
      offered end of each lies at or above the current target, the
      partner point of the current entry, so none is visited twice, and
      the chain ends at an offer of the composite. *)
  Definition visited_ok (V : gset chan) (t : point) : Prop :=
    ∀ v ev, v ∈ V →
      ((ΣC !! v = Some ev ∧ offered_p Σa (C1, E1) (v, false)) ∨
       (ΣC' !! v = Some ev ∧ offered_p Σb (C2, E2) (v, false))) →
      w_eq W t ev.2 ∨ w_lt W t ev.2.

  Lemma visited_ok_step V t t' c ec :
    visited_ok V t → w_eq W t' ec.2 → w_lt W ec.2 t →
    (∀ ev, ((ΣC !! c = Some ev ∧ offered_p Σa (C1, E1) (c, false)) ∨
            (ΣC' !! c = Some ev ∧ offered_p Σb (C2, E2) (c, false))) → ev = ec) →
    visited_ok (V ∪ {[c]}) t'.
  Proof.
    intros Hinv Ht Hlt Hc v ev Hv Hev. apply elem_of_union in Hv as [Hv| ->%elem_of_singleton].
    - right. destruct (Hinv v ev Hv Hev) as [Heq|Hlt'].
      + eapply lt_eq_l; [exact Ht|]. by eapply lt_eq_r.
      + eapply lt_eq_l; [exact Ht|]. by eapply lt_trans_W.
    - left. by rewrite (Hc ev Hev).
  Qed.

  Lemma descent n : ∀ (V : gset chan) (i : bool) k e,
    stable_p p →
    size (C0 ∖ V) ≤ n →
    (if i then tenv_entry (tenv_of Σa) k = Some e ∧ ¬ offered_p Σa (C1, E1) k
     else tenv_entry (tenv_of Σb) k = Some e ∧ ¬ offered_p Σb (C2, E2) k) →
    visited_ok V (pt_dual (entry_head k e)) →
    coffer_below (pt_dual (entry_head k e)).
  Proof.
    induction n as [|n IH]; intros V i k e Hs Hn Hq Hinv.
    all: destruct i; destruct Hq as [Hq1 Hq2].
    all: first [destruct (step_l k e Hs Hq1 Hq2)
                  as [Hdone|(c & e1 & e2 & Hc & He1 & He2 & Hcnt & Hoff & Hpart & Hlt)]
               |destruct (step_r k e Hs Hq1 Hq2)
                  as [Hdone|(c & e1 & e2 & Hc & He1 & He2 & Hcnt & Hoff & Hpart & Hlt)]];
      [done|].
    (* the offered cut end is not visited yet *)
    all: try assert (c ∉ V) as HcV
           by (intros HcV; destruct (Hinv c e1 HcV (or_introl (conj He1 Hoff))) as [Heq|Hlt'];
               [apply (lt_irrefl_W e1.2); eapply lt_eq_r; [exact Hlt|exact Heq]
               |by eapply lt_irrefl_W, lt_trans_W]).
    all: try assert (c ∉ V) as HcV
           by (intros HcV; destruct (Hinv c e2 HcV (or_intror (conj He2 Hoff))) as [Heq|Hlt'];
               [apply (lt_irrefl_W e2.2); eapply lt_eq_r; [exact Hlt|exact Heq]
               |by eapply lt_irrefl_W, lt_trans_W]).
    all: try (exfalso; assert (c ∈ C0 ∖ V) as Hin by set_solver;
         assert (size (C0 ∖ V) ≠ 0) as Hnz
           by (intros Hz; apply size_empty_inv in Hz; rewrite Hz in Hin; set_solver);
         lia).
    all: assert (C0 ∖ (V ∪ {[c]}) ⊂ C0 ∖ V) as Hsub by set_solver;
         apply subset_size in Hsub.
    - (* side a offered at c: continue on side b at e2 *)
      destruct (IH (V ∪ {[c]}) false (c, false) e2) as (k'' & e'' & ? & ? & Hlt'').
      + done.
      + lia.
      + split; [|done]. rewrite tenv_entry_of. by rewrite lookup_b_cut.
      + eapply (visited_ok_step V _ _ c e1); [done| |exact Hlt|].
        * unfold entry_head. simpl. apply eq_sym_W. exact Hcnt.
        * intros ev [[Hev _]|[_ Hev]]; [rewrite He1 in Hev; by injection Hev|done].
      + exists k'', e''. split_and!; [done|done|].
        eapply lt_trans_W; [|exact Hlt]. eapply lt_eq_r; [exact Hlt''|].
        unfold entry_head. simpl. apply eq_sym_W. exact Hcnt.
    - (* side b offered at c: continue on side a at e1 *)
      destruct (IH (V ∪ {[c]}) true (c, false) e1) as (k'' & e'' & ? & ? & Hlt'').
      + done.
      + lia.
      + split; [|done]. rewrite tenv_entry_of. by rewrite lookup_a_cut.
      + eapply (visited_ok_step V _ _ c e2); [done| |exact Hlt|].
        * unfold entry_head. simpl. by apply eq_dual_W.
        * intros ev [[_ Hev]|[Hev _]]; [done|rewrite He2 in Hev; by injection Hev].
      + exists k'', e''. split_and!; [done|done|].
        eapply lt_trans_W; [|exact Hlt]. eapply lt_eq_r; [exact Hlt''|].
        unfold entry_head. simpl. by apply eq_dual_W.
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
        [done|by rewrite difference_empty_L| |intros ?? Hv; set_solver|by apply (Hno k')].
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
        [done|by rewrite difference_empty_L| |intros ?? Hv; set_solver|by apply (Hno k')].
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

  Lemma ready_connect_core : stable_p p → ready_core W Σ p.
  Proof.
    intros Hs. split.
    - intros Hno.
      destruct Hc1 as [Ht1 Hab1].
      destruct Hc2 as [Ht2 Hab2].
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
        * intros ?? Hv. set_solver.
        * by exists k', e'.
      + destruct (descent (size C0) ∅ false k e) as (k' & e' & ? & ? & ?).
        * done.
        * by rewrite difference_empty_L.
        * split.
          -- rewrite Hkk, tenv_entry_of. simpl. by rewrite lookup_b_r.
          -- intros Ho. by apply Hk, ext_r.
        * intros ?? Hv. set_solver.
        * by exists k', e'.
  Qed.
  End core.

  Theorem ready_connect : ready_p W Σ p.
  Proof.
    intros Hs.
    destruct (Hr1 (stable_l Hs)) as [Hl1'|Ho1]; [left; by apply link_l|].
    destruct (Hr2 (stable_r Hs)) as [Hl2'|Ho2]; [left; by apply link_r|].
    right. by apply ready_connect_core.
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

(** A term at a link offers nothing else. *)
Lemma link_t_only t σ t' : link_t t → tstep t (LSess σ) t' → ∃ cd, σ = SLink cd.
Proof.
  intros (cd & t0 & H0) H. destruct (tstep_same_act _ _ _ _ _ H0 H) as (a & Ha & Ha').
  destruct a; simpl in Ha, Ha'; try done. destruct σ; try done. eauto.
Qed.

Lemma slabel_link_dec σ : {cd | σ = SLink cd} + (∀ cd, σ ≠ SLink cd).
Proof. destruct σ; try (right; done). left. by eexists. Qed.

Lemma slabel_clos_dec σ : {d | σ = SClos d} + (∀ d, σ ≠ SClos d).
Proof. destruct σ; try (right; done). left. by eexists. Qed.

(** Two labels of one action select heads of one kind. *)
Lemma offers_same_kind a σ σ' :
  offers a (LSess σ) → offers a (LSess σ') → lkind σ = lkind σ'.
Proof. destruct a, σ, σ'; simpl; intros H1 H2; done. Qed.

Lemma lkind_not_self_dual σ : (∀ cd, σ ≠ SLink cd) → (∀ c, σ ≠ SClos c) →
  lkind σ ≠ kdual (lkind σ).
Proof. intros Hl Hc. destruct σ; simpl; try done; [by destruct (Hc c)|by destruct (Hl cd)]. Qed.

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
    destruct (slabel_link_dec σ) as [[cd ->]|Hl].
    { apply (link_cut_tau cd t' k.1 Hst); [exact (selects_subj _ _ _ Hsel)|done|done]. }
    destruct k as [c' b]; simpl in Hc.
    assert (is_Some (ΘB !! c')) as [o Ho] by (apply elem_of_dom; by rewrite HB).
    destruct (HBoth _ _ Ho) as (e1 & e2 & ->).
    destruct (HBdual _ _ _ Ho) as [Hcnt Hdu].
    pose proof (stable_thread Hs) as Hst_t.
    destruct (Hr Hst_t) as [_ Hab].
    destruct Hab as [Hlk|Hab]; [destruct (link_t_only _ _ _ Hlk Hst) as [cd ->]; by destruct (Hl cd)|].
    (* the other end of c' *)
    assert (tenv_entry Θ (c', negb b) = Some (if b then e1 else e2)) as Hother
      by (rewrite entry_cut by done; unfold tenv_entry; simpl; rewrite Ho; by destruct b).
    assert (tenv_entry Θ (c', b) = Some (if b then e2 else e1)) as Hself
      by (rewrite entry_cut by done; unfold tenv_entry; simpl; rewrite Ho; by destruct b).
    assert (w_eq W (pt_dual (entry_head (c', negb b) (if b then e1 else e2)))
              (entry_head (c', b) (if b then e2 else e1))) as Hhead.
    { unfold entry_head; simpl; destruct HW as [HWf _].
      destruct b; simpl.
      - rewrite <-(pt_dual_dual e2.2). by apply (wf_eq_dual _ HWf).
      - by apply (wf_eq_sym _ HWf). }
    (* the other end is not offered: an offer of it comes from the same action *)
    assert (¬ offered_t Θ t (c', negb b)) as Hnoff.
    { intros (σ' & t'' & Hst' & Hsel').
      destruct (tstep_same_act _ _ _ _ _ Hst Hst') as (a & Ha & Ha').
      pose proof (offers_same_kind _ _ _ Ha Ha') as Hkk.
      destruct (slabel_clos_dec σ) as [[d ->]|Hc'].
      - destruct σ'; simpl in Hkk; try discriminate Hkk.
        destruct Hsel as (Hk1 & ? & Hs1 & Hu1 & Ht1).
        destruct Hsel' as (Hk2 & ? & Hs2 & Hu2 & Ht2).
        simpl in Hk1, Hk2; subst.
        destruct b; simpl in *;
          [apply (Ht1 eq_refl _ Hs2 Hu2)|apply (Ht2 eq_refl _ Hs1 Hu1)].
      - assert (∀ cd, σ' ≠ SLink cd) as Hl'
          by (intros cd ->; destruct σ; simpl in Hkk; try discriminate Hkk; naive_solver).
        pose proof (selects_kind _ _ _ _ Hsel Hself Hl) as K1.
        pose proof (selects_kind _ _ _ _ Hsel' Hother Hl') as K2.
        destruct b; simpl in *; [apply sdual_sym in Hdu|];
          apply sdual_kind in Hdu; rewrite K1, K2, <-Hkk in Hdu;
          by apply (lkind_not_self_dual σ Hl Hc'). }
    pose proof (proj1 (Hab (c', b) _ (ex_intro _ _ (ex_intro _ _ (conj Hst Hsel))) Hself)
                  _ _ Hother Hnoff) as Hlt.
    destruct HW as [HWf Hirr]; apply (Hirr (entry_head (c', b) (if b then e2 else e1)));
      eapply (wf_lt_eq _ HWf); [reflexivity|exact Hlt|exact Hhead].
  Qed.
  Lemma lift_offer k : stable_p p → k.1 ∈ dom Σ → offered_t Θ t k → offered_p Σ p k.
  Proof.
    intros Hs Hk (σ & t' & Hst & Hsel).
    pose proof (selects_subj _ _ _ Hsel) as Hsub.
    assert (subjs σ ## C0) as Hdj.
    { destruct σ as [c v|c v|c|cd|c i|c i].
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
    destruct Hab0 as [(cd & t1 & Hl)|Hab0].
    { left. assert (subjs (SLink cd) ## C0) as Hdj.
      { apply elem_of_disjoint. intros x Hx HxC. by apply (link_cut_tau cd t1 x Hl). }
      exists cd, (C0 ∖ sentc (SLink cd), ∅ ⊎ {[+ t1 +]}).
      rewrite single_soup. by apply PStepSession. }
    right.
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
