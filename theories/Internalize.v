(** * Internalizing a link at component level (ORDERS-SPEC §11, sharp edges 45)

    A process holding one end each of two channels c and d, dual and
    at aliased points, stays related when d is restricted and c is
    renamed to d: the two ends become the two ends of the restricted
    channel d. Index preserving, because send, close and link keep the
    index (sharp edges 45): a synchronization of the fused process on
    d is a free send of p on one end followed by a costly receive on
    the other. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Junk.

(** ** Duality at the head, with payloads and continuations *)

Lemma sdual_snd_inv s r m T s' :
  sdual s r → unfoldS s = SSnd m T s' →
  ∃ U r', unfoldS r = SRcv m U r' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs. destruct (sdual_snd s r m T s' H Hs) as (U & r' & Hr).
  exists U, r'. split; [done|]. split.
  - apply eqT_all. intros n. specialize (H (S n)). simpl in H. unfold dual_step in H.
    rewrite Hs, Hr in H. by destruct H as (_ & ? & _).
  - intros n. specialize (H (S n)). simpl in H. unfold dual_step in H.
    rewrite Hs, Hr in H. by destruct H as (_ & _ & ?).
Qed.

Lemma sdual_rcv_inv s r m T s' :
  sdual s r → unfoldS s = SRcv m T s' →
  ∃ U r', unfoldS r = SSnd m U r' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs. destruct (sdual_rcv s r m T s' H Hs) as (U & r' & Hr).
  exists U, r'. split; [done|]. split.
  - apply eqT_all. intros n. specialize (H (S n)). simpl in H. unfold dual_step in H.
    rewrite Hs, Hr in H. by destruct H as (_ & ? & _).
  - intros n. specialize (H (S n)). simpl in H. unfold dual_step in H.
    rewrite Hs, Hr in H. by destruct H as (_ & _ & ?).
Qed.

Lemma sdual_unique s r r' : sdual s r → sdual s r' → seq r r'.
Proof.
  intros H1 H2. apply sdual_sym, sdual_seq_dual in H1, H2.
  eapply seq_trans; [exact H1|]. by apply seq_sym.
Qed.

(** ** Worlds and roots *)

Lemma wext_fresh_refl W : strict W → wext_fresh W ∅ W.
Proof.
  intros HW. split_and!.
  - by apply wext_refl.
  - apply disjoint_empty_l.
  - by rewrite union_empty_r_L.
  - intros x y _ _. done.
Qed.

Lemma senv_roots_mono Σ Σ' : Σ ⊆ Σ' → senv_roots Σ ⊆ senv_roots Σ'.
Proof.
  intros Hs x. unfold senv_roots. rewrite !elem_of_tenv_roots.
  intros (c0 & o & Ho & Hx). exists c0, o. split; [|done].
  unfold tenv_of in *. rewrite lookup_fmap in Ho |- *.
  destruct (Σ !! c0) as [e|] eqn:E; [|done]. simpl in Ho. injection Ho as <-.
  by rewrite (lookup_weaken Σ Σ' c0 e).
Qed.

(** ** The fused environment *)

Section fused.
  Context (c d : chan) (Hcd : c ≠ d).

  Definition fusedP (Σ : senv) (sc sd : sty) (kc kd : point) : senv :=
    <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ).

  Lemma fusedP_c Σ sc sd kc kd : fusedP Σ sc sd kc kd !! c = Some (sc, kc).
  Proof. unfold fusedP. by rewrite lookup_insert_eq. Qed.

  Lemma fusedP_d Σ sc sd kc kd : fusedP Σ sc sd kc kd !! d = Some (sd, kd).
  Proof. unfold fusedP. by rewrite lookup_insert_ne, lookup_insert_eq. Qed.

  Lemma fusedP_ne Σ sc sd kc kd y :
    y ≠ c → y ≠ d → fusedP Σ sc sd kc kd !! y = Σ !! y.
  Proof. intros. unfold fusedP. by rewrite !lookup_insert_ne. Qed.

  Lemma fusedP_dom Σ sc sd kc kd :
    dom (fusedP Σ sc sd kc kd) = {[c; d]} ∪ dom Σ.
  Proof. unfold fusedP. rewrite !dom_insert_L. set_solver. Qed.

  Lemma fusedP_sub Σ sc sd kc kd :
    c ∉ dom Σ → d ∉ dom Σ → Σ ⊆ fusedP Σ sc sd kc kd.
  Proof.
    intros Hc Hd. unfold fusedP.
    apply insert_subseteq_r.
    { by apply not_elem_of_dom. }
    apply insert_subseteq_r; [by apply not_elem_of_dom|done].
  Qed.

  Lemma fusedP_entry_ne Σ sc sd kc kd k :
    k.1 ≠ c → k.1 ≠ d →
    tenv_entry (tenv_of (fusedP Σ sc sd kc kd)) k = tenv_entry (tenv_of Σ) k.
  Proof.
    intros H1 H2. unfold tenv_entry, tenv_of. by rewrite !lookup_fmap, fusedP_ne.
  Qed.

  Lemma fusedP_entry_c Σ sc sd kc kd b e :
    tenv_entry (tenv_of (fusedP Σ sc sd kc kd)) (c, b) = Some e → b = false ∧ e = (sc, kc).
  Proof.
    unfold tenv_entry, tenv_of. simpl. rewrite lookup_fmap, fusedP_c. simpl.
    destruct b; [done|]. intros [=]. done.
  Qed.

  Lemma fusedP_entry_d Σ sc sd kc kd b e :
    tenv_entry (tenv_of (fusedP Σ sc sd kc kd)) (d, b) = Some e → b = false ∧ e = (sd, kd).
  Proof.
    unfold tenv_entry, tenv_of. simpl. rewrite lookup_fmap, fusedP_d. simpl.
    destruct b; [done|]. intros [=]. done.
  Qed.
End fused.

(** ** Two session steps of one soup by two threads *)

Lemma two_threads C E σ1 σ2 p1 p2 :
  proc_step (C, E) (PSess σ1) p1 → proc_step (C, E) (PSess σ2) p2 →
  (∀ a, offers a (LSess σ1) → offers a (LSess σ2) → False) →
  ∃ F e1 e1' e2 e2', E = F ⊎ {[+ e1 +]} ⊎ {[+ e2 +]} ∧
    tstep e1 (LSess σ1) e1' ∧ tstep e2 (LSess σ2) e2'.
Proof.
  intros H1 H2 Hna.
  apply proc_step_sess_inv in H1 as (F1 & e1 & e1' & -> & Hs1 & _ & _).
  apply proc_step_sess_inv in H2 as (F2 & e2 & e2' & HE & Hs2 & _ & _).
  assert (e1 ≠ e2) as Hne.
  { intros <-. destruct (tstep_same_act _ _ _ _ _ Hs1 Hs2) as (a & Ha1 & Ha2).
    exact (Hna a Ha1 Ha2). }
  assert (e2 ∈ F1) as Hin.
  { assert (e2 ∈ F1 ⊎ {[+ e1 +]}) as H by (rewrite HE; multiset_solver).
    apply gmultiset_elem_of_disj_union in H as [H|H]; [done|].
    apply gmultiset_elem_of_singleton in H. congruence. }
  exists (F1 ∖ {[+ e2 +]}), e1, e1', e2, e2'. split_and!; [|done|done].
  apply gmultiset_disj_union_difference' in Hin. rewrite Hin at 1. multiset_solver.
Qed.

(** ** Steps of p and of the fused process *)

Section steps.
  Context (c d : chan) (Hcd : c ≠ d) (C : gset chan) (E : gmultiset expr).
  Context (HcC : c ∉ C) (HdC : d ∉ C).

  Lemma lift_tau p' :
    proc_step (C, E) PTau p' → ∃ q', proc_step (C ∪ {[d]}, echsubst c d E) PTau q'.
  Proof.
    intros Hq.
    apply ptau_inv in Hq as
      [ (F & e & e' & -> & Hts & _)
      | [ (F & e & c0 & e' & -> & Hts & _)
      | [ (F & e & v & e' & -> & Hts & _)
      | [ (F & c0 & v & e & e' & f & f' & -> & Hts & Htr & _)
      | [ (F & c0 & e & e' & f & f' & -> & Hts & Htr & Hc0C & _)
      | (F & e & c0 & d0 & e' & -> & Hts & Hc0C & _) ]]]]].
    - apply (tstep_chsubst c d) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepBeta.
    - apply (tstep_chsubst c d) in Hts. simpl in Hts.
      destruct (exist_fresh (C ∪ {[d]} ∪ echans (echsubst c d F) ∪ fchans (chsubst c d e)))
        as [z Hz].
      destruct (new_retarget _ _ _ z Hts) as [e'' He''].
      eexists. rewrite echsubst_disj_union1. apply PStepNew; [done|set_solver..].
    - apply (tstep_chsubst c d) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepSpawn.
    - apply (tstep_chsubst c d) in Hts, Htr. eexists.
      rewrite echsubst_disj_union2. by eapply PStepMsg.
    - assert (c0 ≠ c) by set_solver.
      apply (tstep_chsubst c d) in Hts, Htr. simpl in Hts, Htr.
      rewrite csub_ne in Hts, Htr by done. eexists.
      rewrite echsubst_disj_union2. eapply PStepClose; [done|done|set_solver].
    - assert (c0 ≠ c) by set_solver.
      apply (tstep_chsubst c d) in Hts. simpl in Hts. rewrite gsub_upair, csub_ne in Hts by done.
      eexists. rewrite echsubst_disj_union1. eapply PStepLink; [done|set_solver].
  Qed.

  Lemma lift_link_cd cd p' :
    proc_step (C, E) (PSess (SLink cd)) p' → c ∈ cd ∨ d ∈ cd →
    ∃ q', proc_step (C ∪ {[d]}, echsubst c d E) PTau q'.
  Proof.
    intros Hq Hin. apply proc_step_sess_inv in Hq as (F & e & e' & -> & Hst & _ & _).
    destruct (tstep_link_shape _ _ _ Hst) as (a & b & ->).
    assert (∃ b', ({[a; b]} : gset chan) = {[c; b']} ∨ ({[a; b]} : gset chan) = {[d; b']})
      as (b' & Hab).
    { destruct (decide (a = c ∨ a = d)) as [[->| ->]|Ha].
      - exists b. by left.
      - exists b. by right.
      - exists a. rewrite upair_comm. assert (b = c ∨ b = d) as [->| ->] by set_solver;
          [left|right]; done. }
    apply (tstep_chsubst c d) in Hst. simpl in Hst.
    assert (gsub c d {[a; b]} = {[d; csub c d b']}) as Hg.
    { destruct Hab as [Hab|Hab]; rewrite Hab, gsub_upair;
        [by rewrite csub_hit|by rewrite (csub_ne c d d) by done]. }
    rewrite Hg in Hst. eexists. rewrite echsubst_disj_union1.
    eapply PStepLink; [done|set_solver].
  Qed.

  Lemma lift_ext σ p' :
    proc_step (C, E) (PSess σ) p' → c ∉ subjs σ → d ∉ subjs σ →
    ∃ q', proc_step (C ∪ {[d]}, echsubst c d E) (PSess (ssub c d σ)) q'.
  Proof.
    intros Hq Hc Hd. apply proc_step_sess_inv in Hq as (F & e & e' & -> & Hst & HsC & _).
    apply (tstep_chsubst c d) in Hst. simpl in Hst. eexists.
    rewrite echsubst_disj_union1. apply PStepSession; [done|].
    rewrite subjs_ssub, gsub_id by done. set_solver.
  Qed.

  Lemma back_ext σ' q' :
    proc_step (C ∪ {[d]}, echsubst c d E) (PSess σ') q' →
    ∃ σ F e e' f', E = F ⊎ {[+ e +]} ∧ tstep e (LSess σ) e' ∧ ssub_rel c d σ σ' ∧
      c ∉ subjs σ ∧ d ∉ subjs σ ∧ subjs σ ## C ∧ subjs σ' = subjs σ ∧
      tstep (chsubst c d e) (LSess σ') f' ∧
      q' = ((C ∪ {[d]}) ∖ sentc σ', echsubst c d F ⊎ {[+ f' +]}).
  Proof.
    intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
    apply echsubst_decomp in HE as (F & e & -> & -> & ->).
    destruct (tstep_chsubst_back c d e σ' f' Hst) as (σ & e' & He & Hr).
    pose proof (ssub_rel_subjs _ _ _ _ Hr) as Hs.
    assert (c ∉ subjs σ ∧ d ∉ subjs σ) as [Hc Hd].
    { split; intros Hin; apply (elem_of_disjoint _ _) in HsC; apply (HsC d); [|set_solver| |set_solver];
        rewrite Hs; unfold gsub; apply elem_of_map; [exists c|exists d];
        (split; [|done]); unfold csub; [by rewrite decide_True|by rewrite decide_False]. }
    rewrite gsub_id in Hs by done.
    exists σ, F, e, e', f'. split_and!; try done. rewrite <-Hs. set_solver.
  Qed.
End steps.

(** ** Readiness of the fused process *)

Section ready.
  Context (c d : chan) (Hcd : c ≠ d) (W : world) (HW : strict W) (Σ : senv)
    (sc sd : sty) (kc kd : point) (C : gset chan) (E : gmultiset expr).
  Context (HcΣ : c ∉ dom Σ) (HdΣ : d ∉ dom Σ) (HcC : c ∉ C) (HdC : d ∉ C)
    (Hdu : sdual sc sd) (Hal : w_eq W kc kd).
  Local Notation Σp := (fusedP c d Σ sc sd kc kd).
  Local Notation q := (C ∪ {[d]}, echsubst c d E).

  Lemma tenv_of_fused_ne y : y ≠ c → y ≠ d → tenv_of Σp !! y = tenv_of Σ !! y.
  Proof. intros. unfold tenv_of. by rewrite !lookup_fmap, fusedP_ne. Qed.

  Lemma entry_c : tenv_entry (tenv_of Σp) (c, false) = Some (sc, kc).
  Proof. unfold tenv_entry, tenv_of. simpl. by rewrite lookup_fmap, fusedP_c. Qed.

  Lemma entry_d : tenv_entry (tenv_of Σp) (d, false) = Some (sd, kd).
  Proof. unfold tenv_entry, tenv_of. simpl. by rewrite lookup_fmap, fusedP_d. Qed.

  Lemma stable_back : stable_p q → stable_p (C, E).
  Proof.
    intros Hs p' Hp. destruct (lift_tau c d Hcd C E HcC HdC p' Hp) as [q' Hq].
    exact (Hs q' Hq).
  Qed.

  Lemma off_fwd k :
    stable_p q → offered_p Σp (C, E) k → k.1 ≠ c → k.1 ≠ d → offered_p Σ q k.
  Proof.
    intros Hs (σ & p' & Hp & Hsel) Hk1 Hk2.
    destruct (decide (c ∈ subjs σ ∨ d ∈ subjs σ)) as [Ht|Ht].
    - exfalso. destruct σ as [c0 w|c0 w|c0|cd]; simpl in Ht.
      1-3: apply selects_subj in Hsel; simpl in Hsel; set_solver.
      destruct (lift_link_cd c d Hcd C E HcC HdC cd p' Hp Ht) as [q' Hq]. exact (Hs q' Hq).
    - destruct (lift_ext c d Hcd C E HcC HdC σ p' Hp) as [q' Hq]; [tauto|tauto|].
      exists (ssub c d σ), q'. split; [done|].
      assert (ssub_rel c d σ (ssub c d σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select_t c d _ σ (ssub c d σ) k Hr).
      { rewrite subjs_ssub, gsub_id; [done|]. tauto. }
      apply (selects_agree (tenv_of Σp)); [|done].
      intros y Hy. symmetry. apply tenv_of_fused_ne; intros ->; tauto.
  Qed.

  Lemma off_back k : offered_p Σ q k → offered_p Σp (C, E) k ∧ k.1 ≠ c ∧ k.1 ≠ d.
  Proof.
    intros (σ' & q' & Hq & Hsel).
    destruct (back_ext c d Hcd C E HcC HdC σ' q' Hq)
      as (σ & F & e & e' & f' & -> & Hst & Hr & Hc & Hd & HsC & Hs & _ & _).
    pose proof (selects_subj _ _ _ Hsel) as Hk. rewrite Hs in Hk.
    split_and!; [|intros Heq; apply Hc; by rewrite <-Heq|intros Heq; apply Hd; by rewrite <-Heq].
    exists σ, (C ∖ sentc σ, F ⊎ {[+ e' +]}). split; [by apply PStepSession|].
    apply (selects_agree (tenv_of Σ)).
    { intros y Hy. apply tenv_of_fused_ne; intros ->; tauto. }
    by apply (ssub_rel_select_t c d _ σ σ' k Hr).
  Qed.

  Lemma sync_tau :
    offered_p Σp (C, E) (c, false) → offered_p Σp (C, E) (d, false) →
    ∃ q', proc_step q PTau q'.
  Proof.
    intros (σ1 & p1 & H1 & Hs1) (σ2 & p2 & H2 & Hs2).
    destruct σ1 as [c1 w1|c1 w1|c1|cd1];
      [| | |eapply lift_link_cd; [done..|exact H1|left; by apply selects_subj in Hs1]].
    all: destruct σ2 as [c2 w2|c2 w2|c2|cd2];
      [| | |eapply lift_link_cd; [done..|exact H2|right; by apply selects_subj in Hs2]].
    all: simpl in Hs1, Hs2; destruct Hs1 as [Hc1 Hs1], Hs2 as [Hc2 Hs2];
      simpl in Hc1, Hc2; subst c1 c2.
    (* the heads of the two entries *)
    all: first [destruct Hs1 as (e & m & T & s & He1 & Hu1)
               |destruct Hs1 as (e & He1 & Hu1 & _)];
         first [destruct Hs2 as (e' & m' & T' & s' & He2 & Hu2)
               |destruct Hs2 as (e' & He2 & Hu2 & _)].
    all: rewrite entry_c in He1; rewrite entry_d in He2;
      injection He1 as <-; injection He2 as <-; simpl in Hu1, Hu2.
    (* mismatched heads contradict duality *)
    all: try (destruct (sdual_rcv _ _ _ _ _ Hdu Hu1) as (? & ? & Hx); congruence).
    all: try (destruct (sdual_snd _ _ _ _ _ Hdu Hu1) as (? & ? & Hx); congruence).
    all: try (pose proof (sdual_end _ _ Hdu Hu1) as Hx; congruence).
    - (* receive on c, send on d *)
      destruct (two_threads C E _ _ _ _ H1 H2) as (F & e1 & e1' & e2 & e2' & -> & Hst1 & Hst2).
      { intros [] Ha1 Ha2; simpl in Ha1, Ha2; naive_solver. }
      apply (tstep_chsubst c d) in Hst1, Hst2. simpl in Hst1, Hst2.
      rewrite csub_hit in Hst1. rewrite (csub_ne c d d) in Hst2 by done.
      destruct (recv_retarget _ _ _ _ (chsubst c d w2) Hst1) as [f'' Hf''].
      { by apply tstep_send_val in Hst2. }
      eexists. rewrite echsubst_disj_union2.
      replace (echsubst c d F ⊎ {[+ chsubst c d e1 +]} ⊎ {[+ chsubst c d e2 +]})
        with (echsubst c d F ⊎ {[+ chsubst c d e2 +]} ⊎ {[+ chsubst c d e1 +]})
        by multiset_solver.
      by eapply PStepMsg.
    - (* send on c, receive on d *)
      destruct (two_threads C E _ _ _ _ H1 H2) as (F & e1 & e1' & e2 & e2' & -> & Hst1 & Hst2).
      { intros [] Ha1 Ha2; simpl in Ha1, Ha2; naive_solver. }
      apply (tstep_chsubst c d) in Hst1, Hst2. simpl in Hst1, Hst2.
      rewrite csub_hit in Hst1. rewrite (csub_ne c d d) in Hst2 by done.
      destruct (recv_retarget _ _ _ _ (chsubst c d w1) Hst2) as [f'' Hf''].
      { by apply tstep_send_val in Hst1. }
      eexists. rewrite echsubst_disj_union2. by eapply PStepMsg.
    - (* close on both *)
      destruct (two_threads C E _ _ _ _ H1 H2) as (F & e1 & e1' & e2 & e2' & -> & Hst1 & Hst2).
      { intros [] Ha1 Ha2; simpl in Ha1, Ha2; naive_solver. }
      apply (tstep_chsubst c d) in Hst1, Hst2. simpl in Hst1, Hst2.
      rewrite csub_hit in Hst1. rewrite (csub_ne c d d) in Hst2 by done.
      eexists. rewrite echsubst_disj_union2. eapply PStepClose; [done|done|set_solver].
  Qed.

  Lemma lt_eq_false x y : w_lt W x y → w_eq W x y → False.
  Proof.
    intros Hlt Heq. destruct HW as [HWf Hirr]. apply (Hirr y).
    eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|apply HWf].
  Qed.

  Lemma fused_ready :
    ready_p W Σp (C, E) → ¬ terminated (C, E) → stable_p q →
    ((∀ k, ¬ offered_p Σ q k) → False) ∧ above_offered W (tenv_of Σ) (offered_p Σ q).
  Proof.
    intros Hrdy Hnt Hs. destruct HW as [HWf _].
    destruct (Hrdy (stable_back Hs)) as [Hv Ha].
    assert (¬ (offered_p Σp (C, E) (c, false) ∧ offered_p Σp (C, E) (d, false))) as Hnb.
    { intros [H1 H2]. destruct (sync_tau H1 H2) as [q' Hq]. exact (Hs q' Hq). }
    assert (Hcd_key : ∀ k, offered_p Σp (C, E) k → k.1 = c ∨ k.1 = d → k.2 = false).
    { intros [k1 b] (σ & p' & _ & Hsel) Hk. destruct (selects_entry _ _ _ Hsel) as [e He].
      simpl in *. destruct Hk as [->| ->];
        [by apply fusedP_entry_c in He as [-> _]|by apply fusedP_entry_d in He as [-> _]]. }
    (* an offered end of c or d lies above an offer of the fused process *)
    assert (Hkey : ∀ k0 e0, offered_p Σp (C, E) k0 → tenv_entry (tenv_of Σp) k0 = Some e0 →
              k0.1 = c ∨ k0.1 = d →
              ∃ k' e', offered_p Σ q k' ∧ tenv_entry (tenv_of Σ) k' = Some e' ∧
                w_lt W e'.2 e0.2).
    { intros [k1 b] e0 Ho He Hk. pose proof (Hcd_key _ Ho Hk) as Hb. simpl in Hb, Hk. subst b.
      destruct Hk as [->| ->].
      - rewrite entry_c in He. injection He as <-.
        destruct (Ha (d, false) (sd, kd) entry_d) as (k' & e' & Ho' & He' & Hlt).
        { intros Hd'. by apply Hnb. }
        unfold entry_head in Hlt. simpl in Hlt.
        destruct (decide (k'.1 = c)) as [Hk'|Hk'].
        { exfalso. destruct k' as [k1' b']. simpl in Hk'. subst k1'.
          apply fusedP_entry_c in He' as [-> ->]. simpl in Hlt.
          by apply (lt_eq_false kc kd). }
        destruct (decide (k'.1 = d)) as [Hk''|Hk''].
        { exfalso. destruct k' as [k1' b']. simpl in Hk''. subst k1'.
          apply fusedP_entry_d in He' as [-> ->]; [|done]. simpl in Hlt.
          destruct HW as [_ Hirr]. exact (Hirr _ Hlt). }
        exists k', e'. split_and!.
        + by apply off_fwd.
        + by rewrite <-(fusedP_entry_ne c d Σ sc sd kc kd).
        + simpl. eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlt|by apply (wf_eq_sym _ HWf)].
      - rewrite entry_d in He. injection He as <-.
        destruct (Ha (c, false) (sc, kc) entry_c) as (k' & e' & Ho' & He' & Hlt).
        { intros Hc'. by apply Hnb. }
        unfold entry_head in Hlt. simpl in Hlt.
        destruct (decide (k'.1 = d)) as [Hk'|Hk'].
        { exfalso. destruct k' as [k1' b']. simpl in Hk'. subst k1'.
          apply fusedP_entry_d in He' as [-> ->]; [|done]. simpl in Hlt.
          apply (lt_eq_false kd kc); [done|by apply (wf_eq_sym _ HWf)]. }
        destruct (decide (k'.1 = c)) as [Hk''|Hk''].
        { exfalso. destruct k' as [k1' b']. simpl in Hk''. subst k1'.
          apply fusedP_entry_c in He' as [-> ->]. simpl in Hlt.
          destruct HW as [_ Hirr]. exact (Hirr _ Hlt). }
        exists k', e'. split_and!.
        + by apply off_fwd.
        + by rewrite <-(fusedP_entry_ne c d Σ sc sd kc kd).
        + simpl. eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlt|exact Hal]. }
    split.
    - intros Hno. apply Hnt, Hv. intros k Ho.
      destruct (decide (k.1 = c ∨ k.1 = d)) as [Hk|Hk].
      + pose proof Ho as (σ & p' & _ & Hsel). destruct (selects_entry _ _ _ Hsel) as [e He].
        destruct (Hkey k e Ho He Hk) as (k' & e' & Ho' & _). exact (Hno k' Ho').
      + apply (Hno k). apply off_fwd; [done|done|tauto|tauto].
    - intros k e He Hk.
      assert (k.1 ≠ c ∧ k.1 ≠ d) as [Hk1 Hk2].
      { destruct k as [k1 b]. unfold tenv_entry, tenv_of in He. simpl in He |- *.
        rewrite lookup_fmap in He.
        split; intros ->; [rewrite (proj1 (not_elem_of_dom _ _) HcΣ) in He
                          |rewrite (proj1 (not_elem_of_dom _ _) HdΣ) in He]; done. }
      destruct (Ha k e) as (k' & e' & Ho' & He' & Hlt).
      { by rewrite (fusedP_entry_ne c d Σ sc sd kc kd). }
      { intros Ho. apply Hk. by apply off_fwd. }
      unfold entry_head in Hlt.
      destruct (decide (k'.1 = c ∨ k'.1 = d)) as [Hk'|Hk'].
      + destruct (Hkey k' e' Ho' He' Hk') as (k'' & e'' & Ho'' & He'' & Hlt').
        exists k'', e''. split_and!; [done|done|]. unfold entry_head.
        by eapply (wf_lt_trans _ HWf).
      + exists k', e'. split_and!.
        * apply off_fwd; [done|done|tauto|tauto].
        * rewrite <-(fusedP_entry_ne c d Σ sc sd kc kd); [done|tauto|tauto].
        * done.
  Qed.
End ready.
