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
