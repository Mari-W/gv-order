(** * Internalizing a link at component level (ORDERS-SPEC §11, sharp edges 45)

    A process holding one end each of two channels c and d, dual and
    at aliased points, stays related when d is restricted and c is
    renamed to d: the two ends become the two ends of the restricted
    channel d. Index preserving, because send, close and link keep the
    index (sharp edges 45): a synchronization of the fused process on
    d is a free send of p on one end followed by a costly receive on
    the other. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export invariance.JunkRenaming.

(** [set_solver] after dropping the large hypotheses. *)
Local Ltac sset :=
  repeat match goal with
    | H : ?P |- _ =>
        lazymatch P with
        | context [Prel] => clear H
        | context [Pcase_gen] => clear H
        | context [proc_step] => clear H
        | context [Vrel] => clear H
        | context [tstep] => clear H
        | context [recv_ok] => clear H
        | context [ready_p] => clear H
        end
    end; set_solver.

(** ** Duality at the head, with payloads and continuations *)

Lemma sdual_snd_inv s r m T s' :
  sdual s r → unfoldS s = SSeq (SSnd m T) s' →
  ∃ U r', unfoldS r = SSeq (SRcv m U) r' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs. destruct (sdual_snd s r m T s' H Hs) as (U & r' & Hr).
  exists U, r'. destruct (sdual_snd_rcv _ _ _ _ _ _ _ _ H Hs Hr) as (_ & ? & ?). done.
Qed.

Lemma sdual_rcv_inv s r m T s' :
  sdual s r → unfoldS s = SSeq (SRcv m T) s' →
  ∃ U r', unfoldS r = SSeq (SSnd m U) r' ∧ teq T U ∧ sdual s' r'.
Proof.
  intros H Hs. destruct (sdual_rcv s r m T s' H Hs) as (U & r' & Hr).
  exists U, r'. destruct (sdual_rcv_snd _ _ _ _ _ _ _ _ H Hs Hr) as (_ & ? & ?). done.
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
  Lemma fusedP_peel Σ sc sd kc kd Σ1 a x :
    c ∉ dom Σ → d ∉ dom Σ → a ≠ c → a ≠ d →
    fusedP Σ sc sd kc kd = <[a := x]> Σ1 → a ∉ dom Σ1 →
    Σ1 = fusedP (delete a Σ) sc sd kc kd ∧ Σ = <[a := x]> (delete a Σ).
  Proof.
    intros Hc Hd Hac Had Heq Ha. apply not_elem_of_dom in Hc, Hd, Ha.
    assert (∀ y, fusedP Σ sc sd kc kd !! y = (<[a := x]> Σ1) !! y) as H by (by rewrite Heq).
    split.
    - apply map_eq. intros y. specialize (H y). unfold fusedP in *.
      destruct (decide (y = a)) as [->|Hya]; [simplify_map_eq; done|].
      destruct (decide (y = c)) as [->|Hyc]; [simplify_map_eq; done|].
      destruct (decide (y = d)) as [->|Hyd]; simplify_map_eq; done.
    - apply map_eq. intros y. pose proof (H a) as Ha'. unfold fusedP in *.
      simplify_map_eq.
      destruct (decide (y = a)) as [->|Hya]; simplify_map_eq; done.
  Qed.

  Lemma fusedP_insert Σ sc sd kc kd a x :
    a ≠ c → a ≠ d → <[a := x]> (fusedP Σ sc sd kc kd) = fusedP (<[a := x]> Σ) sc sd kc kd.
  Proof.
    intros Hac Had. unfold fusedP.
    rewrite (insert_insert_ne _ a c), (insert_insert_ne _ a d) by done. done.
  Qed.
  Lemma tenv_ones_None Θ y : Θ !! y = None → tenv_ones Θ !! y = None.
  Proof. intros H. unfold tenv_ones. by rewrite lookup_omap, H. Qed.

  Lemma recv_env_fused Σr Θ2 sc sd kc kd :
    c ∉ dom Θ2 → d ∉ dom Θ2 →
    recv_env (fusedP Σr sc sd kc kd) Θ2 = fusedP (recv_env Σr Θ2) sc sd kc kd.
  Proof.
    intros Hc Hd. apply not_elem_of_dom in Hc, Hd. apply map_eq. intros y.
    destruct (decide (y = c)) as [->|Hyc]; [|destruct (decide (y = d)) as [->|Hyd]].
    - rewrite fusedP_c. unfold recv_env.
      rewrite lookup_union, !lookup_difference, fusedP_c, (tenv_ones_None _ c Hc). done.
    - rewrite fusedP_d. unfold recv_env.
      rewrite lookup_union, !lookup_difference, fusedP_d, (tenv_ones_None _ d Hd). done.
    - rewrite fusedP_ne by done. unfold recv_env.
      rewrite !lookup_union, !lookup_difference, fusedP_ne by done. done.
  Qed.

  Lemma recv_back_fused Σr Θ2 sc sd kc kd :
    c ∉ dom Θ2 → d ∉ dom Θ2 →
    recv_back (fusedP Σr sc sd kc kd) Θ2 = recv_back Σr Θ2.
  Proof. intros Hc Hd. unfold recv_back. rewrite fusedP_dom. set_solver. Qed.

  Lemma recv_ok_fused W Σr Θ2 sc sd kc kd :
    c ∉ dom Θ2 → d ∉ dom Θ2 →
    recv_ok W Σr Θ2 → recv_ok W (fusedP Σr sc sd kc kd) Θ2.
  Proof.
    intros Hc Hd (H1 & H2 & H3). split_and!; [|done|].
    - intros y e1 e2 He1 He2.
      assert (y ≠ c ∧ y ≠ d) as [Hyc Hyd].
      { apply not_elem_of_dom in Hc, Hd.
        split; intros ->; [rewrite (tenv_ones_None _ c Hc) in He2
                          |rewrite (tenv_ones_None _ d Hd) in He2]; done. }
      rewrite fusedP_ne in He1 by done. exact (H1 y e1 e2 He1 He2).
    - rewrite fusedP_dom. set_solver.
  Qed.
End fused.

Lemma dom_recv_env Σr Θ2 : dom (recv_env Σr Θ2) ⊆ dom Σr ∪ dom Θ2.
Proof.
  unfold recv_env. rewrite dom_union_L, !dom_difference_L.
  pose proof (dom_omap_subseteq (λ o, match o with One e => Some e | Both _ _ => None end) Θ2).
  unfold tenv_ones. set_solver.
Qed.

Lemma recv_back_dom Σr Θ2 : recv_back Σr Θ2 ⊆ dom Θ2.
Proof. unfold recv_back. set_solver. Qed.

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
      | [ (F & e & c0 & d0 & e' & -> & Hts & Hc0C & _)
      | (F & c0 & i & e & e' & f & f' & -> & Hts & Htr & _) ]]]]]].
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
    - apply (tstep_chsubst c d) in Hts, Htr. eexists.
      rewrite echsubst_disj_union2. by eapply PStepChoice.
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

End steps.

(** ** Readiness of the fused process *)

Section ready.
  Context (c d : chan) (Hcd : c ≠ d) (W : world) (HW : strict W) (Σ : senv)
    (sc sd : sty) (kc kd : point) (C : gset chan) (E : gmultiset expr).
  Context (HcΣ : c ∉ dom Σ) (HdΣ : d ∉ dom Σ) (HcC : c ∉ C) (HdC : d ∉ C)
    (Hdu : sdual sc sd) (Hal : w_eq W kc (pt_dual kd)).
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
    - exfalso. destruct σ as [c0 w|c0 w|c0|cd|c0 i|c0 i]; simpl in Ht.
      1-3,5-6: apply selects_subj in Hsel; simpl in Hsel; set_solver.
      destruct (lift_link_cd c d Hcd C E HcC HdC cd p' Hp Ht) as [q' Hq]. exact (Hs q' Hq).
    - destruct (lift_ext c d Hcd C E HcC HdC σ p' Hp) as [q' Hq]; [tauto|tauto|].
      exists (ssub c d σ), q'. split; [done|].
      assert (ssub_rel c d σ (ssub c d σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select_t c d _ σ (ssub c d σ) k Hr).
      { rewrite subjs_ssub, gsub_id; [done|]. tauto. }
      apply (selects_agree (tenv_of Σp)); [|done].
      intros y Hy. symmetry. apply tenv_of_fused_ne; intros ->; tauto.
  Qed.

  Lemma sync_tau :
    offered_p Σp (C, E) (c, false) → offered_p Σp (C, E) (d, false) →
    ∃ q', proc_step q PTau q'.
  Proof.
    intros (σ1 & p1 & H1 & Hs1) (σ2 & p2 & H2 & Hs2).
    destruct σ1 as [c1 w1|c1 w1|c1|cd1|c1 i1|c1 i1];
      [| | |eapply lift_link_cd; [done..|exact H1|left; by apply selects_subj in Hs1]| |].
    all: destruct σ2 as [c2 w2|c2 w2|c2|cd2|c2 i2|c2 i2];
      [| | |eapply lift_link_cd; [done..|exact H2|right; by apply selects_subj in Hs2]| |].
    (* mismatched heads contradict duality *)
    all: try (pose proof (selects_kind _ _ _ _ Hs1 entry_c ltac:(by intros ? ?)) as K1;
              pose proof (selects_kind _ _ _ _ Hs2 entry_d ltac:(by intros ? ?)) as K2;
              pose proof (sdual_kind _ _ Hdu) as Kd; simpl in K1, K2;
              rewrite K1, K2 in Kd; discriminate Kd).
    all: simpl in Hs1, Hs2; destruct Hs1 as [Hc1 _], Hs2 as [Hc2 _];
      simpl in Hc1, Hc2; subst c1 c2.
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
    - (* select on c, branch on d *)
      destruct (two_threads C E _ _ _ _ H1 H2) as (F & e1 & e1' & e2 & e2' & -> & Hst1 & Hst2).
      { intros [] Ha1 Ha2; simpl in Ha1, Ha2; naive_solver. }
      apply (tstep_chsubst c d) in Hst1, Hst2. simpl in Hst1, Hst2.
      rewrite csub_hit in Hst1. rewrite (csub_ne c d d) in Hst2 by done.
      destruct (bra_retarget _ _ _ _ i1 Hst2) as [f'' Hf''].
      eexists. rewrite echsubst_disj_union2. by eapply PStepChoice.
    - (* branch on c, select on d *)
      destruct (two_threads C E _ _ _ _ H1 H2) as (F & e1 & e1' & e2 & e2' & -> & Hst1 & Hst2).
      { intros [] Ha1 Ha2; simpl in Ha1, Ha2; naive_solver. }
      apply (tstep_chsubst c d) in Hst1, Hst2. simpl in Hst1, Hst2.
      rewrite csub_hit in Hst1. rewrite (csub_ne c d d) in Hst2 by done.
      destruct (bra_retarget _ _ _ _ i2 Hst1) as [f'' Hf''].
      eexists. rewrite echsubst_disj_union2.
      replace (echsubst c d F ⊎ {[+ chsubst c d e1 +]} ⊎ {[+ chsubst c d e2 +]})
        with (echsubst c d F ⊎ {[+ chsubst c d e2 +]} ⊎ {[+ chsubst c d e1 +]})
        by multiset_solver.
      by eapply PStepChoice.
  Qed.

  Lemma lt_eq_false x y : w_lt W x y → w_eq W x y → False.
  Proof.
    intros Hlt Heq. destruct HW as [HWf Hirr]. apply (Hirr y).
    eapply (wf_lt_eq _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hlt|apply HWf].
  Qed.

  Lemma fused_ready :
    ready_p W Σp (C, E) → ¬ terminated (C, E) → stable_p q →
    link_p q ∨
    (((∀ k, ¬ offered_p Σ q k) → False) ∧ above_offered W (tenv_of Σ) (offered_p Σ q)).
  Proof.
    intros Hrdy Hnt Hs. destruct HW as [HWf _].
    destruct (Hrdy (stable_back Hs)) as [(cd & p' & Hp)|[Hv Ha]].
    { (* a link redex on c or d fires in q, any other stays a link redex *)
      left. destruct (decide (c ∈ subjs (SLink cd) ∨ d ∈ subjs (SLink cd))) as [Ht|Ht].
      - destruct (lift_link_cd c d Hcd C E HcC HdC cd p' Hp Ht) as [q' Hq].
        by destruct (Hs q' Hq).
      - destruct (lift_ext c d Hcd C E HcC HdC _ p' Hp) as [q' Hq]; [tauto|tauto|].
        by exists (gsub c d cd), q'. }
    right.
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
          by apply (lt_eq_false kc (pt_dual kd)). }
        destruct (decide (k'.1 = d)) as [Hk''|Hk''].
        { exfalso. destruct k' as [k1' b']. simpl in Hk''. subst k1'.
          apply fusedP_entry_d in He' as [-> ->]; [|done]. apply Hnb. by split. }
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
          apply (lt_eq_false kd (pt_dual kc)); [done|by apply wf_eq_dual_sym]. }
        destruct (decide (k'.1 = c)) as [Hk''|Hk''].
        { exfalso. destruct k' as [k1' b']. simpl in Hk''. subst k1'.
          apply fusedP_entry_c in He' as [-> ->]. apply Hnb. by split. }
        exists k', e'. split_and!.
        + by apply off_fwd.
        + by rewrite <-(fusedP_entry_ne c d Σ sc sd kc kd).
        + simpl. eapply (wf_lt_eq _ HWf); [apply HWf|exact Hlt|by apply wf_eq_dual_l]. }

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

Lemma fchans_chsubst_eq x b e :
  x ∈ fchans e → x ≠ b → fchans (chsubst x b e) = fchans e ∖ {[x]} ∪ {[b]}.
Proof.
  intros Hx Hxb. pose proof (fchans_chsubst x b e). pose proof (fchans_chsubst_sup x b e).
  pose proof (fchans_chsubst_hit x b e Hx). pose proof (fchans_chsubst_notin x b e Hxb).
  apply set_eq. intros y. split; [set_solver|].
  intros Hy. apply elem_of_union in Hy as [Hy| ->%elem_of_singleton]; [|done].
  apply elem_of_difference in Hy as [Hy Hyx]. set_solver.
Qed.

Lemma csub_pair c d c0 c1 :
  csub c d c0 = csub c d c1 → c0 ≠ c1 → (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c).
Proof. unfold csub. repeat case_decide; subst; naive_solver. Qed.

Lemma chsubst_both c d y e :
  c ≠ d → y ≠ c → y ≠ d → chsubst c y (chsubst d c e) = chsubst d y (chsubst c d e).
Proof.
  intros. induction e; simpl; f_equal; auto. unfold csub in *. repeat case_decide; congruence.
Qed.

Lemma echsubst_both c d y E :
  c ≠ d → y ≠ c → y ≠ d → echsubst c y (echsubst d c E) = echsubst d y (echsubst c d E).
Proof.
  intros. unfold echsubst. induction E as [|e E IH] using gmultiset_ind.
  - by rewrite !gmultiset_map_empty.
  - rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH.
    by rewrite chsubst_both.
Qed.

(** Where the two ends sit in a split Σ0 ∪ Σv of the fused environment. *)
Lemma split_shape c d (Hcd : c ≠ d) (Σ0 Σv R : senv) sc sd kc kd :
  Σ0 ∪ Σv = fusedP c d R sc sd kc kd → Σ0 ##ₘ Σv → c ∉ dom R → d ∉ dom R →
  ∃ Σ0' Σv', Σ0' ∪ Σv' = R ∧ Σ0' ##ₘ Σv' ∧
    Σ0' !! c = None ∧ Σ0' !! d = None ∧ Σv' !! c = None ∧ Σv' !! d = None ∧
    ((Σ0 = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ0') ∧ Σv = Σv') ∨
     (Σ0 = <[d := (sd, kd)]> Σ0' ∧ Σv = <[c := (sc, kc)]> Σv') ∨
     (Σ0 = <[c := (sc, kc)]> Σ0' ∧ Σv = <[d := (sd, kd)]> Σv') ∨
     (Σ0 = Σ0' ∧ Σv = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σv'))).
Proof.
  intros Heq Hdj HcR HdR. apply not_elem_of_dom in HcR, HdR.
  assert (Hl : ∀ y, Σ0 !! y ∪ Σv !! y = fusedP c d R sc sd kc kd !! y)
    by (intros y; by rewrite <-lookup_union, Heq).
  pose proof (Hl c) as Hc. pose proof (Hl d) as Hd.
  rewrite fusedP_c in Hc. rewrite (fusedP_d c d Hcd) in Hd.
  rewrite map_disjoint_spec in Hdj.
  exists (delete c (delete d Σ0)), (delete c (delete d Σv)). split_and!.
  - apply map_eq. intros y. rewrite lookup_union.
    destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|].
    destruct (decide (y = d)) as [->|Hyd]; [by simplify_map_eq|].
    rewrite !lookup_delete_ne by done. rewrite Hl. by rewrite fusedP_ne.
  - apply map_disjoint_spec. intros y x1 x2 H1 H2.
    apply lookup_delete_Some in H1 as [_ H1], H2 as [_ H2].
    apply lookup_delete_Some in H1 as [_ H1], H2 as [_ H2]. exact (Hdj _ _ _ H1 H2).
  - by simplify_map_eq.
  - by simplify_map_eq.
  - by simplify_map_eq.
  - by simplify_map_eq.
  - destruct (Σ0 !! c) as [x0|] eqn:E0c, (Σv !! c) as [xv|] eqn:Evc;
      [exfalso; exact (Hdj _ _ _ E0c Evc)| | |done];
    (destruct (Σ0 !! d) as [y0|] eqn:E0d, (Σv !! d) as [yv|] eqn:Evd;
      [exfalso; exact (Hdj _ _ _ E0d Evd)| | |done]); simpl in Hc, Hd;
      injection Hc as ->; injection Hd as ->.
    + left. split; apply map_eq; intros y;
        (destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|]);
        (destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq).
    + right; right; left. split; apply map_eq; intros y;
        (destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|]);
        (destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq).
    + right; left. split; apply map_eq; intros y;
        (destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|]);
        (destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq).
    + right; right; right. split; apply map_eq; intros y;
        (destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|]);
        (destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq).
Qed.

(** ** A message from one end of the fused pair to the other *)

Section send_recv.
  Context (W : world) (Σr Σv Σe : senv) (Θe : tenv) (Cx : gset chan).
  Context (HΘe : dom Θe ⊆ Cx) (HΣv : dom Σv ## Cx) (Hsp : send_split W Σe Θe)
    (HrC : ∀ y, y ∈ Cx → Σr !! y = Σe !! y) (Hrv : ∀ y, y ∈ dom Σv → Σr !! y = None).

  Lemma ones_lookup y :
    tenv_ones (tenv_of Σv ∪ Θe) !! y =
      match Σv !! y with Some e => Some e | None => tenv_ones Θe !! y end.
  Proof.
    unfold tenv_ones, tenv_of. rewrite !lookup_omap, lookup_union, lookup_fmap.
    by destruct (Σv !! y), (Θe !! y).
  Qed.

  Lemma tenv2_lookup y :
    (tenv_of Σv ∪ Θe) !! y = match Σv !! y with Some e => Some (One e) | None => Θe !! y end.
  Proof. unfold tenv_of. rewrite lookup_union, lookup_fmap. by destruct (Σv !! y), (Θe !! y). Qed.

  Lemma Σv_Θe y : y ∈ dom Σv → Θe !! y = None.
  Proof. intros Hy. apply not_elem_of_dom. clear -Hy HΣv HΘe. set_solver. Qed.

  Lemma send_recv_ok : recv_ok W Σr (tenv_of Σv ∪ Θe).
  Proof.
    destruct Hsp as [Hsub Hs]. split_and!.
    - intros y e1 e2 H1 H2. rewrite ones_lookup in H2.
      destruct (Σv !! y) as [ev|] eqn:Ev.
      { rewrite Hrv in H1; [done|by apply elem_of_dom]. }
      unfold tenv_ones in H2. rewrite lookup_omap in H2.
      destruct (Θe !! y) as [[e'|e1' e2']|] eqn:Ee; simpl in H2; try done.
      injection H2 as <-. destruct (Hs y _ Ee) as (e & He & Heq & Hdu).
      rewrite HrC in H1; [|apply HΘe, elem_of_dom; by eexists].
      rewrite He in H1. by injection H1 as <-.
    - intros y e1 e2 H. rewrite tenv2_lookup in H.
      destruct (Σv !! y) eqn:Ev; [done|].
      destruct (Hs y _ H) as (_ & ? & ?). done.
    - apply elem_of_disjoint. intros y Hy Hr.
      apply elem_of_difference in Hy as [Hy Hn].
      apply elem_of_dom in Hy as [o Ho]. rewrite tenv2_lookup in Ho.
      assert (tenv_ones (tenv_of Σv ∪ Θe) !! y = None) as Hn'
        by (by apply not_elem_of_dom).
      rewrite ones_lookup in Hn'.
      destruct (Σv !! y) eqn:Ev; [done|].
      unfold tenv_ones in Hn'. rewrite lookup_omap, Ho in Hn'.
      destruct o as [e'|e1 e2]; [done|].
      destruct (Hs y _ Ho) as (HΣe & _ & _).
      apply elem_of_dom in Hr as [x Hx].
      rewrite HrC in Hx; [|apply HΘe, elem_of_dom; by eexists]. congruence.
  Qed.

  Lemma send_recv_back : recv_back Σr (tenv_of Σv ∪ Θe) = dom Θe.
  Proof.
    destruct Hsp as [Hsub Hs]. apply set_eq. intros y. unfold recv_back.
    rewrite elem_of_union, elem_of_intersection, elem_of_difference, !elem_of_dom.
    rewrite tenv2_lookup, ones_lookup. split.
    - intros [[[o Ho] [x Hx]]|[[o Ho] Hn]].
      + destruct (Σv !! y) eqn:Ev; [rewrite Hrv in Hx; [done|by apply elem_of_dom]|].
        by eexists.
      + destruct (Σv !! y) eqn:Ev; [by destruct Hn; eexists|]. by eexists.
    - intros [o Ho]. assert (Σv !! y = None) as Ev.
      { apply not_elem_of_dom. intros Hin. apply elem_of_dom_2 in Ho.
        clear -Hin Ho HΣv HΘe. set_solver. }
      rewrite Ev. destruct o as [e'|e1 e2].
      + left. split; [by eexists|]. destruct (Hs y _ Ho) as (e & He & _).
        rewrite HrC; [|apply HΘe, elem_of_dom; by eexists]. by eexists.
      + right. split; [by eexists|]. unfold tenv_ones. rewrite lookup_omap, Ho.
        by intros [? ?].
  Qed.

  Lemma send_recv_env_v y : y ∈ dom Σv → recv_env Σr (tenv_of Σv ∪ Θe) !! y = Σv !! y.
  Proof.
    intros Hy. unfold recv_env. rewrite lookup_union, !lookup_difference, ones_lookup.
    rewrite Hrv by done. apply elem_of_dom in Hy as [x Hx]. rewrite Hx. done.
  Qed.

  Lemma send_recv_env_e y : y ∈ dom Θe → recv_env Σr (tenv_of Σv ∪ Θe) !! y = None.
  Proof.
    intros Hy. destruct Hsp as [Hsub Hs].
    assert (Σv !! y = None) as Ev.
    { apply not_elem_of_dom. clear -Hy HΣv HΘe. set_solver. }
    unfold recv_env. rewrite lookup_union, !lookup_difference, ones_lookup, Ev.
    apply elem_of_dom in Hy as [o Ho]. rewrite HrC by (apply HΘe, elem_of_dom; by eexists).
    unfold tenv_ones. rewrite lookup_omap, Ho.
    destruct o as [e'|e1 e2].
    - destruct (Hs y _ Ho) as (e & He & _). rewrite He. done.
    - destruct (Hs y _ Ho) as (He & _). rewrite He. done.
  Qed.

  Lemma send_recv_env_o y :
    y ∉ dom Σv → y ∉ dom Θe → recv_env Σr (tenv_of Σv ∪ Θe) !! y = Σr !! y.
  Proof.
    intros Hv He. apply not_elem_of_dom in Hv, He.
    unfold recv_env. rewrite lookup_union, !lookup_difference, ones_lookup, Hv.
    rewrite (tenv_ones_None _ _ He). by destruct (Σr !! y).
  Qed.
End send_recv.

Lemma Pcase_gen_mono_at (X Y : world → senv → ty → proc → Prop) n' W Σ T p π p' :
  (∀ W Σ p, X W Σ T p → Y W Σ T p) →
  Pcase_gen X n' W Σ T p π p' → Pcase_gen Y n' W Σ T p π p'.
Proof.
  intros HXY. destruct π as [|[c w|c w|c|cd|c i|c i]]; simpl; try done.
  - intros [H1 H2]. split; [done|]. intros Hl Hd. apply HXY. by apply H2.
  - intros (Σ0&Σv&m&U&s&k&Σe&Θe&?&?&?&?&?&?&?&?&HX).
    exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; auto.
  - intros (Σ1&k&?&?&HX). exists Σ1, k. split_and!; auto.
  - intros (c0&d0&Σ1&sc&sd&kc&kd&?&?&?&?&?&?&?&HX).
    exists c0, d0, Σ1, sc, sd, kc, kd. split_and!; auto.
  - intros (Σ1&s1&s2&k&?&?&HX). exists Σ1, s1, s2, k. split_and!; auto.
Qed.

(** ** The lemma *)

Section internalize.
  Context (c d : chan) (Hcd : c ≠ d).

  Definition int_ok (W : world) (Σ : senv) (sc sd : sty) (kc kd : point)
      (C : gset chan) : Prop :=
    strict W ∧ c ∉ dom Σ ∧ d ∉ dom Σ ∧ c ∉ C ∧ d ∉ C ∧ sdual sc sd ∧ w_eq W kc (pt_dual kd).

  Definition fuse_goal (m : nat) (W : world) (Σp : senv) (T : ty) (p : proc) : Prop :=
    ∀ Σ C E sc sd kc kd, Σp = fusedP c d Σ sc sd kc kd → p = (C, E) →
      int_ok W Σ sc sd kc kd C → Prel m W Σ T (C ∪ {[d]}, echsubst c d E).

  Section step.
    Context (n' : nat) (T : ty) (HT : prim T)
      (IH : ∀ j, j ≤ n' → ∀ W Σp p, Prel j W Σp T p → fuse_goal j W Σp T p).
    Context (W : world) (Σ : senv) (sc sd : sty) (kc kd : point)
      (C : gset chan) (E : gmultiset expr).
    Context (HW : strict W) (HcΣ : c ∉ dom Σ) (HdΣ : d ∉ dom Σ) (HcC : c ∉ C)
      (HdC : d ∉ C) (Hdu : sdual sc sd) (Hal : w_eq W kc (pt_dual kd)).
    Local Notation Σp := (fusedP c d Σ sc sd kc kd).
    Local Notation q := (C ∪ {[d]}, echsubst c d E).
    Local Notation X := (λ W Σp T p, Prel (S n') W Σp T p ∧ fuse_goal (S n') W Σp T p).
    Context (Hstep : ∀ π p', proc_step (C, E) π p' → Pcase_gen X n' W Σp T (C, E) π p').

    Lemma int_ok_ext W' Σ' C' :
      wext W W' → c ∉ dom Σ' → d ∉ dom Σ' → c ∉ C' → d ∉ C' → int_ok W' Σ' sc sd kc kd C'.
    Proof.
      intros Hx ????. split_and!; try done.
      - by destruct Hx as (_ & _ & _ & ?).
      - by apply (proj1 (proj2 Hx)).
    Qed.

    Lemma ext_recv a w' q' :
      proc_step q (PSess (SRecv a w')) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SRecv a w')) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      simpl in HsC. cbn [sentc fst snd]. rewrite difference_empty_L.
      destruct (exist_fresh (fchans w' ∪ fchans e ∪ echans F ∪ C ∪ dom Σ ∪ {[c; d]}))
        as [z Hz].
      destruct (tstep_chsubst_recv_inv_swap c d z e a w' f')
        as (c0 & f & Hc0 & Hf & ->); [done|sset|sset|sset|done|sset|].
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by sset.
      pose proof (Hstep _ _ (PStepSession C F e (SRecv a (eswap c z w')) f Hf
                    ltac:(simpl; sset))) as Hp.
      simpl in Hp. destruct Hp as (Σ1 & m & U & s & k & (s0 & HΣ & Hu) & Ha1 & H).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd Σ1 a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha1)
        as [-> HΣ'].
      exists (delete a Σ), m, U, s, k. split_and!.
      { exists s0. done. }
      { rewrite dom_delete_L. sset. }
      intros W' j Θ2 HW' Hj HΘ2 Hok HVw.
      set (Σr := <[a := (s, pt_shift 1 k)]> (delete a Σ)) in *.
      assert (strict W') as HW'' by (by destruct HW' as (_ & _ & _ & ?)).
      assert (z ∉ dom Θ2) as HzΘ.
      { rewrite <-(Vrel_fchans _ _ _ _ _ HVw). clear -Hz. set_solver. }
      assert (a ∈ dom Σ) as HaΣ.
      { rewrite HΣ', dom_insert_L. clear. set_solver. }
      assert (c ∉ dom Σr ∧ z ∉ dom Σr ∧ d ∉ dom Σr) as (HcΣr & HzΣr & HdΣr).
      { unfold Σr. rewrite dom_insert_L, dom_delete_L.
        clear -Hz HcΣ HdΣ Hc0c Had HaΣ. set_solver. }
      set (Θ2p := tenvswap c z Θ2).
      assert (c ∉ dom Θ2p) as HcΘ.
      { unfold Θ2p. rewrite dom_tenvswap, elem_of_gswap', cswap_l. done. }
      assert (d ∉ dom Θ2p) as HdΘ.
      { assert (d ∉ dom Θ2) as Hd2 by (clear -HΘ2; set_solver).
        unfold Θ2p. rewrite dom_tenvswap, elem_of_gswap', cswap_ne; [done| |].
        - clear -Hcd. done.
        - clear -Hz. set_solver. }
      assert (dom Θ2p ## C) as HfrC.
      { unfold Θ2p. rewrite dom_tenvswap. apply elem_of_disjoint. intros y Hy HyC.
        apply elem_of_gswap' in Hy. unfold cswap in Hy.
        repeat case_decide; subst; [clear -HyC HcC; done|clear -HyC Hz; set_solver|].
        apply (elem_of_disjoint _ _) in HΘ2. apply (HΘ2 y); [done|]. clear -HyC. set_solver. }
      assert (recv_ok W' Σr Θ2p) as Hok2.
      { apply (recv_ok_swap c z) in Hok. by rewrite senvswap_fix in Hok. }
      pose proof (H W' j Θ2p HW' Hj) as HP1. cbn [sentc fst snd] in HP1.
      rewrite difference_empty_L, fusedP_insert in HP1 by done.
      rewrite (recv_env_fused c d Hcd), (recv_back_fused c d Hcd) in HP1 by done.
      specialize (HP1 HfrC (recv_ok_fused c d Hcd _ _ _ _ _ _ _ HcΘ HdΘ Hok2)
                    (Vrel_swap c z _ _ _ _ _ HVw)).
      apply (IH j Hj) in HP1.
      specialize (HP1 (recv_env Σr Θ2p) _ _ sc sd kc kd eq_refl eq_refl).
      match type of HP1 with ?A → _ => assert A as Hok' end.
      { pose proof (dom_recv_env Σr Θ2p) as Hd1. pose proof (recv_back_dom Σr Θ2p) as Hd2.
        apply int_ok_ext; [done|clear -Hd1 Hd2 HcΣr HdΣr HcΘ HdΘ HcC HdC; set_solver..]. }
      specialize (HP1 Hok').
      apply (Prel_swap c z) in HP1. unfold pswap in HP1. simpl in HP1. unfold Θ2p in HP1.
      rewrite <-recv_env_swap, senvswap_fix, tenvswap_involutive in HP1 by done.
      rewrite !gswap_union, <-recv_back_swap, senvswap_fix, tenvswap_involutive in HP1
        by done.
      rewrite (gswap_fresh c z C), gswap_singleton, cswap_ne in HP1;
        [|clear -Hcd; done|clear -Hz; set_solver|done|clear -Hz; set_solver].
      rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP1.
      rewrite (msswap_fresh c z (echsubst c d F)) in HP1;
        [|apply echans_echsubst_notin; done|].
      2: { pose proof (echans_echsubst_sub c d F) as Hsub. clear -Hsub Hz. set_solver. }
      assert (C ∪ recv_back Σr Θ2 ∪ {[d]} = C ∪ {[d]} ∪ recv_back Σr Θ2) as Hset
        by (clear; set_solver).
      unfold Σr in Hset. rewrite Hset in HP1. exact HP1.
    Qed.

    Lemma ext_close a q' :
      proc_step q (PSess (SClos a)) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SClos a)) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [sentc fst snd]. rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hstep _ _ (PStepSession C F e (SClos a) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [Pcase_gen] in Hp. destruct Hp as (Σ1 & k & (s0 & HΣ & Hu) & Ha1 & _ & HΦ).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd Σ1 a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha1)
        as [-> HΣ'].
      exists (delete a Σ), k. split_and!.
      { by exists s0. }
      { rewrite dom_delete_L. clear. set_solver. }
      cbn [sentc] in HΦ. rewrite difference_empty_L in HΦ.
      pose proof (HΦ (delete a Σ) _ _ sc sd kc kd eq_refl eq_refl) as HP.
      rewrite echsubst_disj_union1 in HP. apply HP.
      apply int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_delete_L;
        clear -HcΣ HdΣ; set_solver.
    Qed.

    Lemma ext_sel a i q' :
      proc_step q (PSess (SSel a i)) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SSel a i)) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost sentc fst snd].
      rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hstep _ _ (PStepSession C F e (SSel a i) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost] in Hp.
      destruct Hp as (Σ1 & s1 & s2 & k & (s0 & HΣ & Hu) & Ha1 & _ & HΦ).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd Σ1 a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha1)
        as [-> HΣ'].
      exists (delete a Σ), s1, s2, k. split_and!.
      { by exists s0. }
      { rewrite dom_delete_L. clear. set_solver. }
      cbn [sentc] in HΦ. rewrite difference_empty_L in HΦ.
      pose proof (HΦ (<[a := (sbranch i s1 s2, sel_pt k i)]> (delete a Σ)) C (F ⊎ {[+ f +]})
                    sc sd kc kd) as HP.
      rewrite echsubst_disj_union1 in HP. apply HP.
      { unfold fusedP. rewrite (insert_insert_ne _ a c), (insert_insert_ne _ a d) by done. done. }
      { done. }
      apply int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_insert_L, dom_delete_L;
        clear -HcΣ HdΣ Hc0c Had; set_solver.
    Qed.

    Lemma ext_bra a i q' :
      proc_step q (PSess (SBra a i)) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SBra a i)) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost sentc fst snd nlower pred].
      rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hstep _ _ (PStepSession C F e (SBra a i) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost nlower pred] in Hp.
      destruct Hp as (Σ1 & s1 & s2 & k & (s0 & HΣ & Hu) & Ha1 & HP1).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd Σ1 a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha1)
        as [-> HΣ'].
      exists (delete a Σ), s1, s2, k. split_and!.
      { by exists s0. }
      { rewrite dom_delete_L. clear. set_solver. }
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      pose proof (IH n' (le_n _) W _ _ HP1 (<[a := (sbranch i s1 s2, bra_pt k i)]> (delete a Σ))
                    C (F ⊎ {[+ f +]}) sc sd kc kd) as HP.
      rewrite echsubst_disj_union1 in HP. apply HP.
      { unfold fusedP. rewrite (insert_insert_ne _ a c), (insert_insert_ne _ a d) by done. done. }
      { done. }
      apply int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_insert_L, dom_delete_L;
        clear -HcΣ HdΣ Hc0c Had; set_solver.
    Qed.

    Lemma ext_link cd q' :
      proc_step q (PSess (SLink cd)) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SLink cd)) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [sentc fst snd]. rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hcd'.
      assert (c ∉ cd0 ∧ d ∉ cd0) as [Hc0 Hd0].
      { subst cd. split; intros Hin; apply (elem_of_disjoint _ _) in HsC; apply (HsC d);
          [|clear; set_solver| |clear; set_solver];
          unfold gsub; apply elem_of_map; [exists c|exists d]; (split; [|done]);
          [by rewrite csub_hit|by rewrite csub_ne]. }
      rewrite gsub_id in Hcd' by done. subst cd.
      pose proof (Hstep _ _ (PStepSession C F e (SLink cd0) f Hf
                    ltac:(cbn [subjs]; clear -HsC; set_solver))) as Hp.
      cbn [Pcase_gen] in Hp.
      destruct Hp as (c1 & d1 & Σ1 & sc1 & sd1 & kc1 & kd1 & -> & Hne & HΣ & Hc1 & Hd1 &
                      Hdu1 & Hal1 & _ & HΦ).
      assert (c1 ≠ c ∧ c1 ≠ d ∧ d1 ≠ c ∧ d1 ≠ d) as (H1 & H2 & H3 & H4)
        by (clear -Hc0 Hd0; set_solver).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd _ c1 (sc1, kc1) HcΣ HdΣ H1 H2 HΣ)
        as [HΣ1 HΣ']; [rewrite dom_insert_L; clear -Hc1 Hne; set_solver|].
      assert (c ∉ dom (delete c1 Σ) ∧ d ∉ dom (delete c1 Σ)) as [Hc' Hd']
        by (rewrite dom_delete_L; clear -HcΣ HdΣ; set_solver).
      destruct (fusedP_peel c d Hcd (delete c1 Σ) sc sd kc kd Σ1 d1 (sd1, kd1) Hc' Hd' H3 H4
                  (eq_sym HΣ1) Hd1) as [-> HΣ''].
      exists c1, d1, (delete d1 (delete c1 Σ)), sc1, sd1, kc1, kd1. split_and!; try done.
      { rewrite HΣ' at 1. rewrite HΣ'' at 1. done. }
      { rewrite !dom_delete_L. clear. set_solver. }
      { rewrite !dom_delete_L. clear. set_solver. }
      cbn [sentc] in HΦ. rewrite difference_empty_L in HΦ.
      pose proof (HΦ (delete d1 (delete c1 Σ)) _ _ sc sd kc kd eq_refl eq_refl) as HP.
      rewrite echsubst_disj_union1 in HP. apply HP.
      apply int_ok_ext; [by apply wext_refl| | |done|done]; rewrite !dom_delete_L;
        clear -HcΣ HdΣ; set_solver.
    Qed.

    Lemma ext_send a w' q' :
      proc_step q (PSess (SSend a w')) q' →
      Pcase_gen (Prel (S n')) n' W Σ T q (PSess (SSend a w')) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [sentc fst snd].
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 ->.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hstep _ _ (PStepSession C F e (SSend a w0) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [Pcase_gen] in Hp.
      destruct Hp as (Σ0 & Σv & m & U & s & k & Σe & Θe & (s0 & HΣ & Hu) & Hdj & Ha0 & Hav &
                      Hdom & Hsplit & HdΘΣ & HV & HP1 & HΦ).
      cbn [fst snd sentc] in Hdom, HP1, HΦ.
      assert (a ∉ dom (Σ0 ∪ Σv)) as Ha01
        by (rewrite dom_union_L; clear -Ha0 Hav; set_solver).
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd (Σ0 ∪ Σv) a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha01)
        as [H01 HΣ'].
      assert (c ∉ dom (delete a Σ) ∧ d ∉ dom (delete a Σ) ∧ a ∉ dom (delete a Σ))
        as (HcR & HdR & HaR) by (rewrite dom_delete_L; clear -HcΣ HdΣ; set_solver).
      destruct (split_shape c d Hcd Σ0 Σv (delete a Σ) sc sd kc kd H01 Hdj HcR HdR)
        as (Σ0' & Σv' & HR & Hdj' & H0c & H0d & Hvc & Hvd & Hcase).
      rewrite <-HR in HΣ', HaR. rewrite dom_union_L in HaR.
      assert (dom Θe ⊆ C) as HΘeC by (rewrite Hdom; clear; set_solver).
      assert (dom Σe ⊆ dom Θe) as HΣeΘ by (by destruct Hsplit).
      assert (Θe !! c = None ∧ Θe !! d = None) as [HcΘe HdΘe]
        by (rewrite <-!not_elem_of_dom; clear -HΘeC HcC HdC; set_solver).
      assert (Σe !! c = None ∧ Σe !! d = None) as [HcΣe HdΣe]
        by (rewrite <-!not_elem_of_dom; clear -HΣeΘ HΘeC HcC HdC; set_solver).
      assert (fchans w0 = dom Σv ∪ dom Θe) as Hfw.
      { rewrite (Vrel_fchans _ _ _ _ _ HV), dom_union_L. unfold tenv_of. by rewrite dom_fmap_L. }
      assert (dom Θe ## dom Σ) as HΘeΣ.
      { rewrite (fusedP_dom c d Hcd) in HdΘΣ. clear -HdΘΣ. set_solver. }
      assert (strict W) as HW' by done.
      destruct HW' as [HWf _].
      destruct Hcase as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
      - (* neither end is sent *)
        assert (c ∉ fchans w0 ∧ d ∉ fchans w0) as [Hcw Hdw].
        { rewrite Hfw. apply not_elem_of_dom in Hvc, Hvd, HcΘe, HdΘe.
          clear -Hvc Hvd HcΘe HdΘe. set_solver. }
        rewrite (chsubst_id c d w0) by done.
        exists Σ0', Σv', m, U, s, k, Σe, Θe. split_and!.
        + by exists s0.
        + done.
        + clear -HaR. set_solver.
        + clear -HaR. set_solver.
        + cbn [fst]. rewrite Hdom. clear -Hdw. set_solver.
        + done.
        + done.
        + done.
        + pose proof (HΦ (<[a := (s, pt_shift 1 k)]> (Σ0' ∪ Σe)) (C ∖ fchans w0)
                        (F ⊎ {[+ f +]}) sc sd kc kd) as HP.
          rewrite echsubst_disj_union1 in HP.
          replace ((C ∪ {[d]}) ∖ fchans w0) with (C ∖ fchans w0 ∪ {[d]})
            by (clear -Hdw; set_solver).
          apply HP; [|done|].
          * unfold fusedP. rewrite <-!insert_union_l.
            rewrite (insert_insert_ne _ a c), (insert_insert_ne _ a d) by done. done.
          * apply int_ok_ext; [by apply wext_refl| | |clear -HcC; set_solver|clear -HdC; set_solver];
              rewrite dom_insert_L, dom_union_L; apply not_elem_of_dom in H0c, H0d, HcΣe, HdΣe;
              clear -H0c H0d HcΣe HdΣe Hc0c Had; set_solver.
      - (* the end c is sent *)
        assert (c ∈ fchans w0) as Hcw by (rewrite Hfw, dom_insert_L; clear; set_solver).
        exists Σ0', Σv', m, U, s, k, (<[d := (sd, kd)]> Σe), (<[d := One (sc, kc)]> Θe).
        split_and!.
        + by exists s0.
        + done.
        + clear -HaR. set_solver.
        + clear -HaR. set_solver.
        + cbn [fst]. rewrite dom_insert_L, (fchans_chsubst_eq c d w0), Hdom by done.
          clear -HcC. set_solver.
        + split; [rewrite !dom_insert_L; clear -HΣeΘ; set_solver|].
          intros r o Hr. destruct (decide (r = d)) as [->|Hrd].
          * rewrite lookup_insert_eq in Hr. injection Hr as <-. exists (sd, kd).
            rewrite lookup_insert_eq. split_and!; [done|by apply wf_eq_dual_sym|by apply sdual_sym].
          * rewrite lookup_insert_ne in Hr by done. destruct Hsplit as [_ Hs].
            specialize (Hs r o Hr). rewrite lookup_insert_ne by done. done.
        + rewrite dom_insert_L. clear -HΘeΣ HdΣ. set_solver.
        + apply (Vrel_rename _ _ _ _ _ c d) in HV.
          2: { rewrite dom_union_L. unfold tenv_of. rewrite dom_fmap_L, dom_insert_L.
               apply not_elem_of_dom in Hvd, HdΘe. clear -Hvd HdΘe Hcd. set_solver. }
          unfold tenv_of in HV |- *. rewrite fmap_insert, <-insert_union_l, tenvswap_insert,
            cswap_l, tenvswap_fix in HV.
          * rewrite insert_union_r in HV; [done|]. by rewrite lookup_fmap, Hvd.
          * rewrite dom_union_L, dom_fmap_L. apply not_elem_of_dom in Hvc, HcΘe.
            clear -Hvc HcΘe. set_solver.
          * rewrite dom_union_L, dom_fmap_L. apply not_elem_of_dom in Hvd, HdΘe.
            clear -Hvd HdΘe. set_solver.
        + rewrite <-insert_union_r by done. rewrite insert_union_l.
          apply (Prel_junk _ _ _ _ _ _ c d) in HP1.
          * rewrite echsubst_disj_union1 in HP1.
            rewrite (fchans_chsubst_eq c d w0) by done.
            replace ((C ∪ {[d]}) ∖ (fchans w0 ∖ {[c]} ∪ {[d]})) with (C ∖ fchans w0)
              by (clear -HcC HdC; set_solver).
            exact HP1.
          * rewrite dom_insert_L, dom_union_L, dom_insert_L. apply not_elem_of_dom in H0c, HcΣe.
            clear -H0c HcΣe Hc0c Hcd. set_solver.
          * clear -HcC. set_solver.
          * intros Hin. exfalso. clear -Hin HdC. set_solver.
          * done.
      - (* the end d is sent *)
        assert (c ∉ fchans w0 ∧ d ∈ fchans w0) as [Hcw Hdw].
        { rewrite Hfw, dom_insert_L. apply not_elem_of_dom in Hvc, HcΘe.
          clear -Hvc HcΘe Hcd. set_solver. }
        rewrite (chsubst_id c d w0) by done.
        exists Σ0', Σv', m, U, s, k, (<[d := (sc, kc)]> Σe), (<[d := One (sd, kd)]> Θe).
        split_and!.
        + by exists s0.
        + done.
        + clear -HaR. set_solver.
        + clear -HaR. set_solver.
        + cbn [fst]. rewrite dom_insert_L, Hdom. clear -Hdw. set_solver.
        + split; [rewrite !dom_insert_L; clear -HΣeΘ; set_solver|].
          intros r o Hr. destruct (decide (r = d)) as [->|Hrd].
          * rewrite lookup_insert_eq in Hr. injection Hr as <-. exists (sc, kc).
            rewrite lookup_insert_eq. split_and!; done.
          * rewrite lookup_insert_ne in Hr by done. destruct Hsplit as [_ Hs].
            specialize (Hs r o Hr). rewrite lookup_insert_ne by done. done.
        + rewrite dom_insert_L. clear -HΘeΣ HdΣ. set_solver.
        + unfold tenv_of in HV |- *. rewrite fmap_insert, <-insert_union_l in HV.
          rewrite insert_union_r in HV; [done|]. by rewrite lookup_fmap, Hvd.
        + apply (Prel_junk _ _ _ _ _ _ d c) in HP1.
          * apply (Prel_swap c d) in HP1. unfold pswap in HP1. simpl in HP1.
            rewrite msswap_echsubst_flip, gswap_fresh in HP1;
              [|clear -HcC; set_solver|clear -HdC; set_solver].
            rewrite echsubst_disj_union1 in HP1.
            replace ((C ∪ {[d]}) ∖ fchans w0) with (C ∖ fchans w0) by (clear -Hdw; set_solver).
            rewrite <-insert_union_l, senvswap_insert, senvswap_insert, cswap_ne, cswap_l,
              senvswap_fix in HP1.
            -- rewrite <-insert_union_r by done. exact HP1.
            -- rewrite dom_union_L. apply not_elem_of_dom in H0c, HcΣe. clear -H0c HcΣe. set_solver.
            -- rewrite dom_union_L. apply not_elem_of_dom in H0d, HdΣe. clear -H0d HdΣe. set_solver.
            -- done.
            -- done.
          * rewrite dom_insert_L, dom_union_L, dom_insert_L. apply not_elem_of_dom in H0d, HdΣe.
            clear -H0d HdΣe Had Hcd. set_solver.
          * clear -HdC. set_solver.
          * intros Hin. exfalso. clear -Hin HcC. set_solver.
          * done.
      - (* both ends are sent *)
        assert (c ∈ fchans w0) as Hcw by (rewrite Hfw, dom_insert_L; clear; set_solver).
        exists Σ0', Σv', m, U, s, k, Σe, (<[d := Both (sc, kc) (sd, kd)]> Θe).
        split_and!.
        + by exists s0.
        + done.
        + clear -HaR. set_solver.
        + clear -HaR. set_solver.
        + cbn [fst]. rewrite dom_insert_L, (fchans_chsubst_eq c d w0), Hdom by done.
          clear -HcC. set_solver.
        + split; [rewrite dom_insert_L; clear -HΣeΘ; set_solver|].
          intros r o Hr. destruct (decide (r = d)) as [->|Hrd].
          * rewrite lookup_insert_eq in Hr. injection Hr as <-. done.
          * rewrite lookup_insert_ne in Hr by done. destruct Hsplit as [_ Hs].
            exact (Hs r o Hr).
        + rewrite dom_insert_L. clear -HΘeΣ HdΣ. set_solver.
        + set (M := tenv_of Σv' ∪ Θe).
          assert (M !! c = None ∧ M !! d = None) as [HMc HMd].
          { unfold M, tenv_of. rewrite !lookup_union, !lookup_fmap, Hvc, Hvd, HcΘe, HdΘe.
            done. }
          assert (tenv_of (<[c := (sc, kc)]> (<[d := (sd, kd)]> Σv')) ∪ Θe =
                  <[c := One (sc, kc)]> (<[d := One (sd, kd)]> M)) as E1.
          { unfold M, tenv_of. by rewrite !fmap_insert, <-!insert_union_l. }
          assert (tenv_of Σv' ∪ <[d := Both (sc, kc) (sd, kd)]> Θe =
                  <[d := Both (sc, kc) (sd, kd)]> M) as E2.
          { unfold M. rewrite insert_union_r; [done|]. unfold tenv_of. by rewrite lookup_fmap, Hvd. }
          rewrite E1 in HV. rewrite E2.
          apply (proj1 (rel_fuse (S n')) W (<[c := One (sc, kc)]> (<[d := One (sd, kd)]> M))
                   (<[d := Both (sc, kc) (sd, kd)]> M) _ w0 c d HW Hcd); [|exact HV].
          split_and!.
          * by simplify_map_eq.
          * intros y Hyc Hyd. by simplify_map_eq.
          * simplify_map_eq. constructor.
          * intros e1 e2 He1 He2. simplify_map_eq. done.
        + apply (Prel_junk _ _ _ _ _ _ c d) in HP1.
          * rewrite echsubst_disj_union1 in HP1.
            rewrite (fchans_chsubst_eq c d w0) by done.
            replace ((C ∪ {[d]}) ∖ (fchans w0 ∖ {[c]} ∪ {[d]})) with (C ∖ fchans w0)
              by (clear -HcC HdC; set_solver).
            exact HP1.
          * rewrite dom_insert_L, dom_union_L. apply not_elem_of_dom in H0c, HcΣe.
            clear -H0c HcΣe Hc0c. set_solver.
          * clear -HcC. set_solver.
          * intros Hin. exfalso. clear -Hin HdC. set_solver.
          * done.
    Qed.

    Lemma sync_case F2 h h0 g g0 c0 c1 w0 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SSend c0 w0)) h0 → tstep g (LSess (SRecv c1 w0)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) → C ## dom Σ →
      Prel n' W Σ T (C ∪ {[d]}, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros -> Hh Hg Hcc HCΣ. destruct HW as [HWf _].
      assert (c0 ≠ c1 ∧ c0 ∉ C ∧ c1 ∉ C) as (Hc01 & Hc0C & Hc1C)
        by (destruct Hcc as [[-> ->]|[-> ->]]; split_and!; done).
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SSend c0 w0))
                (C ∖ sentc (SSend c0 w0), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hstep _ _ Hst1) as Hp. cbn [Pcase_gen] in Hp.
      destruct Hp as (Σ0 & Σv & m & U & s & k & Σe & Θe & (s0 & HΣ & Hu) & Hdj & Ha0 & Hav &
                      Hdom & Hsplit & HdΘΣ & HV & HP1 & _).
      cbn [fst snd sentc] in Hdom, HP1.
      assert (Hl : ∀ y, fusedP c d Σ sc sd kc kd !! y = (<[c0 := (s0, k)]> (Σ0 ∪ Σv)) !! y)
        by (intros; by rewrite HΣ).
      assert (dom Θe ⊆ C) as HΘeC by (rewrite Hdom; clear; set_solver).
      assert (dom Σe ⊆ dom Θe) as HΣeΘ by (by destruct Hsplit).
      assert (HΣ0C : ∀ y, y ∈ C → Σ0 !! y = None ∧ Σv !! y = None).
      { intros y Hy. specialize (Hl y).
        assert (y ≠ c ∧ y ≠ d ∧ y ≠ c0) as (Hyc & Hyd & Hy0)
          by (split_and!; intros ->; done).
        rewrite fusedP_ne, lookup_insert_ne, lookup_union in Hl by done.
        assert (Σ !! y = None) as Hy' by (apply not_elem_of_dom; clear -HCΣ Hy; set_solver).
        rewrite Hy' in Hl. destruct (Σ0 !! y), (Σv !! y); done. }
      assert (proc_step (C ∖ fchans w0, F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) (PSess (SRecv c1 w0))
                (C ∖ fchans w0 ∖ sentc (SRecv c1 w0), F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Hst2.
      { replace (F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) with (F2 ⊎ {[+ h0 +]} ⊎ {[+ g +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc1C. set_solver. }
      pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst2) as Hp2. cbn [Pcase_gen] in Hp2.
      destruct Hp2 as (Σ1 & m' & U' & s' & k' & (s1 & HΣ1 & Hu1) & Hc1Σ1 & Hrecv).
      cbn [fst snd sentc] in Hrecv. rewrite difference_empty_L in Hrecv.
      set (Σp1 := <[c0 := (s, pt_shift 1 k)]> (Σ0 ∪ Σe)) in *.
      assert (Hl1 : ∀ y, Σp1 !! y = (<[c1 := (s1, k')]> Σ1) !! y) by (intros; by rewrite HΣ1).
      (* the entries of the two ends *)
      assert (fusedP c d Σ sc sd kc kd !! c0 = Some (s0, k)) as E0
        by (rewrite Hl; by rewrite lookup_insert_eq).
      assert (fusedP c d Σ sc sd kc kd !! c1 = Some (s1, k')) as E1.
      { pose proof (Hl1 c1) as H1. unfold Σp1 in H1.
        rewrite lookup_insert_ne, lookup_insert_eq, lookup_union in H1 by done.
        assert (Σe !! c1 = None) as He1
          by (apply not_elem_of_dom; clear -HΣeΘ HΘeC Hc1C; set_solver).
        rewrite He1 in H1. destruct (Σ0 !! c1) as [x|] eqn:Ex; [|done].
        simpl in H1. injection H1 as ->. rewrite Hl, lookup_insert_ne by done.
        by apply lookup_union_Some_l. }
      (* the payload types agree, the continuations are dual *)
      assert (m' = m ∧ teq U U' ∧
              ((c0 = c ∧ c1 = d ∧ sdual s s') ∨ (c0 = d ∧ c1 = c ∧ sdual s' s)) ∧
              w_eq W k (pt_dual k')) as (-> & HUU & Hcont & Hkk).
      { destruct Hcc as [[-> ->]|[-> ->]].
        - rewrite fusedP_c in E0. rewrite (fusedP_d c d Hcd) in E1.
          injection E0 as -> ->. injection E1 as -> ->.
          destruct (sdual_snd_inv _ _ _ _ _ Hdu Hu) as (U2 & r' & Hr & HU2 & Hsr).
          rewrite Hu1 in Hr. injection Hr as -> -> ->. split_and!; [done|done| |done].
          left. done.
        - rewrite (fusedP_d c d Hcd) in E0. rewrite fusedP_c in E1.
          injection E0 as -> ->. injection E1 as -> ->.
          destruct (sdual_rcv_inv _ _ _ _ _ Hdu Hu1) as (U2 & r' & Hr & HU2 & Hsr).
          rewrite Hu in Hr. injection Hr as -> -> ->. split_and!; [done|by apply teq_sym| |].
          + right. done.
          + by apply wf_eq_dual_sym. }
      set (Σr := <[c1 := (s', pt_shift 1 k')]> Σ1).
      assert (HrC : ∀ y, y ∈ C → Σr !! y = Σe !! y).
      { intros y Hy. assert (y ≠ c1 ∧ y ≠ c0) as [Hy1 Hy0] by (split; intros ->; done).
        unfold Σr. rewrite lookup_insert_ne by done.
        pose proof (Hl1 y) as H1. rewrite lookup_insert_ne in H1 by done.
        rewrite <-H1. unfold Σp1. rewrite lookup_insert_ne, lookup_union by done.
        destruct (HΣ0C y Hy) as [-> _]. by destruct (Σe !! y). }
      assert (Hrv : ∀ y, y ∈ dom Σv → Σr !! y = None).
      { intros y Hy. assert (y ≠ c0) as Hy0 by (intros ->; done).
        assert (Σ0 !! y = None) as H0y.
        { apply not_elem_of_dom. intros Hin. rewrite map_disjoint_dom in Hdj.
          clear -Hdj Hin Hy. set_solver. }
        assert (y ≠ c1) as Hy1.
        { intros ->. pose proof (Hl1 c1) as H1. unfold Σp1 in H1.
          rewrite lookup_insert_ne, lookup_insert_eq, lookup_union, H0y in H1 by done.
          apply elem_of_dom in Hy as [x Hx]. pose proof (Hl c1) as H2.
          rewrite E1, lookup_insert_ne, lookup_union, H0y, Hx in H2 by done.
          injection H2 as <-. destruct (Σe !! c1) eqn:Ee; [|done].
          apply elem_of_dom_2 in Ee. clear -Ee HΣeΘ HΘeC Hc1C. set_solver. }
        unfold Σr. rewrite lookup_insert_ne by done.
        pose proof (Hl1 y) as H1. rewrite lookup_insert_ne in H1 by done.
        rewrite <-H1. unfold Σp1. rewrite lookup_insert_ne, lookup_union, H0y by done.
        assert (Σe !! y = None) as -> by
          (apply not_elem_of_dom; intros Hin;
           assert (y ∈ C) as HyC by (clear -Hin HΣeΘ HΘeC; set_solver);
           destruct (HΣ0C y HyC) as [_ Hv]; apply elem_of_dom in Hy as [x Hx]; congruence).
        done. }
      assert (dom Σv ## C) as HΣvC.
      { apply elem_of_disjoint. intros y Hy HyC. destruct (HΣ0C y HyC) as [_ Hv].
        apply elem_of_dom in Hy as [x Hx]. congruence. }
      assert (dom (tenv_of Σv ∪ Θe) ## C ∖ fchans w0) as Hg2.
      { rewrite dom_union_L. unfold tenv_of. rewrite dom_fmap_L, Hdom.
        clear -HΣvC. set_solver. }
      assert (Vrel n' W (tenv_of Σv ∪ Θe) (payload_at m U' k') w0) as HV2.
      { eapply Vrel_tconv; [done| |eapply Vrel_down; [|exact HV]; lia].
        eapply (teqW_trans W HWf);
          [exact (teqW_payload W HWf m U k (pt_dual k') Hkk)|rewrite payload_at_dual].
        apply teq_teqW, teq_ty_inst, HUU. }
      pose proof (send_recv_ok W Σr Σv Σe Θe C) as Sok.
      pose proof (send_recv_back W Σr Σv Σe Θe C) as Sback.
      pose proof (send_recv_env_v Σr Σv Θe Hrv) as Sv.
      pose proof (send_recv_env_e W Σr Σv Σe Θe C HΘeC HΣvC Hsplit HrC) as Se.
      pose proof (send_recv_env_o Σr Σv Θe) as So.
      repeat match goal with
        | H : ?A → _ |- _ =>
            lazymatch H with
            | Sok => specialize (H ltac:(assumption))
            | Sback => specialize (H ltac:(assumption))
            end
        end.
      pose proof (Hrecv W n' (tenv_of Σv ∪ Θe) (wext_refl W HW) (le_n n') Hg2 Sok HV2) as HP2.
      cbn [fst snd] in HP2.
      fold Σr in HP2. rewrite Sback in HP2.
      assert (C ∖ fchans w0 ∪ dom Θe = C) as HC.
      { rewrite Hdom. apply set_eq. intros y. clear. split; [set_solver|]. intros Hy. destruct (decide (y ∈ fchans w0)); set_solver. }
      rewrite HC in HP2.
      assert (c0 ∉ dom Θe ∧ c1 ∉ dom Θe) as [Hc0e Hc1e]
        by (clear -HΘeC Hc0C Hc1C; set_solver).
      assert (c1 ∉ dom Σv) as Hc1v.
      { intros Hin. specialize (Hrv c1 Hin). unfold Σr in Hrv.
        by rewrite lookup_insert_eq in Hrv. }
      assert (recv_env Σr (tenv_of Σv ∪ Θe) =
              <[c0 := (s, pt_shift 1 k)]> (<[c1 := (s', pt_shift 1 k')]> Σ)) as Henv.
      { apply map_eq. intros y.
        destruct (decide (y = c0)) as [->|Hy0].
        { rewrite lookup_insert_eq.
          rewrite So by done.
          unfold Σr. rewrite lookup_insert_ne by done.
          pose proof (Hl1 c0) as H1. rewrite lookup_insert_ne in H1 by done.
          rewrite <-H1. unfold Σp1. by rewrite lookup_insert_eq. }
        destruct (decide (y = c1)) as [->|Hy1].
        { rewrite lookup_insert_ne, lookup_insert_eq by done.
          rewrite So by done.
          unfold Σr. by rewrite lookup_insert_eq. }
        rewrite !lookup_insert_ne by done.
        assert (y ≠ c ∧ y ≠ d) as [Hyc Hyd]
          by (destruct Hcc as [[-> ->]|[-> ->]]; split; congruence).
        pose proof (Hl y) as Hly. rewrite lookup_insert_ne, fusedP_ne, lookup_union in Hly
          by done.
        destruct (decide (y ∈ dom Σv)) as [Hv|Hv].
        { rewrite Sv by done.
          assert (Σ0 !! y = None) as H0y.
          { apply not_elem_of_dom. intros Hin. rewrite map_disjoint_dom in Hdj.
            clear -Hdj Hin Hv. set_solver. }
          rewrite Hly, H0y. by destruct (Σv !! y). }
        destruct (decide (y ∈ dom Θe)) as [He|He].
        { rewrite Se by done.
          symmetry. apply not_elem_of_dom. clear -HCΣ He HΘeC. set_solver. }
        rewrite So by done.
        unfold Σr. rewrite lookup_insert_ne by done.
        pose proof (Hl1 y) as H1. rewrite lookup_insert_ne in H1 by done.
        rewrite <-H1. unfold Σp1. rewrite lookup_insert_ne, lookup_union by done.
        assert (Σe !! y = None) as -> by (apply not_elem_of_dom; clear -He HΣeΘ; set_solver).
        apply not_elem_of_dom in Hv. rewrite Hly, Hv. by destruct (Σ0 !! y). }
      rewrite Henv in HP2.
      destruct Hcont as [(-> & -> & Hss)|(-> & -> & Hss)].
      - rewrite fusedP_c in E0. rewrite (fusedP_d c d Hcd) in E1.
        injection E0 as <- <-. injection E1 as <- <-.
        apply (IH n' (le_n _) W _ _ HP2 Σ C _ s s' (pt_shift 1 kc) (pt_shift 1 kd));
          [done|done|].
        split_and!; try done. rewrite pt_dual_shift. by apply (wf_eq_shift _ HWf).
      - rewrite (fusedP_d c d Hcd) in E0. rewrite fusedP_c in E1.
        injection E0 as <- <-. injection E1 as <- <-.
        apply (IH n' (le_n _) W _ _ HP2 Σ C _ s' s (pt_shift 1 kc) (pt_shift 1 kd));
          [|done|].
        + unfold fusedP. by rewrite insert_insert_ne.
        + split_and!; try done. rewrite pt_dual_shift. by apply (wf_eq_shift _ HWf).
    Qed.

    Lemma choice_case F2 h h0 g g0 c0 c1 i :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SSel c0 i)) h0 → tstep g (LSess (SBra c1 i)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) →
      Prel n' W Σ T (C ∪ {[d]}, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros -> Hh Hg Hcc. pose proof (proj1 HW) as HWf.
      assert (c0 ≠ c1 ∧ c0 ∉ C ∧ c1 ∉ C) as (Hc01 & Hc0C & Hc1C)
        by (destruct Hcc as [[-> ->]|[-> ->]]; split_and!; done).
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SSel c0 i))
                (C ∖ sentc (SSel c0 i), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hstep _ _ Hst1) as Hp. cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost] in Hp.
      destruct Hp as (Σ1 & s1 & s2 & k & (s0 & HΣ & Hu) & Hc0Σ1 & HP1 & _).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      assert (proc_step (C, F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) (PSess (SBra c1 i))
                (C ∖ sentc (SBra c1 i), F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Hst2.
      { replace (F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) with (F2 ⊎ {[+ h0 +]} ⊎ {[+ g +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc1C. set_solver. }
      pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst2) as Hp2.
      cbn [Pcase_gen Pobl Pchoice_case at_cost pcost scost nlower pred] in Hp2.
      destruct Hp2 as (Σ2 & r1 & r2 & k' & (s1' & HΣ2 & Hu') & Hc1Σ2 & HP2).
      cbn [sentc] in HP2. rewrite difference_empty_L in HP2.
      assert (fusedP c d Σ sc sd kc kd !! c0 = Some (s0, k)) as E0
        by (rewrite HΣ; by rewrite lookup_insert_eq).
      assert (Σ1 = delete c0 (fusedP c d Σ sc sd kc kd)) as ->.
      { rewrite HΣ, delete_insert_id; [done|]. by apply not_elem_of_dom. }
      assert ((<[c0 := (sbranch i s1 s2, sel_pt k i)]> (delete c0 (fusedP c d Σ sc sd kc kd)))
                !! c1 = Some (s1', k')) as E1 by (rewrite HΣ2; by rewrite lookup_insert_eq).
      rewrite lookup_insert_ne, lookup_delete_ne in E1 by done.
      assert (Σ2 = delete c1 (<[c0 := (sbranch i s1 s2, sel_pt k i)]>
                                (delete c0 (fusedP c d Σ sc sd kc kd)))) as ->.
      { rewrite HΣ2, delete_insert_id; [done|]. by apply not_elem_of_dom. }
      destruct Hcc as [[-> ->]|[-> ->]].
      - rewrite fusedP_c in E0. rewrite (fusedP_d c d Hcd) in E1.
        injection E0 as <- <-. injection E1 as <- <-.
        destruct (sdual_plus_with _ _ _ _ _ _ Hdu Hu Hu') as [Hd1 Hd2].
        apply (IH n' (le_n _) W _ _ HP2 Σ C _ (sbranch i s1 s2) (sbranch i r1 r2)
                 (sel_pt kc i) (bra_pt kd i)); [|done|].
        + unfold fusedP. apply map_eq. intros y.
          destruct (decide (y = d)) as [->|Hyd]; [by simplify_map_eq|].
          destruct (decide (y = c)) as [->|Hyc]; by simplify_map_eq.
        + split_and!; try done; [by apply sdual_sbranch|].
          unfold sel_pt, bra_pt. apply (wf_eq_dual _ HWf).
          rewrite <-(pt_payload_dual kd). by apply (wf_eq_payload _ HWf).
      - rewrite (fusedP_d c d Hcd) in E0. rewrite fusedP_c in E1.
        injection E0 as <- <-. injection E1 as <- <-.
        destruct (sdual_with_plus _ _ _ _ _ _ Hdu Hu' Hu) as [Hd1 Hd2].
        apply (IH n' (le_n _) W _ _ HP2 Σ C _ (sbranch i r1 r2) (sbranch i s1 s2)
                 (bra_pt kc i) (sel_pt kd i)); [|done|].
        + unfold fusedP. apply map_eq. intros y.
          destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|].
          destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq.
        + split_and!; try done; [by apply sdual_sbranch|].
          unfold sel_pt, bra_pt. rewrite pt_dual_dual.
          rewrite <-(pt_payload_dual kd). by apply (wf_eq_payload _ HWf).
    Qed.

    Lemma close_steps F2 h h0 g g0 c0 c1 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c1)) g0 →
      c0 ∉ C → c1 ∉ C →
      ∃ Σ1 Σ2 k k', senv_hd Σp c0 SEnd k Σ1 ∧ c0 ∉ dom Σ1 ∧
        senv_hd Σ1 c1 SEnd k' Σ2 ∧ c1 ∉ dom Σ2 ∧
        Prel (S n') W Σ2 T (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}).
    Proof.
      intros -> Hh Hg Hc0C Hc1C.
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SClos c0))
                (C ∖ sentc (SClos c0), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hstep _ _ Hst1) as Hp. cbn [Pcase_gen] in Hp.
      destruct Hp as (Σ1 & k & Hhd & Hc0 & HP1 & _).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      assert (proc_step (C, F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) (PSess (SClos c1))
                (C ∖ sentc (SClos c1), F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Hst2.
      { replace (F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) with (F2 ⊎ {[+ h0 +]} ⊎ {[+ g +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc1C. set_solver. }
      pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst2) as Hp2. cbn [Pcase_gen] in Hp2.
      destruct Hp2 as (Σ2 & k' & Hhd2 & Hc1 & HP2).
      cbn [sentc] in HP2. rewrite difference_empty_L in HP2.
      by exists Σ1, Σ2, k, k'.
    Qed.

    Lemma close_case F2 h h0 g g0 c0 c1 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c1)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) →
      Prel (S n') W Σ T (C, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros HE Hh Hg Hcc.
      assert (c0 ∉ C ∧ c1 ∉ C) as [Hc0C Hc1C]
        by (destruct Hcc as [[-> ->]|[-> ->]]; done).
      destruct (close_steps F2 h h0 g g0 c0 c1 HE Hh Hg Hc0C Hc1C)
        as (Σ1 & Σ2 & k & k' & (s0 & HΣ & _) & Hc0 & (s1 & HΣ1 & _) & Hc1 & HP2).
      assert (Σ2 = Σ) as ->.
      { apply map_eq. intros y.
        assert (∀ y, fusedP c d Σ sc sd kc kd !! y = (<[c0 := (s0, k)]> Σ1) !! y) as Hl
          by (intros; by rewrite HΣ).
        assert (∀ y, Σ1 !! y = (<[c1 := (s1, k')]> Σ2) !! y) as Hl1
          by (intros; by rewrite HΣ1).
        apply not_elem_of_dom in Hc0, Hc1.
        destruct (decide (y = c)) as [->|Hyc]; [|destruct (decide (y = d)) as [->|Hyd]].
        - rewrite (proj1 (not_elem_of_dom _ _) HcΣ).
          destruct Hcc as [[-> ->]|[-> ->]]; [|done].
          specialize (Hl1 c). rewrite lookup_insert_ne in Hl1 by done. congruence.
        - rewrite (proj1 (not_elem_of_dom _ _) HdΣ).
          destruct Hcc as [[-> ->]|[-> ->]]; [done|].
          specialize (Hl1 d). rewrite lookup_insert_ne in Hl1 by done. congruence.
        - assert (y ≠ c0 ∧ y ≠ c1) as [Hy0 Hy1]
            by (destruct Hcc as [[-> ->]|[-> ->]]; done).
          specialize (Hl y). specialize (Hl1 y).
          rewrite fusedP_ne, lookup_insert_ne in Hl by done.
          rewrite lookup_insert_ne in Hl1 by done. congruence. }
      apply (Prel_junk _ _ _ _ _ _ c d) in HP2; [done|done|done| |done].
      intros Hin. exfalso. done.
    Qed.

    Lemma close_same F2 h h0 g g0 c0 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c0)) g0 →
      c0 ∉ C → False.
    Proof.
      intros HE Hh Hg Hc0C.
      destruct (close_steps F2 h h0 g g0 c0 c0 HE Hh Hg Hc0C Hc0C)
        as (Σ1 & Σ2 & k & k' & _ & Hc0 & Hhd2 & _ & _).
      apply senv_hd_dom in Hhd2. apply Hc0. rewrite Hhd2. clear. set_solver.
    Qed.

    Lemma link_ext x0 y0 F f f0 :
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[x0; y0]})) f0 → x0 ∉ C → y0 ∉ C →
      ∃ c1 d1 Σ1 sc1 sd1 kc1 kd1, ({[x0; y0]} : gset chan) = {[c1; d1]} ∧ c1 ≠ d1 ∧
        Σp = <[c1 := (sc1, kc1)]> (<[d1 := (sd1, kd1)]> Σ1) ∧ c1 ∉ dom Σ1 ∧ d1 ∉ dom Σ1 ∧
        sdual sd1 sc1 ∧ w_eq W kc1 (pt_dual kd1) ∧ Prel (S n') W Σ1 T (C, F ⊎ {[+ f0 +]}).
    Proof.
      intros HEq Hf Hx0 Hy0.
      assert (proc_step (C, E) (PSess (SLink {[x0; y0]}))
                (C ∖ sentc (SLink {[x0; y0]}), F ⊎ {[+ f0 +]})) as Hst.
      { rewrite HEq. apply PStepSession; [done|]. cbn [subjs]. clear -Hx0 Hy0. set_solver. }
      pose proof (Hstep _ _ Hst) as Hp. cbn [Pcase_gen] in Hp.
      destruct Hp as (c1 & d1 & Σ1 & sc1 & sd1 & kc1 & kd1 & Hcd1 & Hne & HΣ & Hc1 & Hd1 &
                      Hdu1 & Hal1 & HP1 & _).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      by exists c1, d1, Σ1, sc1, sd1, kc1, kd1.
    Qed.

    Lemma link_tau_p y0 x0 F f f0 :
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[y0; x0]})) f0 → y0 ∈ C →
      (C ∖ {[y0]}) ## dom Σ →
      fuse_goal (S n') W Σp T (C ∖ {[y0]}, echsubst y0 x0 (F ⊎ {[+ f0 +]})).
    Proof.
      intros HEq Hf Hy0 Hg.
      assert (proc_step (C, E) PTau (C ∖ {[y0]}, echsubst y0 x0 (F ⊎ {[+ f0 +]}))) as Hst
        by (rewrite HEq; by apply PStepLink).
      refine (proj2 (proj2 (Hstep _ _ Hst) _ _)).
      - exists C, F, f, y0, x0, f0. split_and!; [by rewrite HEq|done|done|done].
      - cbn [fst]. rewrite (fusedP_dom c d Hcd). clear -Hg HcC HdC. set_solver.
    Qed.

    (** An external link of one fused end with a free channel y0: renamed
        onto y0 after the fusion. *)
    Lemma link_out x0 xb y0 F f f0 :
      (x0 = c ∧ xb = d) ∨ (x0 = d ∧ xb = c) → y0 ≠ c → y0 ≠ d → y0 ∉ C →
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[x0; y0]})) f0 →
      Prel (S n') W Σ T (C, echsubst d y0 (echsubst c d (F ⊎ {[+ f0 +]}))).
    Proof.
      intros Hx Hy0c Hy0d Hy0C HEq Hf. destruct HW as [HWf _].
      assert (x0 ∉ C ∧ x0 ≠ y0) as [Hx0C Hx0y]
        by (destruct Hx as [[-> ->]|[-> ->]]; split; [done|congruence|done|congruence]).
      destruct (link_ext x0 y0 F f f0 HEq Hf Hx0C Hy0C)
        as (c1 & d1 & Σ1 & sc1 & sd1 & kc1 & kd1 & Hcd1 & Hne & HΣ & Hc1 & Hd1 &
            Hdu1 & Hal1 & HP1).
      assert (Hl : ∀ y, fusedP c d Σ sc sd kc kd !! y =
                        (<[c1 := (sc1, kc1)]> (<[d1 := (sd1, kd1)]> Σ1)) !! y)
        by (intros; by rewrite HΣ).
      apply not_elem_of_dom in Hc1, Hd1.
      (* the entry of y0 and the environment after the link *)
      set (ex := if decide (x0 = c) then (sd, kd) else (sc, kc)).
      assert (∃ ey, Σ !! y0 = Some ey ∧ entry_conv W ex ey) as (ey & Hey & Hconv).
      { destruct (upair_eq_inv _ _ _ _ Hcd1 Hx0y) as [[<- <-]|[<- <-]].
        - pose proof (Hl x0) as H0. pose proof (Hl y0) as H1.
          rewrite lookup_insert_eq in H0. rewrite lookup_insert_ne, lookup_insert_eq in H1
            by done.
          rewrite fusedP_ne in H1 by done. exists (sd1, kd1). split; [done|].
          unfold ex. destruct Hx as [[-> ->]|[-> ->]].
          + rewrite decide_True by done. rewrite fusedP_c in H0. injection H0 as <- <-.
            split; simpl.
            * apply (sdual_unique sc); [done|by apply sdual_sym].
            * apply (wf_eq_dual_l _ _ _ HWf) in Hal, Hal1.
              eapply (wf_eq_trans _ HWf); [by apply (wf_eq_sym _ HWf)|exact Hal1].
          + rewrite decide_False by done. rewrite (fusedP_d c d Hcd) in H0.
            injection H0 as <- <-. split; simpl.
            * apply (sdual_unique sd); by apply sdual_sym.
            * eapply (wf_eq_trans _ HWf); [exact Hal|by apply wf_eq_dual_l].
        - pose proof (Hl x0) as H0. pose proof (Hl y0) as H1.
          rewrite lookup_insert_eq in H1. rewrite lookup_insert_ne, lookup_insert_eq in H0
            by done.
          rewrite fusedP_ne in H1 by done. exists (sc1, kc1). split; [done|].
          unfold ex. destruct Hx as [[-> ->]|[-> ->]].
          + rewrite decide_True by done. rewrite fusedP_c in H0. injection H0 as <- <-.
            split; simpl.
            * by apply (sdual_unique sc).
            * eapply (wf_eq_trans _ HWf); [apply (wf_eq_sym _ HWf); by apply wf_eq_dual_l|].
              by apply (wf_eq_sym _ HWf).
          + rewrite decide_False by done. rewrite (fusedP_d c d Hcd) in H0.
            injection H0 as <- <-. split; simpl.
            * apply (sdual_unique sd); [by apply sdual_sym|done].
            * eapply (wf_eq_trans _ HWf); [exact Hal|by apply (wf_eq_sym _ HWf)]. }
      assert (Σ1 = <[xb := ex]> (delete y0 Σ)) as HΣ1.
      { apply map_eq. intros y.
        assert (Hcd1' : (c1 = x0 ∧ d1 = y0) ∨ (c1 = y0 ∧ d1 = x0))
          by (destruct (upair_eq_inv _ _ _ _ Hcd1 Hx0y) as [[<- <-]|[<- <-]]; [left|right]; done).
        specialize (Hl y). unfold ex in *.
        destruct (decide (y = xb)) as [->|Hyb].
        { rewrite lookup_insert_eq.
          destruct Hx as [[-> ->]|[-> ->]].
          - rewrite decide_True by done. rewrite (fusedP_d c d Hcd) in Hl.
            destruct Hcd1' as [[-> ->]|[-> ->]];
              rewrite !lookup_insert_ne in Hl by congruence; congruence.
          - rewrite decide_False by done. rewrite fusedP_c in Hl.
            destruct Hcd1' as [[-> ->]|[-> ->]];
              rewrite !lookup_insert_ne in Hl by congruence; congruence. }
        rewrite lookup_insert_ne by done.
        destruct (decide (y = x0)) as [->|Hy0'].
        { rewrite lookup_delete_ne by done.
          assert (Σ1 !! x0 = None) as -> by (destruct Hcd1' as [[-> ->]|[-> ->]]; done).
          destruct Hx as [[-> ->]|[-> ->]]; symmetry; by apply not_elem_of_dom. }
        destruct (decide (y = y0)) as [->|Hyy].
        { rewrite lookup_delete_eq. destruct Hcd1' as [[-> ->]|[-> ->]]; done. }
        rewrite lookup_delete_ne by done.
        assert (y ≠ c ∧ y ≠ d) as [Hyc Hyd]
          by (destruct Hx as [[-> ->]|[-> ->]]; split; congruence).
        rewrite fusedP_ne in Hl by done.
        destruct Hcd1' as [[-> ->]|[-> ->]]; rewrite !lookup_insert_ne in Hl by congruence;
          congruence. }
      assert (sconv W (<[y0 := ex]> (delete y0 Σ)) Σ) as Hsc.
      { intros y. destruct (decide (y = y0)) as [->|Hy].
        - by rewrite lookup_insert_eq, Hey.
        - rewrite lookup_insert_ne, lookup_delete_ne by done.
          destruct (Σ !! y); [apply entry_conv_refl, HWf|done]. }
      rewrite HΣ1 in HP1.
      assert (xb ∉ dom (delete y0 Σ) ∧ y0 ∉ dom (delete y0 Σ)) as [Hxb Hy0Σ].
      { rewrite dom_delete_L.
        destruct Hx as [[-> ->]|[-> ->]]; clear -HcΣ HdΣ; set_solver. }
      apply (Prel_junk _ _ _ _ _ _ x0 xb) in HP1;
        [| rewrite dom_insert_L; destruct Hx as [[-> ->]|[-> ->]];
           rewrite dom_delete_L; clear -HcΣ HdΣ Hcd; set_solver
         | done
         | intros Hin; exfalso; destruct Hx as [[-> ->]|[-> ->]]; done
         | destruct Hx as [[-> ->]|[-> ->]]; congruence].
      apply (Prel_junk _ _ _ _ _ _ y0 xb) in HP1;
        [| rewrite dom_insert_L, dom_delete_L; destruct Hx as [[-> ->]|[-> ->]];
           clear -Hy0c Hy0d; set_solver
         | done
         | intros Hin; exfalso; destruct Hx as [[-> ->]|[-> ->]]; done
         | destruct Hx as [[-> ->]|[-> ->]]; congruence].
      apply (Prel_swap xb y0) in HP1. unfold pswap in HP1. cbn [fst snd] in HP1.
      rewrite msswap_echsubst_flip, gswap_fresh in HP1;
        [|destruct Hx as [[-> ->]|[-> ->]]; done|done].
      rewrite senvswap_insert, cswap_l, senvswap_fix in HP1 by done.
      apply (Prel_sconv _ _ _ _ _ _ HWf Hsc) in HP1.
      destruct Hx as [[-> ->]|[-> ->]]; [exact HP1|].
      rewrite echsubst_both in HP1 by congruence. exact HP1.
    Qed.

    Lemma link_give q' :
      proc_step q PTau q' → ptau_link q q' → Plinktau_case (Prel (S n')) W Σ T q'.
    Proof.
      intros _ (C0 & F' & e' & a & b' & e'' & HeqP & Hts & HaC & ->) Hd.
      injection HeqP as <- HeqE. cbn [fst] in Hd.
      apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hcd'.
      destruct (tstep_link_shape _ _ _ Hf0) as (a0 & b0 & ->).
      rewrite gsub_upair in Hcd'.
      rewrite <-echsubst_disj_union1.
      destruct (decide (a0 = c ∨ a0 = d ∨ b0 = c ∨ b0 = d)) as [Hin|Hnin].
      - assert (∃ x0 y0, ({[a0; b0]} : gset chan) = {[x0; y0]} ∧ (x0 = c ∨ x0 = d))
          as (x0 & y0 & Hxy & Hx0).
        { destruct Hin as [Ha|[Ha|[Hb|Hb]]];
            [exists a0, b0|exists a0, b0|exists b0, a0|exists b0, a0];
            (split; [try done; by rewrite upair_comm|tauto]). }
        rewrite Hxy in Hf0.
        assert (({[a; b']} : gset chan) = {[csub c d x0; csub c d y0]}) as Hab.
        { rewrite Hcd', <-!gsub_upair, Hxy. done. }
        clear Hcd' Hxy.
        assert (csub c d x0 = d) as Hcx0
          by (destruct Hx0 as [->| ->]; [apply csub_hit|by apply csub_ne]).
        rewrite Hcx0 in Hab.
        destruct (decide (y0 = c ∨ y0 = d)) as [Hy0|Hy0].
        + (* both ends of the fused pair: a self-link on d *)
          assert (csub c d y0 = d) as Hcy0
            by (destruct Hy0 as [->| ->]; [apply csub_hit|by apply csub_ne]).
          rewrite Hcy0 in Hab.
          assert (a = d ∧ b' = d) as [-> ->].
          { assert (a ∈ ({[d; d]} : gset chan)) as Ha by (rewrite <-Hab; clear; set_solver).
            assert (b' ∈ ({[d; d]} : gset chan)) as Hb by (rewrite <-Hab; clear; set_solver).
            clear -Ha Hb. set_solver. }
          rewrite echsubst_refl.
          replace ((C ∪ {[d]}) ∖ {[d]}) with C by (clear -HdC; set_solver).
          assert (x0 ∉ C ∧ y0 ∉ C) as [Hx0C Hy0C]
            by (destruct Hx0 as [->| ->], Hy0 as [->| ->]; done).
          destruct (link_ext x0 y0 F f f0 HEq Hf0 Hx0C Hy0C)
            as (c1 & d1 & Σ1 & sc1 & sd1 & kc1 & kd1 & Hcd1 & Hne & HΣ & Hc1 & Hd1 & _ & _ & HP1).
          assert (x0 ≠ y0) as Hxy0.
          { intros <-. apply Hne.
            assert (c1 ∈ ({[x0; x0]} : gset chan)) as H1 by (rewrite Hcd1; clear; set_solver).
            assert (d1 ∈ ({[x0; x0]} : gset chan)) as H2 by (rewrite Hcd1; clear; set_solver).
            clear -H1 H2. set_solver. }
          assert (Σ1 = Σ) as ->.
          { apply map_eq. intros y.
            assert (∀ y, fusedP c d Σ sc sd kc kd !! y =
                         (<[c1 := (sc1, kc1)]> (<[d1 := (sd1, kd1)]> Σ1)) !! y) as Hl
              by (intros; by rewrite HΣ).
            apply not_elem_of_dom in Hc1, Hd1.
            assert ((c1 = c ∧ d1 = d) ∨ (c1 = d ∧ d1 = c)) as Hcd1'.
            { assert (({[c1; d1]} : gset chan) = {[c; d]}) as H.
              { rewrite <-Hcd1. destruct Hx0 as [->| ->], Hy0 as [->| ->]; try done.
                by rewrite upair_comm. }
              destruct (upair_eq_inv _ _ _ _ H Hne) as [[-> ->]|[-> ->]]; tauto. }
            destruct (decide (y = c)) as [->|Hyc].
            { apply not_elem_of_dom in HcΣ. rewrite HcΣ.
              destruct Hcd1' as [[-> ->]|[-> ->]]; done. }
            destruct (decide (y = d)) as [->|Hyd].
            { apply not_elem_of_dom in HdΣ. rewrite HdΣ.
              destruct Hcd1' as [[-> ->]|[-> ->]]; done. }
            specialize (Hl y). rewrite fusedP_ne in Hl by done.
            destruct Hcd1' as [[-> ->]|[-> ->]];
              rewrite !lookup_insert_ne in Hl by congruence; congruence. }
          apply (Prel_junk _ _ _ _ _ _ c d) in HP1; [done|done|done| |done].
          intros Hin'. exfalso. done.
        + rewrite (csub_ne c d y0) in Hab by tauto.
          assert (y0 ≠ c ∧ y0 ≠ d) as [Hy0c Hy0d] by tauto.
          destruct (decide (y0 ∈ C)) as [Hy0C|Hy0C].
          * (* an internal link of p *)
            assert ((a = d ∧ b' = y0) ∨ (a = y0 ∧ b' = d)) as Hab'.
            { destruct (decide (a = b')) as [<-|Hne].
              - exfalso.
                assert (d ∈ ({[a; a]} : gset chan)) as H1 by (rewrite Hab; clear; set_solver).
                assert (y0 ∈ ({[a; a]} : gset chan)) as H2 by (rewrite Hab; clear; set_solver).
                apply Hy0d. clear -H1 H2. set_solver.
              - destruct (upair_eq_inv _ _ _ _ Hab Hne) as [[-> ->]|[-> ->]]; tauto. }
            assert (C ∖ {[y0]} ## dom Σ) as Hg.
            { apply elem_of_disjoint. intros y Hy1 Hy2.
              apply elem_of_difference in Hy1 as [Hy1 Hy1'].
              apply (elem_of_disjoint _ _) in Hd. apply (Hd y); [|done].
              apply elem_of_difference. split; [clear -Hy1; set_solver|].
              intros Hya%elem_of_singleton. subst y.
              destruct Hab' as [[-> _]|[-> _]]; [done|]. by apply Hy1', elem_of_singleton. }
            pose proof (link_tau_p y0 x0 F f f0 HEq ltac:(by rewrite upair_comm) Hy0C Hg)
              as HΦ.
            pose proof (HΦ Σ _ _ sc sd kc kd eq_refl eq_refl) as HP.
            assert (int_ok W Σ sc sd kc kd (C ∖ {[y0]})) as Hok
              by (apply int_ok_ext; [by apply wext_refl|done|done
                                    |clear -HcC; set_solver|clear -HdC; set_solver]).
            specialize (HP Hok).
            assert (echsubst c d (echsubst y0 x0 (F ⊎ {[+ f0 +]})) =
                    echsubst y0 d (echsubst c d (F ⊎ {[+ f0 +]}))) as Hre.
            { destruct Hx0 as [->| ->].
              - by apply echsubst_retarget.
              - symmetry. apply echsubst_comm; congruence. }
            rewrite Hre in HP.
            destruct Hab' as [[-> ->]|[-> ->]].
            -- apply (Prel_swap_restricted d y0) in HP; [|done|clear -Hd Hy0C Hy0d; set_solver].
               unfold pswap in HP. cbn [fst snd] in HP.
               rewrite msswap_echsubst_flip in HP.
               assert (gswap d y0 (C ∖ {[y0]} ∪ {[d]}) = C) as Hgs.
               { clear -Hy0C HdC Hy0d. apply set_eq. intros y. rewrite elem_of_gswap'.
                 unfold cswap. repeat case_decide; subst; set_solver. }
               rewrite Hgs in HP.
               replace ((C ∪ {[d]}) ∖ {[d]}) with C by (clear -HdC; set_solver). exact HP.
            -- replace ((C ∪ {[d]}) ∖ {[y0]}) with (C ∖ {[y0]} ∪ {[d]})
                 by (clear -Hy0d; set_solver).
               exact HP.
          * (* an external link of p *)
            assert (a = d ∧ b' = y0) as [-> ->].
            { assert (a ∈ ({[d; y0]} : gset chan)) as Ha by (rewrite <-Hab; clear; set_solver).
              assert (a ≠ y0) as Hay by (intros ->; clear -HaC Hy0C Hy0d; set_solver).
              assert (a = d) as -> by (clear -Ha Hay; set_solver).
              assert (b' ∈ ({[d; y0]} : gset chan)) as Hb by (rewrite <-Hab; clear; set_solver).
              split; [done|]. destruct (decide (b' = d)) as [->|Hbd]; [|clear -Hb Hbd; set_solver].
              exfalso. assert (y0 ∈ ({[d; d]} : gset chan)) as Hy by (rewrite Hab; clear; set_solver).
              clear -Hy Hy0d. set_solver. }
            replace ((C ∪ {[d]}) ∖ {[d]}) with C by (clear -HdC; set_solver).
            destruct Hx0 as [->| ->].
            -- exact (link_out c d y0 F f f0 (or_introl (conj eq_refl eq_refl)) Hy0c Hy0d Hy0C HEq Hf0).
            -- exact (link_out d c y0 F f f0 (or_intror (conj eq_refl eq_refl)) Hy0c Hy0d Hy0C HEq Hf0).
      - (* neither end *)
        assert (a0 ≠ c ∧ a0 ≠ d ∧ b0 ≠ c ∧ b0 ≠ d) as (H1 & H2 & H3 & H4) by tauto.
        rewrite !csub_ne in Hcd' by done. rewrite <-Hcd' in Hf0.
        assert (a ∈ ({[a0; b0]} : gset chan)) as Ha by (rewrite <-Hcd'; clear; set_solver).
        assert (a ≠ c ∧ a ≠ d ∧ b' ≠ c) as (Hac & Had & Hbc).
        { assert (b' ∈ ({[a0; b0]} : gset chan)) as Hb by (rewrite <-Hcd'; clear; set_solver).
          clear -Ha Hb H1 H2 H3 H4. set_solver. }
        assert (a ∈ C) as HaC' by (clear -HaC Had; set_solver).
        assert (C ∖ {[a]} ## dom Σ) as Hg by (clear -Hd; set_solver).
        pose proof (link_tau_p a b' F f f0 HEq Hf0 HaC' Hg) as HΦ.
        pose proof (HΦ Σ _ _ sc sd kc kd eq_refl eq_refl) as HP.
        assert (int_ok W Σ sc sd kc kd (C ∖ {[a]})) as Hok
          by (apply int_ok_ext; [by apply wext_refl|done|done
                                |clear -HcC; set_solver|clear -HdC; set_solver]).
        specialize (HP Hok).
        rewrite <-(echsubst_comm a b' c d) in HP by congruence.
        replace ((C ∪ {[d]}) ∖ {[a]}) with (C ∖ {[a]} ∪ {[d]}) by (clear -Had; set_solver).
        exact HP.
    Qed.

    Lemma via_tau p1 :
      proc_step (C, E) PTau p1 → p1.1 ## dom Σp → c ∉ p1.1 → d ∉ p1.1 →
      ∃ N W1, N ## senv_roots Σ ∪ ty_roots T ∧ wext_fresh W N W1 ∧
        Prel n' W1 Σ T (p1.1 ∪ {[d]}, echsubst c d p1.2).
    Proof.
      intros Hp Hg Hc Hd.
      destruct (proj1 (Hstep PTau p1 Hp) Hg) as (N & W1 & HN & Hfr & HP1).
      exists N, W1. split_and!; [|done|].
      - pose proof (senv_roots_mono Σ Σp (fusedP_sub c d Σ sc sd kc kd HcΣ HdΣ)) as Hs.
        clear -HN Hs. set_solver.
      - destruct p1 as [C1 E1].
        apply (IH n' (le_n _) W1 _ _ HP1 Σ C1 E1 sc sd kc kd eq_refl eq_refl).
        apply int_ok_ext; [by destruct Hfr|done..].
    Qed.

    Lemma tau_costly q' :
      proc_step q PTau q' →
      (ptau_link q q' → Plinktau_case (Prel (S n')) W Σ T q') →
      Ptau_case (Prel n') W Σ T q'.
    Proof.
      intros Hq Hgive Hd. pose proof Hq as Hq0.
      apply ptau_inv in Hq as
        [ (F' & e' & e'' & HeqE & Hts & ->)
        | [ (F' & e' & c'' & e'' & HeqE & Hts & Hc''C & Hc''F & Hc''e & ->)
        | [ (F' & e' & v' & e'' & HeqE & Hts & ->)
        | [ (F' & c' & v' & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->)
        | [ (F' & c' & e' & e'' & g' & g'' & HeqE & Hts & Htr & Hc'C & ->)
        | [ (F' & e' & a & b' & e'' & HeqE & Hts & HaC & ->)
        | (F' & c' & i & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->) ]]]]]]; cbn [fst] in Hd.
      - (* β *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        apply eq_sym, lsub_beta in Hα as ->.
        destruct (via_tau (C, F ⊎ {[+ f0 +]}) ltac:(rewrite HEq; by apply PStepBeta)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                    HcC HdC) as (N & W1 & HN & Hfr & HP).
        exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
        by rewrite echsubst_disj_union1 in HP.
      - (* new: through a fresh z, then rename z to the image's name *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        destruct (exist_fresh (C ∪ dom Σ ∪ echans F ∪ fchans f ∪ {[c; d; c'']})) as [z Hz].
        destruct (tstep_chsubst_new_inv c d f c'' e'' Hts z) as (f0 & Hf0 & ->);
          [clear -Hz; set_solver..|].
        assert (z ∉ C ∧ z ∉ echans F ∧ z ∉ fchans f) as (HzC & HzF & Hzf)
          by (clear -Hz; set_solver).
        destruct (via_tau (C ∪ {[z]}, F ⊎ {[+ f0 +]}) ltac:(rewrite HEq; by apply PStepNew)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd Hz HcC HdC; set_solver)
                    ltac:(cbn [fst]; clear -Hz HcC; set_solver)
                    ltac:(cbn [fst]; clear -Hz HdC; set_solver)) as (N & W1 & HN & Hfr & HP).
        exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
        assert (c'' ∉ dom Σ) as Hc''Σ by (clear -Hd; set_solver).
        apply (Prel_swap_restricted z c'') in HP; [|clear -Hz; set_solver|done].
        unfold pswap in HP. cbn [fst snd] in HP.
        rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP.
        rewrite (msswap_fresh z c'' (echsubst c d F)) in HP; [|
          pose proof (echans_echsubst_sub c d F) as Hs; clear -Hs Hz; set_solver|done].
        rewrite eswap_chsubst_absent in HP.
        2: { intros Hin. apply fchans_chsubst in Hin.
             pose proof (tstep_fchans _ _ _ Hf0) as Hf. cbn [lchans] in Hf.
             pose proof (fchans_chsubst_sup c d f) as Hsup.
             clear -Hin Hf Hsup Hz Hc''C Hc''e. set_solver. }
        assert (gswap z c'' (C ∪ {[z]} ∪ {[d]}) = C ∪ {[d]} ∪ {[c'']}) as Hg.
        { clear Hstep IH HP Hq0 Hgive Hts Hf0 HN Hfr.
          apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
          repeat case_decide; subst; set_solver. }
        rewrite Hg in HP. exact HP.
      - (* spawn *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
        destruct (via_tau (C, F ⊎ {[+ f0 +]} ⊎ {[+ App v EUnit +]}) ltac:(rewrite HEq; by apply PStepSpawn)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                    HcC HdC) as (N & W1 & HN & Hfr & HP).
        exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
        by rewrite !echsubst_disj_union, !echsubst_singleton in HP.
      - (* message *)
        apply echsubst_decomp in HeqE as (F1 & g & HEq & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0 ->.
        apply tstep_chsubst_recv_inv_subst in Htr as (c1 & g0 & Hc1 & Hg0 & ->).
        destruct (decide (c0 = c1)) as [<-|Hc01].
        + destruct (via_tau (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}) ltac:(rewrite HEq; by eapply PStepMsg)
                      ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                      HcC HdC) as (N & W1 & HN & Hfr & HP).
          exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
          by rewrite echsubst_disj_union2 in HP.
        + exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
          rewrite <-echsubst_disj_union2.
          apply (sync_case F2 h h0 g g0 c0 c1 w0); [exact HEq|done|done| |clear -Hd; set_solver].
          apply csub_pair; [congruence|done].
      - (* close *)
        apply echsubst_decomp in HeqE as (F1 & g & HEq & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0.
        apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα & ->); [|done].
        destruct α as [|[c1 w1|c1 w1|c1|cd1|c1 i1|c1 i1]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc1.
        destruct (decide (c0 = c1)) as [<-|Hc01].
        + destruct (decide (c0 ∈ C)) as [Hc0C|Hc0C].
          * assert (c0 ≠ c ∧ c0 ≠ d) as [Hc0c Hc0d] by (split; intros ->; done).
            rewrite csub_ne in Hc0 by done. subst c'.
            destruct (via_tau (C ∖ {[c0]}, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})
                        ltac:(rewrite HEq; by eapply PStepClose)
                        ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd);
                              clear -Hd HcC HdC Hc0d; set_solver)
                        ltac:(cbn [fst]; clear -HcC; set_solver)
                        ltac:(cbn [fst]; clear -HdC; set_solver)) as (N & W1 & HN & Hfr & HP).
            exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
            rewrite echsubst_disj_union2 in HP.
            replace ((C ∪ {[d]}) ∖ {[c0]}) with (C ∖ {[c0]} ∪ {[d]})
              by (clear -Hc0d; set_solver).
            exact HP.
          * exfalso. exact (close_same F2 h h0 g g0 c0 HEq Hh0 Hg0 Hc0C).
        + assert ((c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c)) as Hcc
            by (apply csub_pair; [congruence|done]).
          assert (c' = d) as ->.
          { rewrite Hc0. destruct Hcc as [[-> _]|[-> _]]; [apply csub_hit|by apply csub_ne]. }
          exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
          apply (Prel_down (S n')); [lia|].
          rewrite <-echsubst_disj_union2.
          replace ((C ∪ {[d]}) ∖ {[d]}) with C by (clear -HdC; set_solver).
          exact (close_case F2 h h0 g g0 c0 c1 HEq Hh0 Hg0 Hcc).
      - (* link: its giving clause gives the costly one *)
        exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
        apply (Prel_down (S n')); [lia|]. apply Hgive; [|exact Hd].
        exists (C ∪ {[d]}), F', e', a, b', e''. split_and!; [by rewrite HeqE|done|done|done].
      - (* choice *)
        apply echsubst_decomp in HeqE as (F1 & g & HEq & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0 Hi0. subst i0.
        apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα & ->); [|done].
        destruct α as [|[c1 w1|c1 w1|c1|cd1|c1 i1|c1 i1]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc1 Hi1. subst i1.
        destruct (decide (c0 = c1)) as [<-|Hc01].
        + destruct (via_tau (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}) ltac:(rewrite HEq; by eapply PStepChoice)
                      ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                      HcC HdC) as (N & W1 & HN & Hfr & HP).
          exists N, W1. split_and!; [done|done|]. cbn [fst snd] in HP.
          by rewrite echsubst_disj_union2 in HP.
        + exists ∅, W. split_and!; [clear; set_solver|by apply wext_fresh_refl|].
          rewrite <-echsubst_disj_union2.
          apply (choice_case F2 h h0 g g0 c0 c1 i); [exact HEq|done|done|].
          apply csub_pair; [congruence|done].
    Qed.

    Lemma ext_case σ' q' :
      proc_step q (PSess σ') q' → Pcase_gen (Prel (S n')) n' W Σ T q (PSess σ') q'.
    Proof.
      intros Hq. destruct σ' as [a w'|a w'|a|cd|a i|a i];
        [by apply ext_recv|by apply ext_send|by apply ext_close|by apply ext_link
        |by apply ext_sel|by apply ext_bra].
    Qed.
  End step.

  Lemma Prel_internalize n : ∀ W Σ T C E sc sd kc kd,
    prim T → int_ok W Σ sc sd kc kd C →
    Prel n W (fusedP c d Σ sc sd kc kd) T (C, E) →
    Prel n W Σ T (C ∪ {[d]}, echsubst c d E).
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    intros W Σ T C E sc sd kc kd HT Hok HP.
    destruct n as [|n']; [apply Prel_0|].
    assert (IH : ∀ j, j ≤ n' → ∀ W Σp p, Prel j W Σp T p → fuse_goal j W Σp T p).
    { intros j Hj W' Σp p HPj Σ' C' E' sc' sd' kc' kd' -> -> Hok'.
      eapply IHn; [lia|done|done|done]. }
    clear IHn.
    enough (∀ W Σp T p, Prel (S n') W Σp T p → prim T →
              (∀ j, j ≤ n' → ∀ W Σp p, Prel j W Σp T p → fuse_goal j W Σp T p) →
              fuse_goal (S n') W Σp T p) as H.
    { eapply H; [exact HP|done|exact IH|done|done|done]. }
    clear W Σ T C E sc sd kc kd HT Hok HP IH.
    intros W Σp T p HP.
    induction HP as [W Σp T p Hirr Hrdy Hstep] using Prel_S_ind.
    intros HT IH Σ C E sc sd kc kd -> -> Hok.
    pose proof Hok as (HW & HcΣ & HdΣ & HcC & HdC & Hdu & Hal).
    assert (Hstep' : ∀ π p', proc_step (C, E) π p' →
              Pcase_gen (λ W Σp T p, Prel (S n') W Σp T p ∧ fuse_goal (S n') W Σp T p)
                n' W (fusedP c d Σ sc sd kc kd) T (C, E) π p').
    { intros π p' Hp. eapply Pcase_gen_mono_at; [|exact (Hstep π p' Hp)].
      intros W' Σ' p'' [HP' HΦ]. split; [done|]. by apply HΦ. }
    clear Hstep.
    assert (Hnp : ¬ pirred (C, E)).
    { intros Hp. destruct (Hirr Hp) as (v & E1 & _ & _ & HV & _).
      apply Vrel_prim_empty in HV; [|done]. apply (f_equal (λ m, m !! c)) in HV.
      unfold tenv_of in HV. rewrite lookup_fmap, fusedP_c, lookup_empty in HV. discriminate. }
    assert (Hnt : ¬ terminated (C, E)) by (intros Ht; by apply Hnp, terminated_pirred).
    pose proof (Hrdy Hnp) as Hrdy'.
    apply Prel_S_iff. split_and!.
    - intros Hq. exfalso.
      assert (stable_p (C ∪ {[d]}, echsubst c d E)) as Hs by (intros q' Hq'; exact (Hq _ _ Hq')).
      destruct (fused_ready c d Hcd W HW Σ sc sd kc kd C E HcΣ HdΣ HcC HdC Hdu Hal Hrdy' Hnt Hs)
        as [(cd & q' & Hq')|[Hno _]]; [exact (Hq _ _ Hq')|].
      apply Hno. intros k (σ & q' & Hq' & _). exact (Hq _ _ Hq').
    - intros _ Hs.
      destruct (fused_ready c d Hcd W HW Σ sc sd kc kd C E HcΣ HdΣ HcC HdC Hdu Hal Hrdy' Hnt Hs)
        as [?|[Hno Hab]]; [by left|right].
      split; [intros H; exfalso; by apply Hno|done].
    - intros π q' Hst. destruct π as [|σ'].
      + simpl. split.
        * eapply tau_costly; try done. intros Hl. eapply link_give; done.
        * intros Hl. eapply link_give; done.
      + eapply ext_case; done.
  Qed.
End internalize.
