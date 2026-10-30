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
