(** * Dual session types along a step (stage S8)

    The soup pairs the two ends of an internal channel at dual session
    types up to annotations in the environment of the relation ([sdual])
    and at protocols P, P′ with dual P ⊑ P′ in the protocol map of the
    fuel layer. When the two ends act, their continuations are related
    again, and the receiver reads the payload at a credit no higher than
    the sender's. A link joins the partners of its two ends, which are
    related again. *)

From GV Require Export soup.OwnFacts compat.Blind static.PointSubst.

(** ** Up to annotations *)

Lemma seqv_dual s r : seqv s r → seqv (dual s) (dual r).
Proof. unfold seqv. rewrite !sty_df_dual. apply sequiv_dual. Qed.

Lemma sdual_snd_both S0 S0' m U S m' U' S' :
  sdual S0 S0' → unfoldS S0 = SSeq (SSnd m U) S → unfoldS S0' = SSeq (SRcv m' U') S' →
  m' = m ∧ teq (ty_df U') (ty_df U) ∧ sdual S S'.
Proof.
  intros Hd Hu Hu'. destruct (sdual_snd _ _ _ _ _ Hd Hu) as (U'' & S'' & Hu'' & HU & HS).
  rewrite Hu' in Hu''. simplify_eq. done.
Qed.

Lemma sdual_plus_both S0 S0' S1 S2 S1' S2' :
  sdual S0 S0' → unfoldS S0 = SPlus S1 S2 → unfoldS S0' = SWith S1' S2' →
  sdual S1 S1' ∧ sdual S2 S2'.
Proof.
  intros Hd Hu Hu'. destruct (sdual_plus _ _ _ _ Hd Hu) as (R1 & R2 & Hu'' & H1 & H2).
  rewrite Hu' in Hu''. simplify_eq. done.
Qed.

(** A link: the partners R1 of S1 and R2 of S2 are dual when S1 and S2 are. *)
Lemma sdual_link S1 S2 R1 R2 : sdual S1 S2 → sdual S1 R1 → sdual S2 R2 → sdual R1 R2.
Proof.
  unfold sdual. intros H12 H1 H2.
  apply seqv_dual in H12, H1. rewrite dual_involutive in H12, H1.
  eapply seqv_trans; [exact H2|]. eapply seqv_trans; [exact H12|]. by apply seqv_sym.
Qed.

Lemma payload_teq m U U' x :
  teq (ty_df U') (ty_df U) → teq (ty_df (payload_at m U x)) (ty_df (payload_at m U' x)).
Proof.
  intros H. rewrite <-!payload_at_df. unfold payload_at, ty_inst. apply teq_pinst. by apply teq_sym.
Qed.

(** ** Up to ≈, with annotations *)

Lemma sequiv_unfold_rcv s S0 m U S :
  sequiv s S0 → unfoldS S0 = SSeq (SRcv m U) S →
  ∃ U' S', unfoldS s = SSeq (SRcv m U') S' ∧ teq U' U ∧ sequiv S' S.
Proof.
  intros Hq Hu. apply sequiv_step in Hq. unfold eq_step in Hq. rewrite (hd_of _ _ Hu) in Hq.
  simpl in Hq. destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_with s S0 S1 S2 :
  sequiv s S0 → unfoldS S0 = SWith S1 S2 →
  ∃ S1' S2', unfoldS s = SWith S1' S2' ∧ sequiv S1' S1 ∧ sequiv S2' S2.
Proof.
  intros Hq Hu. apply sequiv_step in Hq. unfold eq_step in Hq. rewrite (hd_of _ _ Hu) in Hq.
  simpl in Hq. destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma ssub_unfold_rcv s S0 m U S :
  ssub S0 s → unfoldS S0 = SSeq (SRcv m U) S →
  ∃ U' S', unfoldS s = SSeq (SRcv m U') S' ∧ crT U U' ∧ ssub S S'.
Proof.
  intros Hq Hu. apply ssub_hd in Hq. unfold sub_step in Hq. rewrite (hd_of _ _ Hu) in Hq.
  simpl in Hq. destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma ssub_unfold_with s S0 S1 S2 :
  ssub S0 s → unfoldS S0 = SWith S1 S2 →
  ∃ S1' S2', unfoldS s = SWith S1' S2' ∧ ssub S1 S1' ∧ ssub S2 S2'.
Proof.
  intros Hq Hu. apply ssub_hd in Hq. unfold sub_step in Hq. rewrite (hd_of _ _ Hu) in Hq.
  simpl in Hq. destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

(** The two ends of a channel hold protocols P and P′ with dual P ⊑ P′.
    What one end sends, the other receives at a credit no higher. *)
Lemma pdual_snd P0 P0' m T P m' T' P' :
  ssub (dual P0) P0' → unfoldS P0 = SSeq (SSnd m T) P → unfoldS P0' = SSeq (SRcv m' T') P' →
  m' = m ∧ crT T T' ∧ ssub (dual P) P'.
Proof.
  intros Hd Hu Hu'.
  assert (unfoldS (dual P0) = SSeq (SRcv m T) (dual P)) as Hdu by (by rewrite <-dual_unfoldS, Hu).
  destruct (ssub_unfold_rcv _ _ _ _ _ Hd Hdu) as (T'' & P'' & Hu'' & HT & HP).
  rewrite Hu' in Hu''. simplify_eq. done.
Qed.

Lemma pdual_plus P0 P0' P1 P2 P1' P2' :
  ssub (dual P0) P0' → unfoldS P0 = SPlus P1 P2 → unfoldS P0' = SWith P1' P2' →
  ssub (dual P1) P1' ∧ ssub (dual P2) P2'.
Proof.
  intros Hd Hu Hu'.
  assert (unfoldS (dual P0) = SWith (dual P1) (dual P2)) as Hdu by (by rewrite <-dual_unfoldS, Hu).
  destruct (ssub_unfold_with _ _ _ _ Hd Hdu) as (R1 & R2 & Hu'' & H1 & H2).
  rewrite Hu' in Hu''. simplify_eq. done.
Qed.

Lemma pdual_sym P P' : ssub (dual P) P' → ssub (dual P') P.
Proof. intros H. apply ssub_dual in H. by rewrite dual_involutive in H. Qed.

(** The two ends of a link, P ⊑ dual P′. *)
Lemma plink_sym P P' : ssub P (dual P') → ssub P' (dual P).
Proof. intros H. apply ssub_dual in H. by rewrite dual_involutive in H. Qed.

Lemma pdual_link P1 P2 R1 R2 :
  ssub P1 (dual P2) → ssub (dual P1) R1 → ssub (dual P2) R2 → ssub (dual R1) R2.
Proof.
  intros H12 H1 H2. apply pdual_sym in H1.
  eapply ssub_trans; [exact H1|]. by eapply ssub_trans.
Qed.
