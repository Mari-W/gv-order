(** * P-Connect and P-Join (stage S4)

    Two components in P over a cut compose. p1 holds the interface Σ1 and
    the cut ends ΣC, p2 the interface Σ2 and the partners ΣD of the cut
    ends, dual up to ≈ at dual points ([cut_dual]). The composite
    restricts the cut channels:

      p1 ∈ P[κ]^W _ n⟦Σ1 ∪ ΣC ⊢ T⟧ ∧ p2 ∈ P[κ]^W _ n⟦Σ2 ∪ ΣD ⊢ 1⟧ ∧ conn …
        ⟹ (p1.1 ∪ p2.1 ∪ chans_of ΣC, p1.2 ⊎ p2.2) ∈ P[κ]^W _ n⟦Σ1 ∪ Σ2 ⊢ T⟧

    The side conditions [conn] read environments and channel sets only.
    A message across the cut is Q-Send of one side and Q-Recv of the
    other. A link of a cut end renames or fuses the other side by the
    clause (fuse). Readiness of the composite is a chain of cut ends
    whose points descend in a strict world, so it stops at an offer of
    the interface. *)

From GV Require Export compat.Conv.
From GV Require Import fuel.FuelMono.

(** ** Environments of a cut *)

(** No end of Σ has its partner in Σ. *)
Definition pfree (Σ : senv) : Prop := ∀ o, o ∈ dom Σ → edual o ∉ dom Σ.

(** ΣD holds the partners of the ends of ΣC, dual up to ≈ at dual
    points. *)
Definition cut_dual (ΣC ΣD : senv) : Prop :=
  (∀ o, o ∈ dom ΣD ↔ edual o ∈ dom ΣC) ∧
  (∀ o S x, ΣC !! o = Some (S, x) → ∃ S', ΣD !! edual o = Some (S', x‾) ∧ sdual S S').

(** The side conditions of P-Connect, symmetric in the two sides. *)
Inductive conn (Σ1 ΣC : senv) (C1 : gset chan) (Σ2 ΣD : senv) (C2 : gset chan) : Prop :=
  | Conn (cn_d1 : Σ1 ##ₘ ΣC) (cn_d2 : Σ2 ##ₘ ΣD) (cn_cut : cut_dual ΣC ΣD)
      (cn_f1 : pfree Σ1) (cn_f2 : pfree Σ2) (cn_fC : pfree ΣC)
      (cn_12 : chans_of Σ1 ## chans_of Σ2) (cn_1C : chans_of Σ1 ## chans_of ΣC)
      (cn_2C : chans_of Σ2 ## chans_of ΣC) (cn_CC : C1 ## C2)
      (cn_C1 : C1 ## chans_of Σ1 ∪ chans_of Σ2 ∪ chans_of ΣC)
      (cn_C2 : C2 ## chans_of Σ1 ∪ chans_of Σ2 ∪ chans_of ΣC).

(** The composite. *)
Definition pconn (p1 p2 : proc) (K : gset chan) : proc := (p1.1 ∪ p2.1 ∪ K, p1.2 ⊎ p2.2).

(** ** Duality of session types up to ≈ *)

Lemma sdual_sym S S' : sdual S S' → sdual S' S.
Proof.
  unfold sdual, seqv. rewrite !sty_df_dual. intros H.
  apply sequiv_dual in H. rewrite dual_involutive in H. by apply sequiv_sym.
Qed.

Lemma sdual_trans_l S1 S2 S3 : sdual S1 S2 → sdual S1 S3 → seqv S2 S3.
Proof. unfold sdual. intros H1 H2. eapply seqv_trans; [exact H1|by apply seqv_sym]. Qed.

Lemma sdual_dual_dual S1 S2 S3 S4 : sdual S1 S2 → sdual S3 S4 → sdual S1 S3 → sdual S2 S4.
Proof.
  intros H12 H34 H13. unfold sdual, seqv in *. rewrite !sty_df_dual in *.
  eapply sequiv_trans; [exact H34|]. apply sequiv_dual in H13. rewrite dual_involutive in H13.
  eapply sequiv_trans; [exact H13|]. apply sequiv_dual in H12. rewrite dual_involutive in H12.
  by apply sequiv_sym.
Qed.

Lemma unfold_dual_snd S0 m U b S :
  unfoldS S0 = SSeq (SSnd m U b) S → unfoldS (dual S0) = SSeq (SRcv m U b) (dual S).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_rcv S0 m U b S :
  unfoldS S0 = SSeq (SRcv m U b) S → unfoldS (dual S0) = SSeq (SSnd m U b) (dual S).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_end S0 : unfoldS S0 = SEnd → unfoldS (dual S0) = SEnd.
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_plus S0 S1 S2 : unfoldS S0 = SPlus S1 S2 → unfoldS (dual S0) = SWith (dual S1) (dual S2).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_with S0 S1 S2 : unfoldS S0 = SWith S1 S2 → unfoldS (dual S0) = SPlus (dual S1) (dual S2).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.

(** The partner of a send receives the same payload type up to ≈. *)
Lemma sdual_snd S0 S0' m U b S :
  sdual S0 S0' → unfoldS S0 = SSeq (SSnd m U b) S →
  ∃ U' b' S', unfoldS S0' = SSeq (SRcv m U' b') S' ∧ teq (ty_df U') (ty_df U) ∧ sdual S S'.
Proof.
  intros H Hu. destruct (seqv_unfold_rcv S0' (dual S0) m U b (dual S) H (unfold_dual_snd _ _ _ _ _ Hu))
    as (U' & b' & S' & H1 & H2 & H3). eauto 10.
Qed.

Lemma sdual_rcv S0 S0' m U b S :
  sdual S0 S0' → unfoldS S0 = SSeq (SRcv m U b) S →
  ∃ U' b' S', unfoldS S0' = SSeq (SSnd m U' b') S' ∧ teq (ty_df U') (ty_df U) ∧ sdual S S'.
Proof.
  intros H Hu. destruct (seqv_unfold_snd S0' (dual S0) m U b (dual S) H (unfold_dual_rcv _ _ _ _ _ Hu))
    as (U' & b' & S' & H1 & H2 & H3). eauto 10.
Qed.

Lemma sdual_end S0 S0' : sdual S0 S0' → unfoldS S0 = SEnd → unfoldS S0' = SEnd.
Proof. intros H Hu. by eapply seqv_unfold_end; [exact H|apply unfold_dual_end]. Qed.

Lemma sdual_plus S0 S0' S1 S2 :
  sdual S0 S0' → unfoldS S0 = SPlus S1 S2 →
  ∃ S1' S2', unfoldS S0' = SWith S1' S2' ∧ sdual S1 S1' ∧ sdual S2 S2'.
Proof.
  intros H Hu. destruct (seqv_unfold_with S0' (dual S0) (dual S1) (dual S2) H (unfold_dual_plus _ _ _ Hu))
    as (S1' & S2' & H1 & H2 & H3). eauto 10.
Qed.

Lemma sdual_with S0 S0' S1 S2 :
  sdual S0 S0' → unfoldS S0 = SWith S1 S2 →
  ∃ S1' S2', unfoldS S0' = SPlus S1' S2' ∧ sdual S1 S1' ∧ sdual S2 S2'.
Proof.
  intros H Hu. destruct (seqv_unfold_plus S0' (dual S0) (dual S1) (dual S2) H (unfold_dual_with _ _ _ Hu))
    as (S1' & S2' & H1 & H2 & H3). eauto 10.
Qed.

Lemma sdual_bsel i S1 S2 S1' S2' : sdual S1 S1' → sdual S2 S2' → sdual (bsel i S1 S2) (bsel i S1' S2').
Proof. by destruct i. Qed.

Lemma sel_bra_pt x i : (sel_pt x i)‾ = bra_pt x‾ i.
Proof. unfold sel_pt, bra_pt. by rewrite pt_dual_dual, pt_field_dual. Qed.

Lemma bra_sel_pt x i : (bra_pt x i)‾ = sel_pt x‾ i.
Proof. unfold sel_pt, bra_pt. by rewrite pt_field_dual. Qed.

(** ** Cuts *)

Lemma cut_dual_sym ΣC ΣD : pfree ΣC → cut_dual ΣC ΣD → cut_dual ΣD ΣC.
Proof.
  intros _ [Hd Ht]. split.
  - intros o. rewrite Hd, edual_edual. done.
  - intros o S x Ho. assert (edual o ∈ dom ΣC) as Hin by (apply Hd; by eapply elem_of_dom_2).
    apply elem_of_dom in Hin as [[S0 x0] H0]. destruct (Ht _ _ _ H0) as (S' & H1 & H2).
    rewrite edual_edual, Ho in H1. injection H1 as <- ->. exists S0. rewrite pt_dual_dual.
    split; [done|by apply sdual_sym].
Qed.

Lemma cut_dual_chans ΣC ΣD : cut_dual ΣC ΣD → chans_of ΣD = chans_of ΣC.
Proof.
  intros [Hd _]. unfold chans_of. apply set_eq. intros c. rewrite !elem_of_map. split.
  - intros (o & -> & Ho). exists (edual o). rewrite ech_edual. split; [done|by apply Hd].
  - intros (o & -> & Ho). exists (edual o). rewrite ech_edual. split; [done|]. apply Hd. by rewrite edual_edual.
Qed.

Lemma cut_dual_pfree ΣC ΣD : cut_dual ΣC ΣD → pfree ΣC → pfree ΣD.
Proof.
  intros [Hd _] Hf o Ho Ho'. apply Hd in Ho, Ho'. rewrite edual_edual in Ho'. by apply (Hf _ Ho').
Qed.

Lemma elem_of_chans_of o (Σ : senv) : o ∈ dom Σ → ech o ∈ chans_of Σ.
Proof. intros H. unfold chans_of. apply elem_of_map. by exists o. Qed.

Lemma chans_of_union (Σ1 Σ2 : senv) : chans_of (Σ1 ∪ Σ2) = chans_of Σ1 ∪ chans_of Σ2.
Proof. unfold chans_of. by rewrite dom_union_L, set_map_union_L. Qed.

Lemma conn_sym Σ1 ΣC C1 Σ2 ΣD C2 : conn Σ1 ΣC C1 Σ2 ΣD C2 → conn Σ2 ΣD C2 Σ1 ΣC C1.
Proof.
  intros [? ? Hcut ? ? ? ? ? ? ? ? ?]. pose proof (cut_dual_chans _ _ Hcut) as Hch.
  constructor; first [done|by apply cut_dual_sym|by eapply cut_dual_pfree|by symmetry
    |rewrite Hch; set_solver|set_solver].
Qed.

Lemma pconn_sym p1 p2 K : pconn p1 p2 K = pconn p2 p1 K.
Proof. unfold pconn. f_equal; [set_solver|]. apply (comm_L (⊎)). Qed.

(** ** Soups of two components *)

Lemma soup_union M1 M2 : M1 ##ₘ M2 → soup (M1 ∪ M2) = soup M1 ⊎ soup M2.
Proof.
  induction M1 as [|i e M1 Hi IH] using map_ind; intros Hd.
  - by rewrite (left_id_L ∅ (∪)), soup_empty, (left_id_L ∅ (⊎)).
  - apply map_disjoint_insert_l in Hd as [Hi2 Hd]. rewrite <-insert_union_l.
    rewrite !soup_insert; [|done|by rewrite lookup_union, Hi, Hi2]. rewrite IH by done. multiset_solver.
Qed.

Lemma soup_split M E1 E2 : soup M = E1 ⊎ E2 →
  ∃ M1 M2, M = M1 ∪ M2 ∧ M1 ##ₘ M2 ∧ soup M1 = E1 ∧ soup M2 = E2.
Proof.
  revert M. induction E1 as [|e E1 IH] using gmultiset_ind; intros M HM.
  - exists ∅, M. rewrite (left_id_L ∅ (⊎)) in HM. split_and!; [by rewrite (left_id_L ∅ (∪))|
      apply map_disjoint_empty_l|apply soup_empty|done].
  - assert (soup M = (E1 ⊎ E2) ⊎ {[+ e +]}) as HM' by (rewrite HM; multiset_solver).
    destruct (soup_extract M _ e HM') as (i & Hi & Hdel).
    destruct (IH (delete i M) Hdel) as (M1 & M2 & HMd & Hd & H1 & H2).
    exists (<[i := e]> M1), M2.
    assert (M1 !! i = None ∧ M2 !! i = None) as [Hi1 Hi2].
    { assert (delete i M !! i = None) as Hn by apply lookup_delete_eq. rewrite HMd, lookup_union in Hn.
      destruct (M1 !! i), (M2 !! i); simpl in Hn; try discriminate; done. }
    split_and!.
    + rewrite <-insert_union_l, <-HMd, insert_delete_id; done.
    + by apply map_disjoint_insert_l.
    + rewrite soup_insert by done. rewrite H1. multiset_solver.
    + done.
Qed.

(** ** Chains in a strict world stop

    Over a finite list of points, ≺ restricted to the list is well
    founded in a strict world. No decision of ≺ is needed. *)

Lemma finite_lt_acc (W : world) (X : list point) :
  strict W → ∀ y, Acc (λ a b, a ∈ X ∧ W ⊢ a ≺ b) y.
Proof.
  intros [_ Hirr]. induction X as [|x X IH]; intros y.
  - constructor. intros a [Ha _]. by apply not_elem_of_nil in Ha.
  - assert (∀ b, ¬ W ⊢ x ≺ b → Acc (λ a b, a ∈ x :: X ∧ W ⊢ a ≺ b) b) as Hnot.
    { intros b. induction (IH b) as [b _ IHb]. intros Hb. constructor. intros a [Ha Hab].
      apply elem_of_cons in Ha as [->|Ha]; [done|]. apply IHb; [by split|].
      intros Hxa. apply Hb. by eapply w_lt_trans. }
    assert (Acc (λ a b, a ∈ x :: X ∧ W ⊢ a ≺ b) x) as Hx by (apply Hnot, Hirr).
    induction (IH y) as [y _ IHy]. constructor. intros a [Ha Hay].
    apply elem_of_cons in Ha as [->|Ha]; [done|]. by apply IHy.
Qed.
