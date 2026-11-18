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

(** ** Steps of one component inside the composite *)

Lemma new_retarget e ℓ c e' c' : tstep e (LNew ℓ c) e' → ∃ e'', tstep e (LNew ℓ c') e''.
Proof.
  intros H. destruct (act_step _ _ _ H) as (a & Ha & Ho). apply offers_new in Ho as ->.
  by apply (act_offer _ _ _ Ha).
Qed.

Lemma new_at_retarget e κf o c e' c' : tstep e (LNewAt κf o c) e' → ∃ e'', tstep e (LNewAt κf o c') e''.
Proof.
  intros H. destruct (act_step _ _ _ H) as (a & Ha & Ho). apply offers_new_at in Ho as ->.
  apply (act_offer _ _ _ Ha). by split.
Qed.

(** Every lifting of a composite splits into liftings of the two
    components. *)
Lemma pconn_lift q p1 p2 K : erase q = pconn p1 p2 K →
  ∃ M1 M2, q = (p1.1 ∪ p2.1 ∪ K, M1 ∪ M2) ∧ M1 ##ₘ M2 ∧ soup M1 = p1.2 ∧ soup M2 = p2.2.
Proof.
  destruct q as [C M]. unfold erase, pconn. simpl. intros [= <- HM].
  destruct (soup_split M _ _ HM) as (M1 & M2 & -> & Hd & H1 & H2). exists M1, M2. done.
Qed.

Lemma pconn_erase C1 C2 K M1 M2 : M1 ##ₘ M2 →
  erase (C1 ∪ C2 ∪ K, M1 ∪ M2) = pconn (erase (C1, M1)) (erase (C2, M2)) K.
Proof. intros Hd. unfold erase, pconn. simpl. by rewrite soup_union. Qed.

(** A τ step of a component is a τ step of the composite, up to the
    choice of fresh names. *)
Lemma tau_lift C1 C2 K M1 M2 ev q1' :
  M1 ##ₘ M2 → istep (C1, M1) ev q1' → ev_tau ev →
  ∃ ev' q', istep (C1 ∪ C2 ∪ K, M1 ∪ M2) ev' q' ∧ ev_tau ev'.
Proof.
  intros Hd Hst Hτ. set (C := C1 ∪ C2 ∪ K).
  assert (∀ i e, M1 !! i = Some e → (M1 ∪ M2) !! i = Some e) as Hl by (intros; by apply lookup_union_Some_l).
  inversion Hst; subst; try (exfalso; by unfold ev_tau in Hτ).
  - eexists _, _. split; [eapply p_act_beta; eauto|done].
  - destruct (exist_fresh (C ∪ echans (soup (M1 ∪ M2)))) as [c' Hc'].
    match goal with H : tstep _ (LNew _ _) _ |- _ => destruct (new_retarget _ _ _ _ c' H) as [e'' He''] end.
    eexists _, _. split; [eapply p_act_new; [eauto|eauto|set_solver|set_solver]|done].
  - destruct (exist_fresh (C ∪ echans (soup (M1 ∪ M2)))) as [c' Hc'].
    match goal with H : tstep _ (LNewAt _ _ _) _ |- _ => destruct (new_at_retarget _ _ _ _ _ c' H) as [e'' He''] end.
    eexists _, _. split; [eapply p_act_new_at; [eauto|eauto|set_solver|set_solver]|done].
  - destruct (exist_fresh (dom (M1 ∪ M2))) as [j' Hj'].
    eexists _, _. split; [eapply p_act_spawn; [eauto|eauto|by apply not_elem_of_dom]|done].
  - eexists _, _. split; [eapply p_act_msg; eauto|done].
  - eexists _, _. split; [eapply p_act_close; [eauto|eauto|eauto|eauto|eauto|set_solver]|done].
  - eexists _, _. split; [eapply p_act_choice; eauto|done].
  - eexists _, _. split; [eapply p_act_link; [eauto|eauto|set_solver]|done].
Qed.

Lemma stable_pconn_l p1 p2 K : stable_p (pconn p1 p2 K) → stable_p p1.
Proof.
  intros Hs p1' (q1 & ev & q1' & Hq1 & Hst & Hq1' & Hτ).
  destruct (erase_surj (pconn p1 p2 K)) as [q Hq]. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & H1 & H2).
  destruct (pstep_lift (p1.1, M1) (ev_plabel ev) p1') as (ev1 & q1'' & Hst1 & Hl1 & _).
  { unfold erase at 1. simpl. rewrite H1. destruct p1 as [c g]. by exists q1, ev, q1'. }
  rewrite Hτ in Hl1. destruct (tau_lift p1.1 p2.1 K M1 M2 ev1 q1'' Hd Hst1 Hl1) as (ev' & q' & Hst' & Hτ').
  apply (Hs (erase q')). rewrite <-Hq. exists (p1.1 ∪ p2.1 ∪ K, M1 ∪ M2), ev', q'. done.
Qed.

Lemma stable_pconn_r p1 p2 K : stable_p (pconn p1 p2 K) → stable_p p2.
Proof. rewrite pconn_sym. apply stable_pconn_l. Qed.

(** ** External steps of a component *)

(** The end a session label that is no link acts on. *)
Definition ssubj (σ : slabel) : option cend :=
  match σ with
  | SSend o _ _ | SRecv o _ | SClose o | SSel o _ | SBra o _ => Some o
  | SLink _ => None
  end.

(** The head of the session type a label asks. *)
Definition hd_ok (σ : slabel) (u : sty) : Prop :=
  match σ with
  | SSend _ _ _ => ∃ m U b S, u = SSeq (SSnd m U b) S
  | SRecv _ _ => ∃ m U b S, u = SSeq (SRcv m U b) S
  | SClose _ => u = SEnd
  | SSel _ _ => ∃ S1 S2, u = SPlus S1 S2
  | SBra _ _ => ∃ S1 S2, u = SWith S1 S2
  | SLink _ => True
  end.

Section psteps.
  Context (κ : ctable) (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) (X : prel)
    (W : world) (Σ : senv) (T : ty) (p : proc).
  Context (HP : Psteps κ n Vl Pl VN X W Σ T p).

  Lemma Psteps_sends q i σ q' : erase q = p → istep q (EvSess i σ) q' → sends σ ⊆ dom Σ.
  Proof.
    intros Hq Hst. destruct HP as (_ & H2 & H3 & H4 & H5 & H6 & H7).
    destruct σ as [o M w|o w|o|o b|o b|os]; simpl.
    - destruct (H2 _ _ _ _ _ _ Hq Hst) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & A & _).
      apply elem_of_dom_2 in A. set_solver.
    - destruct (H3 _ _ _ _ _ Hq Hst) as (? & ? & ? & ? & ? & ? & A & _). apply elem_of_dom_2 in A. set_solver.
    - destruct (H4 _ _ _ _ Hq Hst) as (? & ? & A & _). apply elem_of_dom_2 in A. set_solver.
    - destruct (H5 _ _ _ _ _ Hq Hst) as (? & ? & ? & ? & A & _). apply elem_of_dom_2 in A. set_solver.
    - destruct (H6 _ _ _ _ _ Hq Hst) as (? & ? & ? & ? & A & _). apply elem_of_dom_2 in A. set_solver.
    - destruct (H7 _ _ _ _ Hq Hst) as (o1 & o2 & ? & ? & ? & -> & _ & A1 & A2 & _).
      apply elem_of_dom_2 in A1, A2. set_solver.
  Qed.

  Lemma Psteps_head q i σ q' o : erase q = p → istep q (EvSess i σ) q' → ssubj σ = Some o →
    ∃ S0 x, Σ !! o = Some (S0, x) ∧ hd_ok σ (unfoldS S0).
  Proof.
    intros Hq Hst Ho. destruct HP as (_ & H2 & H3 & H4 & H5 & H6 & H7).
    destruct σ as [o' M w|o' w|o'|o' b|o' b|os]; simpl in Ho; injection Ho as <- || discriminate.
    - destruct (H2 _ _ _ _ _ _ Hq Hst) as (S0 & x & m & U & b & S & ? & ? & ? & ? & A & B & _). exists S0, x. split; [done|simpl; eauto 10].
    - destruct (H3 _ _ _ _ _ Hq Hst) as (S0 & x & m & U & b & S & A & B & _). exists S0, x. split; [done|simpl; eauto 10].
    - destruct (H4 _ _ _ _ Hq Hst) as (S0 & x & A & B & _). exists S0, x. split; [done|simpl; eauto 10].
    - destruct (H5 _ _ _ _ _ Hq Hst) as (S0 & x & S1 & S2 & A & B & _). exists S0, x. split; [done|simpl; eauto 10].
    - destruct (H6 _ _ _ _ _ Hq Hst) as (S0 & x & S1 & S2 & A & B & _). exists S0, x. split; [done|simpl; eauto 10].
  Qed.
End psteps.

(** Two labels on the two ends of a channel, at dual types. *)
Definition sync (σ1 σ2 : slabel) : Prop :=
  match σ1, σ2 with
  | SSend _ _ _, SRecv _ _ | SRecv _ _, SSend _ _ _ | SClose _, SClose _
  | SSel _ _, SBra _ _ | SBra _ _, SSel _ _ => True
  | _, _ => False
  end.

Lemma hd_ok_sync σ1 σ2 S0 S0' :
  sdual S0 S0' → hd_ok σ1 (unfoldS S0) → hd_ok σ2 (unfoldS S0') →
  ssubj σ1 ≠ None → ssubj σ2 ≠ None → sync σ1 σ2.
Proof.
  intros Hd H1 H2 N1 N2.
  destruct σ1 as [| | | | |], σ2 as [| | | | |]; simpl in *; try done; try congruence;
    repeat match goal with H : ∃ _, _ |- _ => destruct H as [? H] end;
    first
    [ destruct (sdual_snd _ _ _ _ _ _ Hd H1) as (? & ? & ? & E & _)
    | destruct (sdual_rcv _ _ _ _ _ _ Hd H1) as (? & ? & ? & E & _)
    | pose proof (sdual_end _ _ Hd H1) as E
    | destruct (sdual_plus _ _ _ _ Hd H1) as (? & ? & E & _)
    | destruct (sdual_with _ _ _ _ Hd H1) as (? & ? & E & _) ];
    congruence.
Qed.

Lemma Vrel_prim_empty κ n W Θ T v : prim T → Vrel κ n W Θ T v → Θ = ∅.
Proof.
  intros Hp. revert Θ v. induction Hp as [|U a V b HU IHU HV IHV|U a V b HU IHU HV IHV|m k C ub c t U a HU IHU];
    intros Θ v.
  - by intros [-> _]%Vrel_unit_iff.
  - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & -> & H1 & H2)%Vrel_prod_iff.
    rewrite (IHU _ _ H1), (IHV _ _ H2). by rewrite (left_id_L ∅ (∪)).
  - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; eauto.
  - by intros [-> _]%Vrel_box_iff.
Qed.

(** ** Offers of the composite *)

Section offers.
  Context (κ : ctable) (n : nat) (W1 : world) (T1 T2 : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1).
  Context (H1 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T1 q1).
  Context (H2 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) T2 q2).
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Lemma conn_not2 o : o ∈ dom Σ1 → o ∉ dom (Σ2 ∪ ΣD).
  Proof.
    destruct Hc as [? ? Hcut ? ? ? H12 H1C _ _ _ _]. rewrite (dom_union_L Σ2 ΣD).
    intros Ho Ho'. apply elem_of_union in Ho' as [Ho'|Ho'].
    - apply (H12 (ech o)); by apply elem_of_chans_of.
    - apply (H1C (ech o)); [by apply elem_of_chans_of|]. rewrite <-(cut_dual_chans _ _ Hcut).
      by apply elem_of_chans_of.
  Qed.

  (** A step of the composite on an end of Σ1 comes from p1. *)
  Lemma offered_c_1 o : o ∈ dom Σ1 → offered_p (Σ1 ∪ Σ2) pc o → offered_p (Σ1 ∪ ΣC) q1 o.
  Proof.
    intros HoΣ [_ (σ & p' & Hst & Hoσ)]. split; [rewrite dom_union_L; set_solver|].
    destruct (erase_surj pc) as [q Hq]. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
    rewrite <-Hq in Hst. destruct (pstep_lift _ _ _ Hst) as (ev & q' & Hi & Hl & _).
    destruct ev; try discriminate. injection Hl as ->. inversion Hi; subst.
    match goal with Hlk : (M1 ∪ M2) !! _ = Some _ |- _ => apply (lookup_union_Some _ _ _ _ Hd) in Hlk as [Hlk|Hlk] end.
    - exists σ, (erase ((q1.1 ∖ sentc σ), <[i := e']> M1)). split; [|done].
      exists (q1.1, M1), (EvSess i σ), (q1.1 ∖ sentc σ, <[i := e']> M1). split_and!; [|by eapply p_act_session; [eassumption|eassumption|set_solver]|done|done].
      unfold erase. simpl. rewrite HM1. by destruct q1.
    - exfalso. apply (conn_not2 o HoΣ).
      apply (Psteps_sends κ _ _ _ _ _ _ _ _ q2 (proj2 (proj2 H2)) (q2.1, M2) i σ (q2.1 ∖ sentc σ, <[i := e']> M2)).
      + unfold erase. simpl. rewrite HM2. by destruct q2.
      + by eapply p_act_session; [eassumption|eassumption|set_solver].
      + done.
  Qed.

  Lemma sess_lift M1 M2 i σ q1' :
    M1 ##ₘ M2 → istep (q1.1, M1) (EvSess i σ) q1' → subjs σ ## q1.1 ∪ q2.1 ∪ K →
    ∃ q', istep (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) (EvSess i σ) q'.
  Proof.
    intros Hd Hst Hs. inversion Hst; subst. eexists. eapply p_act_session; [|eassumption|done].
    by apply lookup_union_Some_l.
  Qed.

  Lemma pc_erase M1 M2 : M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    erase (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) = pc.
  Proof. intros Hd H1' H2'. unfold erase, pconn. simpl. by rewrite soup_union, H1', H2'. Qed.

  (** A link offer of p1 that touches the composite's restricted channels
      is a τ step of the composite. *)
  Lemma link_tau M1 M2 i os q1' :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 →
    istep (q1.1, M1) (EvSess i (SLink os)) q1' → ¬ (subjs (SLink os) ## q1.1 ∪ q2.1 ∪ K) →
    ¬ stable_p pc.
  Proof.
    intros Hd HM1 HM2 Hst Hs Hstab. inversion Hst; subst.
    match goal with H : tstep _ (LSess (SLink _)) _ |- _ => rename H into Ht end.
    destruct (tstep_link_shape _ _ _ Ht) as (o1 & o2 & Hos). rewrite Hos in Ht, Hs.
    assert (ech o1 ∈ q1.1 ∪ q2.1 ∪ K ∨ ech o2 ∈ q1.1 ∪ q2.1 ∪ K) as Hor.
    { destruct (decide (ech o1 ∈ q1.1 ∪ q2.1 ∪ K)); [by left|]. destruct (decide (ech o2 ∈ q1.1 ∪ q2.1 ∪ K)); [by right|].
      exfalso. apply Hs. simpl. rewrite set_map_union_L, !set_map_singleton_L. set_solver. }
    assert ((M1 ∪ M2) !! i = Some e) as Hi by (by apply lookup_union_Some_l).
    destruct Hor as [Ho|Ho].
    - eapply (Hstab _). rewrite <-(pc_erase M1 M2) by done. eexists _, _, _.
      split; [done|]. split; [by eapply p_act_link|]. split; reflexivity.
    - eapply (Hstab _). rewrite <-(pc_erase M1 M2) by done. eexists _, _, _.
      split; [done|]. split; [eapply p_act_link; [done|by rewrite upair_comm|done]|]. split; reflexivity.
  Qed.

  (** An offer of p1 on an end of Σ1 is an offer of the composite. *)
  Lemma offered_1_c o : o ∈ dom Σ1 → stable_p pc → offered_p (Σ1 ∪ ΣC) q1 o → offered_p (Σ1 ∪ Σ2) pc o.
  Proof.
    intros HoΣ Hstab [_ (σ & p1' & Hst & Hoσ)]. split; [rewrite dom_union_L; set_solver|].
    destruct (erase_surj pc) as [q Hq]. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
    destruct (pstep_lift (q1.1, M1) (PSess σ) p1') as (ev & q1' & Hi & Hl & _).
    { unfold erase. simpl. rewrite HM1. by destruct q1. }
    destruct ev; try discriminate. injection Hl as ->.
    destruct (decide (subjs σ ## q1.1 ∪ q2.1 ∪ K)) as [Hs|Hs].
    - destruct (sess_lift M1 M2 i σ q1' Hd Hi Hs) as [q' Hq']. exists σ, (erase q'). split; [|done].
      rewrite <-Hq. by exists (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2), (EvSess i σ), q'.
    - exfalso. destruct σ as [o' M w|o' w|o'|o' b|o' b|os].
      6: by apply (link_tau M1 M2 i os q1').
      all: simpl in Hoσ; apply elem_of_singleton in Hoσ as ->; apply Hs; simpl;
        destruct Hc as [? ? Hcut ? ? ? H12 H1C _ _ HC1 HC2];
        intros c Hc' Hc''; apply elem_of_singleton in Hc' as ->;
        pose proof (elem_of_chans_of _ _ HoΣ) as Hco; set_solver.
  Qed.
End offers.

Lemma ssubj_sends σ o : ssubj σ = Some o → sends σ = {[o]}.
Proof. by destruct σ; simpl; intros [= ->]. Qed.

Lemma sends_ssubj σ o : o ∈ sends σ → (∃ os, σ = SLink os) ∨ ssubj σ = Some o.
Proof. destruct σ; simpl; try (intros ->%elem_of_singleton; by right). eauto. Qed.

Lemma disj_lookup {A} (m1 m2 : gmap cend A) i x y : m1 ##ₘ m2 → m1 !! i = Some x → m2 !! i = Some y → False.
Proof. intros Hd H1 H2. exact (proj1 (map_disjoint_spec m1 m2) Hd i x y H1 H2). Qed.

Lemma disj_lookup_n {A} (m1 m2 : gmap nat A) i x y : m1 ##ₘ m2 → m1 !! i = Some x → m2 !! i = Some y → False.
Proof. intros Hd H1 H2. exact (proj1 (map_disjoint_spec m1 m2) Hd i x y H1 H2). Qed.

(** An offer on a cut end and an offer on its partner meet. *)
Lemma dual_offers κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 o :
  conn Σ1 ΣC q1.1 Σ2 ΣD q2.1 →
  Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T1 q1 →
  Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) T2 q2 →
  o ∈ dom ΣC → offered_p (Σ1 ∪ ΣC) q1 o → offered_p (Σ2 ∪ ΣD) q2 (edual o) →
  ¬ stable_p (pconn q1 q2 (chans_of ΣC)).
Proof.
  intros Hc H1 H2 HoC [_ (σ1 & p1' & Hs1 & Ho1)] [_ (σ2 & p2' & Hs2 & Ho2)] Hstab.
  set (K := chans_of ΣC).
  assert (ech o ∈ K) as HoK by (by apply elem_of_chans_of).
  destruct (erase_surj (pconn q1 q2 K)) as [q Hq]. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
  destruct (pstep_lift (q1.1, M1) (PSess σ1) p1') as (ev1 & r1 & Hi1 & Hl1 & _).
  { unfold erase. simpl. rewrite HM1. by destruct q1. }
  destruct (pstep_lift (q2.1, M2) (PSess σ2) p2') as (ev2 & r2 & Hi2 & Hl2 & _).
  { unfold erase. simpl. rewrite HM2. by destruct q2. }
  destruct ev1; try discriminate. injection Hl1 as ->. destruct ev2; try discriminate. injection Hl2 as ->.
  rename i into i1, i0 into i2.
  (* links meet a restricted channel *)
  destruct (sends_ssubj _ _ Ho1) as [[os ->]|E1].
  { apply (link_tau κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2 M1 M2 i1 os r1 Hd HM1 HM2 Hi1); [|done].
    intros Hs. apply (Hs (ech o)); [|set_solver]. simpl. apply elem_of_map. by exists o. }
  destruct (sends_ssubj _ _ Ho2) as [[os ->]|E2].
  { pose proof (conn_sym _ _ _ _ _ _ Hc) as Hc'. rewrite pconn_sym in Hstab.
    rewrite <-(cut_dual_chans ΣC ΣD) in Hstab by (by destruct Hc).
    apply (link_tau κ n W1 T2 T1 X2 X1 Σ2 ΣD Σ1 ΣC q2 q1 Hc' H2 H1 M2 M1 i2 os r2 (map_disjoint_sym _ _ Hd) HM2 HM1 Hi2);
      [|by rewrite (cut_dual_chans ΣC ΣD) in Hstab |- * by (by destruct Hc)].
    intros Hs. apply (Hs (ech o)); [|rewrite (cut_dual_chans ΣC ΣD) by (by destruct Hc); set_solver].
    simpl. apply elem_of_map. exists (edual o). by rewrite ech_edual. }
  assert (erase (q1.1, M1) = q1) as Hq1e by (unfold erase; simpl; rewrite HM1; by destruct q1).
  assert (erase (q2.1, M2) = q2) as Hq2e by (unfold erase; simpl; rewrite HM2; by destruct q2).
  destruct (Psteps_head κ _ _ _ _ _ _ _ _ _ (proj2 (proj2 H1)) _ _ _ _ o Hq1e Hi1 E1) as (S0 & x & L1 & D1).
  destruct (Psteps_head κ _ _ _ _ _ _ _ _ _ (proj2 (proj2 H2)) _ _ _ _ (edual o) Hq2e Hi2 E2) as (S0' & x' & L2 & D2).
  destruct Hc as [Hd1 Hd2 [Hcd Hct] ? ? HfC ? ? ? ? ? ?].
  assert (ΣC !! o = Some (S0, x)) as L1'.
  { rewrite lookup_union_r in L1; [done|]. apply eq_None_not_Some. intros [? ?].
    apply elem_of_dom in HoC as [? ?]. eapply (disj_lookup Σ1 ΣC); eassumption. }
  destruct (Hct _ _ _ L1') as (S'' & L3 & Hdu).
  assert (ΣD !! edual o = Some (S0', x')) as L2'.
  { rewrite lookup_union_r in L2; [done|]. apply eq_None_not_Some. intros [? ?].
    assert (edual o ∈ dom ΣD) as [? ?]%elem_of_dom by (apply Hcd; by rewrite edual_edual).
    eapply (disj_lookup Σ2 ΣD); eassumption. }
  rewrite L2' in L3. injection L3 as -> ->.
  assert (sync σ1 σ2) as Hsy by (eapply hd_ok_sync; [exact Hdu|exact D1|exact D2|congruence|congruence]).
  assert (∀ ev q', istep (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2) ev q' → ev_tau ev → False) as Hno.
  { intros ev q' Hst Hτ. apply (Hstab (erase q')). unfold preduction. rewrite <-(pc_erase ΣC q1 q2 M1 M2) by done.
    rewrite <-Hτ. by exists (q1.1 ∪ q2.1 ∪ chans_of ΣC, M1 ∪ M2), ev, q'. }
  inversion Hi1 as [| | | | | | | |C0 M0 j e σ e1 Hj He HsC]; subst.
  inversion Hi2 as [| | | | | | | |C0' M0' j' f σ' f1 Hj' Hf HsC']; subst.
  assert ((M1 ∪ M2) !! i1 = Some e) as Hl1 by (by apply lookup_union_Some_l).
  assert ((M1 ∪ M2) !! i2 = Some f) as Hl2 by (by apply lookup_union_Some_r).
  assert (i1 ≠ i2) as Hne by (intros ->; eapply (disj_lookup_n M1 M2); eassumption).
  assert (ech o ∈ q1.1 ∪ q2.1 ∪ K) as HoC' by set_solver.
  destruct σ1 as [o1 M w|o1 w|o1|o1 b|o1 b|os], σ2 as [o2 M' w'|o2 w'|o2|o2 b'|o2 b'|os'];
    simpl in Hsy; try done; simpl in E1, E2; injection E1 as ->; injection E2 as ->.
  - pose proof (tstep_label_val _ _ _ He) as Hw. destruct (recv_retarget _ _ _ _ w Hf Hw) as [f2 Hf2].
    eapply (Hno (EvMsg i1 i2 o M)); [|done]. by eapply p_act_msg.
  - pose proof (tstep_label_val _ _ _ Hf) as Hw. destruct (recv_retarget _ _ _ _ w' He Hw) as [e2 He2].
    eapply (Hno (EvMsg i2 i1 (edual o) M')); [|done]. eapply p_act_msg; [done|done|done|done|].
    by rewrite edual_edual.
  - eapply (Hno (EvClose i1 i2 o)); [|done]. by eapply p_act_close.
  - destruct (bra_retarget _ _ _ _ b Hf) as [f2 Hf2].
    eapply (Hno (EvChoice i1 i2 o b)); [|done]. by eapply p_act_choice.
  - destruct (bra_retarget _ _ _ _ b' He) as [e2 He2].
    eapply (Hno (EvChoice i2 i1 (edual o) b')); [|done]. eapply p_act_choice; [done|done|done|done|].
    by rewrite edual_edual.
Qed.

(** ** Readiness of the composite *)

Lemma terminated_pirred p : terminated p → pirred p.
Proof.
  intros (v & E & -> & Hv & HE) π p' (q & ev & q' & Hq & Hst & _).
  destruct (istep_parts_nonempty _ _ _ Hst) as [t Ht].
  destruct (istep_parts_some _ _ _ t Hst Ht) as [e He].
  destruct (istep_actor _ _ _ t e Hst Ht He) as (α & e' & Hs & _).
  assert (e ∈ soup q.2) as Hin by (apply elem_of_soup; eauto).
  destruct q as [C M]. injection Hq as _ HM. simpl in Hin. rewrite HM in Hin.
  apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin].
  - apply gmultiset_elem_of_singleton in Hin as ->. by apply (val_no_tstep _ _ _ Hs).
  - rewrite (HE e Hin) in Hs. by apply (val_no_tstep _ _ _ Hs).
Qed.

Lemma chans_disj_map (Σ1 Σ2 : senv) : chans_of Σ1 ## chans_of Σ2 → Σ1 ##ₘ Σ2.
Proof.
  intros H. apply map_disjoint_dom. intros o H1 H2.
  apply (H (ech o)); by apply elem_of_chans_of.
Qed.

Lemma offered_p_comm (Σ1 Σ2 : senv) p o : offered_p (Σ1 ∪ Σ2) p o ↔ offered_p (Σ2 ∪ Σ1) p o.
Proof. unfold offered_p. by rewrite !dom_union_L, (comm_L (∪) (dom Σ1)). Qed.

Lemma all_vals_pirred (p : proc) : (∀ e, e ∈ p.2 → is_val e) → pirred p.
Proof.
  intros Hv π p' (q & ev & q' & Hq & Hst & _).
  destruct (istep_parts_nonempty _ _ _ Hst) as [t Ht].
  destruct (istep_parts_some _ _ _ t Hst Ht) as [e He].
  destruct (istep_actor _ _ _ t e Hst Ht He) as (α & e' & Hs & _).
  apply (val_no_tstep _ _ _ Hs). apply Hv. rewrite <-Hq. apply elem_of_soup. eauto.
Qed.

(** One component, stable and without a link offer, at a primitive
    type. *)
Lemma comp_ready κ n W1 T X Σ q :
  prim T → Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X W1 Σ T q →
  stable_p q →
  link_p q ∨
  (above_offered W1 Σ (offered_p Σ q) ∧
   ((∀ o, ¬ offered_p Σ q o) →
      ∃ v E, q = (∅, {[+ v +]} ⊎ E) ∧ Vrel κ (S n) W1 Σ T v ∧ ∀ e, e ∈ E → e = EUnit)).
Proof.
  intros HT (Hs & Hr & _) Hstab.
  assert (pirred q → Σ = ∅) as HΣ.
  { intros Hi. destruct (Hs Hi) as (v & E & _ & Hv & _). by eapply Vrel_prim_empty. }
  destruct (decide (Forall is_val (elements q.2))) as [Hall|Hall].
  - assert (pirred q) as Hi.
    { apply all_vals_pirred. intros e He. apply gmultiset_elem_of_elements in He.
      apply list_elem_of_In in He. by eapply Forall_forall in Hall; [|exact He]. }
    right. split.
    + intros o S x Ho. by rewrite (HΣ Hi), lookup_empty in Ho.
    + intros _. destruct (Hs Hi) as (v & E & -> & Hv & HE). eauto.
  - assert (¬ pirred q) as Hni.
    { intros Hi. destruct (Hs Hi) as (v & E & Hq & Hv & HE). apply Hall. apply Forall_forall.
      intros e He. apply list_elem_of_In, gmultiset_elem_of_elements in He. rewrite Hq in He. simpl in He.
      apply gmultiset_elem_of_disj_union in He as [He|He].
      - apply gmultiset_elem_of_singleton in He as ->. by eapply Vrel_val.
      - by rewrite (HE e He). }
    destruct (Hr Hni Hstab) as [?|[Ht Ha]]; [by left|right]. split; [done|].
    intros Hno. destruct (Ht Hno) as (v & E & Hq & Hv & HE). exfalso. apply Hall. apply Forall_forall.
    intros e He. apply list_elem_of_In, gmultiset_elem_of_elements in He. rewrite Hq in He. simpl in He.
    apply gmultiset_elem_of_disj_union in He as [He|He].
    + by apply gmultiset_elem_of_singleton in He as ->.
    + by rewrite (HE e He).
Qed.

Lemma link_p_lift κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 :
  conn Σ1 ΣC q1.1 Σ2 ΣD q2.1 →
  Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T1 q1 →
  Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) T2 q2 →
  link_p q1 → stable_p (pconn q1 q2 (chans_of ΣC)) → link_p (pconn q1 q2 (chans_of ΣC)).
Proof.
  intros Hc H1 H2 (os & p1' & Hst) Hs. set (K := chans_of ΣC).
  destruct (erase_surj (pconn q1 q2 K)) as [q Hq]. destruct (pconn_lift _ _ _ _ Hq) as (M1 & M2 & -> & Hd & HM1 & HM2).
  destruct (pstep_lift (q1.1, M1) (PSess (SLink os)) p1') as (ev & q1' & Hi & Hl & _).
  { unfold erase. simpl. rewrite HM1. by destruct q1. }
  destruct ev; try discriminate. injection Hl as ->.
  destruct (decide (subjs (SLink os) ## q1.1 ∪ q2.1 ∪ K)) as [Hsj|Hsj].
  - destruct (sess_lift ΣC q1 q2 M1 M2 i _ q1' Hd Hi Hsj) as [q' Hq'].
    exists os, (erase q'). rewrite <-Hq. by exists (q1.1 ∪ q2.1 ∪ K, M1 ∪ M2), (EvSess i (SLink os)), q'.
  - exfalso. by apply (link_tau κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2 M1 M2 i os q1' Hd HM1 HM2 Hi).
Qed.

Definition pts (Σ : senv) : list point := (λ kv : cend * (sty * point), kv.2.2) <$> map_to_list Σ.

Lemma pts_elem (Σ : senv) o S x : Σ !! o = Some (S, x) → x ∈ pts Σ.
Proof. intros H. apply list_elem_of_fmap. exists (o, (S, x)). split; [done|]. by apply elem_of_map_to_list. Qed.

Lemma lookup_union_cases (m1 m2 : senv) o v :
  (m1 ∪ m2) !! o = Some v → m1 !! o = Some v ∨ (m1 !! o = None ∧ m2 !! o = Some v).
Proof. rewrite lookup_union_Some_raw. done. Qed.

Lemma lookup_union_disj_r (m1 m2 : senv) o v : m1 ##ₘ m2 → m2 !! o = Some v → (m1 ∪ m2) !! o = Some v.
Proof. intros Hd H. by apply lookup_union_Some_r. Qed.

Section rdy.
  Context (κ : ctable) (n : nat) (W1 : world) (HS : strict W1) (T1 T2 : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1).
  Context (H1 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T1 q1).
  Context (H2 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) T2 q2).
  Context (HT1 : prim T1) (HT2 : prim T2).
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma Hc' : conn Σ2 ΣD q2.1 Σ1 ΣC q1.1.
  Proof. by apply conn_sym. Qed.

  Local Lemma HKD : chans_of ΣD = K.
  Proof. apply cut_dual_chans. by destruct Hc. Qed.

  Local Lemma pc_sym : pconn q2 q1 (chans_of ΣD) = pc.
  Proof. by rewrite HKD, pconn_sym. Qed.

  Local Lemma HΣ12 : Σ1 ##ₘ Σ2.
  Proof. apply chans_disj_map. by destruct Hc. Qed.

  Lemma offered_2_c o : o ∈ dom Σ2 → stable_p pc → offered_p (Σ2 ∪ ΣD) q2 o → offered_p (Σ1 ∪ Σ2) pc o.
  Proof.
    intros Ho Hs H. apply offered_p_comm. rewrite <-pc_sym.
    apply (offered_1_c κ n W1 T2 T1 X2 X1 Σ2 ΣD Σ1 ΣC q2 q1 Hc' H2 H1); [done| |done].
    by rewrite pc_sym.
  Qed.

  Lemma link_p_2 : link_p q2 → stable_p pc → link_p pc.
  Proof.
    intros Hl Hs. rewrite <-pc_sym.
    apply (link_p_lift κ n W1 T2 T1 X2 X1 Σ2 ΣD Σ1 ΣC q2 q1 Hc' H2 H1); [done|by rewrite pc_sym].
  Qed.

  Lemma not_offered_dual_1 o : o ∈ dom ΣC → stable_p pc → offered_p (Σ1 ∪ ΣC) q1 o →
    ¬ offered_p (Σ2 ∪ ΣD) q2 (edual o).
  Proof. intros Ho Hs H1o H2o. by apply (dual_offers κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 o Hc H1 H2 Ho H1o H2o). Qed.

  Lemma not_offered_dual_2 o : o ∈ dom ΣD → stable_p pc → offered_p (Σ2 ∪ ΣD) q2 o →
    ¬ offered_p (Σ1 ∪ ΣC) q1 (edual o).
  Proof.
    intros Ho Hs H2o H1o. rewrite <-pc_sym in Hs.
    by apply (dual_offers κ n W1 T2 T1 X2 X1 Σ2 ΣD Σ1 ΣC q2 q1 o Hc' H2 H1 Ho H2o H1o).
  Qed.

  Local Lemma HdC : Σ1 ##ₘ ΣC.
  Proof. by destruct Hc. Qed.
  Local Lemma HdD : Σ2 ##ₘ ΣD.
  Proof. by destruct Hc. Qed.

  Lemma chain (Hs : stable_p pc)
      (A1 : above_offered W1 (Σ1 ∪ ΣC) (offered_p (Σ1 ∪ ΣC) q1))
      (A2 : above_offered W1 (Σ2 ∪ ΣD) (offered_p (Σ2 ∪ ΣD) q2)) :
    ∀ y e S, (ΣC !! e = Some (S, y) ∧ offered_p (Σ1 ∪ ΣC) q1 e) ∨
             (ΣD !! e = Some (S, y) ∧ offered_p (Σ2 ∪ ΣD) q2 e) →
    ∃ o' S' y', offered_p (Σ1 ∪ Σ2) pc o' ∧ (Σ1 ∪ Σ2) !! o' = Some (S', y') ∧ W1 ⊢ y' ≺ y.
  Proof.
    intros y. induction (finite_lt_acc W1 (pts ΣC ++ pts ΣD) HS y) as [y _ IH].
    pose proof Hc as Hc0. destruct Hc0 as [_ _ Hcut ? ? HfC ? ? ? ? ? ?].
    pose proof (cut_dual_sym _ _ HfC Hcut) as Hcut'.
    intros e S [[He Ho]|[He Ho]].
    - destruct (proj2 Hcut _ _ _ He) as (S' & He' & _).
      destruct (A2 (edual e) S' y‾) as (o2 & S2 & x2 & Ho2 & L2 & Hlt).
      { by apply lookup_union_disj_r; [apply HdD|]. }
      { by apply not_offered_dual_1; [eapply elem_of_dom_2|..]. }
      rewrite pt_dual_dual in Hlt.
      destruct (lookup_union_cases _ _ _ _ L2) as [L|[_ L]].
      + exists o2, S2, x2. split_and!; [apply offered_2_c; [by eapply elem_of_dom_2|done|done]| |done].
        by apply lookup_union_disj_r; [apply HΣ12|].
      + destruct (IH x2) with o2 S2 as (o' & S3 & y' & H1' & H2' & H3').
        { split; [apply elem_of_app; right; by eapply pts_elem|done]. }
        { right. by split. }
        exists o', S3, y'. split_and!; [done|done|by eapply w_lt_trans].
    - destruct (proj2 Hcut' _ _ _ He) as (S' & He' & _).
      destruct (A1 (edual e) S' y‾) as (o1 & S1 & x1 & Ho1 & L1 & Hlt).
      { by apply lookup_union_disj_r; [apply HdC|]. }
      { by apply not_offered_dual_2; [eapply elem_of_dom_2|..]. }
      rewrite pt_dual_dual in Hlt.
      destruct (lookup_union_cases _ _ _ _ L1) as [L|[_ L]].
      + exists o1, S1, x1. split_and!; [apply (offered_1_c κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2);
          [by eapply elem_of_dom_2|done|done]| |done].
        by apply lookup_union_Some_l.
      + destruct (IH x1) with o1 S1 as (o' & S3 & y' & H1' & H2' & H3').
        { split; [apply elem_of_app; left; by eapply pts_elem|done]. }
        { left. by split. }
        exists o', S3, y'. split_and!; [done|done|by eapply w_lt_trans].
  Qed.

  Lemma pc_ready : T2 = TUnit → ready _ W1(Σ1 ∪ Σ2, pc).
  Proof.
    intros HTU Hs. pose proof (stable_pconn_l _ _ _ Hs) as Hs1. pose proof (stable_pconn_r _ _ _ Hs) as Hs2.
    destruct (comp_ready κ n W1 T1 X1 _ _ HT1 H1 Hs1) as [Hl1|[A1 R1]].
    { left. by apply (link_p_lift κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2). }
    destruct (comp_ready κ n W1 T2 X2 _ _ HT2 H2 Hs2) as [Hl2|[A2 R2]].
    { left. by apply link_p_2. }
    assert (∀ o, offered_p (Σ1 ∪ ΣC) q1 o → offered_p (Σ1 ∪ Σ2) pc o ∨
              ∃ o' S' y', offered_p (Σ1 ∪ Σ2) pc o' ∧ (Σ1 ∪ Σ2) !! o' = Some (S', y')) as F1.
    { intros o Ho. destruct Ho as [Hd Ho']. apply elem_of_dom in Hd as [[S x] L].
      destruct (lookup_union_cases _ _ _ _ L) as [L'|[_ L']].
      - left. apply (offered_1_c κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2); [by eapply elem_of_dom_2|done|].
        split; [rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|done].
      - right. destruct (chain Hs A1 A2 x o S) as (o' & S' & y' & ? & ? & _); [left; split; [done|by split; [eapply elem_of_dom_2|]]|].
        eauto. }
    assert (∀ o, offered_p (Σ2 ∪ ΣD) q2 o → offered_p (Σ1 ∪ Σ2) pc o ∨
              ∃ o' S' y', offered_p (Σ1 ∪ Σ2) pc o' ∧ (Σ1 ∪ Σ2) !! o' = Some (S', y')) as F2.
    { intros o Ho. destruct Ho as [Hd Ho']. apply elem_of_dom in Hd as [[S x] L].
      destruct (lookup_union_cases _ _ _ _ L) as [L'|[_ L']].
      - left. apply offered_2_c; [by eapply elem_of_dom_2|done|].
        split; [rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|done].
      - right. destruct (chain Hs A1 A2 x o S) as (o' & S' & y' & ? & ? & _); [right; split; [done|by split; [eapply elem_of_dom_2|]]|].
        eauto. }
    right. split.
    - intros Hno.
      destruct (R1) as (v1 & E1 & Hq1 & Hv1 & HE1).
      { intros o Ho. destruct (F1 o Ho) as [?|(o' & _ & _ & ? & _)]; by eapply Hno. }
      destruct (R2) as (v2 & E2 & Hq2 & Hv2 & HE2).
      { intros o Ho. destruct (F2 o Ho) as [?|(o' & _ & _ & ? & _)]; by eapply Hno. }
      pose proof (Vrel_prim_empty _ _ _ _ _ _ HT1 Hv1) as HE1'.
      assert (ΣC = ∅) as HC0.
      { apply dom_empty_iff_L. apply (f_equal dom) in HE1'. rewrite dom_union_L, dom_empty_L in HE1'. set_solver. }
      rewrite HTU in Hv2. apply Vrel_unit_iff in Hv2 as [_ ->].
      exists v1, (E1 ⊎ ({[+ EUnit +]} ⊎ E2)). unfold pconn. rewrite Hq1, Hq2. simpl.
      rewrite HC0. unfold chans_of. rewrite dom_empty_L, set_map_empty. split_and!.
      + f_equal. multiset_solver.
      + by eapply Vrel_val.
      + intros e He. apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply HE1|].
        apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply gmultiset_elem_of_singleton in He|by apply HE2].
    - intros o S x Ho Hno. destruct (lookup_union_cases _ _ _ _ Ho) as [L|[Ln L]].
      + destruct (A1 o S x) as (o1 & S1 & x1 & Ho1 & L1 & Hlt).
        { by apply lookup_union_Some_l. }
        { intros Hof. apply Hno. apply (offered_1_c κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2); [by eapply elem_of_dom_2|done|done]. }
        destruct (lookup_union_cases _ _ _ _ L1) as [L1'|[_ L1']].
        * exists o1, S1, x1. split_and!; [|by apply lookup_union_Some_l|done].
          apply (offered_1_c κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2); [by eapply elem_of_dom_2|done|done].
        * destruct (chain Hs A1 A2 x1 o1 S1) as (o' & S' & y' & ? & ? & ?); [by left|].
          exists o', S', y'. split_and!; [done|done|by eapply w_lt_trans].
      + destruct (A2 o S x) as (o2 & S2 & x2 & Ho2 & L2 & Hlt).
        { by apply lookup_union_Some_l. }
        { intros Hof. apply Hno. apply offered_2_c; [by eapply elem_of_dom_2|done|done]. }
        destruct (lookup_union_cases _ _ _ _ L2) as [L2'|[_ L2']].
        * exists o2, S2, x2. split_and!; [apply offered_2_c; [by eapply elem_of_dom_2|done|done]| |done].
          by apply lookup_union_disj_r; [apply HΣ12|].
        * destruct (chain Hs A1 A2 x2 o2 S2) as (o' & S' & y' & ? & ? & ?); [by right|].
          exists o', S', y'. split_and!; [done|done|by eapply w_lt_trans].
  Qed.

  Lemma pc_stop : T2 = TUnit → pirred pc →
    ∃ v E, pc = (∅, {[+ v +]} ⊎ E) ∧ Vrel κ (S n) W1 (Σ1 ∪ Σ2) T1 v ∧ ∀ e, e ∈ E → e = EUnit.
  Proof.
    intros HTU Hi.
    assert (stable_p pc) as Hs by (intros p' Hp; by apply (Hi PTau p')).
    assert (∀ o, ¬ offered_p (Σ1 ∪ Σ2) pc o) as Hno by (intros o [_ (σ & p' & Hp & _)]; by apply (Hi (PSess σ) p')).
    assert (¬ link_p pc) as Hnl by (intros (os & p' & Hp); by apply (Hi (PSess (SLink os)) p')).
    pose proof (stable_pconn_l _ _ _ Hs) as Hs1. pose proof (stable_pconn_r _ _ _ Hs) as Hs2.
    destruct (comp_ready κ n W1 T1 X1 _ _ HT1 H1 Hs1) as [Hl1|[A1 R1]].
    { exfalso. apply Hnl. by apply (link_p_lift κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2). }
    destruct (comp_ready κ n W1 T2 X2 _ _ HT2 H2 Hs2) as [Hl2|[A2 R2]].
    { exfalso. apply Hnl. by apply link_p_2. }
    destruct R1 as (v1 & E1 & Hq1 & Hv1 & HE1).
    { intros o [Hd Ho]. apply elem_of_dom in Hd as [[S x] L].
      destruct (lookup_union_cases _ _ _ _ L) as [L'|[_ L']].
      - apply (Hno o). apply (offered_1_c κ n W1 T1 T2 X1 X2 Σ1 ΣC Σ2 ΣD q1 q2 Hc H1 H2); [by eapply elem_of_dom_2|done|].
        split; [rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|done].
      - destruct (chain Hs A1 A2 x o S) as (o' & S' & y' & ? & ? & _); [left; split; [done|by split; [eapply elem_of_dom_2|]]|].
        by apply (Hno o'). }
    destruct R2 as (v2 & E2 & Hq2 & Hv2 & HE2).
    { intros o [Hd Ho]. apply elem_of_dom in Hd as [[S x] L].
      destruct (lookup_union_cases _ _ _ _ L) as [L'|[_ L']].
      - apply (Hno o). apply offered_2_c; [by eapply elem_of_dom_2|done|].
        split; [rewrite dom_union_L; apply elem_of_union_l; by eapply elem_of_dom_2|done].
      - destruct (chain Hs A1 A2 x o S) as (o' & S' & y' & ? & ? & _); [right; split; [done|by split; [eapply elem_of_dom_2|]]|].
        by apply (Hno o'). }
    pose proof (Vrel_prim_empty _ _ _ _ _ _ HT1 Hv1) as HE1'.
    pose proof (Vrel_prim_empty _ _ _ _ _ _ HT2 Hv2) as HE2'.
    assert (ΣC = ∅) as HC0.
    { apply dom_empty_iff_L. apply (f_equal dom) in HE1'. rewrite dom_union_L, dom_empty_L in HE1'. set_solver. }
    assert (Σ2 = ∅) as H20.
    { apply dom_empty_iff_L. apply (f_equal dom) in HE2'. rewrite dom_union_L, dom_empty_L in HE2'. set_solver. }
    rewrite HTU in Hv2. apply Vrel_unit_iff in Hv2 as [_ ->].
    exists v1, (E1 ⊎ ({[+ EUnit +]} ⊎ E2)). unfold pconn. rewrite Hq1, Hq2. simpl.
    rewrite HC0. unfold chans_of. rewrite dom_empty_L, set_map_empty. split_and!.
    - f_equal. multiset_solver.
    - rewrite H20, (right_id_L ∅ (∪)). rewrite HC0, (right_id_L ∅ (∪)) in Hv1. done.
    - intros e He. apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply HE1|].
      apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply gmultiset_elem_of_singleton in He|by apply HE2].
  Qed.
End rdy.

(** ** Steps of the composite that one component takes alone *)

Definition ev_local (C1 : gset chan) (M1 : gmap nat expr) (ev : event) : Prop :=
  ev_parts ev ⊆ dom M1 ∧
  match ev with
  | EvClose _ _ o => ech o ∈ C1
  | EvLink _ o1 _ => ech o1 ∈ C1
  | EvSess _ _ => False
  | _ => True
  end.

Definition ev_ren (ev : event) : cend → cend :=
  match ev with EvLink _ o1 o2 => csub o1 o2 | _ => id end.

Lemma fmap_emap_id (M : gmap nat expr) : emap id <$> M = M.
Proof. apply map_eq. intros i. rewrite lookup_fmap. destruct (M !! i); simpl; [by rewrite emap_id|done]. Qed.

Lemma istep_local C1 C2 K M1 M2 ev q' :
  M1 ##ₘ M2 → C1 ## C2 ∪ K → istep (C1 ∪ C2 ∪ K, M1 ∪ M2) ev q' → ev_local C1 M1 ev →
  ∃ q1', istep (C1, M1) ev q1' ∧ q' = (q1'.1 ∪ C2 ∪ K, q1'.2 ∪ (emap (ev_ren ev) <$> M2)) ∧
    q1'.1 ⊆ q'.1 ∧ q1'.1 ## C2 ∪ K ∧ q1'.2 ##ₘ M2.
Proof.
  intros Hd HC Hst [Hp Hl].
  assert (∀ i e, (M1 ∪ M2) !! i = Some e → i ∈ dom M1 → M1 !! i = Some e) as Hlk.
  { intros i e H Hi. apply elem_of_dom in Hi as [e' He']. rewrite (lookup_union_Some_l _ _ _ _ He') in H. congruence. }
  assert (∀ i, i ∈ dom M1 → M2 !! i = None) as Hn2.
  { intros i Hi. apply elem_of_dom in Hi as [e He]. apply eq_None_not_Some. intros [e' He'].
    eapply (disj_lookup_n M1 M2); eassumption. }
  inversion Hst; subst; simpl in Hp, Hl; try done.
  - eexists (_, _). split; [eapply p_act_beta; [apply Hlk; [eassumption|set_solver]|eassumption]|]. simpl.
    rewrite fmap_emap_id. split; [by rewrite insert_union_l|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_new; [apply Hlk; [eassumption|set_solver]|eassumption|set_solver|]|]. 
    { intros Hc. match goal with H : c ∉ echans _ |- _ => apply H end. rewrite soup_union by done.
      rewrite echans_disj_union. set_solver. }
    simpl. rewrite fmap_emap_id. split; [f_equal; [set_solver|by rewrite insert_union_l]|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_new_at; [apply Hlk; [eassumption|set_solver]|eassumption|set_solver|]|].
    { intros Hc. match goal with H : c ∉ echans _ |- _ => apply H end. rewrite soup_union by done.
      rewrite echans_disj_union. set_solver. }
    simpl. rewrite fmap_emap_id. split; [f_equal; [set_solver|by rewrite insert_union_l]|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_spawn; [apply Hlk; [eassumption|set_solver]|eassumption|]|].
    { match goal with H : (M1 ∪ M2) !! j = None |- _ => apply lookup_union_None in H as [? _]; done end. }
    simpl. rewrite fmap_emap_id. split; [by rewrite !insert_union_l|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_msg; [done|apply Hlk; [eassumption|set_solver]|apply Hlk; [eassumption|set_solver]|eassumption|eassumption]|].
    simpl. rewrite fmap_emap_id. split; [by rewrite !insert_union_l|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_close; [done|apply Hlk; [eassumption|set_solver]|apply Hlk; [eassumption|set_solver]|eassumption|eassumption|done]|].
    simpl. rewrite fmap_emap_id. split; [f_equal; [set_solver|by rewrite !insert_union_l]|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_choice; [done|apply Hlk; [eassumption|set_solver]|apply Hlk; [eassumption|set_solver]|eassumption|eassumption]|].
    simpl. rewrite fmap_emap_id. split; [by rewrite !insert_union_l|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
  - eexists (_, _). split; [eapply p_act_link; [apply Hlk; [eassumption|set_solver]|eassumption|done]|].
    simpl. split; [f_equal; [set_solver|by rewrite insert_union_l, map_fmap_union]|]. split; [set_solver|]. split; [set_solver|]. apply map_disjoint_dom; rewrite ?dom_fmap_L, ?dom_insert_L; apply map_disjoint_dom in Hd; repeat match goal with H : (M1 ∪ M2) !! _ = None |- _ => apply lookup_union_None in H as [? ?] end; repeat match goal with H : _ !! _ = None |- _ => apply not_elem_of_dom in H end; set_solver.
Qed.

(** ** Induction over the steps of cost 0, closed under fusion *)

Definition Φfuse (Φ : prel) : prel :=
  λ W Σ T p, ∀ h D, fuse_ok h D Σ p → Φ W (sdrop D (kren h Σ)) T (pfuse h D p).

Lemma Pbody_fuse κ n Vl Pl VN X W Σ T p h D :
  fuse_ok h D Σ p → Pbody κ n Vl Pl VN X W Σ T p → Pbody κ n Vl Pl VN X W (sdrop D (kren h Σ)) T (pfuse h D p).
Proof.
  intros Hh HP W1 HW1 HS1 g D' Hg.
  rewrite (fuse_sdrop_compose h g D D' Σ p Hh Hg), (pfuse_compose h g D D' Σ p Hh Hg).
  apply HP; [done|done|]. by apply fuse_ok_compose.
Qed.

Lemma Prel_S_ind_fuse κ n (Φ : prel) :
  (∀ W Σ T p,
     Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n))
       (λ W Σ T p, Prel κ (S n) W Σ T p ∧ Φfuse Φ W Σ T p) W Σ T p →
     Φ W Σ T p) →
  ∀ W Σ T p, Prel κ (S n) W Σ T p → Φfuse Φ W Σ T p.
Proof.
  intros Hind. refine (Prel_S_ind κ n _ _). intros W Σ T p Hb h D Hh.
  apply Hind. by apply Pbody_fuse.
Qed.

Lemma Φfuse_id (Φ : prel) W Σ T p : Φfuse Φ W Σ T p → Φ W Σ T p.
Proof.
  intros H. pose proof (H id ∅ (fuse_ok_id Σ p)) as H'.
  by rewrite sdrop_empty, kren_id_map, pfuse_empty, pmap_id in H'.
Qed.

(** ** Renamings that fix every held end *)

Lemma csub_dcomm_all o1 o2 : dcomm (csub o1 o2).
Proof.
  destruct (decide (ech o2 = ech o1)) as [He|He]; [|by apply csub_dcomm].
  symmetry in He. apply ech_eq in He as [->| ->]; intros o; unfold csub;
    repeat case_decide; subst; rewrite ?edual_edual in *; try done;
    repeat match goal with
    | H : edual ?a = ?a |- _ => by destruct (edual_ne a)
    | H : ?a = edual ?a |- _ => by destruct (edual_ne a)
    | H : edual ?a = edual ?b |- _ => apply edual_inj in H; subst
    | H : ?a ≠ ?a |- _ => by destruct H
    end; congruence.
Qed.

Lemma ren_held_id (g : cend → cend) (Σ : senv) (p : proc) :
  dcomm g → (∀ o, pheld Σ p o → g o = o) →
  pren_ok g Σ p ∧ kren g Σ = Σ ∧ (pmap g p).1 = p.1.
Proof.
  intros Hd Hid. split_and!.
  - split_and!; [done| |].
    + intros o1 o2 H1 H2. by rewrite (Hid o1 H1), (Hid o2 H2).
    + intros o1 o2 H1 H2. by rewrite (Hid o1 H1), (Hid o2 H2).
  - apply kren_id. intros o Ho. apply Hid. by left.
  - unfold pmap. simpl. apply set_eq. intros c. rewrite elem_of_map. split.
    + intros (c' & -> & Hc'). unfold gch. rewrite Hid; [done|by right].
    + intros Hc. exists c. split; [|done]. unfold gch. rewrite Hid; [done|by right].
Qed.

Lemma csub_held_id o1 o2 (Σ : senv) (p : proc) :
  ech o1 ∉ chans_of Σ ∪ p.1 → ∀ o, pheld Σ p o → csub o1 o2 o = o.
Proof.
  intros Hn o [Ho|Ho]; apply csub_ne; intros He; apply Hn; rewrite <-He; [apply elem_of_union_l; by apply elem_of_chans_of|set_solver].
Qed.

(** A renaming that fixes the held ends keeps a process in P at its
    interface. *)
Lemma Prel_ren_id κ m W Σ T p g :
  dcomm g → (∀ o, pheld Σ p o → g o = o) → Prel κ m W Σ T p → Prel κ m W Σ T (pmap g p).
Proof.
  intros Hd Hid HP. destruct (ren_held_id g Σ p Hd Hid) as (Hok & Hk & _).
  rewrite <-Hk at 1. by apply Prel_rename.
Qed.

Lemma conn_C1 Σ1 ΣC C1 Σ2 ΣD C2 C1' :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → C1' ## C2 ∪ chans_of ΣC → C1' ## chans_of Σ1 ∪ chans_of Σ2 →
  conn Σ1 ΣC C1' Σ2 ΣD C2.
Proof. intros [] H1 H2. constructor; try done; set_solver. Qed.

Lemma conn_C2 Σ1 ΣC C1 Σ2 ΣD C2 C2' :
  conn Σ1 ΣC C1 Σ2 ΣD C2 → C2' ## C1 ∪ chans_of ΣC → C2' ## chans_of Σ1 ∪ chans_of Σ2 →
  conn Σ1 ΣC C1 Σ2 ΣD C2'.
Proof. intros [] H1 H2. constructor; try done; set_solver. Qed.

