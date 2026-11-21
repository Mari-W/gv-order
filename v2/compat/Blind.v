(** * R^κ is blind to annotations (stage S4)

    The relation reads no annotation of a type and compares session
    types up to ≈ after erasing their annotations ([seqv]). So V, E and
    P at T and at T' agree whenever the erasures of T and T' are ≈
    ([Vrel_teq], [Erel_teq], [Prel_teq]), and in particular whenever
    ty_df T = ty_df T' ([Vrel_blind], [Erel_blind]). Stage S5 needs this
    for D-Box and D-Conv.

    The head of a session type that is ≈ to a known head after erasure
    has the same shape ([seqv_unfold_snd] and its siblings). The
    operator redexes of compat/Redex.v read the environment's session
    type through these lemmas, because V at S@x holds the end at a type
    S' with S' ≈ S only. *)

From GV Require Export types.Erasure types.Duality static.PointSubst relation.Closure.

(** ** Session types up to annotations *)

Lemma seqv_refl s : seqv s s.
Proof. apply sequiv_refl. Qed.
Lemma seqv_sym s r : seqv s r → seqv r s.
Proof. apply sequiv_sym. Qed.
Lemma seqv_trans s r t : seqv s r → seqv r t → seqv s t.
Proof. apply sequiv_trans. Qed.

Local Ltac hd_inv Hq Hu :=
  apply sequiv_step in Hq; unfold eq_step in Hq; rewrite !hd_df, (hd_of _ _ Hu) in Hq;
  simpl in Hq.

Lemma seqv_unfold_snd s S0 m U S :
  seqv s S0 → unfoldS S0 = SSeq (SSnd m U) S →
  ∃ U' S', unfoldS s = SSeq (SSnd m U') S' ∧ teq (ty_df U') (ty_df U) ∧ seqv S' S.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma seqv_unfold_rcv s S0 m U S :
  seqv s S0 → unfoldS S0 = SSeq (SRcv m U) S →
  ∃ U' S', unfoldS s = SSeq (SRcv m U') S' ∧ teq (ty_df U') (ty_df U) ∧ seqv S' S.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma seqv_unfold_end s S0 : seqv s S0 → unfoldS S0 = SEnd → unfoldS s = SEnd.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. by rewrite unfoldS_unview, Hs.
Qed.

Lemma seqv_unfold_plus s S0 S1 S2 :
  seqv s S0 → unfoldS S0 = SPlus S1 S2 →
  ∃ S1' S2', unfoldS s = SPlus S1' S2' ∧ seqv S1' S1 ∧ seqv S2' S2.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma seqv_unfold_with s S0 S1 S2 :
  seqv s S0 → unfoldS S0 = SWith S1 S2 →
  ∃ S1' S2', unfoldS s = SWith S1' S2' ∧ seqv S1' S1 ∧ seqv S2' S2.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma seqv_bsel i S1 S2 S1' S2' : seqv S1' S1 → seqv S2' S2 → seqv (bsel i S1' S2') (bsel i S1 S2).
Proof. by destruct i. Qed.

(** ** Identity session substitution *)

Lemma sty_up_svar a : sty_up SVar a = SVar a.
Proof. by destruct a. Qed.

Lemma iter_sty_up_svar k a : Nat.iter k sty_up SVar a = SVar a.
Proof.
  revert a. induction k as [|k IH]; intros a; [done|]. simpl.
  rewrite (sty_up_ext _ SVar); [apply sty_up_svar|apply IH].
Qed.

Lemma sinst_svar_mut :
  (∀ T σ, (∀ a, σ a = SVar a) → sinst_ty σ T = T) ∧
  (∀ s σ, (∀ a, σ a = SVar a) → sinst σ s = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - apply H. intros a. rewrite (iter_sty_up_ext _ _ SVar) by done. apply iter_sty_up_svar.
  - apply H. intros a. rewrite (sty_up_ext _ SVar) by done. apply sty_up_svar.
  - by rewrite H.
Qed.

Lemma sinst_ty_slist_nil T : sinst_ty (slist []) T = T.
Proof. apply sinst_svar_mut. intros a. unfold slist. simpl. f_equal. lia. Qed.

(** ** Sizes *)

Lemma tsize_df T : tsize (ty_df T) = tsize T.
Proof. induction T; simpl; auto. Qed.

Lemma eqT_tsize ρ T : ∀ T', eqT ρ T T' → tsize T = tsize T'.
Proof. induction T; intros [] H; simpl in *; try done; destruct_and?; repeat case_match; subst; auto. Qed.

Lemma teq_df_tsize T T' : teq (ty_df T) (ty_df T') → tsize T = tsize T'.
Proof. intros H. rewrite <-(tsize_df T), <-(tsize_df T'). by eapply eqT_tsize. Qed.

Section blind.
  Context (κ : ctable).

  (** ** E reads its type only through V *)

  Lemma Erel_teq_1 n : ∀ T T',
    (∀ m W Θ v, ole m n → Vrel κ m W Θ T v → Vrel κ m W Θ T' v) →
    ∀ W Θ F e, Erel κ n W Θ T F e → Erel κ n W Θ T' F e.
  Proof.
    induction n as [n IHn] using oind. intros T T' HV W Θ F e HE.
    revert W Θ F e HE.
    cut (∀ W Θ T0 F e, Erel κ n W Θ T0 F e → T0 = T → Erel κ n W Θ T' F e).
    { intros H W Θ F e HE. by eapply H. }
    refine (Erel_ind κ n _ _). intros W Θ T0 F e H ->. apply Erel_iff. intros W1 HW1.
    destruct (H W1 HW1) as (Hs & Hr & H1 & H2 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c W Θ F e',
      at_cost_E n c (Erel κ) (λ W Θ T0 F e, Erel κ n W Θ T0 F e ∧
                                     (T0 = T → Erel κ n W Θ T' F e)) W Θ T F e' →
      at_cost_E n c (Erel κ) (Erel κ n) W Θ T' F e') as Hac.
    { intros c W0 Θ0 F0 e' [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc j Hj. apply (IHn j (oadd_lt _ _ _ Hc Hj) T T'); [|by apply A2].
        intros m W2 Θ2 v Hm. apply HV. exact (ole_trans _ _ _ Hm (oadd_le_l _ _ _ Hj)). }
    split; [|split; [|unfold Esteps; split_and!]].
    - intros Hirr. apply HV; [apply ole_refl|]. by apply Hs.
    - done.
    - intros e' Hst. by apply Hac, H1.
    - intros c e' Hst Hc. destruct (H2 c e' Hst Hc) as (S & π & Wn & HWn & HS). exists S, π, Wn. split; [done|]. by apply Hac.
    - intros v e' Hst. destruct (H4 v e' Hst) as (ΘM & Θr & A1 & A2 & A4 & A5).
      exists ΘM, Θr. split_and!; [done|done| |by apply Hac].
      revert A4. apply Varr_mono; [by intros|by intros|by intros|]. by intros _ ? ? ? ? ? ? [? _].
    - intros o w e' Hst.
      destruct (H5 o w e' Hst) as (S0 & x & m' & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      exists S0, x, m', U, S, ΘM, Θr. split_and!; [done..|by apply Hac].
    - intros o w e' Hst. destruct (H6 o w e' Hst) as (S0 & x & m' & U & S & A1 & A2 & A3).
      exists S0, x, m', U, S. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (IHn j (c_take_lt κ n j Hj) T T'); [|by apply A3].
      intros m W2 Θ2 v Hm. apply HV. exact (ole_trans _ _ _ Hm (oadd_le_l _ _ _ Hj)).
    - intros o e' Hst. destruct (H7 o e' Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H8 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H9 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros os e' Hst. destruct (H10 os e' Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.

  Lemma Erel_teq n T T' :
    (∀ m W Θ v, ole m n → Vrel κ m W Θ T v ↔ Vrel κ m W Θ T' v) →
    ∀ W Θ F e, Erel κ n W Θ T F e ↔ Erel κ n W Θ T' F e.
  Proof.
    intros HV W Θ F e. split; apply Erel_teq_1; intros m W' Θ' v Hm; by apply HV.
  Qed.

  (** ** V up to ≈ of the erasures *)

  Lemma teq_thunk ub X X' :
    teq (ty_df X) (ty_df X') → teq (ty_df (tthunk ub X)) (ty_df (tthunk ub X')).
  Proof. intros H. unfold teq in *. cbn. split_and!; try done. Qed.

  Lemma Vrel_teq_k k : ∀ T T', tsize T ≤ k → teq (ty_df T) (ty_df T') →
    ∀ n W Θ v, Vrel κ n W Θ T v ↔ Vrel κ n W Θ T' v.
  Proof.
    induction k as [k IHk] using lt_wf_ind. intros T T' Hk Heq n W Θ v.
    pose proof (teq_df_tsize _ _ Heq) as Hsz.
    assert (∀ T1 T1', tsize T1 < tsize T → teq (ty_df T1) (ty_df T1') →
              ∀ n W Θ v, Vrel κ n W Θ T1 v ↔ Vrel κ n W Θ T1' v) as IH.
    { intros T1 T1' H1 H2. apply (IHk (tsize T1)); [lia|lia|done]. }
    clear IHk.
    destruct T as [|ub lb c T1 U a|T1 U|T1 U|m kk C ub c U|s x a mt|lb m C T1],
      T' as [|ub' lb' c' T1' U' a'|T1' U'|T1' U'|m' kk' C' ub' c' U'|s' x' a' mt'|lb' m' C' T1'];
      unfold teq in Heq; simpl in Heq; try done; destruct_and?; subst.
    - rewrite !Vrel_lolli_iff. unfold Varr_rel.
      assert (∀ j W Θ w, Vrel κ j W Θ T1 w ↔ Vrel κ j W Θ T1' w) as E1.
      { intros. apply IH; [simpl; lia|done]. }
      assert (∀ j W Θ F e, Erel κ j W Θ U F e ↔ Erel κ j W Θ U' F e) as E2.
      { intros j. apply Erel_teq. intros. apply IH; [simpl; lia|done]. }
      by setoid_rewrite E1; setoid_rewrite E2.
    - rewrite !Vrel_prod_iff.
      assert (∀ W Θ w, Vrel κ n W Θ T1 w ↔ Vrel κ n W Θ T1' w) as E1.
      { intros. apply IH; [simpl; lia|done]. }
      assert (∀ W Θ w, Vrel κ n W Θ U w ↔ Vrel κ n W Θ U' w) as E2.
      { intros. apply IH; [simpl; lia|done]. }
      by setoid_rewrite E1; setoid_rewrite E2.
    - rewrite !Vrel_sum_iff.
      assert (∀ W Θ w, Vrel κ n W Θ T1 w ↔ Vrel κ n W Θ T1' w) as E1.
      { intros. apply IH; [simpl; lia|done]. }
      assert (∀ W Θ w, Vrel κ n W Θ U w ↔ Vrel κ n W Θ U' w) as E2.
      { intros. apply IH; [simpl; lia|done]. }
      by setoid_rewrite E1; setoid_rewrite E2.
    - rewrite !Vrel_box_iff.
      assert (∀ W' xs ss, length ss = kk' →
        ∀ v, Vrel κ n W' ∅ (tthunk (pt_inst (plist xs) <$> ub') (sinst_ty (slist ss) (ty_inst xs U))) v ↔
             Vrel κ n W' ∅ (tthunk (pt_inst (plist xs) <$> ub') (sinst_ty (slist ss) (ty_inst xs U'))) v)
        as E.
      { intros W' xs ss Hss v0. apply IH.
        { rewrite tsize_tthunk. unfold ty_inst. rewrite tsize_sinst, tsize_pinst. simpl. lia. }
        apply teq_thunk. destruct kk' as [|kk'].
        - destruct ss; [|done]. rewrite !sinst_ty_slist_nil, <-!ty_inst_df. by apply teq_pinst.
        - rewrite !ty_df_sinst, <-!ty_inst_df. match goal with H : ty_df U = ty_df U' |- _ => rewrite H end.
          apply teq_refl. }
      split; intros (-> & e & -> & Hfe & H); (split; [done|]); exists e; (split; [done|]); (split; [done|]);
        intros W' xs ss HW Hxs Hss Hsc HC; specialize (H W' xs ss HW Hxs Hss Hsc HC);
        by apply E.
    - rewrite !Vrel_sess_iff. split; intros (o & s0 & -> & -> & Hs); exists o, s0;
        split_and!; try done; unfold seqv in *; eapply sequiv_trans; eauto using sequiv_sym.
    - rewrite !Vrel_ex_iff.
      assert (∀ xs W Θ w, Vrel κ n W Θ (ty_inst xs T1) w ↔ Vrel κ n W Θ (ty_inst xs T1') w) as E.
      { intros xs. apply IH; [unfold ty_inst; rewrite tsize_pinst; simpl; lia|].
        rewrite <-!ty_inst_df. by apply teq_pinst. }
      by setoid_rewrite E.
  Qed.

  Lemma Vrel_teq n W Θ T T' v :
    teq (ty_df T) (ty_df T') → Vrel κ n W Θ T v ↔ Vrel κ n W Θ T' v.
  Proof. intros H. by apply (Vrel_teq_k (tsize T)). Qed.

  Lemma Erel_teq_ty n W Θ T T' F e :
    teq (ty_df T) (ty_df T') → Erel κ n W Θ T F e ↔ Erel κ n W Θ T' F e.
  Proof. intros H. apply Erel_teq. intros. by apply Vrel_teq. Qed.

  (** ** The blindness lemma *)

  Lemma Vrel_blind n W Θ T T' v : ty_df T = ty_df T' → Vrel κ n W Θ T v ↔ Vrel κ n W Θ T' v.
  Proof. intros H. apply Vrel_teq. rewrite H. apply teq_refl. Qed.

  Lemma Erel_blind n W Θ T T' F e : ty_df T = ty_df T' → Erel κ n W Θ T F e ↔ Erel κ n W Θ T' F e.
  Proof. intros H. apply Erel_teq_ty. rewrite H. apply teq_refl. Qed.

  (** ** P reads its type only through V *)

End blind.

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

Lemma unfold_dual_snd S0 m U S :
  unfoldS S0 = SSeq (SSnd m U) S → unfoldS (dual S0) = SSeq (SRcv m U) (dual S).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_rcv S0 m U S :
  unfoldS S0 = SSeq (SRcv m U) S → unfoldS (dual S0) = SSeq (SSnd m U) (dual S).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_end S0 : unfoldS S0 = SEnd → unfoldS (dual S0) = SEnd.
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_plus S0 S1 S2 : unfoldS S0 = SPlus S1 S2 → unfoldS (dual S0) = SWith (dual S1) (dual S2).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.
Lemma unfold_dual_with S0 S1 S2 : unfoldS S0 = SWith S1 S2 → unfoldS (dual S0) = SPlus (dual S1) (dual S2).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.

(** The partner of a send receives the same payload type up to ≈. *)
Lemma sdual_snd S0 S0' m U S :
  sdual S0 S0' → unfoldS S0 = SSeq (SSnd m U) S →
  ∃ U' S', unfoldS S0' = SSeq (SRcv m U') S' ∧ teq (ty_df U') (ty_df U) ∧ sdual S S'.
Proof.
  intros H Hu. destruct (seqv_unfold_rcv S0' (dual S0) m U (dual S) H (unfold_dual_snd _ _ _ _ Hu))
    as (U' & S' & H1 & H2 & H3). eauto 10.
Qed.

Lemma sdual_rcv S0 S0' m U S :
  sdual S0 S0' → unfoldS S0 = SSeq (SRcv m U) S →
  ∃ U' S', unfoldS S0' = SSeq (SSnd m U') S' ∧ teq (ty_df U') (ty_df U) ∧ sdual S S'.
Proof.
  intros H Hu. destruct (seqv_unfold_snd S0' (dual S0) m U (dual S) H (unfold_dual_rcv _ _ _ _ Hu))
    as (U' & S' & H1 & H2 & H3). eauto 10.
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

(** A value of a [tfree] type holds no end. *)
Lemma Vrel_tfree_empty κ n W Θ T v : tfree T → Vrel κ n W Θ T v → Θ = ∅.
Proof.
  intros Hp. revert Θ v. induction Hp as [|m k C ub c U|U V HU IHU HV IHV|U V HU IHU HV IHV];
    intros Θ v.
  - by intros [-> _]%Vrel_unit_iff.
  - by intros [-> _]%Vrel_box_iff.
  - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & -> & H1 & H2)%Vrel_prod_iff.
    rewrite (IHU _ _ H1), (IHV _ _ H2). by rewrite (left_id_L ∅ (∪)).
  - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; eauto.
Qed.
