(** * P-Connect and P-Join for the live relation (composition/PConnect.v)

    [lconn_level] composes two components at one level by induction on
    the τ layers of both: the outer induction on the first component,
    the inner one on the second. The τ layer holds the links too: a link
    of one component leaves the other one as it is, and its effect on
    the other component's ends is applied to the composite
    (LiveConnect.v, [lsteps_link]). The composite world lies above both
    base worlds, so a component that creates a channel at a fresh
    extension is read there directly, and the other component keeps its
    derivation at its base world (liveness.md §4). The other steps of
    the composite are channel steps and go to the outer induction on
    the index through the step cases of LiveConnect.v.

    [LPrel_connect] is [Prel_connect] with LPrel in place of Prel, and
    P-Join is its instance at two worlds. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveConnect.

Local Set Warnings "-register-all".
Implicit Types W : world.

Lemma LPtau_case_conv X W Σ Σ' T p q :
  Σ = Σ' → p = q → LPtau_case X W Σ T p → LPtau_case X W Σ' T q.
Proof. by intros -> ->. Qed.

Lemma LPobl_conv Vl Pl n W Σ Σ' T p q σ p' q' :
  Σ = Σ' → p = q → p' = q' → LPobl Vl Pl n W Σ T p σ p' → LPobl Vl Pl n W Σ' T q σ q'.
Proof. by intros -> -> ->. Qed.

Lemma Plink_case_conv X W Σ Σ' T cd p p' :
  Σ = Σ' → p = p' → Plink_case X W Σ T cd p → Plink_case X W Σ' T cd p'.
Proof. by intros -> ->. Qed.

Lemma cut_ok_mono W W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 :
  wext_r W W' → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 → cut_ok W' Σ1 Σ2 ΣC ΣC' C0 C1 C2.
Proof.
  intros [->|Hx] Hok; [done|]. destruct Hok. split; try done. by destruct Hx as (_ & _ & _ & ?).
Qed.

Lemma cut_ok_new1 W Σ1 Σ2 ΣC ΣC' C0 C1 C2 c :
  cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 → c ∉ dom Σ1 → c ∉ dom Σ2 → c ∉ C0 → c ∉ C2 →
  cut_ok W Σ1 Σ2 ΣC ΣC' C0 (C1 ∪ {[c]}) C2.
Proof. intros []. split; try done; set_solver. Qed.

Lemma senv_roots_union_sub Σ1 ΣC : Σ1 ##ₘ ΣC → senv_roots Σ1 ⊆ senv_roots (Σ1 ∪ ΣC).
Proof. intros _. apply senv_roots_mono, map_union_subseteq_l. Qed.

Lemma ctys_roots TA TB T : ctys TA TB T → ty_roots TA ⊆ ty_roots T ∧ ty_roots TB ⊆ ty_roots T.
Proof. intros [[-> ->]|[-> ->]]; simpl; set_solver. Qed.

Section lassembly.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → lconn_at j T).

  (** The goal for two derivations at their base worlds W1 and W2. *)
  Definition lconn_goal (W1 : world) (Σa : senv) (TA : ty) (p1 : proc)
      (W2 : world) (Σb : senv) (TB : ty) (p2 : proc) : Prop :=
    ∀ W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2,
      Σa = Σ1 ∪ ΣC → p1 = (C1, E1) → Σb = Σ2 ∪ ΣC' → p2 = (C2, E2) →
      ctys TA TB T → wext_r W1 W → wext_r W2 W → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
      LPrel (S n') W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).

  Lemma lconn_level W1 Σa TA p1 :
    LPrel (S n') W1 Σa TA p1 → ∀ W2 Σb TB p2, LPrel (S n') W2 Σb TB p2 →
    lconn_goal W1 Σa TA p1 W2 Σb TB p2.
  Proof.
    revert W1 Σa TA p1.
    refine (LPrel_S_ind n' (λ W1 Σa TA p1, ∀ W2 Σb TB p2, LPrel (S n') W2 Σb TB p2 →
              lconn_goal W1 Σa TA p1 W2 Σb TB p2) _).
    intros W1 Σa TA p1 H1 W2 Σb TB p2 HP2b.
    assert (HP1b : LPrel (S n') W1 Σa TA p1).
    { apply LPrel_S_iff. eapply LPstep_mono; [|exact H1]. by intros ? ? ? ? [? _]. }
    revert W2 Σb TB p2 HP2b.
    refine (LPrel_S_ind n' (λ W2 Σb TB p2, lconn_goal W1 Σa TA p1 W2 Σb TB p2) _).
    intros W2 Σb TB p2 H2 W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 -> -> -> -> Hty HW1 HW2 Hok0.
    assert (HP2b : LPrel (S n') W2 (Σ2 ∪ ΣC') TB (C2, E2)).
    { apply LPrel_S_iff. eapply LPstep_mono; [|exact H2]. by intros ? ? ? ? [? _]. }
    apply LPrel_S_iff. intros W' HW'.
    assert (wext_r W1 W' ∧ wext_r W2 W') as [HW1' HW2'] by (split; by eapply wext_r_trans).
    pose proof (cut_ok_mono _ _ _ _ _ _ _ _ _ HW' Hok0) as Hok.
    assert (HP1 : LPrel (S n') W' (Σ1 ∪ ΣC) TA (C1, E1)) by (eapply LPrel_mono; [exact HW1'|exact HP1b]).
    assert (HP2 : LPrel (S n') W' (Σ2 ∪ ΣC') TB (C2, E2)) by (eapply LPrel_mono; [exact HW2'|exact HP2b]).
    assert (HP1n : LPrel n' W' (Σ1 ∪ ΣC) TA (C1, E1)) by (eapply LPrel_down; [|exact HP1]; lia).
    assert (HP2n : LPrel n' W' (Σ2 ∪ ΣC') TB (C2, E2)) by (eapply LPrel_down; [|exact HP2]; lia).
    destruct (H1 W' HW1') as (_ & _ & Ha1 & _ & Hl1 & _).
    destruct (H2 W' HW2') as (_ & _ & Ha2 & _ & Hl2 & _).
    clear H1 H2.
    (* the inductions on the τ layers, for the links of either component *)
    assert (HQ1 : ∀ cd p1', proc_step (C1, E1) (PSess (SLink cd)) p1' →
              Plink_case (λ W0 Σa _ q, lc_succ n' T Σ2 ΣC' C2 E2 W0 Σa q) W' (Σ1 ∪ ΣC) TA cd p1').
    { intros cd p1' Hst. eapply Plink_case_mono; [|exact (Hl1 cd p1' Hst)].
      intros Σa' [_ HΦ] Σ1' Σ2' ΣC1 ΣC2 C0' C1' E1' HΣa Hq HΣb Hok'.
      eapply (HΦ W2 _ TB (C2, E2) HP2b); [exact HΣa|exact Hq|exact HΣb|done|done|by left|exact HW2'|exact Hok']. }
    assert (HA1 : ∀ p1', padmin (C1, E1) p1' → p1'.1 ## dom (Σ1 ∪ ΣC) →
              lc_succ n' T Σ2 ΣC' C2 E2 W' (Σ1 ∪ ΣC) p1').
    { intros p1' Hp Hd. destruct (Ha1 p1' Hp Hd) as (_ & HΦ).
      intros Σ1' Σ2' ΣC1 ΣC2 C0' C1' E1' HΣa Hq HΣb Hok'.
      eapply (HΦ W2 _ TB (C2, E2) HP2b); [exact HΣa|exact Hq|exact HΣb|done|done|by left|exact HW2'|exact Hok']. }
    assert (HQ2 : ∀ cd p2', proc_step (C2, E2) (PSess (SLink cd)) p2' →
              Plink_case (λ W0 Σb _ q, lc_succ n' T Σ1 ΣC C1 E1 W0 Σb q) W' (Σ2 ∪ ΣC') TB cd p2').
    { intros cd p2' Hst. eapply Plink_case_mono; [|exact (Hl2 cd p2' Hst)].
      intros Σb' [_ HΦ] Σ2' Σ1' ΣC2 ΣC1 C0' C2' E2' HΣb Hq HΣa Hok'.
      pose proof (cut_ok_sym _ _ _ _ _ _ _ _ Hok') as Hok''.
      pose proof (HΦ W' Σ1' Σ2' ΣC1 ΣC2 C0' C1 C2' E1 E2' HΣa eq_refl HΣb Hq Hty HW1' (wext_r_refl _) Hok'')
        as HP.
      rewrite (co_union_comm _ _ _ _ _ _ _ _ Hok''), union3_comm, (comm_L (⊎) E1 E2') in HP. exact HP. }
    assert (HA2 : ∀ p2', padmin (C2, E2) p2' → p2'.1 ## dom (Σ2 ∪ ΣC') →
              lc_succ n' T Σ1 ΣC C1 E1 W' (Σ2 ∪ ΣC') p2').
    { intros p2' Hp Hd. destruct (Ha2 p2' Hp Hd) as (_ & HΦ).
      intros Σ2' Σ1' ΣC2 ΣC1 C0' C2' E2' HΣb Hq HΣa Hok'.
      pose proof (cut_ok_sym _ _ _ _ _ _ _ _ Hok') as Hok''.
      pose proof (HΦ W' Σ1' Σ2' ΣC1 ΣC2 C0' C1 C2' E1 E2' HΣa eq_refl HΣb Hq Hty HW1' (wext_r_refl _) Hok'')
        as HP.
      rewrite (co_union_comm _ _ _ _ _ _ _ _ Hok''), union3_comm, (comm_L (⊎) E1 E2') in HP. exact HP. }
    pose proof (ctys_sym _ _ _ Hty) as Hty'. pose proof (cut_ok_sym _ _ _ _ _ _ _ _ Hok) as Hok'.
    assert (Σ2 ∪ Σ1 = Σ1 ∪ Σ2) as HΣs by (symmetry; apply (co_union_comm _ _ _ _ _ _ _ _ Hok)).
    assert (C2 ∪ C1 ∪ C0 = C1 ∪ C2 ∪ C0) as HCs by apply union3_comm.
    assert (E2 ⊎ E1 = E1 ⊎ E2) as HEs by apply (comm_L (⊎)).
    pose proof (co_d1 _ _ _ _ _ _ _ _ Hok) as Hd1. pose proof (co_d2 _ _ _ _ _ _ _ _ Hok) as Hd2.
    pose proof (co_dom _ _ _ _ _ _ _ _ Hok) as HC0. pose proof (co_dom' _ _ _ _ _ _ _ _ Hok) as HC0'.
    pose proof (co_C1Σ2 _ _ _ _ _ _ _ _ Hok) as HC1Σ2. pose proof (co_C2Σ1 _ _ _ _ _ _ _ _ Hok) as HC2Σ1.
    pose proof (co_C1Σ1 _ _ _ _ _ _ _ _ Hok) as HC1Σ1. pose proof (co_C2Σ2 _ _ _ _ _ _ _ _ Hok) as HC2Σ2.
    pose proof (co_C10 _ _ _ _ _ _ _ _ Hok) as HC10. pose proof (co_C20 _ _ _ _ _ _ _ _ Hok) as HC20.
    pose proof (co_C12 _ _ _ _ _ _ _ _ Hok) as HC12.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct (ctys_roots _ _ _ Hty) as [HrA HrB].
    assert (HrΣ : senv_roots (Σ1 ∪ Σ2) ⊆ senv_roots (Σ1 ∪ ΣC) ∪ senv_roots (Σ2 ∪ ΣC')).
    { pose proof (senv_roots_union Σ1 Σ2).
      pose proof (senv_roots_union_sub Σ1 ΣC Hd1). pose proof (senv_roots_union_sub Σ2 ΣC' Hd2).
      set_solver. }
    split_and!.
    - (* P-Stop *)
      destruct Hty as [[-> ->]|[-> ->]].
      + exact (lc_conn_stop n' T HT W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + intros Hirr. pose proof (lc_conn_stop n' T HT W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        rewrite HΣs, HCs, HEs in H. by apply H.
    - (* P-Step *)
      intros _. destruct Hty as [[-> ->]|[-> ->]].
      + exact (lc_conn_ready n' T HT W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + pose proof (lc_conn_ready n' T HT W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        by rewrite HΣs, HCs, HEs in H.
    - (* Q-Admin: by the inductions on the τ layers *)
      intros q' Hq Hd. simpl in Hd.
      apply padmin_inv in Hq as
        [ (F & e & e' & HE & Hs & ->)
        | [ (F & e & c & yp & e' & HE & Hs & HcC & HcF & Hce & ->)
        | [ (F & e & v & e' & HE & Hs & ->)
        | (C' & E & e & c & bc & d & bd & e' & Heq & Hst & HcC & ->) ]]]; simpl in Hd; rewrite ?dom_union_L in Hd.
      4: { (* link, a τ at the index *)
        injection Heq as <- HE.
        destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        + exact (lc2_link_give n' T HT W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA Hok HP1 HQ1 HA1
                   F1 e c bc d bd e' HE1 Hst HcC).
        + pose proof (lc2_link_give n' T HT W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB Hok' HP2 HQ2 HA2
                        F2 e c bc d bd e' HE2 Hst ltac:(by rewrite HCs)) as H.
          rewrite HΣs, HCs in H.
          assert (F2 ⊎ E1 ⊎ {[+ e' +]} = E1 ⊎ F2 ⊎ {[+ e' +]}) as <- by multiset_solver. exact H. }
      + destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        * destruct (Ha1 (C1, F1 ⊎ {[+ e' +]}) ltac:(rewrite HE1; by apply PABeta)
                      ltac:(simpl; rewrite dom_union_L, HC0; set_solver))
            as (_ & HΦ).
          assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
          eapply (HΦ W2 _ TB (C2, E2) HP2b); try done.
          all: try (by left).
          all: try (exact HW2').
          all: try (exact Hok).
        * destruct (Ha2 (C2, F2 ⊎ {[+ e' +]}) ltac:(rewrite HE2; by apply PABeta)
                      ltac:(simpl; rewrite dom_union_L, HC0'; set_solver))
            as (_ & HΦ).
          assert (E1 ⊎ F2 ⊎ {[+ e' +]} = E1 ⊎ (F2 ⊎ {[+ e' +]})) as -> by multiset_solver.
          eapply HΦ; try done.
          all: try (exact HW1').
          all: try (by left).
          all: try (exact Hok).
      +
        destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        * rewrite echans_disj_union in HcF.
          destruct (Ha1 (C1 ∪ {[c]}, F1 ⊎ {[+ e' +]})
                      ltac:(rewrite HE1; eapply PANew; [done|set_solver|set_solver|done])
                      ltac:(simpl; rewrite dom_union_L, HC0; set_solver))
            as (_ & HΦ).
          assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
          assert (C1 ∪ C2 ∪ C0 ∪ {[c]} = C1 ∪ {[c]} ∪ C2 ∪ C0) as -> by set_solver.
          eapply (HΦ W2 _ TB (C2, E2) HP2b); try done.
          all: try (by left).
          all: try (exact HW2').
          all: try (apply cut_ok_new1; [exact Hok|set_solver..]).
        * rewrite echans_disj_union in HcF.
          destruct (Ha2 (C2 ∪ {[c]}, F2 ⊎ {[+ e' +]})
                      ltac:(rewrite HE2; eapply PANew; [done|set_solver|set_solver|done])
                      ltac:(simpl; rewrite dom_union_L, HC0'; set_solver))
            as (_ & HΦ).
          assert (E1 ⊎ F2 ⊎ {[+ e' +]} = E1 ⊎ (F2 ⊎ {[+ e' +]})) as -> by multiset_solver.
          assert (C1 ∪ C2 ∪ C0 ∪ {[c]} = C1 ∪ (C2 ∪ {[c]}) ∪ C0) as -> by set_solver.
          eapply HΦ; try done.
          all: try (exact HW1').
          all: try (by left).
          all: try (apply cut_ok_sym, cut_ok_new1; [exact Hok'|set_solver..]).
      + destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        * destruct (Ha1 (C1, F1 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}) ltac:(rewrite HE1; by apply PASpawn)
                      ltac:(simpl; rewrite dom_union_L, HC0; set_solver))
            as (_ & HΦ).
          assert (F1 ⊎ E2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]} =
                  (F1 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}) ⊎ E2) as -> by multiset_solver.
          eapply (HΦ W2 _ TB (C2, E2) HP2b); try done.
          all: try (by left).
          all: try (exact HW2').
          all: try (exact Hok).
        * destruct (Ha2 (C2, F2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}) ltac:(rewrite HE2; by apply PASpawn)
                      ltac:(simpl; rewrite dom_union_L, HC0'; set_solver))
            as (_ & HΦ).
          assert (E1 ⊎ F2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]} =
                  E1 ⊎ (F2 ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})) as -> by multiset_solver.
          eapply HΦ; try done.
          all: try (exact HW1').
          all: try (by left).
          all: try (exact Hok).
    - (* Q-Comm *)
      intros q' Hq.
      destruct (decide (n' = 0)) as [Hn0|Hn0].
      { intros Hd. rewrite Hn0. apply LPrel_0. }
      assert (∃ n'', n' = S n'') as [n'' Hn] by (exists (pred n'); lia).
      apply pcomm_inv in Hq as
        [ (F & c & β & v & e & e' & f & f' & HE & Hs1 & Hs2 & ->)
        | [ (F & c & β & e & e' & f & f' & HE & Hs1 & Hs2 & HcC & ->)
        | (F & c & β & i & e & e' & f & f' & HE & Hs1 & Hs2 & ->) ]].
      + destruct (gmultiset_split_in2 _ _ _ _ _ HE)
          as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
        * exact (lc2_tau_msg n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 c β v e e' f f' HE1 Hs1 Hs2).
        * eapply LPtau_case_conv; [exact HΣs| |exact (lc2_tau_msg n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                   E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 c β v e e' f f' HE2 Hs1 Hs2)].
          f_equal; [done|clear -HΣs; multiset_solver].
        * exact (lc2_cross_msg n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 F2 e e' f f' c β v HE1 HE2 Hs1 Hs2).
        * eapply LPtau_case_conv; [exact HΣs| |exact (lc2_cross_msg n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                   E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 F1 e e' f f' c β v HE2 HE1 Hs1 Hs2)].
          f_equal; [done|clear -HΣs; multiset_solver].
      + destruct (gmultiset_split_in2 _ _ _ _ _ HE)
          as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
        * destruct (decide (c ∈ C1)) as [Hc1|Hc1].
          -- exact (lc2_tau_close n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                      F1 c β e e' f f' HE1 Hs1 Hs2 Hc1).
          -- exfalso. exact (lc2_own_close_contra n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok
                               HP1 HP2 HP1n HP2n n'' Hn F1 e e' f f' c β (negb β) HE1 Hs1 Hs2 Hc1).
        * destruct (decide (c ∈ C2)) as [Hc2|Hc2].
          -- eapply LPtau_case_conv; [exact HΣs| |exact (lc2_tau_close n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 c β e e' f f' HE2 Hs1 Hs2 Hc2)].
             f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
          -- exfalso. exact (lc2_own_close_contra n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hty' Hok'
                               HP2 HP1 HP2n HP1n n'' Hn F2 e e' f f' c β (negb β) HE2 Hs1 Hs2 Hc2).
        * exact (lc2_cross_close n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 F2 e e' f f' c β HE1 HE2 Hs1 Hs2).
        * eapply LPtau_case_conv; [exact HΣs| |exact (lc2_cross_close n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                   E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 F1 e e' f f' c β HE2 HE1 Hs1 Hs2)].
          f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
      + destruct (gmultiset_split_in2 _ _ _ _ _ HE)
          as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
        * exact (lc2_tau_choice n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 c β i e e' f f' HE1 Hs1 Hs2).
        * eapply LPtau_case_conv; [exact HΣs| |exact (lc2_tau_choice n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                   E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 c β i e e' f f' HE2 Hs1 Hs2)].
          f_equal; [done|clear -HΣs; multiset_solver].
        * exact (lc2_cross_choice n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 F2 e e' f f' c β i HE1 HE2 Hs1 Hs2).
        * eapply LPtau_case_conv; [exact HΣs| |exact (lc2_cross_choice n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1
                   E2 E1 TB TA Hty' Hok' HP2 HP1 HP2n HP1n F2 F1 e e' f f' c β i HE2 HE1 Hs1 Hs2)].
          f_equal; [done|clear -HΣs; multiset_solver].
    - (* Q-Link: an external link, at the index *)
      intros cd q' Hst.
      apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & Hsub & ->).
      destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
      + exact (lc2_ext_link n' T HT W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA Hok HP1 HQ1 HA1
                 F1 e cd e' HE1 Hs Hsub).
      + rewrite <-HCs in Hsub.
        eapply Plink_case_conv; [exact HΣs| |exact (lc2_ext_link n' T HT W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB
                   Hok' HP2 HQ2 HA2 F2 e cd e' HE2 Hs Hsub)].
        f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
    - (* Q-σ *)
      intros σ q' Hst.
      apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & Hsub & ->).
      destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
      + destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; simpl in Hsub.
        * exact (lc_ext_recv n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 e c β w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
        * exact (lc_ext_send n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 e c β w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
        * exact (lc_ext_close n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 e c β e' HE1 Hs ltac:(clear -Hsub; set_solver)).
        * exact I.
        * exact (lc_ext_sel n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 e c β i e' HE1 Hs ltac:(clear -Hsub; set_solver)).
        * exact (lc_ext_bra n' T HT IHo W' Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2 HP1n HP2n
                   F1 e c β i e' HE1 Hs ltac:(clear -Hsub; set_solver)).
      + rewrite <-HCs in Hsub.
        destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; simpl in Hsub.
        * eapply LPobl_conv; [exact HΣs| | |exact (lc_ext_recv n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA
                   Hty' Hok' HP2 HP1 HP2n HP1n F2 e c β w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
            [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
        * eapply LPobl_conv; [exact HΣs| | |exact (lc_ext_send n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA
                   Hty' Hok' HP2 HP1 HP2n HP1n F2 e c β w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
            [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
        * eapply LPobl_conv; [exact HΣs| | |exact (lc_ext_close n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA
                   Hty' Hok' HP2 HP1 HP2n HP1n F2 e c β e' HE2 Hs ltac:(clear -Hsub; set_solver))];
            [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
        * exact I.
        * eapply LPobl_conv; [exact HΣs| | |exact (lc_ext_sel n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA
                   Hty' Hok' HP2 HP1 HP2n HP1n F2 e c β i e' HE2 Hs ltac:(clear -Hsub; set_solver))];
            [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
        * eapply LPobl_conv; [exact HΣs| | |exact (lc_ext_bra n' T HT IHo W' Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA
                   Hty' Hok' HP2 HP1 HP2n HP1n F2 e c β i e' HE2 Hs ltac:(clear -Hsub; set_solver))];
            [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
  Qed.
End lassembly.

(** ** P-Connect at two worlds *)

Lemma lconn_two n : ∀ T, prim T →
  ∀ W1 W2 W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB,
    ctys TA TB T → wext_r W1 W → wext_r W2 W → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    LPrel n W1 (Σ1 ∪ ΣC) TA (C1, E1) → LPrel n W2 (Σ2 ∪ ΣC') TB (C2, E2) →
    LPrel n W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Proof.
  induction n as [n IHn] using lt_wf_ind. intros T HT.
  destruct n as [|n'].
  { intros. apply LPrel_0. }
  assert (IHo : ∀ j, j ≤ n' → lconn_at j T).
  { intros j Hj W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2.
    eapply (IHn j ltac:(lia) T HT W W W); [done|by left|by left|done|done|done]. }
  intros W1 W2 W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty HW1 HW2 Hok HP1 HP2.
  exact (lconn_level n' T HT IHo W1 _ TA _ HP1 W2 _ TB _ HP2 W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2
           eq_refl eq_refl eq_refl eq_refl Hty HW1 HW2 Hok).
Qed.

Lemma lconn_all n T : prim T → lconn_at n T.
Proof.
  intros HT W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2.
  eapply (lconn_two n T HT W W W); [done|by left|by left|done|done|done].
Qed.

(** P-Connect (§11), [Prel_connect] with LPrel in place of Prel. *)
Theorem LPrel_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  prim T →
  (∀ n, LPrel n W1 (Σ1 ∪ ΣC) T (C1, E1)) → (∀ n, LPrel n W2 (Σ2 ∪ ΣC') TUnit (C2, E2)) →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  strict (wjoin W1 W2) → world_wf W1 → world_wf W2 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  ∀ n, LPrel n (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Proof.
  intros HT HP1 HP2 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HW HW1 HW2 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 n.
  apply (lconn_two n T HT W1 W2 (wjoin W1 W2) Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T TUnit).
  - by left.
  - right. by apply wext_join_l'.
  - right. by apply wext_join_r'.
  - by split.
  - apply HP1.
  - apply HP2.
Qed.

(** P-Join: P-Connect for two components typed at their own worlds is
    [LPrel_connect]; the statement of [fundamental_join]'s semantic step. *)
Corollary LPrel_join W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  prim T →
  (∀ n, LPrel n W1 (Σ1 ∪ ΣC) T (C1, E1)) → (∀ n, LPrel n W2 (Σ2 ∪ ΣC') TUnit (C2, E2)) →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  strict W1 → strict W2 →
  strict (wjoin (wrestrict W1 (w_names W1 ∩ w_names W2))
                (wrestrict W2 (w_names W1 ∩ w_names W2))) →
  ∀ n, LPrel n (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Proof.
  intros HT HP1 HP2 HC0 HC0' Hcut HC1Σ2 HC2Σ1 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 HS1 HS2 HA.
  assert (strict (wjoin W1 W2)) as HJ by (by apply amalgamation).
  eapply LPrel_connect; try done; [apply HS1|apply HS2].
Qed.
