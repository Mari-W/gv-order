(** * P-Connect (§11)

    Two components P-related in the same world compose over a cut C₀,
    and components at n give the composite at n (sharp edges 45).
    [conn_level] assembles the step cases of ConnectCut.v and
    ConnectSteps.v. [Prel_connect] reaches the world W₁ ⊔ W₂ by
    monotonicity. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export composition.ConnectSteps.

(** Branch no-eq: [w_eq W] abbreviates equality and leaves W untyped. *)
Implicit Types W : world.


(** Section lemmas take every section variable, so that both
    orientations of a configuration can be passed uniformly. *)
Set Default Proof Using "All".

(** ** Assembly *)

Lemma Ptau_case_conv X W Σ Σ' T p q :
  Σ = Σ' → p = q → Ptau_case X W Σ T p → Ptau_case X W Σ' T q.
Proof. by intros -> ->. Qed.

Lemma Pcase_conv X n' W Σ Σ' T p q π p' q' :
  Σ = Σ' → p = q → p' = q' → Pcase_gen X n' W Σ T p π p' → Pcase_gen X n' W Σ' T q π q'.
Proof. by intros -> -> ->. Qed.

Section assembly.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → conn_at j T).
  Context (m : nat) (IHi : conn_lt (S n') T m).

  Lemma conn_level W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB :
    msize (E1 ⊎ E2) = m → ctys TA TB T → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    Prel (S n') W (Σ1 ∪ ΣC) TA (C1, E1) → Prel (S n') W (Σ2 ∪ ΣC') TB (C2, E2) →
    Prel (S n') W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
  Proof.
    intros Hm Hty Hok HP1 HP2.
    assert (msize (E2 ⊎ E1) = m) as Hm' by (by rewrite (comm_L (⊎))).
    pose proof (ctys_sym _ _ _ Hty) as Hty'. pose proof (cut_ok_sym _ _ _ _ _ _ _ _ Hok) as Hok'.
    assert (Σ2 ∪ Σ1 = Σ1 ∪ Σ2) as HΣs by (symmetry; apply (co_union_comm _ _ _ _ _ _ _ _ Hok)).
    assert (C2 ∪ C1 ∪ C0 = C1 ∪ C2 ∪ C0) as HCs by apply union3_comm.
    assert (E2 ⊎ E1 = E1 ⊎ E2) as HEs by apply (comm_L (⊎)).
    assert (Hgive : ∀ p', ptau_link (C1 ∪ C2 ∪ C0, E1 ⊎ E2) p' → Prel (S n') W (Σ1 ∪ Σ2) T p').
    { intros p' (C' & E & e & c & bc & d & bd & e' & Heq & Hst & HcC & ->). injection Heq as <- HE.
      destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
      - exact (link_give n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                 F1 e c bc d bd e' HE1 Hst HcC).
      - pose proof (link_give n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c bc d bd e' HE2 Hst ltac:(by rewrite HCs)) as H.
        rewrite HΣs, HCs in H.
        assert (F2 ⊎ E1 ⊎ {[+ e' +]} = E1 ⊎ F2 ⊎ {[+ e' +]}) as <- by multiset_solver. exact H. }
    apply Prel_S_intro.
    - destruct Hty as [[-> ->]|[-> ->]].
      + exact (conn_stop n' T HT W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + intros Hirr. pose proof (conn_stop n' T HT W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        rewrite HΣs, HCs, HEs in H. by apply H.
    - intros _. destruct Hty as [[-> ->]|[-> ->]].
      + exact (conn_ready n' T HT W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 Hok HP1 HP2).
      + pose proof (conn_ready n' T HT W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 Hok' HP2 HP1) as H.
        by rewrite HΣs, HCs, HEs in H.
    - intros π p' Hst. destruct π as [|σ].
      + simpl. split; [|intros Hl _; by apply Hgive].
        pose proof Hst as Hst0.
        apply ptau_inv in Hst as [(F & e & e' & HE & Hs & ->)
          |[(F & e & c & x & e' & HE & Hs & HcC & HcF & Hce & ->)
          |[(F & e & v & e' & HE & Hs & ->)
          |[(F & c & β & v & e & e' & f & f' & HE & Hs1 & Hs2 & ->)
          |[(F & c & β & e & e' & f & f' & HE & Hs1 & Hs2 & HcC & ->)
          |[(F & e & c & bc & d & bd & e' & HE & Hs & HcC & ->)
          |(F & c & β & i & e & e' & f & f' & HE & Hs1 & Hs2 & ->)]]]]]].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_beta n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e e' HE1 Hs).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_beta n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e e' HE2 Hs)].
             f_equal; [done|clear -HΣs; multiset_solver].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_new n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c x e' HE1 Hs HcC HcF Hce).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_new n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e c x e' HE2 Hs ltac:(by rewrite HCs)
                      ltac:(by rewrite (comm_L (⊎) F2)) Hce)].
             f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
        * destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
          -- exact (tau_spawn n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e v e' HE1 Hs).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_spawn n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 e v e' HE2 Hs)].
             f_equal; [done|clear -HΣs; multiset_solver].
        * destruct (gmultiset_split_in2 _ _ _ _ _ HE)
            as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
          -- exact (tau_msg n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 c β v e e' f f' HE1 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_msg n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 c β v e e' f f' HE2 Hs1 Hs2)].
             f_equal; [done|clear -HΣs; multiset_solver].
          -- exact (cross_msg n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 F2 e e' f f' c β v HE1 HE2 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (cross_msg n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 F1 e e' f f' c β v HE2 HE1 Hs1 Hs2)].
             f_equal; [done|clear -HΣs; multiset_solver].
        * destruct (gmultiset_split_in2 _ _ _ _ _ HE)
            as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
          -- exact (tau_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 c β e e' f f' HE1 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 c β e e' f f' HE2 Hs1 Hs2)].
             f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
          -- exact (cross_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 F2 e e' f f' c β HE1 HE2 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (cross_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 F1 e e' f f' c β HE2 HE1 Hs1 Hs2)].
             f_equal; [by rewrite HCs|clear -HΣs; multiset_solver].
        * intros Hg.
          eapply Prel_down; [|apply Hgive]; [lia|].
          exists (C1 ∪ C2 ∪ C0), F, e, c, bc, d, bd, e'. by rewrite HE.
        * destruct (gmultiset_split_in2 _ _ _ _ _ HE)
            as [(F1 & HE1 & ->)|[(F2 & HE2 & ->)|[(F1 & F2 & HE1 & HE2 & ->)|(F1 & F2 & HE1 & HE2 & ->)]]].
          -- exact (tau_choice n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 c β i e e' f f' HE1 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (tau_choice n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 c β i e e' f f' HE2 Hs1 Hs2)].
             f_equal; [done|clear -HΣs; multiset_solver].
          -- exact (cross_choice n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 F2 e e' f f' c β i HE1 HE2 Hs1 Hs2).
          -- eapply Ptau_case_conv; [exact HΣs| |exact (cross_choice n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1
                      E2 E1 TB TA Hm' Hty' Hok' HP2 HP1 F2 F1 e e' f f' c β i HE2 HE1 Hs1 Hs2)].
             f_equal; [done|clear -HΣs; multiset_solver].
      + apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & Hsub & ->).
        destruct (gmultiset_split_in _ _ _ _ HE) as [(F1 & HE1 & ->)|(F2 & HE2 & ->)].
        * destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; simpl in Hsub.
          -- exact (ext_recv n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c β w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_send n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c β w e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_close n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c β e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_link n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e cd e' HE1 Hs Hsub).
          -- exact (ext_sel n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c β i e' HE1 Hs ltac:(clear -Hsub; set_solver)).
          -- exact (ext_bra n' T HT IHo m IHi W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hm Hty Hok HP1 HP2
                      F1 e c β i e' HE1 Hs ltac:(clear -Hsub; set_solver)).
        * rewrite <-HCs in Hsub.
          destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; simpl in Hsub.
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_recv n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c β w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_send n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c β w e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_close n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c β e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_link n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e cd e' HE2 Hs Hsub)];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_sel n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c β i e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
          -- eapply Pcase_conv; [exact HΣs| | |exact (ext_bra n' T HT IHo m IHi W Σ2 Σ1 ΣC' ΣC C0 C2 C1 E2 E1 TB TA Hm' Hty' Hok' HP2 HP1
                      F2 e c β i e' HE2 Hs ltac:(clear -Hsub; set_solver))];
               [first [by rewrite HCs, HEs|reflexivity]|f_equal; [by rewrite HCs|clear -HΣs; multiset_solver]].
  Qed.
End assembly.

(** ** P-Connect *)

Lemma conn_all n : ∀ T, prim T → conn_at n T.
Proof.
  induction n as [n IHn] using lt_wf_ind. intros T HT.
  destruct n as [|n'].
  { intros ? ? ? ? ? ? ? ? ? ? ? ? _ _ _ _. apply Prel_0. }
  assert (IHo : ∀ j, j ≤ n' → conn_at j T) by (intros j Hj; apply IHn; [lia|done]).
  assert (∀ m, conn_lt (S n') T m) as Hlt.
  { intros m. induction m as [m IHm] using lt_wf_ind.
    intros W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hsz Hty Hok HP1 HP2.
    exact (conn_level n' T HT IHo (msize (E1 ⊎ E2)) (IHm _ Hsz)
             W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB eq_refl Hty Hok HP1 HP2). }
  intros W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB Hty Hok HP1 HP2.
  exact (Hlt (S (msize (E1 ⊎ E2))) W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB (Nat.lt_succ_diag_r _)
           Hty Hok HP1 HP2).
Qed.

Lemma wext_join_l' W1 W2 : strict (wjoin W1 W2) → wext W1 (wjoin W1 W2).
Proof.
  intros H. split_and!; try done; [simpl; set_solver|apply wjoin_l].
Qed.

Lemma wext_join_r' W1 W2 : strict (wjoin W1 W2) → wext W2 (wjoin W1 W2).
Proof.
  intros H. split_and!; try done; [simpl; set_solver|apply wjoin_r].
Qed.

(** P-Connect (§11). Component 1 runs at T, component 2 at ∗, and they
    share the cut C₀: Σ_C and Σ_C′ hold the two ends of each channel of
    C₀, dual and at dual points of W₁ ⊔ W₂ (end points). The remaining premises
    are the spec's implicit well-formedness: worlds well formed, and the
    restricted sets and the interfaces pairwise disjoint. *)
Theorem Prel_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  prim T →
  sem_ptyped W1 (Σ1 ∪ ΣC) (C1, E1) T → sem_ptyped W2 (Σ2 ∪ ΣC') (C2, E2) TUnit →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  strict (wjoin W1 W2) → world_wf W1 → world_wf W2 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  sem_ptyped (wjoin W1 W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.
Proof.
  intros HT HP1 HP2 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HW HW1 HW2 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 n.
  apply (conn_all n T HT (wjoin W1 W2) Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T TUnit).
  - by left.
  - by split.
  - eapply (Prel_mono n W1); [done|by apply wext_join_l'|apply HP1].
  - eapply (Prel_mono n W2); [done|by apply wext_join_r'|apply HP2].
Qed.
