(** * Internalizing a link for the live relation (composition/Internalize.v)

    A process holding one end each of two channels c and d, dual and at
    dual points, stays related when d is restricted and c is renamed to
    d. Index preserving: a synchronization of the fused process on d
    costs two, and it is a send of p on one end, at cost one, followed
    by a receive on the other, at cost one (liveness.md §2). β, new and
    spawn of the fused process are those of p at cost zero, read by
    induction on the τ layer of p. So is a link: a link τ of the fused
    process is an internal or an external link of p, both at cost zero
    (lock-freedom plan §6.1). The environment and stepping lemmas
    are reused from Internalize.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveEconv composition.Internalize.

Local Set Warnings "-register-all".
Implicit Types W : world.

Local Ltac sset :=
  repeat match goal with
    | H : ?P |- _ =>
        lazymatch P with
        | context [LPrel] => clear H
        | context [LPobl] => clear H
        | context [LPtau_case] => clear H
        | context [proc_step] => clear H
        | context [LVrel] => clear H
        | context [tstep] => clear H
        | context [recv_ok] => clear H
        | context [ready_p] => clear H
        end
    end; set_solver.

Lemma LVrel_prim_empty n W Θ T v : prim T → LVrel n W Θ T v → Θ = ∅.
Proof.
  intros Hp. revert Θ v. induction Hp as [|T1 U H1 IH1 H2 IH2|T1 U H1 IH1 H2 IH2|m k C T1]; intros Θ v.
  - by intros [-> _]%LVrel_unit_iff.
  - intros (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & HV1 & HV2)%LVrel_prod_iff.
    rewrite (IH1 _ _ HV1), (IH2 _ _ HV2) in Hj. by apply tenv_join_empty.
  - intros [(v' & -> & H)|(v' & -> & H)]%LVrel_sum_iff; eauto.
  - apply LVrel_box_empty.
Qed.

Lemma int_ok_wext c d W W1 Σ sc sd kc kd C :
  wext_r W W1 → int_ok c d W Σ sc sd kc kd C → int_ok c d W1 Σ sc sd kc kd C.
Proof.
  intros [->|Hx] H; [done|]. destruct H as (HW & ? & ? & ? & ? & ? & ?).
  split_and!; try done. by destruct Hx as (_ & _ & _ & ?).
Qed.

Section linternalize.
  Context (c d : chan) (Hcd : c ≠ d).
  Local Notation int_ok := (composition.Internalize.int_ok c d).

  Definition lfuse_goal (m : nat) (W : world) (Σp : senv) (T : ty) (p : proc) : Prop :=
    ∀ Σ C E sc sd kc kd, Σp = fusedP c d Σ sc sd kc kd → p = (C, E) →
      int_ok W Σ sc sd kc kd C → LPrel m W Σ T (C ∪ {[d]}, echsubst c d E).

  Section lstep.
    Context (n' : nat) (T : ty) (HT : prim T)
      (IH : ∀ j, j ≤ n' → ∀ W Σp p, LPrel j W Σp T p → lfuse_goal j W Σp T p).
    Context (W : world) (Σ : senv) (sc sd : sty) (kc kd : point)
      (C : gset chan) (E : gmultiset expr).
    Context (HW : strict W) (HcΣ : c ∉ dom Σ) (HdΣ : d ∉ dom Σ) (HcC : c ∉ C)
      (HdC : d ∉ C) (Hdu : sdual sc sd) (Hal : w_eq W kc (pt_dual kd)).
    Local Notation Σp := (fusedP c d Σ sc sd kc kd).
    Local Notation q := (C ∪ {[d]}, echsubst c d E).
    Context (Hσ : ∀ σ p', proc_step (C, E) (PSess σ) p' →
      LPobl LVrel LPrel (S n') W Σp T (C, E) σ p').
    Context (Hcm : ∀ p', pcomm (C, E) p' → LPtau_case (LPrel (pred n')) W Σp T p').
    Context (Hlx : ∀ cd p', proc_step (C, E) (PSess (SLink cd)) p' →
      Plink_case (λ W Σ T p, LPrel (S n') W Σ T p ∧ lfuse_goal (S n') W Σ T p) W Σp T cd p').
    Context (Hadm : ∀ p', padmin (C, E) p' → p'.1 ## dom Σp → lfuse_goal (S n') W Σp T p').

    Lemma li_int_ok_ext W' Σ' C' :
      wext W W' → c ∉ dom Σ' → d ∉ dom Σ' → c ∉ C' → d ∉ C' → int_ok W' Σ' sc sd kc kd C'.
    Proof.
      intros Hx ????. split_and!; try done.
      all: by destruct Hx as (_ & _ & _ & ?).
    Qed.

    Lemma li_ext_recv a w' q' :
      proc_step q (PSess (SRecv a w')) q' →
      LPobl LVrel LPrel (S n') W Σ T q (SRecv a w') q'.
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
      pose proof (Hσ _ _ (PStepSession C F e (SRecv a (eswap c z w')) f Hf
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
      { rewrite <-(LVrel_fchans _ _ _ _ _ HVw). clear -Hz. set_solver. }
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
                    (LVrel_swap c z _ _ _ _ _ HVw)).
      apply (IH j Hj) in HP1.
      specialize (HP1 (recv_env Σr Θ2p) _ _ sc sd kc kd eq_refl eq_refl).
      match type of HP1 with ?A → _ => assert A as Hok' end.
      { pose proof (dom_recv_env Σr Θ2p) as Hd1. pose proof (recv_back_dom Σr Θ2p) as Hd2.
        apply li_int_ok_ext; [done|clear -Hd1 Hd2 HcΣr HdΣr HcΘ HdΘ HcC HdC; set_solver..]. }
      specialize (HP1 Hok').
      apply (LPrel_swap c z) in HP1. unfold pswap in HP1. simpl in HP1. unfold Θ2p in HP1.
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

    Lemma li_ext_close a q' :
      proc_step q (PSess (SClos a)) q' →
      LPobl LVrel LPrel (S n') W Σ T q (SClos a) q'.
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
      pose proof (Hσ _ _ (PStepSession C F e (SClos a) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp. destruct Hp as (Σ1 & k & (s0 & HΣ & Hu) & Ha1 & HP1).
      pose proof (IH n' (le_n _) W _ _ HP1) as HΦ.
      destruct (fusedP_peel c d Hcd Σ sc sd kc kd Σ1 a (s0, k) HcΣ HdΣ Hc0c Had HΣ Ha1)
        as [-> HΣ'].
      exists (delete a Σ), k. split_and!.
      { by exists s0. }
      { rewrite dom_delete_L. clear. set_solver. }
      cbn [sentc] in HΦ. rewrite difference_empty_L in HΦ.
      pose proof (HΦ (delete a Σ) _ _ sc sd kc kd eq_refl eq_refl) as HP.
      rewrite echsubst_disj_union1 in HP. apply HP.
      apply li_int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_delete_L;
        clear -HcΣ HdΣ; set_solver.
    Qed.

    Lemma li_ext_sel a i q' :
      proc_step q (PSess (SSel a i)) q' →
      LPobl LVrel LPrel (S n') W Σ T q (SSel a i) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [LPobl Pchoice_case pred sentc fst snd].
      rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hσ _ _ (PStepSession C F e (SSel a i) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [LPobl Pchoice_case pred] in Hp.
      destruct Hp as (Σ1 & s1 & s2 & k & (s0 & HΣ & Hu) & Ha1 & HP1).
      pose proof (IH n' (le_n _) W _ _ HP1) as HΦ.
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
      apply li_int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_insert_L, dom_delete_L;
        clear -HcΣ HdΣ Hc0c Had; set_solver.
    Qed.

    Lemma li_ext_bra a i q' :
      proc_step q (PSess (SBra a i)) q' →
      LPobl LVrel LPrel (S n') W Σ T q (SBra a i) q'.
    Proof.
      intros Hq. apply proc_step_sess_inv in Hq as (F' & e1 & f' & HE & Hst & HsC & ->).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      cbn [subjs] in HsC. cbn [LPobl Pchoice_case pred sentc fst snd].
      rewrite difference_empty_L.
      apply tstep_chsubst_det_inv in Hst as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ c) as Hc0c.
      { intros ->. rewrite csub_hit in Hc0. subst a. clear -HsC. set_solver. }
      rewrite csub_ne in Hc0 by done. subst c0.
      assert (a ≠ d ∧ a ∉ C) as [Had HaC] by (clear -HsC; set_solver).
      pose proof (Hσ _ _ (PStepSession C F e (SBra a i) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [LPobl Pchoice_case pred] in Hp.
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
      apply li_int_ok_ext; [by apply wext_refl| | |done|done]; rewrite dom_insert_L, dom_delete_L;
        clear -HcΣ HdΣ Hc0c Had; set_solver.
    Qed.

    Lemma li_ext_link cd q' :
      proc_step q (PSess (SLink cd)) q' →
      Plink_case (LPrel (S n')) W Σ T cd q'.
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
      pose proof (Hlx _ _ (PStepSession C F e (SLink cd0) f Hf
                    ltac:(cbn [subjs]; clear -HsC; set_solver))) as Hp.
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
      apply li_int_ok_ext; [by apply wext_refl| | |done|done]; rewrite !dom_delete_L;
        clear -HcΣ HdΣ; set_solver.
    Qed.

    Lemma li_ext_send a w' q' :
      proc_step q (PSess (SSend a w')) q' →
      LPobl LVrel LPrel (S n') W Σ T q (SSend a w') q'.
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
      pose proof (Hσ _ _ (PStepSession C F e (SSend a w0) f Hf
                    ltac:(cbn [subjs]; clear -HaC; set_solver))) as Hp.
      cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp.
      destruct Hp as (Σ0 & Σv & m & U & s & k & Σe & Θe & (s0 & HΣ & Hu) & Hdj & Ha0 & Hav &
                      Hdom & Hsplit & HdΘΣ & HV & HP1).
      pose proof (IH n' (le_n _) W _ _ HP1) as HΦ.
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
      { rewrite (LVrel_fchans _ _ _ _ _ HV), dom_union_L. unfold tenv_of. by rewrite dom_fmap_L. }
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
          * apply li_int_ok_ext; [by apply wext_refl| | |clear -HcC; set_solver|clear -HdC; set_solver];
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
            rewrite lookup_insert_eq. split_and!; [done|by apply eq_dual_sym|by apply sdual_sym].
          * rewrite lookup_insert_ne in Hr by done. destruct Hsplit as [_ Hs].
            specialize (Hs r o Hr). rewrite lookup_insert_ne by done. done.
        + rewrite dom_insert_L. clear -HΘeΣ HdΣ. set_solver.
        + apply (LVrel_rename _ _ _ _ _ c d) in HV.
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
          apply (LPrel_junk _ _ _ _ _ _ c d) in HP1.
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
        + apply (LPrel_junk _ _ _ _ _ _ d c) in HP1.
          * apply (LPrel_swap c d) in HP1. unfold pswap in HP1. simpl in HP1.
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
          apply (LVrel_fuse n' W (<[c := One (sc, kc)]> (<[d := One (sd, kd)]> M))
                   (<[d := Both (sc, kc) (sd, kd)]> M) _ w0 c d HW Hcd); [|exact HV].
          split_and!.
          * by simplify_map_eq.
          * intros y Hyc Hyd. by simplify_map_eq.
          * simplify_map_eq. constructor.
          * intros e1 e2 He1 He2. simplify_map_eq. done.
        + apply (LPrel_junk _ _ _ _ _ _ c d) in HP1.
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

    Lemma li_sync_case n'' (Hn : n' = S n'') F2 h h0 g g0 c0 c1 w0 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SSend c0 w0)) h0 → tstep g (LSess (SRecv c1 w0)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) → C ## dom Σ →
      LPrel n'' W Σ T (C ∪ {[d]}, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros -> Hh Hg Hcc HCΣ. destruct HW as [HWf _].
      assert (c0 ≠ c1 ∧ c0 ∉ C ∧ c1 ∉ C) as (Hc01 & Hc0C & Hc1C)
        by (destruct Hcc as [[-> ->]|[-> ->]]; split_and!; done).
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SSend c0 w0))
                (C ∖ sentc (SSend c0 w0), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hσ _ _ Hst1) as Hp. cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp.
      destruct Hp as (Σ0 & Σv & m & U & s & k & Σe & Θe & (s0 & HΣ & Hu) & Hdj & Ha0 & Hav &
                      Hdom & Hsplit & HdΘΣ & HV & HP1).
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
      rewrite Hn in HP1. pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst2) as Hp2. cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp2.
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
          + by apply eq_dual_sym. }
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
      assert (LVrel n'' W (tenv_of Σv ∪ Θe) (payload_at m U' k') w0) as HV2.
      { eapply LVrel_tconv; [done| |eapply LVrel_down; [|exact HV]; lia].
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
      pose proof (Hrecv W n'' (tenv_of Σv ∪ Θe) (wext_refl W HW) (le_n n'') Hg2 Sok HV2) as HP2.
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
        apply (IH n'' ltac:(lia) W _ _ HP2 Σ C _ s s' (pt_shift 1 kc) (pt_shift 1 kd));
          [done|done|].
        split_and!; try done. rewrite pt_dual_shift. by apply (wf_eq_shift _ HWf).
      - rewrite (fusedP_d c d Hcd) in E0. rewrite fusedP_c in E1.
        injection E0 as <- <-. injection E1 as <- <-.
        apply (IH n'' ltac:(lia) W _ _ HP2 Σ C _ s' s (pt_shift 1 kc) (pt_shift 1 kd));
          [|done|].
        + unfold fusedP. by rewrite insert_insert_ne.
        + split_and!; try done. rewrite pt_dual_shift. by apply (wf_eq_shift _ HWf).
    Qed.

    Lemma li_choice_case n'' (Hn : n' = S n'') F2 h h0 g g0 c0 c1 i :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SSel c0 i)) h0 → tstep g (LSess (SBra c1 i)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) →
      LPrel n'' W Σ T (C ∪ {[d]}, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros -> Hh Hg Hcc. pose proof (proj1 HW) as HWf.
      assert (c0 ≠ c1 ∧ c0 ∉ C ∧ c1 ∉ C) as (Hc01 & Hc0C & Hc1C)
        by (destruct Hcc as [[-> ->]|[-> ->]]; split_and!; done).
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SSel c0 i))
                (C ∖ sentc (SSel c0 i), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hσ _ _ Hst1) as Hp. cbn [LPobl Pchoice_case pred] in Hp.
      destruct Hp as (Σ1 & s1 & s2 & k & (s0 & HΣ & Hu) & Hc0Σ1 & HP1).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      assert (proc_step (C, F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) (PSess (SBra c1 i))
                (C ∖ sentc (SBra c1 i), F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Hst2.
      { replace (F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) with (F2 ⊎ {[+ h0 +]} ⊎ {[+ g +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc1C. set_solver. }
      rewrite Hn in HP1. pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst2) as Hp2.
      cbn [LPobl Pchoice_case pred] in Hp2.
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
        apply (IH n'' ltac:(lia) W _ _ HP2 Σ C _ (sbranch i s1 s2) (sbranch i r1 r2)
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
        apply (IH n'' ltac:(lia) W _ _ HP2 Σ C _ (sbranch i r1 r2) (sbranch i s1 s2)
                 (bra_pt kc i) (sel_pt kd i)); [|done|].
        + unfold fusedP. apply map_eq. intros y.
          destruct (decide (y = c)) as [->|Hyc]; [by simplify_map_eq|].
          destruct (decide (y = d)) as [->|Hyd]; by simplify_map_eq.
        + split_and!; try done; [by apply sdual_sbranch|].
          unfold sel_pt, bra_pt. rewrite pt_dual_dual.
          rewrite <-(pt_payload_dual kd). by apply (wf_eq_payload _ HWf).
    Qed.

    Lemma li_close_steps n'' (Hn : n' = S n'') F2 h h0 g g0 c0 c1 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c1)) g0 →
      c0 ∉ C → c1 ∉ C →
      ∃ Σ1 Σ2 k k', senv_hd Σp c0 SEnd k Σ1 ∧ c0 ∉ dom Σ1 ∧
        senv_hd Σ1 c1 SEnd k' Σ2 ∧ c1 ∉ dom Σ2 ∧
        LPrel n'' W Σ2 T (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}).
    Proof.
      intros -> Hh Hg Hc0C Hc1C.
      assert (proc_step (C, F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) (PSess (SClos c0))
                (C ∖ sentc (SClos c0), F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]})) as Hst1.
      { replace (F2 ⊎ {[+ h +]} ⊎ {[+ g +]}) with (F2 ⊎ {[+ g +]} ⊎ {[+ h +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc0C. set_solver. }
      pose proof (Hσ _ _ Hst1) as Hp. cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp.
      destruct Hp as (Σ1 & k & Hhd & Hc0 & HP1).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      assert (proc_step (C, F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) (PSess (SClos c1))
                (C ∖ sentc (SClos c1), F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})) as Hst2.
      { replace (F2 ⊎ {[+ g +]} ⊎ {[+ h0 +]}) with (F2 ⊎ {[+ h0 +]} ⊎ {[+ g +]})
          by multiset_solver.
        apply PStepSession; [done|]. cbn [subjs]. clear -Hc1C. set_solver. }
      rewrite Hn in HP1. pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP1 Hst2) as Hp2. cbn [LPobl Pclos_case Plink_case Psend_case pred] in Hp2.
      destruct Hp2 as (Σ2 & k' & Hhd2 & Hc1 & HP2).
      cbn [sentc] in HP2. rewrite difference_empty_L in HP2.
      by exists Σ1, Σ2, k, k'.
    Qed.

    Lemma li_close_case n'' (Hn : n' = S n'') F2 h h0 g g0 c0 c1 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c1)) g0 →
      (c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c) →
      LPrel n'' W Σ T (C, echsubst c d (F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})).
    Proof.
      intros HE Hh Hg Hcc.
      assert (c0 ∉ C ∧ c1 ∉ C) as [Hc0C Hc1C]
        by (destruct Hcc as [[-> ->]|[-> ->]]; done).
      destruct (li_close_steps n'' Hn F2 h h0 g g0 c0 c1 HE Hh Hg Hc0C Hc1C)
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
      apply (LPrel_junk _ _ _ _ _ _ c d) in HP2; [done|done|done| |done].
      intros Hin. exfalso. done.
    Qed.

    Lemma li_close_same n'' (Hn : n' = S n'') F2 h h0 g g0 c0 :
      E = F2 ⊎ {[+ h +]} ⊎ {[+ g +]} →
      tstep h (LSess (SClos c0)) h0 → tstep g (LSess (SClos c0)) g0 →
      c0 ∉ C → False.
    Proof.
      intros HE Hh Hg Hc0C.
      destruct (li_close_steps n'' Hn F2 h h0 g g0 c0 c0 HE Hh Hg Hc0C Hc0C)
        as (Σ1 & Σ2 & k & k' & _ & Hc0 & Hhd2 & _ & _).
      apply senv_hd_dom in Hhd2. apply Hc0. rewrite Hhd2. clear. set_solver.
    Qed.

    Lemma li_link_ext x0 y0 F f f0 :
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[x0; y0]})) f0 → x0 ∉ C → y0 ∉ C →
      ∃ c1 d1 Σ1 sc1 sd1 kc1 kd1, ({[x0; y0]} : gset chan) = {[c1; d1]} ∧ c1 ≠ d1 ∧
        Σp = <[c1 := (sc1, kc1)]> (<[d1 := (sd1, kd1)]> Σ1) ∧ c1 ∉ dom Σ1 ∧ d1 ∉ dom Σ1 ∧
        sdual sd1 sc1 ∧ w_eq W kc1 (pt_dual kd1) ∧ LPrel (S n') W Σ1 T (C, F ⊎ {[+ f0 +]}).
    Proof.
      intros HEq Hf Hx0 Hy0.
      assert (proc_step (C, E) (PSess (SLink {[x0; y0]}))
                (C ∖ sentc (SLink {[x0; y0]}), F ⊎ {[+ f0 +]})) as Hst.
      { rewrite HEq. apply PStepSession; [done|]. cbn [subjs]. clear -Hx0 Hy0. set_solver. }
      pose proof (Hlx _ _ Hst) as Hp.
      destruct Hp as (c1 & d1 & Σ1 & sc1 & sd1 & kc1 & kd1 & Hcd1 & Hne & HΣ & Hc1 & Hd1 &
                      Hdu1 & Hal1 & HP1 & _).
      cbn [sentc] in HP1. rewrite difference_empty_L in HP1.
      by exists c1, d1, Σ1, sc1, sd1, kc1, kd1.
    Qed.

    Lemma li_link_tau_p y0 x0 F f f0 :
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[y0; x0]})) f0 → y0 ∈ C →
      (C ∖ {[y0]}) ## dom Σ →
      lfuse_goal (S n') W Σp T (C ∖ {[y0]}, echsubst y0 x0 (F ⊎ {[+ f0 +]})).
    Proof.
      intros HEq Hf Hy0 Hg.
      assert (ptau_link (C, E) (C ∖ {[y0]}, echsubst y0 x0 (F ⊎ {[+ f0 +]}))) as Hpl.
      { exists C, F, f, y0, x0, f0. split_and!; [by rewrite HEq|done|done|done]. }
      assert ((C ∖ {[y0]}) ## dom Σp) as Hd'.
      { rewrite (fusedP_dom c d Hcd). clear -Hg HcC HdC. set_solver. }
      exact (Hadm _ (padmin_link _ _ Hpl) Hd').
    Qed.

    Lemma li_link_out x0 xb y0 F f f0 :
      (x0 = c ∧ xb = d) ∨ (x0 = d ∧ xb = c) → y0 ≠ c → y0 ≠ d → y0 ∉ C →
      E = F ⊎ {[+ f +]} → tstep f (LSess (SLink {[x0; y0]})) f0 →
      LPrel (S n') W Σ T (C, echsubst d y0 (echsubst c d (F ⊎ {[+ f0 +]}))).
    Proof.
      intros Hx Hy0c Hy0d Hy0C HEq Hf. destruct HW as [HWf _].
      assert (x0 ∉ C ∧ x0 ≠ y0) as [Hx0C Hx0y]
        by (destruct Hx as [[-> ->]|[-> ->]]; split; [done|congruence|done|congruence]).
      destruct (li_link_ext x0 y0 F f f0 HEq Hf Hx0C Hy0C)
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
            * eapply (wf_eq_trans _ HWf); [exact Hal|by apply eq_dual_l].
        - pose proof (Hl x0) as H0. pose proof (Hl y0) as H1.
          rewrite lookup_insert_eq in H1. rewrite lookup_insert_ne, lookup_insert_eq in H0
            by done.
          rewrite fusedP_ne in H1 by done. exists (sc1, kc1). split; [done|].
          unfold ex. destruct Hx as [[-> ->]|[-> ->]].
          + rewrite decide_True by done. rewrite fusedP_c in H0. injection H0 as <- <-.
            split; simpl.
            * by apply (sdual_unique sc).
            * eapply (wf_eq_trans _ HWf); [apply (wf_eq_sym _ HWf); by apply eq_dual_l|].
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
      apply (LPrel_junk _ _ _ _ _ _ x0 xb) in HP1;
        [| rewrite dom_insert_L; destruct Hx as [[-> ->]|[-> ->]];
           rewrite dom_delete_L; clear -HcΣ HdΣ Hcd; set_solver
         | done
         | intros Hin; exfalso; destruct Hx as [[-> ->]|[-> ->]]; done
         | destruct Hx as [[-> ->]|[-> ->]]; congruence].
      apply (LPrel_junk _ _ _ _ _ _ y0 xb) in HP1;
        [| rewrite dom_insert_L, dom_delete_L; destruct Hx as [[-> ->]|[-> ->]];
           clear -Hy0c Hy0d; set_solver
         | done
         | intros Hin; exfalso; destruct Hx as [[-> ->]|[-> ->]]; done
         | destruct Hx as [[-> ->]|[-> ->]]; congruence].
      apply (LPrel_swap xb y0) in HP1. unfold pswap in HP1. cbn [fst snd] in HP1.
      rewrite msswap_echsubst_flip, gswap_fresh in HP1;
        [|destruct Hx as [[-> ->]|[-> ->]]; done|done].
      rewrite senvswap_insert, cswap_l, senvswap_fix in HP1 by done.
      apply (LPrel_sconv _ _ _ _ _ _ HWf Hsc) in HP1.
      destruct Hx as [[-> ->]|[-> ->]]; [exact HP1|].
      rewrite echsubst_both in HP1 by congruence. exact HP1.
    Qed.

    Lemma li_via_admin p1 :
      padmin (C, E) p1 → p1.1 ## dom Σp → c ∉ p1.1 → d ∉ p1.1 →
      LPrel (S n') W Σ T (p1.1 ∪ {[d]}, echsubst c d p1.2).
    Proof.
      intros Hp Hg Hc Hd.
      pose proof (Hadm p1 Hp Hg) as HΦ.
      destruct p1 as [C1 E1].
      apply (HΦ Σ C1 E1 sc sd kc kd eq_refl eq_refl).
      apply li_int_ok_ext; [by apply wext_refl|done..].
    Qed.

    Lemma li_via_comm p1 :
      pcomm (C, E) p1 → p1.1 ## dom Σp → c ∉ p1.1 → d ∉ p1.1 →
      LPrel (pred n') W Σ T (p1.1 ∪ {[d]}, echsubst c d p1.2).
    Proof.
      intros Hp Hg Hc Hd.
      pose proof (Hcm p1 Hp Hg) as HP1.
      destruct p1 as [C1 E1].
      apply (IH (pred n') ltac:(lia) W _ _ HP1 Σ C1 E1 sc sd kc kd eq_refl eq_refl).
      apply li_int_ok_ext; [by apply wext_refl|done..].
    Qed.

    Lemma li_link_give q' :
      ptau_link q q' → LPtau_case (LPrel (S n')) W Σ T q'.
    Proof.
      intros (C0 & F' & e' & a & b' & e'' & HeqP & Hts & HaC & ->) Hd.
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
          destruct (li_link_ext x0 y0 F f f0 HEq Hf0 Hx0C Hy0C)
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
          apply (LPrel_junk _ _ _ _ _ _ c d) in HP1; [done|done|done| |done].
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
            pose proof (li_link_tau_p y0 x0 F f f0 HEq ltac:(by rewrite upair_comm) Hy0C Hg) as HΦ.
            pose proof (HΦ Σ _ _ sc sd kc kd eq_refl eq_refl) as HP.
            assert (int_ok W Σ sc sd kc kd (C ∖ {[y0]})) as Hok
              by (apply li_int_ok_ext; [by apply wext_refl|done|done
                                    |clear -HcC; set_solver|clear -HdC; set_solver]).
            specialize (HP Hok).
            assert (echsubst c d (echsubst y0 x0 (F ⊎ {[+ f0 +]})) =
                    echsubst y0 d (echsubst c d (F ⊎ {[+ f0 +]}))) as Hre.
            { destruct Hx0 as [->| ->].
              - by apply echsubst_retarget.
              - symmetry. apply echsubst_comm; congruence. }
            rewrite Hre in HP.
            destruct Hab' as [[-> ->]|[-> ->]].
            -- apply (LPrel_swap_restricted d y0) in HP; [|done|clear -Hd Hy0C Hy0d; set_solver].
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
            -- exact (li_link_out c d y0 F f f0 (or_introl (conj eq_refl eq_refl)) Hy0c Hy0d Hy0C HEq Hf0).
            -- exact (li_link_out d c y0 F f f0 (or_intror (conj eq_refl eq_refl)) Hy0c Hy0d Hy0C HEq Hf0).
      - (* neither end *)
        assert (a0 ≠ c ∧ a0 ≠ d ∧ b0 ≠ c ∧ b0 ≠ d) as (H1 & H2 & H3 & H4) by tauto.
        rewrite !csub_ne in Hcd' by done. rewrite <-Hcd' in Hf0.
        assert (a ∈ ({[a0; b0]} : gset chan)) as Ha by (rewrite <-Hcd'; clear; set_solver).
        assert (a ≠ c ∧ a ≠ d ∧ b' ≠ c) as (Hac & Had & Hbc).
        { assert (b' ∈ ({[a0; b0]} : gset chan)) as Hb by (rewrite <-Hcd'; clear; set_solver).
          clear -Ha Hb H1 H2 H3 H4. set_solver. }
        assert (a ∈ C) as HaC' by (clear -HaC Had; set_solver).
        assert (C ∖ {[a]} ## dom Σ) as Hg by (clear -Hd; set_solver).
        pose proof (li_link_tau_p a b' F f f0 HEq Hf0 HaC' Hg) as HΦ.
        pose proof (HΦ Σ _ _ sc sd kc kd eq_refl eq_refl) as HP.
        assert (int_ok W Σ sc sd kc kd (C ∖ {[a]})) as Hok
          by (apply li_int_ok_ext; [by apply wext_refl|done|done
                                |clear -HcC; set_solver|clear -HdC; set_solver]).
        specialize (HP Hok).
        rewrite <-(echsubst_comm a b' c d) in HP by congruence.
        replace ((C ∪ {[d]}) ∖ {[a]}) with (C ∖ {[a]} ∪ {[d]}) by (clear -Had; set_solver).
        exact HP.
    Qed.

    Lemma li_admin q' :
      padmin q q' → q'.1 ## dom Σ → LPrel (S n') W Σ T q'.
    Proof.
      intros Hq Hd.
      apply padmin_inv in Hq as
        [ (F' & e' & e'' & HeqE & Hts & ->)
        | [ (F' & e' & c'' & e'' & HeqE & Hts & Hc''C & Hc''F & Hc''e & ->)
        | [ (F' & e' & v' & e'' & HeqE & Hts & ->)
        | Hlink ]]]; cbn [fst] in Hd.
      4: { (* link: a τ at the index *) exact (li_link_give q' Hlink Hd). }
      - (* β *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        apply eq_sym, lsub_beta in Hα as ->.
        pose proof (li_via_admin (C, F ⊎ {[+ f0 +]}) ltac:(rewrite HEq; by apply PABeta)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                    HcC HdC) as HP. cbn [fst snd] in HP.
        by rewrite echsubst_disj_union1 in HP.
      - (* new: through a fresh z, then rename z to the image's name *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        destruct (exist_fresh (C ∪ dom Σ ∪ echans F ∪ fchans f ∪ {[c; d; c'']})) as [z Hz].
        destruct (tstep_chsubst_new_inv c d f c'' e'' Hts z) as (f0 & Hf0 & ->);
          [clear -Hz; set_solver..|].
        assert (z ∉ C ∧ z ∉ echans F ∧ z ∉ fchans f) as (HzC & HzF & Hzf)
          by (clear -Hz; set_solver).
        pose proof (li_via_admin (C ∪ {[z]}, F ⊎ {[+ f0 +]}) ltac:(rewrite HEq; by apply PANew)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd Hz HcC HdC; set_solver)
                    ltac:(cbn [fst]; clear -Hz HcC; set_solver)
                    ltac:(cbn [fst]; clear -Hz HdC; set_solver)) as HP. cbn [fst snd] in HP.
        assert (c'' ∉ dom Σ) as Hc''Σ by (clear -Hd; set_solver).
        apply (LPrel_swap_restricted z c'') in HP; [|clear -Hz; set_solver|done].
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
        { clear Hσ Hcm Hlx Hadm IH HP Hts Hf0.
          apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
          repeat case_decide; subst; set_solver. }
        rewrite Hg in HP. exact HP.
      - (* spawn *)
        apply echsubst_decomp in HeqE as (F & f & HEq & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
        destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
        pose proof (li_via_admin (C, F ⊎ {[+ f0 +]} ⊎ {[+ App v EUnit +]}) ltac:(rewrite HEq; by apply PASpawn)
                    ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                    HcC HdC) as HP. cbn [fst snd] in HP.
        by rewrite !echsubst_disj_union, !echsubst_singleton in HP.
    Qed.

    Lemma li_comm q' :
      pcomm q q' → LPtau_case (LPrel (pred n')) W Σ T q'.
    Proof.
      intros Hq Hd.
      destruct (decide (n' = 0)) as [Hn0|Hn0].
      { rewrite Hn0. apply LPrel_0. }
      assert (∃ n'', n' = S n'') as [n'' Hn] by (exists (pred n'); lia).
      apply pcomm_inv in Hq as
        [ (F' & c' & v' & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->)
        | [ (F' & c' & e' & e'' & g' & g'' & HeqE & Hts & Htr & Hc'C & ->)
        | (F' & c' & i & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->) ]]; cbn [fst] in Hd.
      - (* message *)
        apply echsubst_decomp in HeqE as (F1 & g & HEq & HeqE1 & ->).
        symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
        apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
        destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
        injection Hα as Hc0 ->.
        apply tstep_chsubst_recv_inv_subst in Htr as (c1 & g0 & Hc1 & Hg0 & ->).
        destruct (decide (c0 = c1)) as [<-|Hc01].
        + pose proof (li_via_comm (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}) ltac:(rewrite HEq; by eapply PCMsg)
                      ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                      HcC HdC) as HP. cbn [fst snd] in HP.
          by rewrite echsubst_disj_union2 in HP.
        + rewrite Hn. cbn [pred]. rewrite <-echsubst_disj_union2.
          apply (li_sync_case n'' Hn F2 h h0 g g0 c0 c1 w0); [exact HEq|done|done| |clear -Hd; set_solver].
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
            pose proof (li_via_comm (C ∖ {[c0]}, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]})
                        ltac:(rewrite HEq; by eapply PCClose)
                        ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd);
                              clear -Hd HcC HdC Hc0d; set_solver)
                        ltac:(cbn [fst]; clear -HcC; set_solver)
                        ltac:(cbn [fst]; clear -HdC; set_solver)) as HP. cbn [fst snd] in HP.
            rewrite echsubst_disj_union2 in HP.
            replace ((C ∪ {[d]}) ∖ {[c0]}) with (C ∖ {[c0]} ∪ {[d]})
              by (clear -Hc0d; set_solver).
            exact HP.
          * exfalso. exact (li_close_same n'' Hn F2 h h0 g g0 c0 HEq Hh0 Hg0 Hc0C).
        + assert ((c0 = c ∧ c1 = d) ∨ (c0 = d ∧ c1 = c)) as Hcc
            by (apply csub_pair; [congruence|done]).
          assert (c' = d) as ->.
          { rewrite Hc0. destruct Hcc as [[-> _]|[-> _]]; [apply csub_hit|by apply csub_ne]. }
          rewrite Hn. cbn [pred].
          rewrite <-echsubst_disj_union2.
          replace ((C ∪ {[d]}) ∖ {[d]}) with C by (clear -HdC; set_solver).
          exact (li_close_case n'' Hn F2 h h0 g g0 c0 c1 HEq Hh0 Hg0 Hcc).
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
        + pose proof (li_via_comm (C, F2 ⊎ {[+ h0 +]} ⊎ {[+ g0 +]}) ltac:(rewrite HEq; by eapply PCChoice)
                      ltac:(cbn [fst]; rewrite (fusedP_dom c d Hcd); clear -Hd HcC HdC; set_solver)
                      HcC HdC) as HP. cbn [fst snd] in HP.
          by rewrite echsubst_disj_union2 in HP.
        + rewrite Hn. cbn [pred]. rewrite <-echsubst_disj_union2.
          apply (li_choice_case n'' Hn F2 h h0 g g0 c0 c1 i); [exact HEq|done|done|].
          apply csub_pair; [congruence|done].
    Qed.

    Lemma li_ext_case σ' q' :
      proc_step q (PSess σ') q' → LPobl LVrel LPrel (S n') W Σ T q σ' q'.
    Proof.
      intros Hq. destruct σ' as [a w'|a w'|a|cd|a i|a i];
        [by apply li_ext_recv|by apply li_ext_send|by apply li_ext_close|exact I
        |by apply li_ext_sel|by apply li_ext_bra].
    Qed.
  End lstep.

  Lemma LPrel_internalize n : ∀ W Σ T C E sc sd kc kd,
    prim T → int_ok W Σ sc sd kc kd C →
    LPrel n W (fusedP c d Σ sc sd kc kd) T (C, E) →
    LPrel n W Σ T (C ∪ {[d]}, echsubst c d E).
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    intros W Σ T C E sc sd kc kd HT Hok HP.
    destruct n as [|n']; [apply LPrel_0|].
    assert (IH : ∀ j, j ≤ n' → ∀ W Σp p, LPrel j W Σp T p → lfuse_goal j W Σp T p).
    { intros j Hj W' Σp p HPj Σ' C' E' sc' sd' kc' kd' -> -> Hok'.
      eapply IHn; [lia|done|done|done]. }
    clear IHn.
    enough (∀ W Σp T' p, LPrel (S n') W Σp T' p → T' = T → lfuse_goal (S n') W Σp T p) as H.
    { eapply H; [exact HP|done|done|done|done]. }
    clear W Σ C E sc sd kc kd Hok HP.
    refine (LPrel_S_ind n' _ _).
    intros W0 Σp T' p H -> Σ C E sc sd kc kd -> -> Hok0.
    apply LPrel_S_iff. intros W HW1.
    pose proof (int_ok_wext c d W0 W Σ sc sd kc kd C HW1 Hok0) as Hok.
    pose proof Hok as (HW & HcΣ & HdΣ & HcC & HdC & Hdu & Hal).
    destruct (H W HW1) as (Hirr & Hrdy & Hadm & Hcm & Hlk & Hσ).
    clear H HW1 Hok0.
    assert (Hlx : ∀ cd p', proc_step (C, E) (PSess (SLink cd)) p' →
      Plink_case (λ W Σ T p, LPrel (S n') W Σ T p ∧ lfuse_goal (S n') W Σ T p) W
        (fusedP c d Σ sc sd kc kd) T cd p').
    { intros cd p' Hst. eapply Plink_case_mono; [|exact (Hlk cd p' Hst)].
      intros Σ1 [HP1 HΦ]. split; [done|]. intros ? ? ? ? ? ? ? ? ? ?. by eapply HΦ. }
    clear Hlk.
    assert (Hadm' : ∀ p', padmin (C, E) p' → p'.1 ## dom (fusedP c d Σ sc sd kc kd) →
      lfuse_goal (S n') W (fusedP c d Σ sc sd kc kd) T p').
    { intros p' Hp Hd. destruct (Hadm p' Hp Hd) as (_ & HΦ).
      intros ? ? ? ? ? ? ? ? ? ?. by eapply HΦ. }
    clear Hadm. rename Hadm' into Hadm.
    assert (Hnp : ¬ pirred (C, E)).
    { intros Hp. destruct (Hirr Hp) as (v & E1 & _ & _ & HV & _).
      apply LVrel_prim_empty in HV; [|done]. apply (f_equal (λ m, m !! c)) in HV.
      unfold tenv_of in HV. rewrite lookup_fmap, fusedP_c, lookup_empty in HV. discriminate. }
    assert (Hnt : ¬ terminated (C, E)) by (intros Ht; by apply Hnp, terminated_pirred).
    pose proof (Hrdy Hnp) as Hrdy'.
    split_and!.
    - intros Hq. exfalso.
      assert (stable_p (C ∪ {[d]}, echsubst c d E)) as Hs by (intros q' Hq'; exact (Hq _ _ Hq')).
      destruct (fused_ready c d Hcd W HW Σ sc sd kc kd C E HcΣ HdΣ HcC HdC Hdu Hal Hrdy' Hnt Hs)
        as [(cd & q' & Hq')|[Hno _]]; [exact (Hq _ _ Hq')|].
      apply Hno. intros k (σ & q' & Hq' & _). exact (Hq _ _ Hq').
    - intros _ Hs.
      destruct (fused_ready c d Hcd W HW Σ sc sd kc kd C E HcΣ HdΣ HcC HdC Hdu Hal Hrdy' Hnt Hs)
        as [?|[Hno Hab]]; [by left|right].
      split; [intros H; exfalso; by apply Hno|done].
    - eapply li_admin; eassumption.
    - eapply li_comm; eassumption.
    - eapply li_ext_link; eassumption.
    - eapply li_ext_case; eassumption.
  Qed.
End linternalize.
