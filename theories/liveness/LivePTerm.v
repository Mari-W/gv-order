(** * P-Term for the live relation (composition/PTerm.v)

    A thread related at E with an environment Σ, Θ_B, where Θ_B holds
    both ends of the restricted channels C₀, gives the one-thread
    process (C₀, {t}) at P with the same index. The proof inducts on the
    τ layer of the thread: β and new of the thread are those of the
    process, and a spawn composes the two threads by P-Connect at the
    same index, with the spawned closure read inside the thread's
    derivation. A link stays at the index too: an internal link fuses
    or renames the remaining end by Internalize or a swap at the process
    level. Channel steps keep their costs and go to the outer
    induction. The environment lemmas are reused from PTerm.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LivePConnect composition.PTerm.

Local Set Warnings "-register-all".
Implicit Types W : world.
Set Default Proof Using "All".

Definition lterm_at (n : nat) (T : ty) : Prop :=
  ∀ W Σ ΘB C0 t, tok W Σ ΘB C0 →
    LErel n W (tenv_of Σ ∪ ΘB) T ∅ t → LPrel n W Σ T (C0, {[+ t +]}).

Lemma tok_mono_r W W' Σ ΘB C0 : wext_r W W' → tok W Σ ΘB C0 → tok W' Σ ΘB C0.
Proof. intros [->|Hx] H; [done|by eapply tok_mono]. Qed.

Lemma ltok_add_both W' Σ ΘB C0 c k1 k2 :
  tok W' Σ ΘB C0 → c ∉ dom Σ → c ∉ C0 → w_eq W' k1.2 (pt_dual k2.2) → sdual k1.1 k2.1 →
  tok W' Σ (<[c := Both k1 k2]> ΘB) (C0 ∪ {[c]}).
Proof.
  intros [HW Hd Hdj Hb Hdu] HcΣ HcC Hq Hdd. split; try done.
  - by rewrite dom_insert_L, Hd, (comm_L (∪)).
  - clear -Hdj HcΣ. set_solver.
  - intros x o. destruct (decide (x = c)) as [->|Hx]; tlk; [intros [= <-]; eauto|apply Hb].
  - intros x f1 f2. destruct (decide (x = c)) as [->|Hx]; tlk; [intros [= <- <-]; done|apply Hdu].
Qed.

(** [link_env] before the move: the environment after a link of the
    restricted channel c with d, split into interface and restricted
    part. For d restricted the remaining ends of c and d are on the
    interface, ready for Internalize. For d on the interface the
    remaining end of c is on the interface in place of d's. *)
Lemma link_env_split W Σ ΘB C0 Θm Θ1 c' d' ec ed c d :
  tok W Σ ΘB C0 → c ∈ C0 → {[c'; d']} = ({[c; d]} : gset chan) →
  tenv_ext Θ1 d' ed Θm → tenv_ext Θm c' ec (tenv_of Σ ∪ ΘB) →
  sdual ed.1 ec.1 → w_eq W ec.2 (pt_dual ed.2) →
  (c = d ∧ Θ1 = tenv_of Σ ∪ delete c ΘB) ∨
  (c ≠ d ∧ ∃ rc rd, d ∈ C0 ∧
     Θ1 = tenv_of (<[c := rc]> (<[d := rd]> Σ)) ∪ delete c (delete d ΘB) ∧
     sdual rc.1 rd.1 ∧ w_eq W rc.2 (pt_dual rd.2)) ∨
  (c ≠ d ∧ ∃ rc a, Σ !! d = Some a ∧
     Θ1 = tenv_of (<[c := rc]> (delete d Σ)) ∪ delete c ΘB ∧
     seq rc.1 a.1 ∧ w_eq W rc.2 a.2).
Proof.
  intros Hok HcC Hcd H1 H2 Hdu Heq.
  pose proof (tok_strict _ _ _ _ Hok) as HW.
  assert (∀ x y, w_eq W x y → w_eq W y x) as Hsym by apply (wf_eq_sym _ (proj1 HW)).
  assert (∀ x y, w_eq W x (pt_dual y) → w_eq W y (pt_dual x)) as Hdsym
    by (intros; by apply (wf_eq_dual_sym _ _ _ (proj1 HW))).
  assert (∀ x y z, w_eq W x y → w_eq W y z → w_eq W x z) as Htr by apply (wf_eq_trans _ (proj1 HW)).
  assert (∀ x y, w_eq W x (pt_dual y) → w_eq W (pt_dual x) y) as Hdl
    by (intros; by apply (wf_eq_dual_l _ _ _ (proj1 HW))).
  destruct (tok_at W Σ ΘB C0 c Hok) as (HC & HΣB & HB).
  destruct (proj1 HC HcC) as [oc Hoc].
  destruct (HB oc Hoc) as (c1 & c2 & -> & Hq12 & Hd12).
  assert (Σ !! c = None) as HΣc by (destruct HΣB; congruence).
  apply tenv_ext_inv in H1 as [Hr1 Ho1]. apply tenv_ext_inv in H2 as [Hr2 Ho2].
  destruct (decide (c = d)) as [<-|Hne].
  - left. split; [done|].
    assert (c' = c ∧ d' = c) as [-> ->].
    { assert (c' ∈ ({[c; c]} : gset chan)) as Hc' by (rewrite <-Hcd; clear; set_solver).
      assert (d' ∈ ({[c; c]} : gset chan)) as Hd' by (rewrite <-Hcd; clear; set_solver).
      clear -Hc' Hd'. set_solver. }
    apply map_eq. intros x. destruct (decide (x = c)) as [->|Hx].
    + destruct Hr2 as [(_ & HH)|(e' & HH & _)].
      { exfalso. revert HH. tlk. rewrite HΣc, Hoc. simpl. rewrite ounion_None. discriminate. }
      destruct Hr1 as [(HH1 & _)|(e'' & HH1 & [HH'|HH'])]; [|congruence|congruence].
      rewrite HH1. tlk. by rewrite HΣc.
    + rewrite Ho1, Ho2 by done. tlk. done.
  - right.
    assert (c' ≠ d') as Hne'.
    { intros ->. apply Hne.
      assert (c ∈ ({[d'; d']} : gset chan)) as Hc' by (rewrite Hcd; clear; set_solver).
      assert (d ∈ ({[d'; d']} : gset chan)) as Hd' by (rewrite Hcd; clear; set_solver).
      clear -Hc' Hd'. set_solver. }
    assert (removed (tenv_of Σ ∪ ΘB) Θ1 c' ec) as Rc'.
    { destruct Hr2 as [(HH & ?)|(e' & HH & ?)]; [left|right; exists e']; rewrite Ho1 by done; auto. }
    assert (removed (tenv_of Σ ∪ ΘB) Θ1 d' ed) as Rd'.
    { destruct Hr1 as [(HH & HH')|(e' & HH & HH')]; [left|right; exists e'];
        rewrite <-(Ho2 d') by done; auto. }
    assert (∀ y, y ≠ c → y ≠ d → Θ1 !! y = (tenv_of Σ ∪ ΘB) !! y) as Ho.
    { intros y Hy1 Hy2. assert (y ≠ c' ∧ y ≠ d') as [? ?].
      { assert (c' ∈ ({[c; d]} : gset chan)) as Hy by (rewrite <-Hcd; clear; set_solver).
        assert (d' ∈ ({[c; d]} : gset chan)) as Hy' by (rewrite <-Hcd; clear; set_solver).
        clear -Hy Hy' Hy1 Hy2. split; intros ->; set_solver. }
      rewrite Ho1, Ho2 by done. done. }
    assert (∃ xc xd, removed (tenv_of Σ ∪ ΘB) Θ1 c xc ∧ removed (tenv_of Σ ∪ ΘB) Θ1 d xd ∧
              sdual xc.1 xd.1 ∧ w_eq W xc.2 (pt_dual xd.2)) as (xc & xd & Rc & Rd & Hxd & Hxq).
    { assert ((c' = c ∧ d' = d) ∨ (c' = d ∧ d' = c)) as [[-> ->]|[-> ->]].
      { assert (c ∈ ({[c'; d']} : gset chan)) as Hc' by (rewrite Hcd; clear; set_solver).
        assert (c' ∈ ({[c; d]} : gset chan)) as Hc'' by (rewrite <-Hcd; clear; set_solver).
        assert (d' ∈ ({[c; d]} : gset chan)) as Hd' by (rewrite <-Hcd; clear; set_solver).
        clear -Hc' Hc'' Hd' Hne'. set_solver. }
      - exists ec, ed. split_and!; [done|done|by apply sdual_sym|done].
      - exists ed, ec. split_and!; [done|done|done|by apply Hdsym]. }
    assert (∃ rc, Θ1 !! c = Some (One rc) ∧ sdual xc.1 rc.1 ∧ w_eq W xc.2 (pt_dual rc.2))
      as (rc & Hrc & Hrcd & Hrcq).
    { destruct (removed_both _ _ _ _ _ _ _ Rc HΣc Hoc) as (r & Hr & [[-> ->]|[-> ->]]);
        exists r; split_and!; eauto using sdual_sym. }
    assert (seq rc.1 xd.1) as Hseq by (eapply sdual_unique; [exact Hrcd|exact Hxd]).
    destruct (tok_at W Σ ΘB C0 d Hok) as (HCd & HΣBd & HBd).
    destruct (ΘB !! d) as [od|] eqn:Hod.
    + (* d restricted *)
      left. split; [done|].
      destruct (HBd od eq_refl) as (d1 & d2 & -> & Hq12' & Hd12').
      assert (Σ !! d = None) as HΣd by (destruct HΣBd; congruence).
      assert (∃ rd, Θ1 !! d = Some (One rd) ∧ sdual xd.1 rd.1 ∧ w_eq W xd.2 (pt_dual rd.2))
        as (rd & Hrd & Hrdd & Hrdq).
      { destruct (removed_both _ _ _ _ _ _ _ Rd HΣd Hod) as (r & Hr & [[-> ->]|[-> ->]]);
          exists r; split_and!; eauto using sdual_sym. }
      exists rc, rd. split_and!.
      * apply HCd. by eexists.
      * apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
        { rewrite Hrc. tlk. done. }
        destruct (decide (x = d)) as [->|Hxd'].
        { rewrite Hrd. tlk. done. }
        rewrite Ho by done. tlk. done.
      * eapply sdual_seq_l; [apply seq_sym, Hseq|exact Hrdd].
      * eapply Htr; [apply Hdsym; exact Hrcq|]. eapply Htr; [apply Hdl; exact Hxq|exact Hrdq].
    + (* d in the interface *)
      right. split; [done|].
      destruct (Σ !! d) as [a|] eqn:HΣd.
      2: { exfalso. destruct (removed_some _ _ _ _ Rd) as [o Ho']. revert Ho'. tlk.
           rewrite HΣd, Hod. simpl. rewrite ounion_None. discriminate. }
      destruct (removed_one _ _ _ _ _ _ Rd HΣd Hod) as [Hd1 ->].
      exists rc, a. split_and!.
      * done.
      * apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc].
        { rewrite Hrc. tlk. done. }
        destruct (decide (x = d)) as [->|Hxd'].
        { rewrite Hd1. tlk. by rewrite Hod. }
        rewrite Ho by done. tlk. done.
      * done.
      * first [eapply Htr; [apply Hdsym; exact Hrcq|apply Hdl; exact Hxq]
              |apply Hsym; eapply Htr; [apply Hdsym; exact Hrcq|apply Hdl; exact Hxq]].
Qed.

Lemma pcomm_single C t p' : ¬ pcomm (C, {[+ t +]}) p'.
Proof.
  intros Hp. apply pcomm_inv in Hp as [(F & ? & ? & ? & e & ? & f & ? & HE & _)|[(F & ? & ? & e & ? & f & ? & HE & _)
    |(F & ? & ? & ? & e & ? & f & ? & HE & _)]]; symmetry in HE; by eapply soup_single_two.
Qed.

Lemma tstep_app_lam_unit eb α e' :
  tstep (App (Lam eb) EUnit) α e' → α = LBeta ∧ e' = subst1 EUnit eb.
Proof.
  intros Hst. inversion Hst as [? ? ? Hh| ? ? ? ? Hs| ? ? ? ? ? Hs| | | | | | |]; subst.
  - by inversion Hh; subst.
  - exfalso. by apply (val_no_tstep _ _ _ Hs).
  - exfalso. by apply (val_no_tstep _ _ _ Hs).
Qed.

(** A spawned closure applied to ∗: one β step to the body. *)
Lemma LPrel_spawned n' W Σ C eb :
  strict W →
  (∀ W1, wext W W1 → LPrel (S n') W1 Σ TUnit (C, {[+ subst1 EUnit eb +]})) →
  LPrel (S n') W Σ TUnit (C, {[+ App (Lam eb) EUnit +]}).
Proof.
  intros HW HB. apply LPrel_S_iff. intros W1 HW1.
  assert (wext W W1) as Hx by (destruct HW1 as [->|?]; [by apply wext_refl|done]).
  assert (strict W1) as HW1s by (by destruct Hx as (_ & _ & _ & ?)).
  assert (Hb : tstep (App (Lam eb) EUnit) LBeta (subst1 EUnit eb)) by (constructor; by constructor).
  assert (Hp : proc_step (C, {[+ App (Lam eb) EUnit +]}) PTau (C, {[+ subst1 EUnit eb +]})).
  { rewrite <-(left_id_L ∅ (⊎) {[+ App (Lam eb) EUnit +]}), <-(left_id_L ∅ (⊎) {[+ subst1 EUnit eb +]}).
    by apply PStepBeta. }
  split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hp).
  - intros _ Hs. exfalso. exact (Hs _ Hp).
  - intros p' Hst Hd.
    apply padmin_inv in Hst as [(F & e & e' & HE & Hs & ->)|[(F & e & c & y & e' & HE & Hs & _)
      |[(F & e & v & e' & HE & Hs & _)|Hlink]]].
    4: { exfalso. destruct Hlink as (C' & E & e & c & bc & d & bd & e' & Heq & Hst & _).
         injection Heq as _ HE. symmetry in HE. apply soup_single_inv in HE as [_ ->].
         by apply tstep_app_lam_unit in Hst as [? _]. }
    all: symmetry in HE; apply soup_single_inv in HE as [-> ->];
      apply tstep_app_lam_unit in Hs as [Hα ->]; try discriminate.
    rewrite (left_id_L ∅ (⊎)). by apply HB.
  - intros p' Hst. exfalso. by eapply pcomm_single.
  - intros cd p' Hst. exfalso.
    apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & _).
    symmetry in HE. apply soup_single_inv in HE as [_ ->].
    by apply tstep_app_lam_unit in Hs as [? _].
  - intros σ p' Hst. exfalso.
    apply proc_step_sess_inv in Hst as (E0 & e & e' & HE & Hs & _).
    symmetry in HE. apply soup_single_inv in HE as [_ ->].
    by apply tstep_app_lam_unit in Hs as [? _].
Qed.

Section llevel.
  Context (n' : nat) (IHo : ∀ j T, j ≤ n' → prim T → lterm_at j T).
  Context (T : ty) (HT : prim T).
  Context (W : world) (Σ : senv) (ΘB : tenv) (C0 : gset chan) (t : expr).
  Context (Hok : tok W Σ ΘB C0).
  Context (HE : LErel (S n') W (tenv_of Σ ∪ ΘB) T ∅ t).

  Local Notation Θ := (tenv_of Σ ∪ ΘB).

  Lemma lt_HWs : strict W.
  Proof. apply (tok_strict _ _ _ _ Hok). Qed.

  Lemma lt_case_recv c β w t' :
    tstep t (LSess (SRecv (c, β) w)) t' → c ∉ C0 →
    LPobl LVrel LPrel (S n') W Σ T (C0, {[+ t +]}) (SRecv (c, β) w) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θ1 & m0 & U & s & k & [Hhd _] & Hcont).
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    pose proof (ΘB_none_of _ _ _ _ _ Hok HcC) as HBc.
    exists (delete c Σ), m0, U, s, k. split_and!.
    - exists s0. split; [|done]. by rewrite insert_delete_id.
    - by rewrite dom_delete_L; clear; set_solver.
    - intros W' j Θ2 HW' Hj Hd Hrok HV. cbn [nlower pcost scost pred] in Hj.
      assert (tok W (<[c := (s, pt_shift 1 k)]> (delete c Σ)) ΘB C0) as Hok1.
      { apply tok_insert; [done|]. eapply tok_sub; [|exact Hok]. apply delete_subseteq. }
      destruct (recv_comp W W' _ ΘB C0 Θ2 Hok1 HW' Hd Hrok) as [Hok' Hcomp].
      simpl. eapply (IHo j T); [lia|done|exact Hok'|].
      eapply (Hcont W' j Θ2); [done|done| |exact Hcomp|done].
      left. split.
      + tlk. by rewrite HBc.
      + by rewrite ins_one.
  Qed.

  Lemma lt_case_close c β t' :
    tstep t (LSess (SClos (c, β))) t' → c ∉ C0 →
    LPobl LVrel LPrel (S n') W Σ T (C0, {[+ t +]}) (SClos (c, β)) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θ1 & k & [Hhd _] & HE').
    unfold Pclos_case; cbn [fst snd].
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    exists (delete c Σ), k. split_and!.
    - exists s0. split; [|done]. by rewrite insert_delete_id.
    - by rewrite dom_delete_L; clear; set_solver.
    - apply (IHo n' T (le_n _) HT W (delete c Σ) ΘB C0); [eapply tok_sub; [apply delete_subseteq|exact Hok]|done].
  Qed.

  Lemma lt_case_choice c β i t' (bra : bool) :
    tstep t (LSess (if bra then SBra (c, β) i else SSel (c, β) i)) t' → c ∉ C0 →
    Pchoice_case (LPrel n') W Σ T (c, β) i
      (if bra then SWith else SPlus) (if bra then bra_pt else sel_pt) (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc0.
    assert (∃ Θr s1 s2 k Θ', tenv_hd_end (tenv_of Σ ∪ ΘB) (c, β) ((if bra then SWith else SPlus) s1 s2) k Θr ∧
              tenv_ext Θr c (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i) Θ' ∧
              LErel n' W Θ' T ∅ t') as Hc
      by (destruct bra; exact Hc0).
    clear Hc0. destruct Hc as (Θr & s1 & s2 & k & Θ' & [Hhd _] & Hext & HE').
    unfold Pchoice_case; cbn [fst snd].
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    pose proof (ΘB_none_of _ _ _ _ _ Hok HcC) as HBc.
    assert (Θ' = tenv_of (<[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> (delete c Σ)) ∪ ΘB) as ->.
    { rewrite <-ins_one by done.
      destruct Hext as [(_ & ->)|(e' & HH & _)]; [done|]. exfalso. revert HH. tlk.
      rewrite HBc. simpl. by rewrite ounion_None. }
    assert (tok W (<[c := (sbranch i s1 s2, (if bra then bra_pt else sel_pt) k i)]> (delete c Σ)) ΘB C0) as Hok1.
    { apply tok_insert; [done|]. eapply tok_sub; [|exact Hok]. apply delete_subseteq. }
    exists (delete c Σ), s1, s2, k. split_and!.
    - exists s0. split; [|done]. by rewrite insert_delete_id.
    - by rewrite dom_delete_L; clear; set_solver.
    - destruct bra.
      + exact (IHo n' T (le_n _) HT W _ ΘB C0 t' Hok1 HE').
      + exact (IHo n' T (le_n _) HT W _ ΘB C0 t' Hok1 HE').
  Qed.

  Lemma lt_case_send c β w t' :
    tstep t (LSess (SSend (c, β) w)) t' → c ∉ C0 →
    LPobl LVrel LPrel (S n') W Σ T (C0, {[+ t +]}) (SSend (c, β) w) (C0 ∖ fchans w, {[+ t' +]}).
  Proof.
    intros Hst HcC. pose proof (LErel_S_step _ _ _ _ _ _ _ _ HE Hst) as Hc. simpl in Hc |- *.
    destruct Hc as (Θr & Θ1 & Θ2 & m0 & U & s & k & Θ' & [Hhd _] & Hcomp & HV & Hext & HE').
    unfold Psend_case; cbn [fst snd].
    destruct (hd_iface _ _ _ _ _ _ _ _ Hok HcC Hhd) as (s0 & HΣc & Hu & ->).
    pose proof (ΘB_none_of _ _ _ _ _ Hok HcC) as HBc.
    assert (tok W (delete c Σ) ΘB C0) as Hok0 by (eapply tok_sub; [apply delete_subseteq|exact Hok]).
    assert (c ∉ dom (delete c Σ)) as HcΣ by (rewrite dom_delete_L; clear; set_solver).
    destruct (send_env W (delete c Σ) ΘB C0 Θ1 Θ2 c (s, pt_shift 1 k) Hok0 HcC HcΣ Hcomp)
      as (H2 & H1 & Hdj & HΣeq & Hdome & Hsplit & Hde & Hok').
    assert (Θ1 !! c = None) as H1c.
    { destruct (comp_at W (delete c Σ) ΘB C0 Θ1 Θ2 c Hok0 Hcomp) as
        [(_&_&?&_)|[(?&_&HH&_)|[(?&_&HH&_)|(?&?&HH&_)]]]; [done|..];
        rewrite ?lookup_delete_eq in HH; congruence. }
    assert (Θ' = <[c := One (s, pt_shift 1 k)]> Θ1) as ->.
    { destruct Hext as [(_ & ->)|(e' & HH & _)]; [done|congruence]. }
    exists (mdrop (delete c Σ) Θ2), (mkeep (delete c Σ) Θ2), m0, U, s, k,
      (tenv_ones (mkeep Θ1 ΘB)), (mkeep Θ2 ΘB). split_and!.
    - exists s0. split; [|done]. rewrite <-HΣeq. by rewrite insert_delete_id.
    - done.
    - intros Hin. apply HcΣ. rewrite HΣeq, dom_union_L. clear -Hin. set_solver.
    - intros Hin. apply HcΣ. rewrite HΣeq, dom_union_L. clear -Hin. set_solver.
    - simpl. by rewrite (LVrel_fchans _ _ _ _ _ HV).
    - done.
    - intros x Hx1 Hx2. apply (Hde x Hx1). rewrite dom_delete_L.
      destruct (decide (x = c)); [clear -e; set_solver|clear -Hx2 n; set_solver].
    - by rewrite <-H2.
    - rewrite (LVrel_fchans _ _ _ _ _ HV). apply (IHo n' T (le_n _) HT W _ (mdrop ΘB Θ2) (C0 ∖ dom Θ2)); [exact Hok'|by rewrite <-H1].
  Qed.

  (** The τ layer of the thread, after a link: the process of the
      continuation at the index, for every split of its environment. *)
  Definition lt_cont (W0 : world) (Θ0 : tenv) (F0 : gset point) (e0 : expr) : Prop :=
    ∀ Σ' ΘB' C0', Θ0 = tenv_of Σ' ∪ ΘB' → tok W0 Σ' ΘB' C0' → LPrel (S n') W0 Σ' T (C0', {[+ e0 +]}).

  Lemma lt_case_slink cd t' :
    tstep t (LSess (SLink cd)) t' → (set_map fst cd : gset chan) ## C0 → LElink lt_cont W Θ ∅ cd t' →
    Plink_case (LPrel (S n')) W Σ T cd (C0, {[+ t' +]}).
  Proof.
    intros Hst HcC Hc.
    destruct Hc as (c & d & Θ1 & Θm & sc & sd & kc & kd & -> & H1 & H2 & Hdu & Heq & HE').
    rewrite set_map_union_L, !set_map_singleton_L in HcC.
    assert (c ∉ C0 ∧ d ∉ C0) as [Hc0 Hd0] by (clear -HcC; set_solver).
    pose proof (ΘB_none_of _ _ _ _ _ Hok Hc0) as HBc.
    pose proof (ΘB_none_of _ _ _ _ _ Hok Hd0) as HBd.
    apply tenv_ext_inv in H1 as [Hr1 Ho1]. apply tenv_ext_inv in H2 as [Hr2 Ho2].
    destruct (Σ !! c) as [a|] eqn:HΣc.
    2: { exfalso. destruct (removed_some _ _ _ _ Hr2) as [o Ho]. revert Ho. tlk.
         rewrite HΣc, HBc. simpl. rewrite ounion_None. discriminate. }
    destruct (removed_one _ _ _ _ _ _ Hr2 HΣc HBc) as [Hmc Ha]. subst a.
    assert (c ≠ d) as Hne.
    { intros <-. destruct (removed_some _ _ _ _ Hr1) as [o Ho]. congruence. }
    apply (removed_eq _ (tenv_of Σ ∪ ΘB)) in Hr1; [|symmetry; by apply Ho2].
    destruct (Σ !! d) as [b|] eqn:HΣd.
    2: { exfalso. destruct (removed_some _ _ _ _ Hr1) as [o Ho]. revert Ho. tlk.
         rewrite HΣd, HBd. simpl. rewrite ounion_None. discriminate. }
    destruct (removed_one _ _ _ _ _ _ Hr1 HΣd HBd) as [H1d Hb]. subst b.
    exists c, d, (delete c (delete d Σ)), sc, sd, kc, kd. split_and!; try done.
    - apply map_eq. intros x. destruct (decide (x = c)) as [->|Hxc]; [tlk; done|].
      destruct (decide (x = d)) as [->|Hxd]; tlk; done.
    - rewrite dom_delete_L. clear. set_solver.
    - rewrite !dom_delete_L. clear. set_solver.
    - apply (HE' (delete c (delete d Σ)) ΘB C0).
      + apply map_eq. intros x. destruct (decide (x = d)) as [->|Hxd].
        { rewrite H1d. tlk. by rewrite HBd. }
        destruct (decide (x = c)) as [->|Hxc].
        { rewrite Ho1 by done. rewrite Hmc. tlk. by rewrite HBc. }
        rewrite Ho1, Ho2 by done. tlk. done.
      + eapply tok_sub; [|exact Hok]. etrans; apply delete_subseteq.
  Qed.


  Lemma lt_case_tlink c bc d bd t' :
    tstep t (LSess (SLink {[(c, bc); (d, bd)]})) t' → c ∈ C0 → LElink lt_cont W Θ ∅ {[(c, bc); (d, bd)]} t' →
    LPtau_case (LPrel (S n')) W Σ T (C0 ∖ {[c]}, {[+ chsubst c d t' +]}).
  Proof.
    intros Hst HcC Hc.
    destruct Hc as (c' & d' & Θ1 & Θm & sc & sd & kc & kd & Hcd' & H1 & H2 & Hdu & Heq & HE').
    assert (({[c; d]} : gset chan) = {[c'; d']}) as Hcd.
    { apply (f_equal (λ X : gset cend, (set_map fst X : gset chan))) in Hcd'. simpl in Hcd'.
      by rewrite !set_map_union_L, !set_map_singleton_L in Hcd'. }
    pose proof lt_HWs as HWs.
    pose proof (tok_disj _ _ _ _ Hok) as HΣC.
    assert (c ∉ dom Σ) as HcΣ by (clear -HΣC HcC; set_solver).
    assert (LPrel (S n') W Σ T (C0 ∖ {[c]}, {[+ chsubst c d t' +]})) as HP.
    { destruct (link_env_split W Σ ΘB C0 Θm Θ1 c' d' (sc, kc) (sd, kd) c d Hok HcC (eq_sym Hcd)
                  H1 H2 Hdu Heq)
        as [(<- & HΘ1)|[(Hne & rc & rd & HdC & HΘ1 & Hrr & Hrq)|(Hne & rc & a & HΣd & HΘ1 & Hsa & Hqa)]].
      - rewrite chsubst_self. apply (HE' Σ (delete c ΘB) (C0 ∖ {[c]})); [done|by apply tok_delete].
      - (* d restricted: the remaining ends of c and d fuse (Internalize) *)
        assert (d ∉ dom Σ) as HdΣ by (clear -HΣC HdC; set_solver).
        assert (tok W (<[c := rc]> (<[d := rd]> Σ)) (delete c (delete d ΘB)) (C0 ∖ {[c; d]}))
          as Hok1.
        { assert (C0 ∖ {[c; d]} = (C0 ∖ {[d]}) ∖ {[c]}) as -> by (clear; set_solver).
          apply tok_insert; [clear; set_solver|]. apply tok_insert; [clear; set_solver|].
          by apply tok_delete, tok_delete. }
        pose proof (HE' _ _ _ HΘ1 Hok1) as HP1.
        assert (<[c := rc]> (<[d := rd]> Σ) = fusedP c d Σ rc.1 rd.1 rc.2 rd.2) as Hf
          by (destruct rc, rd; done).
        rewrite Hf in HP1.
        assert (int_ok c d W Σ rc.1 rd.1 rc.2 rd.2 (C0 ∖ {[c; d]})) as Hio.
        { split_and!; try done; clear; set_solver. }
        pose proof (LPrel_internalize c d Hne (S n') W Σ T _ _ rc.1 rd.1 rc.2 rd.2 HT Hio HP1) as HP2.
        rewrite echsubst_singleton in HP2.
        replace (C0 ∖ {[c; d]} ∪ {[d]}) with (C0 ∖ {[c]}) in HP2; [exact HP2|].
        apply set_eq. intros x. destruct (decide (x = d)) as [->|Hxd]; [clear -Hne HdC; set_solver|].
        clear -Hxd. set_solver.
      - (* d on the interface: the remaining end of c is renamed to d *)
        assert (d ∉ C0) as HdC0.
        { intros Hd. apply (elem_of_disjoint _ _) in HΣC. apply (HΣC d); [|done].
          by apply elem_of_dom_2 in HΣd. }
        assert (tok W (<[c := rc]> (delete d Σ)) (delete c ΘB) (C0 ∖ {[c]})) as Hok1.
        { apply tok_insert; [clear; set_solver|]. eapply tok_sub; [apply delete_subseteq|].
          by apply tok_delete. }
        pose proof (HE' _ _ _ HΘ1 Hok1) as HP1.
        apply (LPrel_swap c d) in HP1. unfold pswap in HP1. cbn [fst snd] in HP1.
        rewrite gswap_fresh in HP1 by (clear -HdC0; set_solver).
        apply (LPrel_junk _ _ _ _ _ _ c d) in HP1.
        + rewrite echsubst_msswap_same, echsubst_singleton in HP1.
          eapply LPrel_sconv; [apply HWs| |exact HP1].
          intros r. rewrite lookup_senvswap'.
          destruct (decide (r = c)) as [->|Hrc]; [|destruct (decide (r = d)) as [->|Hrd]].
          * rewrite cswap_l, lookup_insert_ne, lookup_delete_eq by done.
            by rewrite (not_elem_of_dom_1 _ _ HcΣ).
          * rewrite cswap_r, lookup_insert_eq, HΣd. by split.
          * rewrite cswap_ne by done. rewrite lookup_insert_ne, lookup_delete_ne by done.
            destruct (Σ !! r); simpl; [|done]. split; [apply seq_refl|apply (wf_eq_refl _ (proj1 HWs))].
        + rewrite dom_senvswap, elem_of_gswap', cswap_l, dom_insert_L, dom_delete_L.
          clear -Hne. set_solver.
        + clear. set_solver.
        + intros Hd'. exfalso. clear -Hd' HdC0. set_solver.
        + done. }
    intros _. exact HP.
  Qed.
End llevel.

Lemma lterm_level n' (IHo : ∀ j T, j ≤ n' → prim T → lterm_at j T) :
  ∀ W Θ T F t, LErel (S n') W Θ T F t → F = ∅ → prim T →
    ∀ Σ ΘB C0, Θ = tenv_of Σ ∪ ΘB → tok W Σ ΘB C0 → LPrel (S n') W Σ T (C0, {[+ t +]}).
Proof.
  refine (LErel_S_ind n' _ _).
  intros W0 Θ T F t H -> HT Σ ΘB C0 -> Hok0.
  assert (HE0 : LErel (S n') W0 (tenv_of Σ ∪ ΘB) T ∅ t).
  { apply LErel_S_iff. eapply LEstep_mono; [|exact H]. by intros ? ? ? ? ? [? _]. }
  apply LPrel_S_iff. intros W HW1.
  pose proof (tok_mono_r _ _ _ _ _ HW1 Hok0) as Hok.
  assert (HE : LErel (S n') W (tenv_of Σ ∪ ΘB) T ∅ t) by (by eapply LErel_mono).
  pose proof (tok_strict _ _ _ _ Hok) as HWs.
  destruct (proj2 H W HW1) as (Hval & Hrdy & Hb & Hnew & Hsp & Hσ & Hlk).
  clear H HE0 Hok0.
  assert (Hlk' : ∀ cd t', tstep t (LSess (SLink cd)) t' →
            LElink (lt_cont n' T) W (tenv_of Σ ∪ ΘB) ∅ cd t').
  { intros cd t' Hs. eapply LElink_mono; [|exact (Hlk _ _ Hs)].
    intros Θ1 [_ HΦ] Σ' ΘB' C0' HΘ Hok'. exact (HΦ eq_refl HT Σ' ΘB' C0' HΘ Hok'). }
  assert (irred t → Σ = ∅ ∧ C0 = ∅ ∧ LVrel (S n') W ∅ T t) as Hstop.
  { intros Hirr. pose proof (Hval Hirr) as HV.
    pose proof (LVrel_prim_empty _ _ _ _ _ HT HV) as H0.
    destruct (tok_empty _ _ _ _ Hok H0) as [-> ->]. rewrite H0 in HV. done. }
  assert (¬ irred t → ready_p W Σ (C0, {[+ t +]})) as Hready.
  { intros Hn. destruct Hok as [HW Hd Hdj Hb' Hdu].
    eapply (ready_term W Σ ΘB C0 t HW Hd Hdj Hb' Hdu).
    all: first [exact (Hrdy Hn)|exact Hn|
      intros σ t' Hst; exact (Loffered_some _ _ _ _ _ _ _ _ HE Hst)]. }
  split_and!.
  - intros Hirr. destruct (tstep_progress t) as [Hi|(α & t' & Hs)].
    + destruct (Hstop Hi) as (-> & -> & HV). exists t, ∅. split_and!.
      * by rewrite (right_id_L ∅ (⊎)).
      * by eapply LVrel_val.
      * unfold tenv_of. by rewrite fmap_empty.
      * intros e He. exfalso. clear -He. multiset_solver.
    + exfalso. assert (¬ irred t) as Hn by (intros Hi; exact (Hi _ _ Hs)).
      destruct (Hready Hn (λ p' Hp', Hirr _ _ Hp')) as [(cd & q & Hq)|[Ht _]];
        [by destruct (Hirr _ _ Hq)|].
      destruct (Ht (λ k Hk, match Hk with ex_intro _ σ (ex_intro _ q (conj Hq _)) => Hirr _ _ Hq end))
        as (v & E & Heq & Hv & _).
      injection Heq as _ HE'. assert (v ∈ ({[+ t +]} : gmultiset expr)) as Hin.
      { rewrite HE'. apply gmultiset_elem_of_disj_union. left. by apply gmultiset_elem_of_singleton. }
      apply gmultiset_elem_of_singleton in Hin as Htv. symmetry in Htv.
      rewrite <-Htv in Hv. exact (val_no_tstep _ _ _ Hs Hv).
  - intros Hn. destruct (tstep_progress t) as [Hi|(α & t' & Hs)].
    + exfalso. apply Hn. destruct (Hstop Hi) as (_ & -> & HV). apply vals_pirred.
      intros e He. apply gmultiset_elem_of_singleton in He as ->. by eapply LVrel_val.
    + apply Hready. intros Hi. exact (Hi _ _ Hs).
  - (* Q-Admin, by induction on the τ layer of the thread *)
    intros p' Hst Hd.
    apply padmin_inv in Hst as [(F & e & t' & HE' & Hs & ->)|[(F & e & c & x & t' & HE' & Hs & HcC & HcF & Hce & ->)
      |[(F & e & v & t' & HE' & Hs & ->)|Hlink]]].
    4: { (* link of a restricted channel, a τ at the index *)
      destruct Hlink as (C' & E & e & c & bc & d & bd & t' & Heq & Hst & HcC & ->).
      injection Heq as <- HE'. symmetry in HE'. apply soup_single_inv in HE' as [-> ->].
      rewrite (left_id_L ∅ (⊎)), echsubst_singleton.
      exact (lt_case_tlink n' IHo T HT W Σ ΘB C0 t Hok HE c bc d bd t' Hst HcC (Hlk' _ _ Hst) Hd). }
    all: symmetry in HE'; apply soup_single_inv in HE' as [-> ->]; rewrite (left_id_L ∅ (⊎)); simpl in Hd.
    + destruct (Hb t' Hs) as [_ HΦ]. exact (HΦ eq_refl HT Σ ΘB C0 eq_refl Hok).
    + assert (c ∉ dom Σ) as HcΣ by (clear -Hd; set_solver).
      assert (c ∉ dom (tenv_of Σ ∪ ΘB)) as Hc0.
      { unfold tenv_of. rewrite dom_union_L, dom_fmap_L, (tok_dom _ _ _ _ Hok). clear -HcΣ HcC. set_solver. }
      destruct (Hnew c x t' Hs Hc0) as (Hx & s & s' & Hdd & _ & HΦ).
      apply (HΦ eq_refl HT Σ (<[c := Both (s, x) (s', pt_dual x)]> ΘB)).
      * rewrite <-ins_both; [done|]. by apply not_elem_of_dom.
      * apply ltok_add_both; [done|done|done| |done].
        simpl. rewrite ?pt_dual_dual. apply (wf_eq_refl _ (proj1 HWs)).
    + destruct (Hsp v t' Hs) as (Θ1 & Θ2 & ub & lb & Hcomp & Hv & _ & HΦ2).
      destruct (spawn_env W Σ ΘB C0 Θ1 Θ2 Hok Hcomp) as (H2 & H1 & Hok2 & Hok1 & Hcut & HΣ & HC).
      pose proof (λ Heq, HΦ2 eq_refl HT _ _ _ Heq Hok2) as HP1.
      specialize (HP1 ltac:(by rewrite <-H2)).
      destruct Hv as [(eb & -> & Hfc & Hlb & HL)|(k & T0 & -> & -> & Hk & Heq)].
      *
        match type of Hcut with cut_ok _ ?S1 ?S2 ?SC ?SC' ?D0 ?D1 ?D2 =>
          match type of Hok1 with tok _ ?Sb ?Bb ?Cb =>
            assert (LPrel (S n') W Sb TUnit (Cb, {[+ App (Lam eb) EUnit +]})) as HP2' end end.
        { apply LPrel_spawned; [exact HWs|]. intros W1 HW1'.
          destruct (HL W1 (S n') ∅ Θ1 EUnit ∅ HW1' (le_n _)) as [_ K2].
          { split; [intros c'; rewrite lookup_empty; destruct (Θ1 !! c'); constructor|].
            intros c' e1 e2 _ Hc'. by rewrite lookup_empty in Hc'. }
          { destruct ub; simpl; [intros y Hy; set_solver|done]. }
          destruct (K2 eq_refl eq_refl eq_refl) as [_ HΦ'].
          refine (HΦ' eq_refl prim_unit _ _ _ _ (tok_mono _ _ _ _ _ HW1' Hok1)).
          by rewrite <-H1. }
        pose proof (lconn_all (S n') T HT _ _ _ _ _ _ _ _ _ _ T TUnit ltac:(by left) Hcut HP1 HP2') as HP.
        by rewrite HΣ, HC in HP.
      * exfalso. inversion Hk as [kq Tq Gq xq Hsig| | |]; subst; try (inversion Hsig; subst);
          simpl in Heq; naive_solver.
  - intros p' Hst. exfalso. by eapply pcomm_single.
  - (* Q-Link: an external link, at the index *)
    intros cd p' Hst.
    apply proc_step_sess_inv in Hst as (E0 & e & t' & HE' & Hs & Hsub & ->).
    symmetry in HE'. apply soup_single_inv in HE' as [-> ->]. rewrite (left_id_L ∅ (⊎)).
    simpl in Hsub. cbn [sentc]. rewrite difference_empty_L.
    exact (lt_case_slink n' IHo T HT W Σ ΘB C0 t Hok HE cd t' Hs Hsub (Hlk' _ _ Hs)).
  - intros σ p' Hst.
    apply proc_step_sess_inv in Hst as (E0 & e & t' & HE' & Hs & Hsub & ->).
    symmetry in HE'. apply soup_single_inv in HE' as [-> ->]. rewrite (left_id_L ∅ (⊎)).
    destruct σ as [[c β] w|[c β] w|[c β]|cd|[c β] i|[c β] i]; simpl in Hsub |- *.
    + rewrite difference_empty_L. apply (lt_case_recv n' IHo T HT W Σ ΘB C0 t Hok HE c β); [done|clear -Hsub; set_solver].
    + apply (lt_case_send n' IHo T HT W Σ ΘB C0 t Hok HE c β); [done|clear -Hsub; set_solver].
    + rewrite difference_empty_L. apply (lt_case_close n' IHo T HT W Σ ΘB C0 t Hok HE c β); [done|clear -Hsub; set_solver].
    + exact I.
    + rewrite difference_empty_L. apply (lt_case_choice n' IHo T HT W Σ ΘB C0 t Hok HE c β i t' false); [done|clear -Hsub; set_solver].
    + rewrite difference_empty_L. apply (lt_case_choice n' IHo T HT W Σ ΘB C0 t Hok HE c β i t' true); [done|clear -Hsub; set_solver].
Qed.

Lemma lterm_all n : ∀ T, prim T → lterm_at n T.
Proof.
  induction n as [n IHn] using lt_wf_ind. intros T HT. destruct n as [|n'].
  { intros ? ? ? ? ? _ _. apply LPrel_0. }
  assert (IHo : ∀ j T, j ≤ n' → prim T → lterm_at j T)
    by (intros j T' Hj HT'; apply IHn; [lia|done]).
  intros W Σ ΘB C0 t Hok HE.
  exact (lterm_level n' IHo W _ T ∅ t HE eq_refl HT Σ ΘB C0 eq_refl Hok).
Qed.

(** P-Term (§11), [Prel_term] with the live judgments. *)
Theorem LPrel_term W Σ ΘB C0 t T :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  lsem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  ∀ n, LPrel n W Σ T (C0, {[+ t +]}).
Proof.
  intros HT HW Hd Hdj Hb Hdu Ht n.
  apply (lterm_all n T HT W Σ ΘB C0 t); [by split|].
  pose proof (Ht n W ∅ _ Var (wext_refl W HW) (tenv_comp_empty_r _ _) eq_refl) as H.
  by rewrite subst_ids in H.
Qed.

(** Independence: P-Connect with an empty cut. *)
Theorem LPrel_indep W1 W2 Σ1 Σ2 C1 C2 E1 E2 T :
  prim T →
  (∀ n, LPrel n W1 Σ1 T (C1, E1)) → (∀ n, LPrel n W2 Σ2 TUnit (C2, E2)) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  strict (wjoin W1 W2) → world_wf W1 → world_wf W2 → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C2 →
  ∀ n, LPrel n (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2, E1 ⊎ E2).
Proof.
  intros HT HP1 HP2 H12 H21 HW HW1 HW2 Hd HC1 HC2 HC12.
  rewrite <-(right_id_L ∅ (∪) (C1 ∪ C2)).
  apply (LPrel_connect W1 W2 Σ1 Σ2 ∅ ∅ ∅); try done.
  all: first [by rewrite (right_id_L ∅ (∪)) | apply dom_empty_L
             | (intros c e e' H; by rewrite lookup_empty in H)
             | apply map_disjoint_empty_r | apply disjoint_empty_r].
Qed.
