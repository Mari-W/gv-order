(** * Monotonicity in the world and frame weakening (§10)

      W ⊑ W′  ⇒  V^W ⊆ V^{W′},  E^W ⊆ E^{W′},  P^W ⊆ P^{W′}
                                    ([Vrel_mono], [Erel_mono], [Prel_mono])
      F′ ⊆ F  ⇒  E^W_n⟦Θ ⊢ T ≺ F⟧ ⊆ E^W_n⟦Θ ⊢ T ≺ F′⟧  ([Erel_frame])

    Facts only ever help: ready, the frame and every alias the relation
    asks for are positive in ≡ and ≺, and the clauses that quantify
    over future worlds see fewer of them from a larger world. The
    clauses that need an argument are O-New and Q-Tau: the points the
    step placed are first renamed away from the larger world W′
    ([Points.Erel_new_rename], [Points.Prel_tau_rename]), and the fresh
    extension is then joined with W′, which stays a fresh extension of
    W′ ([wext_fresh_join]). *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Convert.

(** ** Ingredients *)

Lemma lb_below_mono W W' lb H :
  wext W W' → lb_below W lb H → lb_below W' lb H.
Proof.
  intros (_ & He & Hl & _). destruct lb as [x|]; simpl; [|done].
  intros Hb y Hy. destruct (Hb y Hy); [left|right]; auto.
Qed.

Lemma ub_below_mono W W' ub F :
  wext W W' → ub_below W ub F → ub_below W' ub F.
Proof.
  intros (_ & _ & Hl & _). destruct ub as [x|]; simpl; [|done]. eauto.
Qed.

Lemma above_offered_mono W W' Θ off :
  wext W W' → above_offered W Θ off → above_offered W' Θ off.
Proof.
  intros (_ & _ & Hl & _) H k e He Hk.
  destruct (H k e He Hk) as (k' & e' & ? & ? & ?). eauto 10.
Qed.

Lemma ready_t_mono W W' Θ e : wext W W' → ready_t W Θ e → ready_t W' Θ e.
Proof.
  intros HW H Hs. destruct (H Hs) as [? ?]. split; [done|].
  by eapply above_offered_mono.
Qed.

Lemma ready_p_mono W W' Σ p : wext W W' → ready_p W Σ p → ready_p W' Σ p.
Proof.
  intros HW H Hs. destruct (H Hs) as [? ?]. split; [done|].
  by eapply above_offered_mono.
Qed.

Lemma frame_t_mono_w W W' Θ e F :
  wext W W' → frame_t W Θ e F → frame_t W' Θ e F.
Proof.
  intros (_ & _ & Hl & _) H Hs k e0 Ho He y Hy. apply Hl. by eapply H.
Qed.

Lemma wext_join_l W1 W' :
  strict (wjoin W1 W') → wext W1 (wjoin W1 W').
Proof.
  intros Hs. split_and!; [simpl; set_solver|apply wjoin_l|apply wjoin_l|done].
Qed.

(** ** Frame weakening *)

Lemma Erel_frame n W Θ T F F' e :
  F' ⊆ F → Erel n W Θ T F e → Erel n W Θ T F' e.
Proof.
  intros HF. revert W Θ T e.
  induction n as [n IH] using lt_wf_ind; intros W Θ T e HE.
  destruct n as [|n]; [apply Erel_0|].
  assert (∀ j W0 Θ0 T0 e0, j ≤ n → Erel j W0 Θ0 T0 F e0 → Erel j W0 Θ0 T0 F' e0)
    as IHj by (intros; apply IH; [lia|done]).
  apply Erel_S_iff in HE as (Hval & Hrdy & Hstep).
  apply Erel_S_iff. split_and!; [done| |].
  { intros Hirr. destruct (Hrdy Hirr). split; [done|].
    by eapply frame_t_mono. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
  - by apply IHj.
  - destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ12 HW Hj Hc HVw.
    destruct (H W' j Θ2 Θ12 HW Hj Hc HVw) as (Θ' & Hext & HE').
    exists Θ'. split; [done|]. by apply IHj.
  - destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                       Hhd & Hc & HVw & Hext & HE').
    exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done. by apply IHj.
  - destruct Hstep as (Θ1 & k & Hhd & HE').
    exists Θ1, k. split; [done|]. by apply IHj.
  - destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                       -> & ? & ? & ? & ? & HE').
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. by apply IHj.
  - intros Hc. destruct (Hstep Hc) as (a & s & s' & W' & Ha & ? & ? & HE').
    exists a, s, s', W'. split_and!; [|done|done|by apply IHj].
    assert (frame_roots F' ⊆ frame_roots F) by (unfold frame_roots; set_solver).
    set_solver.
  - destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
    exists Θ1, Θ2, ub, lb. split_and!; [done|done|]. by apply IHj.
Qed.

(** ** Monotonicity of V, E and P in the world *)

Lemma rel_mono n :
  (∀ W W' Θ T v, world_wf W → wext W W' → Vrel n W Θ T v → Vrel n W' Θ T v) ∧
  (∀ W W' Θ T F e, world_wf W → wext W W' →
     Erel n W Θ T F e → Erel n W' Θ T F e) ∧
  (∀ W W' Σ T p, world_wf W → wext W W' → Prel n W Σ T p → Prel n W' Σ T p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ W W' Θ T v, world_wf W → wext W W' →
            Vrel n W Θ T v → Vrel n W' Θ T v) as HV.
  { intros W W' Θ T. revert Θ.
    induction T as [|ub lb T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2|T1 IHT1 T2 IHT2
                   |m T1 IHT1|s x];
      intros Θ v HW HWW' HVv.
    - by apply Vrel_unit_iff in HVv; apply Vrel_unit_iff.
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hsup & Hlb & HL)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!; [done|done| |].
        { by eapply lb_below_mono. }
        intros W'' j Θ' Θ'' w F HW' Hj Hc HVw Hub.
        apply (HL W'' j Θ' Θ'' w F); [|done..]. by eapply wext_trans.
      + apply Vrel_lolli_iff. right. exists k, T0.
        destruct HWW' as (_ & He & Hl & _). split_and!; [done|done| |].
        * eapply konst_ty_mono; [| |exact Hk]; auto.
        * by eapply teqW_mono.
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hsp & H1 & H2).
      apply Vrel_prod_iff. exists v1, v2, Θ1, Θ2. split_and!; eauto.
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; exists v'; eauto.
    - apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & HK).
      apply Vrel_box_iff. split; [done|]. exists eb. split_and!; [done|done|].
      intros W'' j xs HW' Hj Hxs. apply HK; [|done..]. by eapply wext_trans.
    - apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs0 & Hx).
      apply Vrel_sess_iff. exists c, s0, k. split_and!; [done..|].
      destruct HWW' as (_ & He & _). auto. }
  split_and!; [exact HV| |].
  - intros W W' Θ T F e HW HWW' HE.
    destruct n as [|n']; [apply Erel_0|].
    assert (∀ j W0 W0' Θ0 T0 F0 e0, j ≤ n' → world_wf W0 → wext W0 W0' →
              Erel j W0 Θ0 T0 F0 e0 → Erel j W0' Θ0 T0 F0 e0) as HEj.
    { intros j ? ? ? ? ? ? Hj. apply (proj1 (proj2 (IHn j ltac:(lia)))). }
    apply Erel_S_iff in HE as (Hval & Hrdy & Hstep).
    apply Erel_S_iff. split_and!.
    { intros Hirr. eapply HV; [done|done|]. by apply Hval. }
    { intros Hirr. destruct (Hrdy Hirr). split.
      - by eapply ready_t_mono.
      - by eapply frame_t_mono_w. }
    intros α e' Hst. specialize (Hstep α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
    + eapply HEj; [lia|done|done|exact Hstep].
    + destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists Θ1, m, U, s, k. split; [done|].
      intros W'' j Θ2 Θ12 HW' Hj Hc HVw.
      apply (H W'' j Θ2 Θ12); [by eapply wext_trans|done..].
    + destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done.
      * eapply HV; done.
      * eapply HEj; [lia|done|done|exact HE'].
    + destruct Hstep as (Θ1 & k & Hhd & HE').
      exists Θ1, k. split; [done|]. eapply HEj; [lia|done|done|exact HE'].
    + destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & ? & ? & ? & Hal & HE').
      exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..| |].
      * destruct HWW' as (_ & He & _). auto.
      * eapply HEj; [lia|done|done|exact HE'].
    + (* O-New: rename the new point away from W', then join *)
      intros Hc.
      destruct (Hstep Hc) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
      destruct (fresh_const (w_names W' ∪ tenv_roots Θ ∪ ty_roots T ∪ frame_roots F))
        as [a1 Ha1].
      assert (w_names W ⊆ w_names W') by (by destruct HWW').
      destruct (Erel_new_rename _ _ _ _ _ _ _ c s s' a a1 HW Hfr Ha
                  ltac:(set_solver) HE') as (W1' & Hfr' & HE1).
      pose proof (wext_fresh_join W {[NConst a1]} W1' W' HW Hfr' HWW'
                    ltac:(set_solver)) as Hfr''.
      exists a1, (stysw a a1 s), (stysw a a1 s'), (wjoin W1' W'). split_and!.
      * set_solver.
      * by apply sdual_sw.
      * done.
      * eapply HEj; [lia| |apply wext_join_l|exact HE1].
        -- by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
        -- by destruct Hfr'' as ((_ & _ & _ & ?) & _).
    + destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
      exists Θ1, Θ2, ub, lb. split_and!; [done| |].
      * eapply HV; done.
      * eapply HEj; [lia|done|done|exact HE'].
  - intros W W' Σ T p HW HWW' HP.
    destruct n as [|n']; [apply Prel_0|].
    assert (∀ j W0 W0' Σ0 p0, j ≤ n' → world_wf W0 → wext W0 W0' →
              Prel j W0 Σ0 T p0 → Prel j W0' Σ0 T p0) as HPj.
    { intros j ? ? ? ? Hj. apply (proj2 (proj2 (IHn j ltac:(lia)))). }
    apply Prel_S_iff in HP as (Hirr & Hrdy & Hstep).
    apply Prel_S_iff. split_and!.
    { intros Hp. destruct (Hirr Hp) as (v & E & -> & ? & HVv & ?).
      exists v, E. split_and!; [done|done| |done]. by eapply HV. }
    { intros Hp. by eapply ready_p_mono, Hrdy. }
    intros π q Hst. specialize (Hstep π q Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* Q-Tau: rename the placed points away from W', then join *)
      destruct Hstep as (N & W1 & HN & Hfr & HP').
      destruct (Prel_tau_rename n' (w_names W') _ W N W1 Σ T q eq_refl HW Hfr HN HP')
        as (N' & W1' & HN'W & HN' & Hfr' & HP1).
      pose proof (wext_fresh_join W N' W1' W' HW Hfr' HWW' HN'W) as Hfr''.
      exists N', (wjoin W1' W'). split_and!; [done|done|].
      eapply HPj; [lia| |apply wext_join_l|exact HP1].
      * by destruct Hfr' as ((_ & _ & _ & [? _]) & _).
      * by destruct Hfr'' as ((_ & _ & _ & ?) & _).
    + destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists Σ1, m, U, s, k. split_and!; [done|done|].
      intros W'' j Θ2 HW' Hj Hok HVw.
      apply (H W'' j Θ2); [by eapply wext_trans|done..].
    + destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         ? & ? & ? & ? & ? & ? & HVw & HP').
      exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done.
      * eapply HV; done.
      * eapply HPj; [lia|done|done|exact HP'].
    + destruct Hstep as (Σ1 & k & Hhd & ? & HP').
      exists Σ1, k. split_and!; [done|done|]. eapply HPj; [lia|done|done|exact HP'].
    + destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & ? & -> & ? & ? & ? & Hal & HP').
      exists c, d, Σ1, sc, sd, kc, kd. split_and!; [done..| |].
      * destruct HWW' as (_ & He & _). auto.
      * eapply HPj; [lia|done|done|exact HP'].
Qed.

Lemma Vrel_mono n W W' Θ T v :
  world_wf W → wext W W' → Vrel n W Θ T v → Vrel n W' Θ T v.
Proof. apply (proj1 (rel_mono n)). Qed.

Lemma Erel_mono n W W' Θ T F e :
  world_wf W → wext W W' → Erel n W Θ T F e → Erel n W' Θ T F e.
Proof. apply (proj1 (proj2 (rel_mono n))). Qed.

Lemma Prel_mono n W W' Σ T p :
  world_wf W → wext W W' → Prel n W Σ T p → Prel n W' Σ T p.
Proof. apply (proj2 (proj2 (rel_mono n))). Qed.
