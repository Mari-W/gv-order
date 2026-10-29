(** * Monotonicity in the world and frame weakening (§10)

      W ⊑ W′  ⇒  V^W ⊆ V^{W′},  E^W ⊆ E^{W′}        ([Vrel_mono], [Erel_mono])
      F′ ⊆ F  ⇒  E^W_n⟦Θ ⊢ T ≺ F⟧ ⊆ E^W_n⟦Θ ⊢ T ≺ F′⟧  ([Erel_frame])

    Facts only ever help: ready, the frame and every alias the relation
    asks for are positive in ≡ and ≺, and the clauses that quantify
    over future worlds see fewer of them from a larger world. The one
    clause that needs an argument is O-New: the fresh extension W ⊑ₒ W₁
    the term picks is joined with the larger world W′, which stays a
    fresh extension of W′ ([wext_fresh_join]). *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Relation.

(** ** Ingredients *)

Lemma konst_ty_mono (peq plt peq' plt' : tpoint → tpoint → Prop) k T :
  (∀ x y, peq x y → peq' x y) → (∀ x y, plt x y → plt' x y) →
  konst_ty peq plt k T → konst_ty peq' plt' k T.
Proof.
  intros He Hl. destruct 1; econstructor; eauto.
Qed.

Lemma slot_aliases_mono (peq peq' : point → point → Prop) xs m x :
  (∀ x y, peq x y → peq' x y) → slot_aliases peq xs m x → slot_aliases peq' xs m x.
Proof. intros H [? Hx]. split; [done|]. eauto. Qed.

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
    intros W' j Θ2 Θ12 xs HW Hj Hc Hxs HVw.
    destruct (H W' j Θ2 Θ12 xs HW Hj Hc Hxs HVw) as (Θ' & Hext & HE').
    exists Θ'. split; [done|]. by apply IHj.
  - destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & xs &
                       Hhd & Hc & Hxs & HVw & Hext & HE').
    exists Θr, Θ1, Θ2, m, U, s, k, Θ', xs. split_and!; try done. by apply IHj.
  - destruct Hstep as (Θ1 & k & Hhd & HE').
    exists Θ1, k. split; [done|]. by apply IHj.
  - destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                       -> & ? & ? & ? & ? & HE').
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. by apply IHj.
  - intros Hc Hn. destruct (Hstep Hc Hn) as (s & s' & W' & ? & ? & HE').
    exists s, s', W'. split_and!; [done|done|]. by apply IHj.
  - destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
    exists Θ1, Θ2, ub, lb. split_and!; [done|done|]. by apply IHj.
Qed.

(** ** Monotonicity of V and E in the world *)

Lemma Vrel_Erel_mono n :
  (∀ W W' Θ T v, world_wf W → wext W W' → Vrel n W Θ T v → Vrel n W' Θ T v) ∧
  (∀ W W' Θ T F e, world_wf W → wext W W' →
     Erel n W Θ T F e → Erel n W' Θ T F e).
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
      + apply Vrel_lolli_iff. right. exists k, T0. split_and!; [done|done| |done].
        destruct HWW' as (_ & He & Hl & _).
        eapply konst_ty_mono; [| |exact Hk]; unfold tw_eq, tw_lt; auto.
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
  split; [exact HV|].
  intros W W' Θ T F e HW HWW' HE.
  destruct n as [|n']; [apply Erel_0|].
  assert (∀ j W0 W0' Θ0 F0 e0, j ≤ n' → world_wf W0 → wext W0 W0' →
            Erel j W0 Θ0 T F0 e0 → Erel j W0' Θ0 T F0 e0) as HEj.
  { intros j ? ? ? ? ? Hj. apply (proj2 (IHn j ltac:(lia))). }
  apply Erel_S_iff in HE as (Hval & Hrdy & Hstep).
  apply Erel_S_iff. split_and!.
  { intros Hirr. eapply HV; [done|done|]. by apply Hval. }
  { intros Hirr. destruct (Hrdy Hirr). split.
    - by eapply ready_t_mono.
    - by eapply frame_t_mono_w. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
  - eapply HEj; [lia|done|done|exact Hstep].
  - destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W'' j Θ2 Θ12 xs HW' Hj Hc Hxs HVw.
    apply (H W'' j Θ2 Θ12 xs); [by eapply wext_trans|done..].
  - destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & xs &
                       Hhd & Hc & Hxs & HVw & Hext & HE').
    exists Θr, Θ1, Θ2, m, U, s, k, Θ', xs. split_and!; try done.
    + eapply slot_aliases_mono; [|exact Hxs]. by destruct HWW' as (_ & ? & _).
    + eapply HV; done.
    + eapply HEj; [lia|done|done|exact HE'].
  - destruct Hstep as (Θ1 & k & Hhd & HE').
    exists Θ1, k. split; [done|]. eapply HEj; [lia|done|done|exact HE'].
  - destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                       -> & ? & ? & ? & Hal & HE').
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..| |].
    + destruct HWW' as (_ & He & _). auto.
    + eapply HEj; [lia|done|done|exact HE'].
  - (* O-New: join the term's fresh extension with the larger world *)
    intros Hc Hn.
    assert (NChan c ∉ w_names W) as Hn0.
    { destruct HWW' as (Hsub & _). set_solver. }
    destruct (Hstep Hc Hn0) as (s & s' & W1 & Hdu & Hfr & HE').
    pose proof (wext_fresh_join W {[NChan c]} W1 W' HW Hfr HWW'
                  ltac:(set_solver)) as Hfr'.
    exists s, s', (wjoin W1 W'). split_and!; [done|done|].
    eapply HEj; [lia| |apply wext_join_l|exact HE'].
    + destruct Hfr as ((_ & _ & _ & [? _]) & _). done.
    + by destruct Hfr' as ((_ & _ & _ & ?) & _).
  - destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
    exists Θ1, Θ2, ub, lb. split_and!; [done| |].
    + eapply HV; done.
    + eapply HEj; [lia|done|done|exact HE'].
Qed.

Lemma Vrel_mono n W W' Θ T v :
  world_wf W → wext W W' → Vrel n W Θ T v → Vrel n W' Θ T v.
Proof. apply (proj1 (Vrel_Erel_mono n)). Qed.

Lemma Erel_mono n W W' Θ T F e :
  world_wf W → wext W W' → Erel n W Θ T F e → Erel n W' Θ T F e.
Proof. apply (proj2 (Vrel_Erel_mono n)). Qed.

